#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SEO Audit Machine - Streamlit приложение для технического SEO-аудита.

pip install streamlit requests beautifulsoup4 lxml pandas plotly fake-useragent openpyxl urllib3
"""

# === IMPORTS ===
import hashlib
import io
import json
import logging
import os
import re
import socket
import ssl
import threading
import time
import uuid
from collections import Counter, defaultdict, deque
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime
from difflib import SequenceMatcher
from typing import Any, Dict, List, Optional, Set, Tuple
from urllib.parse import (
    parse_qs, urlencode, urljoin, urlparse, urlunparse, quote
)
from urllib.robotparser import RobotFileParser

import pandas as pd
import plotly.express as px
import plotly.graph_objects as go
import requests
import streamlit as st
import urllib3
from bs4 import BeautifulSoup, Comment
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry

try:
    from fake_useragent import UserAgent
    _UA = UserAgent(fallback="Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36")
except Exception:
    _UA = None

# === LOGGING ===
logging.basicConfig(level=logging.INFO, format="%(asctime)s [%(levelname)s] %(message)s")
logger = logging.getLogger("seo_audit")

# === CONSTANTS ===

PENALTY_WEIGHTS = {"critical": 5, "warning": 2, "info": 0}
MAX_CATEGORY_PENALTY = 30

SEVERITY_ORDER = {"critical": 0, "warning": 1, "info": 2}

# Thresholds
TITLE_MIN = 30
TITLE_MAX = 60
DESC_MIN = 70
DESC_MAX = 160
H1_MAX_LEN = 70
THIN_CONTENT_THRESHOLD = 300
VERY_THIN_CONTENT_THRESHOLD = 100
TEXT_HTML_RATIO_LOW = 10
TTFB_WARNING = 1.5
TTFB_CRITICAL = 3.0
MAX_REDIRECTS = 5
LARGE_IMAGE_BYTES = 500 * 1024  # 500KB

IS_RENDER = os.getenv("RENDER", "").lower() == "true" or bool(os.getenv("RENDER_SERVICE_ID"))
MAX_WORKERS = 3 if IS_RENDER else 5
MAX_HTML_SIZE = 2 * 1024 * 1024 if IS_RENDER else 5 * 1024 * 1024  # bytes
MAX_STORED_HTML_CHARS = 120000
MAX_CONTENT_TEXT_CHARS = 12000
MAX_EXTERNAL_CHECKS = 200 if IS_RENDER else 400
MAX_UNCRAWLED_STATUS_CHECKS = 250 if IS_RENDER else 500
UI_MAX_PAGES_LIMIT = 120 if IS_RENDER else 200
UI_DEFAULT_MAX_PAGES = 40 if IS_RENDER else 50

# URL patterns that often cause infinite crawl traps
TRAP_PATTERNS = [
    r'/\?.*page=\d+',
    r'/\?.*sort=',
    r'/\?.*filter=',
    r'/calendar/',
    r'/tag/',
    r'/\d{4}/\d{2}/\d{2}/',
]

RECOMMENDATIONS_RU = {
    "broken_links": {
        "title": "Исправить {count} битых внутренних ссылок (404)",
        "impact": "Поисковые роботы не могут пройти по этим ссылкам -- тратится краулинговый бюджет впустую, а пользователи видят ошибку.",
        "fix": "Настроить 301-редирект на актуальные страницы или обновить/удалить ссылки в навигации и контенте.",
        "effort": "quick",
    },
    "missing_h1": {
        "title": "Добавить заголовок H1 на {count} страниц",
        "impact": "Без H1 поисковик не понимает основную тему страницы. Это напрямую влияет на ранжирование.",
        "fix": "В редакторе страницы добавить один тег H1 с основным ключевым запросом.",
        "effort": "quick",
    },
    "multiple_h1": {
        "title": "Убрать лишние H1 на {count} страницах (оставить по одному)",
        "impact": "Несколько H1 размывают семантический фокус. Поисковик не знает, какой заголовок главный.",
        "fix": "Оставить один H1, остальные понизить до H2 или H3.",
        "effort": "quick",
    },
    "missing_title": {
        "title": "Добавить Title на {count} страниц",
        "impact": "Без Title страница практически невидима в поиске -- сниппет формируется случайно.",
        "fix": "Заполнить поле Title в SEO-настройках каждой страницы (30-60 символов, с ключевым словом).",
        "effort": "medium",
    },
    "empty_title": {
        "title": "Заполнить пустые Title на {count} страницах",
        "impact": "Пустой Title равнозначен его отсутствию -- Google сгенерирует заголовок автоматически, часто неудачно.",
        "fix": "Написать уникальный Title 30-60 символов с ключевым словом для каждой страницы.",
        "effort": "medium",
    },
    "missing_description": {
        "title": "Написать Meta Description для {count} страниц",
        "impact": "Без описания Google/Яндекс показывает случайный текст со страницы -- снижается CTR.",
        "fix": "Написать уникальное описание 150-160 символов с УТП и вхождением ключевого слова.",
        "effort": "medium",
    },
    "duplicate_titles": {
        "title": "Разнести дублирующиеся Title ({count} групп)",
        "impact": "Одинаковые заголовки создают каннибализацию -- страницы конкурируют друг с другом в поиске.",
        "fix": "Сделать каждый Title уникальным, добавив специфику: город, тип услуги, цену.",
        "effort": "medium",
    },
    "duplicate_descriptions": {
        "title": "Сделать уникальными Description ({count} групп)",
        "impact": "Дублирующиеся описания -- сигнал для Google/Яндекс о низком качестве страниц.",
        "fix": "Переписать описания с уникальными формулировками для каждой страницы.",
        "effort": "medium",
    },
    "missing_alt": {
        "title": "Прописать ALT-атрибуты для {count} изображений",
        "impact": "Без ALT картинки не попадают в поиск по изображениям и ухудшается доступность.",
        "fix": "Добавить краткое описание на русском в поле ALT каждого изображения.",
        "effort": "medium",
    },
    "missing_canonical": {
        "title": "Настроить Canonical на {count} страницах",
        "impact": "Без canonical поисковик может выбрать неправильную версию страницы как основную.",
        "fix": "В SEO-настройках указать абсолютный URL (https://...) как canonical для каждой страницы.",
        "effort": "medium",
    },
    "slow_pages": {
        "title": "Ускорить {count} медленных страниц (TTFB > 2 сек)",
        "impact": "Медленная загрузка = потеря пользователей и снижение позиций (Core Web Vitals).",
        "fix": "Сжать изображения, включить Lazy Load, убрать тяжёлые анимации на мобильных.",
        "effort": "complex",
    },
    "no_schema": {
        "title": "Внедрить микроразметку Schema.org",
        "impact": "Без структурированных данных сайт не получает расширенные сниппеты (звёзды, FAQ, хлебные крошки).",
        "fix": "Добавить JSON-LD разметку: Organization, LocalBusiness, FAQPage, BreadcrumbList.",
        "effort": "complex",
    },
    "no_https_redirect": {
        "title": "Настроить редирект HTTP -> HTTPS",
        "impact": "Без редиректа часть трафика идёт на незащищённую версию -- Google может индексировать обе.",
        "fix": "В настройках хостинга/домена включить принудительный HTTPS-редирект (301).",
        "effort": "quick",
    },
    "redirect_chains": {
        "title": "Устранить {count} цепочек редиректов",
        "impact": "Каждый лишний хоп увеличивает время загрузки и тратит краулинговый бюджет.",
        "fix": "Заменить промежуточные редиректы прямым 301 на конечный URL.",
        "effort": "medium",
    },
    "missing_viewport": {
        "title": "Добавить meta viewport на {count} страниц",
        "impact": "Без viewport мобильная версия отображается некорректно -- Google снижает мобильный рейтинг.",
        "fix": 'Добавить <meta name="viewport" content="width=device-width, initial-scale=1"> в head.',
        "effort": "quick",
    },
    "orphan_pages": {
        "title": "Добавить внутренние ссылки на {count} сиротских страниц",
        "impact": "Страницы без входящих ссылок плохо индексируются -- роботы их не находят.",
        "fix": "Добавить ссылки на эти страницы из навигации, блога или связанных разделов.",
        "effort": "medium",
    },
    "thin_content": {
        "title": "Расширить контент на {count} страницах (<300 слов)",
        "impact": "Тонкий контент воспринимается как малоинформативный -- Google/Яндекс не ранжирует такие страницы.",
        "fix": "Дополнить страницы полезным текстом: FAQ, описания услуг, кейсы, инструкции.",
        "effort": "complex",
    },
    "missing_og": {
        "title": "Добавить Open Graph теги на {count} страниц",
        "impact": "Без OG-тегов при расшаривании в соцсетях отображается случайный текст и картинка.",
        "fix": "Прописать og:title, og:description, og:image в настройках каждой страницы.",
        "effort": "medium",
    },
    "missing_charset": {
        "title": "Указать кодировку UTF-8 на {count} страницах",
        "impact": "Без кодировки браузер может неправильно отобразить кириллицу и спецсимволы.",
        "fix": 'Добавить <meta charset="UTF-8"> в начало <head>.',
        "effort": "quick",
    },
    "mixed_content": {
        "title": "Устранить смешанный контент на {count} страницах",
        "impact": "HTTPS-страницы загружающие HTTP-ресурсы помечаются как небезопасные в браузере.",
        "fix": "Обновить все ссылки на ресурсы (картинки, скрипты, стили) на HTTPS-версии.",
        "effort": "medium",
    },
    "heading_hierarchy": {
        "title": "Исправить иерархию заголовков на {count} страницах",
        "impact": "Нарушенная иерархия (H3 перед H2) затрудняет для поисковиков понимание структуры контента.",
        "fix": "Упорядочить заголовки последовательно: H1 -> H2 -> H3, без пропусков уровней.",
        "effort": "medium",
    },
    "noindex_linked": {
        "title": "Проверить {count} страниц с noindex, на которые ведут внутренние ссылки",
        "impact": "Ссылки на noindex-страницы тратят краулинговый бюджет впустую.",
        "fix": "Либо убрать noindex, либо удалить внутренние ссылки на эти страницы.",
        "effort": "medium",
    },
    "no_hreflang": {
        "title": "Настроить hreflang для мультиязычного сайта",
        "impact": "Без hreflang Яндекс и Google могут показывать неправильную языковую версию.",
        "fix": "Добавить теги hreflang для каждой языковой версии страницы.",
        "effort": "complex",
    },
    "yandex_clean_param": {
        "title": "Добавить Clean-param в robots.txt для Яндекса",
        "impact": "Без Clean-param Яндекс индексирует дубли страниц с UTM-метками и фильтрами.",
        "fix": "Добавить директиву Clean-param в robots.txt для параметров utm_*, sort, filter и т.д.",
        "effort": "quick",
    },
}

ERROR_MESSAGES_RU = {
    "invalid_url": "Некорректный URL. Убедитесь, что адрес начинается с https:// или http://",
    "connection_error": "Не удалось подключиться к сайту. Проверьте адрес и доступность.",
    "timeout": "Сайт не ответил за 15 секунд. Возможно, он перегружен.",
    "ssl_error": "Ошибка SSL-сертификата. Сайт может быть небезопасен.",
    "blocked": "Сайт заблокировал запрос (403/429). Попробуйте увеличить задержку.",
    "cloudflare": "Обнаружена защита Cloudflare. Инструмент не может пройти проверку.",
    "no_pages": "Не удалось найти внутренние страницы. Сайт может использовать JS-навигацию.",
    "empty_response": "Сайт вернул пустой ответ. Проверьте, открывается ли он в браузере.",
    "busy": "Сервис сейчас выполняет другой аудит. Подождите завершения и запустите снова.",
}

# JS framework detection patterns
JS_FRAMEWORKS = {
    "Tilda": ["tilda", "t-body", "t-records", "t-store"],
    "Wix": ["wix.com", "_wix", "wixsite"],
    "React": ["__NEXT_DATA__", "_next/", "react-root", "__next"],
    "Vue.js": ["__vue__", "v-app", "nuxt"],
    "Angular": ["ng-version", "ng-app"],
    "WordPress": ["wp-content", "wp-includes", "wordpress"],
    "Bitrix": ["bitrix", "bx-panel"],
    "1C-Bitrix": ["1c-bitrix"],
    "Joomla": ["joomla", "/components/com_"],
    "Drupal": ["drupal", "sites/default/files"],
    "Shopify": ["shopify", "cdn.shopify.com"],
    "Squarespace": ["squarespace"],
    "Webflow": ["webflow"],
    "Modx": ["modx", "assets/components"],
}

COLORS = {
    "primary": "#6366F1",
    "primary_light": "#A5B4FC",
    "primary_dark": "#4338CA",
    "bg_main": "#0F172A",
    "bg_card": "#1E293B",
    "bg_card_hover": "#334155",
    "bg_sidebar": "#0F172A",
    "bg_input": "#1E293B",
    "text_primary": "#F8FAFC",
    "text_secondary": "#94A3B8",
    "text_muted": "#64748B",
    "critical": "#EF4444",
    "critical_bg": "#7F1D1D",
    "warning": "#F59E0B",
    "warning_bg": "#78350F",
    "success": "#10B981",
    "success_bg": "#064E3B",
    "info": "#3B82F6",
    "info_bg": "#1E3A5F",
    "border": "#334155",
    "border_light": "#475569",
    "progress_track": "#1E293B",
    "progress_fill": "#6366F1",
    "chart_palette": [
        "#6366F1", "#10B981", "#F59E0B", "#EF4444", "#3B82F6",
        "#8B5CF6", "#EC4899", "#14B8A6", "#F97316", "#06B6D4",
    ],
}

ICONS = {
    "score": "🏆",
    "pages": "📄",
    "critical": "🔴",
    "warning": "🟡",
    "info": "🔵",
    "success": "🟢",
    "speed": "⚡",
    "link": "🔗",
    "image": "🖼️",
    "code": "🔧",
    "content": "📝",
    "security": "🔒",
    "export": "📥",
    "search": "🔍",
    "chart": "📊",
    "warning_sign": "⚠️",
    "rocket": "🚀",
    "target": "🎯",
    "clock": "🕐",
    "globe": "🌐",
}

EFFORT_LABELS = {
    "quick": "Быстрое исправление (~15 мин)",
    "medium": "Средняя сложность (~1 час)",
    "complex": "Сложное (нужен разработчик)",
}

PLOTLY_LAYOUT = dict(
    template="plotly_dark",
    paper_bgcolor="rgba(0,0,0,0)",
    plot_bgcolor="rgba(0,0,0,0)",
    font=dict(family="Inter, sans-serif", color="#CBD5E1"),
    margin=dict(l=20, r=20, t=40, b=20),
)

LOG_BUFFER: deque[str] = deque(maxlen=200)


class BufferLogHandler(logging.Handler):
    """Копит системные предупреждения для показа в Streamlit-сайдбаре."""

    def emit(self, record: logging.LogRecord) -> None:
        message = self.format(record)
        if record.levelno >= logging.WARNING:
            LOG_BUFFER.append(message)


if not any(isinstance(h, BufferLogHandler) for h in logger.handlers):
    mem_handler = BufferLogHandler()
    mem_handler.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s"))
    logger.addHandler(mem_handler)

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)


@dataclass
class AuditRuntimeGuard:
    """Глобальная блокировка, чтобы не запускать несколько тяжёлых аудитов одновременно."""

    lock: threading.Lock = field(default_factory=threading.Lock)
    active_session_id: str = ""
    started_at: float = 0.0


@st.cache_resource(show_spinner=False)
def get_runtime_guard() -> AuditRuntimeGuard:
    """Возвращает singleton-guard на процесс Streamlit."""
    return AuditRuntimeGuard()


# === DATA CLASSES ===

@dataclass
class PageIssue:
    severity: str       # critical, warning, info
    category: str       # technical, content, links, images, structured_data, security
    code: str           # machine key e.g. missing_h1
    message: str        # human-readable Russian description
    current_value: str = ""
    expected_value: str = ""

    def to_dict(self) -> dict:
        return {
            "severity": self.severity,
            "category": self.category,
            "code": self.code,
            "message": self.message,
            "currentValue": self.current_value,
            "expectedValue": self.expected_value,
        }


@dataclass
class PageResult:
    url: str
    status_code: int = 0
    ttfb: float = 0.0
    content_type: str = ""
    content_length: int = 0
    title: str = ""
    title_length: int = 0
    description: str = ""
    description_length: int = 0
    h1_list: List[str] = field(default_factory=list)
    h1_count: int = 0
    headings: List[Dict[str, str]] = field(default_factory=list)
    word_count: int = 0
    text_html_ratio: float = 0.0
    content_hash: str = ""
    canonical: str = ""
    canonical_status: str = ""  # ok, missing, mismatch, error
    has_meta_robots: bool = False
    meta_robots: str = ""
    x_robots_tag: str = ""
    is_indexable: bool = True
    internal_links: int = 0
    external_links: int = 0
    internal_link_urls: List[str] = field(default_factory=list)
    external_link_urls: List[str] = field(default_factory=list)
    empty_href_links: int = 0
    internal_links_nofollow: int = 0
    broken_links_on_page: List[str] = field(default_factory=list)
    broken_internal_links: int = 0
    broken_external_links: int = 0
    images_total: int = 0
    images_missing_alt: int = 0
    images_empty_alt: int = 0
    images_missing_dimensions: int = 0
    images_broken: int = 0
    images_large: int = 0
    has_schema: bool = False
    schema_types: List[str] = field(default_factory=list)
    has_microdata: bool = False
    has_og: bool = False
    og_tags: Dict[str, str] = field(default_factory=dict)
    has_twitter_card: bool = False
    has_viewport: bool = False
    has_charset: bool = False
    charset_value: str = ""
    has_mixed_content: bool = False
    redirect_chain: List[str] = field(default_factory=list)
    redirect_type: int = 0
    response_headers: Dict[str, str] = field(default_factory=dict)
    has_hsts: bool = False
    crawl_depth: int = 0
    issues: List[PageIssue] = field(default_factory=list)
    error_message: str = ""
    detected_framework: str = ""
    has_lang: bool = False
    lang_value: str = ""
    has_hreflang: bool = False
    hreflang_tags: List[Dict[str, str]] = field(default_factory=list)
    content_text: str = ""
    raw_html: str = ""
    canonical_absolute: str = ""
    canonical_target_status: int = 0
    js_render_warning: bool = False

    def to_dict(self) -> dict:
        return {
            "url": self.url,
            "statusCode": self.status_code,
            "ttfb": round(self.ttfb, 3),
            "contentType": self.content_type,
            "title": self.title,
            "titleLength": self.title_length,
            "description": self.description,
            "descriptionLength": self.description_length,
            "h1List": self.h1_list,
            "h1Count": self.h1_count,
            "headings": self.headings,
            "wordCount": self.word_count,
            "textHtmlRatio": round(self.text_html_ratio, 1),
            "contentHash": self.content_hash,
            "canonical": self.canonical,
            "canonicalStatus": self.canonical_status,
            "isIndexable": self.is_indexable,
            "metaRobots": self.meta_robots,
            "xRobotsTag": self.x_robots_tag,
            "internalLinks": self.internal_links,
            "externalLinks": self.external_links,
            "internalLinkUrls": self.internal_link_urls[:200],
            "externalLinkUrls": self.external_link_urls[:200],
            "emptyHrefLinks": self.empty_href_links,
            "internalLinksNofollow": self.internal_links_nofollow,
            "brokenLinksOnPage": self.broken_links_on_page,
            "brokenInternalLinks": self.broken_internal_links,
            "brokenExternalLinks": self.broken_external_links,
            "imagesTotal": self.images_total,
            "imagesMissingAlt": self.images_missing_alt,
            "imagesEmptyAlt": self.images_empty_alt,
            "imagesMissingDimensions": self.images_missing_dimensions,
            "imagesBroken": self.images_broken,
            "imagesLarge": self.images_large,
            "hasSchema": self.has_schema,
            "schemaTypes": self.schema_types,
            "hasMicrodata": self.has_microdata,
            "hasOg": self.has_og,
            "ogTags": self.og_tags,
            "hasTwitterCard": self.has_twitter_card,
            "hasViewport": self.has_viewport,
            "hasCharset": self.has_charset,
            "hasMixedContent": self.has_mixed_content,
            "redirectChain": self.redirect_chain,
            "hasHsts": self.has_hsts,
            "crawlDepth": self.crawl_depth,
            "issues": [i.to_dict() for i in self.issues],
            "errorMessage": self.error_message,
            "detectedFramework": self.detected_framework,
            "hasLang": self.has_lang,
            "langValue": self.lang_value,
            "hasHreflang": self.has_hreflang,
            "canonicalAbsolute": self.canonical_absolute,
            "canonicalTargetStatus": self.canonical_target_status,
            "jsRenderWarning": self.js_render_warning,
        }


@dataclass
class SiteAuditResult:
    base_url: str
    domain: str
    pages: Dict[str, PageResult] = field(default_factory=dict)
    duration: float = 0.0
    total_scanned: int = 0
    sitemap_urls: Set[str] = field(default_factory=set)
    sitemap_entries: List[Dict[str, str]] = field(default_factory=list)
    sitemap_raw: str = ""
    robots_txt_content: str = ""
    robots_rules: List[Dict[str, str]] = field(default_factory=list)
    robots_sitemaps: List[str] = field(default_factory=list)
    robots_has_host: bool = False
    robots_host_value: str = ""
    robots_has_clean_param: bool = False
    robots_linked_blocked: List[str] = field(default_factory=list)
    ssl_valid: bool = True
    ssl_error: str = ""
    tls_version: str = ""
    http_to_https: bool = False
    www_consistency: str = ""  # "www", "non-www", "inconsistent", "unknown"
    homepage_status_code: int = 0
    homepage_ttfb: float = 0.0
    homepage_headers: Dict[str, str] = field(default_factory=dict)
    detected_frameworks: List[str] = field(default_factory=list)
    has_llms_txt: bool = False
    llms_txt_content: str = ""
    # Cross-page analysis results (filled after crawl)
    duplicate_titles: List[Dict] = field(default_factory=list)
    duplicate_descriptions: List[Dict] = field(default_factory=list)
    duplicate_content: List[Dict] = field(default_factory=list)
    orphan_pages: List[str] = field(default_factory=list)
    deep_pages: List[Dict] = field(default_factory=list)
    zero_inlink_pages: List[str] = field(default_factory=list)
    noindex_linked_pages: List[str] = field(default_factory=list)
    redirect_map: List[Dict] = field(default_factory=list)
    broken_link_map: List[Dict] = field(default_factory=list)
    url_pattern_duplicates: List[Dict[str, Any]] = field(default_factory=list)
    thin_content_clusters: List[Dict[str, Any]] = field(default_factory=list)
    sitemap_vs_crawled: Dict[str, List[str]] = field(default_factory=dict)
    no_structured_data: bool = False
    # Scoring
    health_score: int = 0
    category_scores: Dict[str, int] = field(default_factory=dict)
    # Recommendations
    recommendations: List[Dict] = field(default_factory=list)
    # Stats
    status_codes: Dict[str, int] = field(default_factory=dict)
    issues_by_severity: Dict[str, int] = field(default_factory=dict)
    issues_by_category: Dict[str, Dict[str, int]] = field(default_factory=dict)


# === CRAWLER ENGINE ===

class CrawlerEngine:
    """BFS-based web crawler with parallel fetching."""

    def __init__(
        self,
        start_url: str,
        max_pages: int = 50,
        max_depth: int = 5,
        crawl_delay: float = 0.3,
        respect_robots: bool = True,
        check_external: bool = False,
    ):
        parsed = urlparse(start_url)
        if not parsed.scheme:
            start_url = "https://" + start_url
            parsed = urlparse(start_url)

        self.start_url = start_url
        self.domain = parsed.netloc
        self.scheme = parsed.scheme
        self.base_origin = f"{parsed.scheme}://{parsed.netloc}"
        self.max_pages = max_pages
        self.max_depth = max_depth
        self.crawl_delay = crawl_delay
        self.respect_robots = respect_robots
        self.check_external = check_external
        self.max_workers = MAX_WORKERS

        self.visited: Set[str] = set()
        self.queue: List[Tuple[str, int]] = []
        self.results: Dict[str, PageResult] = {}
        self.all_discovered_links: Set[str] = set()
        self.internal_link_targets: Dict[str, Set[str]] = defaultdict(set)  # target -> set of source pages
        self.external_links_found: Set[str] = set()
        self.page_outgoing_links: Dict[str, Dict[str, Set[str]]] = defaultdict(
            lambda: {"internal": set(), "external": set(), "blocked": set()}
        )
        self.raw_url_variants: Dict[str, Set[str]] = defaultdict(set)

        self.session = requests.Session()
        retry = Retry(
            total=2,
            read=2,
            connect=2,
            backoff_factor=0.7,
            status_forcelist=[500, 502, 503, 504],
            allowed_methods=frozenset(["GET", "HEAD"]),
            raise_on_status=False,
        )
        pool_size = max(10, self.max_workers * 4)
        adapter = HTTPAdapter(max_retries=retry, pool_connections=pool_size, pool_maxsize=pool_size)
        self.session.mount("http://", adapter)
        self.session.mount("https://", adapter)

        ua_string = _UA.random if _UA else (
            "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
            "(KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36"
        )
        self.session.headers.update({
            "User-Agent": ua_string,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "ru-RU,ru;q=0.9,en-US;q=0.8,en;q=0.7",
            "Accept-Encoding": "gzip, deflate, br",
        })
        self.session.max_redirects = MAX_REDIRECTS

        self.robots_parser: Optional[RobotFileParser] = None
        self.robots_txt_content = ""
        self.robots_rules: List[Dict[str, str]] = []
        self.robots_sitemaps: List[str] = []
        self.robots_has_host = False
        self.robots_host_value = ""
        self.robots_has_clean_param = False
        self.sitemap_urls: Set[str] = set()
        self.sitemap_entries: List[Dict[str, str]] = []
        self.sitemap_raw = ""

        self.ssl_valid = True
        self.ssl_error = ""
        self.tls_version = ""
        self.http_to_https = False
        self.www_consistency = "unknown"
        self.homepage_status_code = 0
        self.homepage_ttfb = 0.0
        self.homepage_headers: Dict[str, str] = {}
        self.has_llms_txt = False
        self.llms_txt_content = ""
        self.linked_but_robots_blocked: Set[str] = set()

        self._progress_callback = None
        self._stop_flag = False
        self._url_param_counts: Dict[str, int] = defaultdict(int)

    def _request_headers(self) -> Dict[str, str]:
        """Возвращает заголовки с ротируемым User-Agent."""
        headers = dict(self.session.headers)
        try:
            if _UA:
                headers["User-Agent"] = _UA.random
        except Exception:
            pass
        return headers

    def normalize_url(self, url: str) -> str:
        """Normalize URL: strip fragment, trailing slash (except root), sort query params."""
        try:
            parsed = urlparse(url)
            scheme = parsed.scheme.lower() if parsed.scheme else self.scheme
            netloc = parsed.netloc.lower() if parsed.netloc else self.domain
            path = parsed.path.rstrip("/") or "/"
            path = quote(path, safe="/%:@")
            # Sort query params for deduplication
            qs = parse_qs(parsed.query, keep_blank_values=True)
            sorted_qs = urlencode(sorted(qs.items()), doseq=True)
            return urlunparse((scheme, netloc, path, "", sorted_qs, ""))
        except Exception:
            return url

    def is_internal(self, url: str) -> bool:
        try:
            parsed = urlparse(url)
            if parsed.netloc == "":
                return True
            netloc = parsed.netloc.lower()
            domain = self.domain.lower()
            return netloc == domain or netloc.replace("www.", "") == domain.replace("www.", "")
        except Exception:
            return False

    def is_crawlable_url(self, url: str) -> bool:
        """Check if URL should be crawled (skip non-HTML resources)."""
        parsed = urlparse(url)
        path_lower = parsed.path.lower()
        skip_extensions = {
            ".pdf", ".jpg", ".jpeg", ".png", ".gif", ".svg", ".webp", ".ico",
            ".css", ".js", ".json", ".xml", ".txt", ".zip", ".rar", ".gz",
            ".mp3", ".mp4", ".avi", ".mov", ".wmv", ".doc", ".docx", ".xls",
            ".xlsx", ".ppt", ".pptx", ".woff", ".woff2", ".ttf", ".eot",
        }
        for ext in skip_extensions:
            if path_lower.endswith(ext):
                return False
        return parsed.scheme in ("http", "https", "")

    def is_trap_url(self, url: str) -> bool:
        """Detect infinite crawl traps."""
        for pattern in TRAP_PATTERNS:
            if re.search(pattern, url):
                base = urlparse(url).path.split("?")[0]
                self._url_param_counts[base] += 1
                if self._url_param_counts[base] > 3:
                    return True
        return False

    # --- Pre-crawl checks ---

    def fetch_robots_txt(self) -> None:
        """Fetch and parse robots.txt."""
        robots_url = f"{self.base_origin}/robots.txt"
        try:
            resp = self.session.get(robots_url, timeout=10, headers=self._request_headers())
            if resp.status_code == 200:
                self.robots_txt_content = resp.text
                self._parse_robots_txt(resp.text)
                # Standard RobotFileParser
                self.robots_parser = RobotFileParser()
                self.robots_parser.set_url(robots_url)
                self.robots_parser.parse(resp.text.splitlines())
        except Exception as e:
            logger.warning(f"Failed to fetch robots.txt: {e}")

    def _parse_robots_txt(self, content: str) -> None:
        """Extract rules, sitemaps, Yandex-specific directives from robots.txt."""
        current_ua = "*"
        for line in content.splitlines():
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = line.split(":", 1)
            if len(parts) != 2:
                continue
            directive = parts[0].strip().lower()
            value = parts[1].strip()

            if directive == "user-agent":
                current_ua = value
            elif directive in ("allow", "disallow"):
                self.robots_rules.append({
                    "userAgent": current_ua,
                    "directive": directive.capitalize(),
                    "path": value,
                })
            elif directive == "sitemap":
                self.robots_sitemaps.append(value)
            elif directive == "host":
                self.robots_has_host = True
                self.robots_host_value = value
            elif directive == "clean-param":
                self.robots_has_clean_param = True

    def fetch_sitemap(self) -> None:
        """Fetch and parse sitemap.xml (follows sitemap index)."""
        sitemap_urls_to_check = [f"{self.base_origin}/sitemap.xml"]
        sitemap_urls_to_check.extend(self.robots_sitemaps)
        seen_sitemaps = set()

        for sitemap_url in sitemap_urls_to_check:
            if sitemap_url in seen_sitemaps:
                continue
            seen_sitemaps.add(sitemap_url)
            try:
                resp = self.session.get(sitemap_url, timeout=10, headers=self._request_headers())
                if resp.status_code != 200:
                    continue
                content = resp.content
                if not self.sitemap_raw:
                    self.sitemap_raw = resp.text[:5000]

                soup = BeautifulSoup(content, "lxml-xml")

                # Check for sitemap index
                sitemapindex_locs = soup.find_all("sitemap")
                if sitemapindex_locs:
                    for sm in sitemapindex_locs:
                        loc = sm.find("loc")
                        if loc and loc.text not in seen_sitemaps:
                            sitemap_urls_to_check.append(loc.text.strip())
                    continue

                # Regular sitemap
                for url_tag in soup.find_all("url"):
                    loc = url_tag.find("loc")
                    if loc:
                        normalized = self.normalize_url(loc.text.strip())
                        self.sitemap_urls.add(normalized)
                        lastmod_tag = url_tag.find("lastmod")
                        self.sitemap_entries.append(
                            {
                                "url": normalized,
                                "lastmod": (lastmod_tag.text.strip() if lastmod_tag and lastmod_tag.text else ""),
                            }
                        )
            except Exception as e:
                logger.warning(f"Failed to parse sitemap {sitemap_url}: {e}")

        # Deduplicate entries while preserving first seen lastmod
        unique_entries: Dict[str, Dict[str, str]] = {}
        for item in self.sitemap_entries:
            if item["url"] not in unique_entries:
                unique_entries[item["url"]] = item
        self.sitemap_entries = list(unique_entries.values())

    def check_ssl(self) -> None:
        """Check SSL certificate validity."""
        try:
            requests.get(f"https://{self.domain}", timeout=10, verify=True)
            self.ssl_valid = True
            try:
                context = ssl.create_default_context()
                with socket.create_connection((self.domain, 443), timeout=8) as sock:
                    with context.wrap_socket(sock, server_hostname=self.domain) as secure_sock:
                        self.tls_version = secure_sock.version() or ""
            except Exception:
                self.tls_version = ""
        except requests.exceptions.SSLError as e:
            self.ssl_valid = False
            self.ssl_error = str(e)[:200]
        except Exception:
            pass

    def check_http_redirect(self) -> None:
        """Check if HTTP redirects to HTTPS."""
        try:
            resp = requests.get(
                f"http://{self.domain}",
                timeout=10,
                allow_redirects=True,
                verify=False,
                headers=self._request_headers(),
            )
            final_url = resp.url
            self.http_to_https = urlparse(final_url).scheme == "https"
        except Exception:
            pass

    def check_www_consistency(self) -> None:
        """Check www vs non-www consistency."""
        try:
            domain_parts = self.domain.split(".")
            if self.domain.startswith("www."):
                alt_domain = self.domain[4:]
            else:
                alt_domain = "www." + self.domain

            resp = requests.get(
                f"https://{alt_domain}",
                timeout=10,
                allow_redirects=True,
                verify=False,
                headers=self._request_headers(),
            )
            final_domain = urlparse(resp.url).netloc

            if final_domain == self.domain:
                self.www_consistency = "www" if self.domain.startswith("www.") else "non-www"
            else:
                self.www_consistency = "inconsistent"
        except Exception:
            self.www_consistency = "unknown"

    def check_llms_txt(self) -> None:
        """Check if /llms.txt exists."""
        try:
            resp = self.session.get(f"{self.base_origin}/llms.txt", timeout=10, headers=self._request_headers())
            if resp.status_code == 200 and len(resp.text) > 0:
                self.has_llms_txt = True
                self.llms_txt_content = resp.text[:2000]
        except Exception:
            pass

    def check_homepage(self) -> None:
        """Фиксирует код, TTFB и заголовки главной страницы."""
        try:
            resp = self.session.get(
                self.start_url,
                timeout=15,
                allow_redirects=True,
                headers=self._request_headers(),
            )
            self.homepage_status_code = resp.status_code
            self.homepage_ttfb = resp.elapsed.total_seconds()
            self.homepage_headers = dict(resp.headers)
        except Exception as exc:
            logger.warning("Не удалось проверить главную страницу: %s", exc)

    def run_pre_checks(self, callback=None) -> None:
        """Run all pre-crawl checks."""
        steps = [
            ("Проверка robots.txt...", self.fetch_robots_txt),
            ("Загрузка sitemap.xml...", self.fetch_sitemap),
            ("Проверка SSL...", self.check_ssl),
            ("Проверка HTTP -> HTTPS...", self.check_http_redirect),
            ("Проверка www-консистентности...", self.check_www_consistency),
            ("Проверка llms.txt...", self.check_llms_txt),
            ("Проверка главной страницы...", self.check_homepage),
        ]
        for msg, func in steps:
            if callback:
                callback({"type": "pre_check", "message": msg})
            try:
                func()
            except Exception as e:
                logger.error(f"Pre-check error ({msg}): {e}")

    # --- Main crawl ---

    def crawl(self, progress_callback=None) -> SiteAuditResult:
        """Run BFS crawl and return full audit result."""
        self._progress_callback = progress_callback

        # Pre-checks
        self.run_pre_checks(progress_callback)

        # Start BFS
        start_norm = self.normalize_url(self.start_url)
        self.queue.append((self.start_url, 0))
        self.visited.add(start_norm)

        start_time = time.time()

        while self.queue and len(self.results) < self.max_pages and not self._stop_flag:
            # Take batch from queue
            batch = []
            while self.queue and len(batch) < self.max_workers and (len(self.results) + len(batch)) < self.max_pages:
                batch.append(self.queue.pop(0))

            if not batch:
                break

            # Process batch in parallel
            with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
                futures = {}
                for url, depth in batch:
                    futures[executor.submit(self._fetch_and_analyze, url, depth)] = (url, depth)

                for future in as_completed(futures):
                    url, depth = futures[future]
                    try:
                        page_result, discovered_internal, discovered_external = future.result()
                        if page_result:
                            source_key = self.normalize_url(url)
                            page_result.url = source_key
                            self.results[source_key] = page_result

                            # Report progress
                            if progress_callback:
                                progress_callback({
                                    "type": "page_done",
                                    "url": source_key,
                                    "statusCode": page_result.status_code,
                                    "ttfb": round(page_result.ttfb, 2),
                                    "pagesScanned": len(self.results),
                                    "totalDiscovered": len(self.visited),
                                    "queueSize": len(self.queue),
                                    "errorsCount": sum(
                                        1 for p in self.results.values()
                                        if any(i.severity == "critical" for i in p.issues)
                                    ),
                                })

                            for link in discovered_internal:
                                norm = self.normalize_url(link)
                                self.page_outgoing_links[source_key]["internal"].add(norm)
                                self.raw_url_variants[norm].add(link)
                                self.internal_link_targets[norm].add(source_key)

                                if depth >= self.max_depth:
                                    continue
                                if norm in self.visited or not self.is_internal(link):
                                    continue
                                if not self.is_crawlable_url(link) or self.is_trap_url(link):
                                    continue
                                if self.robots_parser and not self.robots_parser.can_fetch("*", link):
                                    self.linked_but_robots_blocked.add(norm)
                                    self.page_outgoing_links[source_key]["blocked"].add(norm)
                                    if self.respect_robots:
                                        continue
                                self.visited.add(norm)
                                self.queue.append((link, depth + 1))

                            for external_link in discovered_external:
                                self.external_links_found.add(external_link)
                                self.page_outgoing_links[source_key]["external"].add(external_link)

                    except Exception as e:
                        logger.error(f"Error processing {url}: {e}")
                        err_result = PageResult(url=url, error_message=str(e)[:200])
                        err_result.issues.append(PageIssue(
                            "critical", "technical", "crawl_error",
                            f"Ошибка при сканировании: {str(e)[:100]}",
                        ))
                        self.results[self.normalize_url(url)] = err_result
                        if progress_callback:
                            progress_callback({
                                "type": "page_error",
                                "url": self.normalize_url(url),
                                "error": str(e)[:100],
                                "pagesScanned": len(self.results),
                                "totalDiscovered": len(self.visited),
                                "queueSize": len(self.queue),
                            })

            # Crawl delay
            time.sleep(self.crawl_delay)

        unresolved_internal_status = self._resolve_uncrawled_internal_statuses()
        canonical_status_cache = self._resolve_canonical_statuses()
        external_status_cache = {}
        if self.check_external and self.external_links_found:
            external_status_cache = self._check_external_links(progress_callback)

        elapsed = time.time() - start_time

        # Build result
        result = SiteAuditResult(
            base_url=self.start_url,
            domain=self.domain,
            pages=self.results,
            duration=round(elapsed, 2),
            total_scanned=len(self.results),
            sitemap_urls=self.sitemap_urls,
            sitemap_entries=self.sitemap_entries,
            sitemap_raw=self.sitemap_raw,
            robots_txt_content=self.robots_txt_content,
            robots_rules=self.robots_rules,
            robots_sitemaps=self.robots_sitemaps,
            robots_has_host=self.robots_has_host,
            robots_host_value=self.robots_host_value,
            robots_has_clean_param=self.robots_has_clean_param,
            robots_linked_blocked=sorted(self.linked_but_robots_blocked),
            ssl_valid=self.ssl_valid,
            ssl_error=self.ssl_error,
            tls_version=self.tls_version,
            http_to_https=self.http_to_https,
            www_consistency=self.www_consistency,
            homepage_status_code=self.homepage_status_code,
            homepage_ttfb=self.homepage_ttfb,
            homepage_headers=dict(self.homepage_headers),
            has_llms_txt=self.has_llms_txt,
            llms_txt_content=self.llms_txt_content,
        )

        # Run cross-page analysis
        analyzer = SiteAnalyzer(
            result,
            self.internal_link_targets,
            self.sitemap_urls,
            self.page_outgoing_links,
            unresolved_internal_status,
            external_status_cache,
            self.raw_url_variants,
            canonical_status_cache,
        )
        analyzer.analyze()

        # Scoring
        scorer = ReportGenerator(result)
        scorer.calculate_scores()
        scorer.generate_recommendations()

        try:
            self.session.close()
        except Exception:
            pass

        return result

    def stop(self):
        self._stop_flag = True

    def _fetch_url_status(self, url: str, timeout: int = 10) -> int:
        """Возвращает HTTP-статус URL (HEAD -> GET)."""
        try:
            head = self.session.head(
                url,
                timeout=timeout,
                allow_redirects=True,
                verify=True,
                headers=self._request_headers(),
            )
            if head.status_code >= 400 or head.status_code == 405:
                get_resp = self.session.get(
                    url,
                    timeout=timeout,
                    allow_redirects=True,
                    verify=True,
                    headers=self._request_headers(),
                )
                return get_resp.status_code
            return head.status_code
        except requests.exceptions.SSLError:
            try:
                get_resp = self.session.get(
                    url,
                    timeout=timeout,
                    allow_redirects=True,
                    verify=False,
                    headers=self._request_headers(),
                )
                return get_resp.status_code
            except Exception:
                return 0
        except Exception:
            return 0

    def _resolve_uncrawled_internal_statuses(self) -> Dict[str, int]:
        """Проверяет статусы внутренних URL, которые встретились в ссылках, но не были просканированы."""
        unresolved = set()
        crawled_norm = {self.normalize_url(u) for u in self.results.keys()}
        for links in self.page_outgoing_links.values():
            for target in links["internal"]:
                if target not in crawled_norm:
                    unresolved.add(target)

        status_map: Dict[str, int] = {}
        if not unresolved:
            return status_map

        for url in list(unresolved)[:MAX_UNCRAWLED_STATUS_CHECKS]:
            status_map[url] = self._fetch_url_status(url, timeout=8)
        return status_map

    def _resolve_canonical_statuses(self) -> Dict[str, int]:
        """Проверяет коды ответа canonical-URL и сохраняет в страницах."""
        canonical_targets = set()
        for page in self.results.values():
            if page.canonical:
                absolute = page.canonical if page.canonical.startswith("http") else urljoin(page.url, page.canonical)
                absolute = self.normalize_url(absolute)
                page.canonical_absolute = absolute
                canonical_targets.add(absolute)

        if not canonical_targets:
            return {}

        status_cache: Dict[str, int] = {}
        for target in canonical_targets:
            if target in self.results:
                status_cache[target] = self.results[target].status_code
            else:
                status_cache[target] = self._fetch_url_status(target, timeout=8)

        for page in self.results.values():
            if page.canonical_absolute:
                page.canonical_target_status = status_cache.get(page.canonical_absolute, 0)
                if page.canonical_target_status >= 400:
                    page.issues.append(PageIssue(
                        "critical",
                        "technical",
                        "canonical_target_error",
                        "Canonical указывает на URL с ошибкой 4xx/5xx",
                        str(page.canonical_target_status),
                        "200",
                    ))
        return status_cache

    def _check_external_links(self, progress_callback=None) -> Dict[str, int]:
        """Проверяет внешние ссылки (если опция включена)."""
        external_urls = list(self.external_links_found)[:MAX_EXTERNAL_CHECKS]
        status_map: Dict[str, int] = {}
        if not external_urls:
            return status_map

        if progress_callback:
            progress_callback({"type": "pre_check", "message": "Проверка внешних ссылок..."})

        with ThreadPoolExecutor(max_workers=self.max_workers) as executor:
            futures = {executor.submit(self._fetch_url_status, url, 8): url for url in external_urls}
            for future in as_completed(futures):
                status_map[futures[future]] = future.result()
        return status_map

    def _fetch_and_analyze(self, url: str, depth: int) -> Tuple[Optional[PageResult], List[str], List[str]]:
        """Fetch a single page and run per-page analysis."""
        result = PageResult(url=url, crawl_depth=depth)
        discovered_internal: List[str] = []
        discovered_external: List[str] = []

        try:
            resp = self.session.get(
                url, timeout=15, allow_redirects=True, verify=True,
                headers=self._request_headers(),
                stream=True,
            )
        except requests.exceptions.SSLError:
            try:
                resp = self.session.get(
                    url,
                    timeout=15,
                    allow_redirects=True,
                    verify=False,
                    headers=self._request_headers(),
                    stream=True,
                )
            except Exception as e:
                result.error_message = f"SSL + fallback error: {str(e)[:100]}"
                result.issues.append(PageIssue("critical", "security", "ssl_error",
                    "Ошибка SSL-сертификата", str(e)[:100], "Валидный сертификат"))
                return result, [], []
        except requests.exceptions.Timeout:
            result.error_message = "Timeout"
            result.issues.append(PageIssue("critical", "technical", "timeout",
                "Таймаут: сервер не ответил за 15 секунд"))
            return result, [], []
        except requests.exceptions.ConnectionError as e:
            result.error_message = str(e)[:100]
            result.issues.append(PageIssue("critical", "technical", "connection_error",
                "Ошибка соединения"))
            return result, [], []
        except requests.exceptions.InvalidURL as e:
            result.error_message = str(e)[:150]
            result.issues.append(PageIssue("critical", "technical", "invalid_url",
                "Некорректный URL", str(e)[:100], "валидный URL"))
            return result, [], []
        except requests.exceptions.TooManyRedirects:
            result.error_message = "Too many redirects"
            result.issues.append(PageIssue("critical", "technical", "redirect_loop",
                "Бесконечный цикл редиректов", ">5 хопов", "1-2 хопа"))
            return result, [], []
        except Exception as e:
            result.error_message = str(e)[:200]
            return result, [], []

        # Basic response info
        result.url = self.normalize_url(resp.url or url)
        result.status_code = resp.status_code
        result.ttfb = resp.elapsed.total_seconds()
        result.content_type = resp.headers.get("Content-Type", "")
        result.response_headers = {k: v for k, v in resp.headers.items()}
        if "text/html" not in result.content_type.lower():
            result.issues.append(PageIssue(
                "warning",
                "technical",
                "non_html_content",
                "Контент страницы не text/html",
                result.content_type or "unknown",
                "text/html",
            ))
            try:
                resp.close()
            except Exception:
                pass
            return result, [], []

        raw_chunks: List[bytes] = []
        loaded_size = 0
        too_large = False
        content_len_header = resp.headers.get("Content-Length", "").strip()
        declared_size = int(content_len_header) if content_len_header.isdigit() else 0
        if declared_size > MAX_HTML_SIZE:
            too_large = True
        else:
            try:
                for chunk in resp.iter_content(chunk_size=65536):
                    if not chunk:
                        continue
                    loaded_size += len(chunk)
                    if loaded_size > MAX_HTML_SIZE:
                        too_large = True
                        break
                    raw_chunks.append(chunk)
            except Exception:
                pass

        raw_bytes = b"".join(raw_chunks)
        result.content_length = len(raw_bytes) if raw_bytes else declared_size

        try:
            resp.close()
        except Exception:
            pass

        if result.content_length == 0:
            result.issues.append(PageIssue(
                "critical",
                "technical",
                "empty_response",
                "Сайт вернул пустой ответ",
                "0 байт",
                ">0 байт",
            ))
            return result, [], []
        if too_large:
            page_kb = max(result.content_length, declared_size) // 1024
            result.issues.append(PageIssue(
                "warning",
                "technical",
                "large_page",
                f"Слишком большая HTML-страница: {page_kb}KB",
                f"{page_kb}KB",
                f"<{MAX_HTML_SIZE // 1024}KB",
            ))
            return result, [], []

        try:
            encoding = resp.encoding or "utf-8"
            html_text = raw_bytes.decode(encoding, errors="replace")
        except (LookupError, UnicodeDecodeError):
            html_text = raw_bytes.decode("utf-8", errors="replace")
        result.raw_html = html_text[:MAX_STORED_HTML_CHARS]
        # Используем уже загруженный буфер, чтобы анализатор не перечитывал тело ответа.
        resp._content = raw_bytes

        if result.status_code in (403, 429):
            result.issues.append(PageIssue(
                "warning",
                "technical",
                "blocked_by_server",
                "Сайт ограничивает краулинг (403/429). Увеличьте задержку и проверьте доступ.",
                str(result.status_code),
                "200",
            ))
        body_preview = html_text[:2500].lower()
        if "cloudflare" in body_preview and ("attention required" in body_preview or "cf-challenge" in body_preview):
            result.issues.append(PageIssue(
                "warning",
                "technical",
                "cloudflare_protection",
                "Обнаружена защита Cloudflare. Часть страниц может быть недоступна.",
            ))

        # Redirect chain
        if resp.history:
            result.redirect_chain = [r.url for r in resp.history] + [resp.url]
            if len(resp.history) > 0:
                result.redirect_type = resp.history[0].status_code

        # HSTS
        result.has_hsts = "strict-transport-security" in resp.headers

        # X-Robots-Tag
        x_robots = resp.headers.get("X-Robots-Tag", "")
        if x_robots:
            result.x_robots_tag = x_robots
            lower_xrobots = x_robots.lower()
            if "noindex" in lower_xrobots:
                result.is_indexable = False
                result.issues.append(PageIssue(
                    "info",
                    "technical",
                    "xrobots_noindex",
                    "X-Robots-Tag содержит noindex",
                ))
            if "nofollow" in lower_xrobots:
                result.issues.append(PageIssue(
                    "info",
                    "technical",
                    "xrobots_nofollow",
                    "X-Robots-Tag содержит nofollow",
                ))

        # Parse HTML
        try:
            soup = BeautifulSoup(raw_bytes, "lxml")
        except Exception:
            soup = BeautifulSoup(raw_bytes, "html.parser")

        # Run all per-page checks
        page_analyzer = PageAnalyzer(url, resp, soup, result, self.domain, self.base_origin, self.session, self._request_headers)
        page_analyzer.analyze_all()

        # Extract links for crawler
        discovered_internal, discovered_external = page_analyzer.extract_links()
        result.internal_link_urls = [self.normalize_url(x) for x in discovered_internal][:300]
        result.external_link_urls = discovered_external[:300]

        return result, discovered_internal, discovered_external


# === PAGE ANALYZER ===

class PageAnalyzer:
    """Performs all per-page SEO checks."""

    def __init__(self, url: str, response: requests.Response, soup: BeautifulSoup,
                 result: PageResult, domain: str, base_origin: str,
                 session: requests.Session, headers_factory):
        self.url = url
        self.response = response
        self.soup = soup
        self.r = result
        self.domain = domain
        self.base_origin = base_origin
        self.session = session
        self.headers_factory = headers_factory

    def add_issue(self, severity: str, category: str, code: str, message: str,
                  current: str = "", expected: str = ""):
        self.r.issues.append(PageIssue(severity, category, code, message, current, expected))

    def analyze_all(self):
        self._check_url_structure()
        self._check_status()
        self._check_ttfb()
        self._check_redirects()
        self._check_title()
        self._check_description()
        self._check_meta_robots()
        self._check_headings()
        self._check_content()
        self._check_canonical()
        self._check_images()
        self._check_schema()
        self._check_og()
        self._check_twitter()
        self._check_viewport()
        self._check_charset()
        self._check_mixed_content()
        self._check_lang()
        self._check_hreflang()
        self._detect_framework()
        self._detect_js_render_risk()

    def _check_url_structure(self):
        parsed = urlparse(self.url)
        if len(self.url) > 1024:
            self.add_issue(
                "warning",
                "technical",
                "long_url",
                "URL слишком длинный (может мешать индексации)",
                str(len(self.url)),
                "<=1024",
            )
        query_params = parse_qs(parsed.query, keep_blank_values=True)
        if len(query_params) > 6:
            self.add_issue(
                "info",
                "technical",
                "too_many_query_params",
                "Слишком много URL-параметров (риск дублей)",
                str(len(query_params)),
                "<=6",
            )

    def _fetch_resource_info(self, resource_url: str) -> Tuple[int, int]:
        """Возвращает код ответа и размер ресурса (байты)."""
        try:
            head = self.session.head(
                resource_url,
                timeout=8,
                allow_redirects=True,
                verify=True,
                headers=self.headers_factory(),
            )
            size = int(head.headers.get("Content-Length", "0") or "0")
            if head.status_code == 405:
                get_resp = self.session.get(
                    resource_url,
                    timeout=8,
                    allow_redirects=True,
                    verify=True,
                    headers=self.headers_factory(),
                    stream=True,
                )
                size = int(get_resp.headers.get("Content-Length", "0") or "0")
                return get_resp.status_code, size
            return head.status_code, size
        except requests.exceptions.SSLError:
            try:
                get_resp = self.session.get(
                    resource_url,
                    timeout=8,
                    allow_redirects=True,
                    verify=False,
                    headers=self.headers_factory(),
                    stream=True,
                )
                size = int(get_resp.headers.get("Content-Length", "0") or "0")
                return get_resp.status_code, size
            except Exception:
                return 0, 0
        except Exception:
            return 0, 0

    # --- Individual checks ---

    def _check_status(self):
        code = self.r.status_code
        if code >= 500:
            self.add_issue("critical", "technical", "server_error",
                f"Ошибка сервера: {code}", str(code), "200")
        elif code >= 400:
            self.add_issue("critical", "technical", "client_error",
                f"Страница не найдена: {code}", str(code), "200")
        elif 300 <= code < 400:
            self.add_issue("warning", "technical", "redirect",
                f"Редирект: {code}", str(code), "200")

    def _check_ttfb(self):
        ttfb = self.r.ttfb
        if ttfb > TTFB_CRITICAL:
            self.add_issue("critical", "technical", "slow_ttfb",
                f"Очень медленный ответ: {ttfb:.2f}с", f"{ttfb:.2f}с", "<1.5с")
        elif ttfb > TTFB_WARNING:
            self.add_issue("warning", "technical", "slow_ttfb",
                f"Медленный ответ сервера: {ttfb:.2f}с", f"{ttfb:.2f}с", "<1.5с")

    def _check_redirects(self):
        chain = self.r.redirect_chain
        if len(chain) > 2:
            severity = "critical" if len(chain) > 3 else "warning"
            self.add_issue(severity, "technical", "redirect_chain",
                f"Цепочка редиректов: {len(chain)} хопов", f"{len(chain)} хопов", "1-2 хопа")
        if len(chain) > MAX_REDIRECTS:
            self.add_issue("critical", "technical", "redirect_loop",
                "Похоже на цикл редиректов", f"{len(chain)} хопов", "1-2 хопа")

    def _check_title(self):
        title_tag = self.soup.find("title")
        if not title_tag:
            self.add_issue("critical", "content", "missing_title", "Отсутствует тег Title")
            return

        title_text = title_tag.get_text(strip=True)
        self.r.title = title_text
        self.r.title_length = len(title_text)

        if not title_text:
            self.add_issue("critical", "content", "empty_title",
                "Пустой тег Title", "пусто", "30-60 символов")
        elif len(title_text) < TITLE_MIN:
            self.add_issue("warning", "content", "short_title",
                f"Title слишком короткий: {len(title_text)} симв.",
                f"{len(title_text)} симв.", f">{TITLE_MIN} симв.")
        elif len(title_text) > TITLE_MAX:
            self.add_issue("warning", "content", "long_title",
                f"Title слишком длинный: {len(title_text)} симв.",
                f"{len(title_text)} симв.", f"<{TITLE_MAX} симв.")

    def _check_description(self):
        desc_tag = self.soup.find("meta", attrs={"name": re.compile(r"^description$", re.I)})
        if not desc_tag:
            self.add_issue("warning", "content", "missing_description",
                "Отсутствует Meta Description")
            return

        desc_text = desc_tag.get("content", "").strip()
        self.r.description = desc_text
        self.r.description_length = len(desc_text)

        if not desc_text:
            self.add_issue("warning", "content", "empty_description",
                "Пустой Meta Description", "пусто", "70-160 символов")
        elif len(desc_text) < DESC_MIN:
            self.add_issue("info", "content", "short_description",
                f"Description короткий: {len(desc_text)} симв.",
                f"{len(desc_text)} симв.", f">{DESC_MIN} симв.")
        elif len(desc_text) > DESC_MAX:
            self.add_issue("warning", "content", "long_description",
                f"Description длинный: {len(desc_text)} симв.",
                f"{len(desc_text)} симв.", f"<{DESC_MAX} симв.")

    def _check_meta_robots(self):
        meta_robots = self.soup.find("meta", attrs={"name": re.compile(r"^robots$", re.I)})
        if meta_robots:
            content = meta_robots.get("content", "").lower()
            self.r.has_meta_robots = True
            self.r.meta_robots = content
            if "noindex" in content:
                self.r.is_indexable = False
                self.add_issue("info", "technical", "noindex",
                    "Страница закрыта от индексации (meta robots noindex)")
            if "nofollow" in content:
                self.add_issue("info", "technical", "nofollow",
                    "Ссылки на странице не передают вес (meta robots nofollow)")
            for directive in ("noarchive", "nosnippet"):
                if directive in content:
                    self.add_issue("info", "technical", f"meta_{directive}",
                        f"Обнаружен директивный тег robots: {directive}")

    def _check_headings(self):
        # H1
        h1_tags = self.soup.find_all("h1")
        self.r.h1_list = [h.get_text(strip=True) for h in h1_tags]
        self.r.h1_count = len(h1_tags)
        empty_h1_count = sum(1 for h in h1_tags if not h.get_text(strip=True))

        if not h1_tags:
            self.add_issue("critical", "content", "missing_h1",
                "Отсутствует заголовок H1", "0 шт.", "1 шт.")
        elif empty_h1_count > 0:
            self.add_issue("critical", "content", "empty_h1",
                f"Пустой заголовок H1: {empty_h1_count} шт.", str(empty_h1_count), "0")
        if len(h1_tags) > 1:
            self.add_issue("warning", "content", "multiple_h1",
                f"Несколько заголовков H1: {len(h1_tags)} шт.",
                f"{len(h1_tags)} шт.", "1 шт.")
        elif len(h1_tags) == 1:
            h1_text = h1_tags[0].get_text(strip=True)
            if len(h1_text) > H1_MAX_LEN:
                self.add_issue("info", "content", "long_h1",
                    f"H1 слишком длинный: {len(h1_text)} симв.",
                    f"{len(h1_text)} симв.", f"<{H1_MAX_LEN} симв.")

        # H1 vs Title
        if self.r.title and self.r.h1_list:
            if self.r.title.strip().lower() == self.r.h1_list[0].strip().lower():
                self.add_issue("info", "content", "h1_equals_title",
                    "H1 идентичен Title (рекомендуется различать)")

        # Full heading hierarchy in DOM order
        headings = []
        for h in self.soup.find_all(re.compile(r"^h[1-6]$", re.I)):
            level = int(h.name[1])
            headings.append({"level": level, "text": h.get_text(strip=True)[:100]})
        self.r.headings = headings

        # Check hierarchy
        if headings:
            prev_level = 0
            hierarchy_broken = False
            for h in headings:
                if h["level"] > prev_level + 1 and prev_level > 0:
                    hierarchy_broken = True
                    break
                prev_level = h["level"]
            if hierarchy_broken:
                self.add_issue("info", "content", "heading_hierarchy",
                    "Нарушена иерархия заголовков (пропущен уровень)")

    def _check_content(self):
        try:
            clean_soup = BeautifulSoup(self.response.content, "lxml")
        except Exception:
            clean_soup = BeautifulSoup(self.response.content, "html.parser")

        # Remove script/style/comment content for word count
        for elem in clean_soup(["script", "style", "noscript"]):
            elem.decompose()
        # Remove comments
        for comment in clean_soup.find_all(string=lambda t: isinstance(t, Comment)):
            comment.extract()

        text = clean_soup.get_text(separator=" ", strip=True)
        words = text.split()
        self.r.word_count = len(words)
        self.r.content_text = re.sub(r"\s+", " ", text).strip()[:MAX_CONTENT_TEXT_CHARS]

        # Content hash
        clean_text = re.sub(r"\s+", " ", text.lower().strip())
        self.r.content_hash = hashlib.md5(clean_text.encode("utf-8")).hexdigest()

        # Text to HTML ratio
        html_len = self.r.content_length
        text_len = len(text.encode("utf-8"))
        self.r.text_html_ratio = (text_len / max(1, html_len)) * 100

        # Thin content checks
        is_blog_like = "/blog" in self.url.lower() or "/news" in self.url.lower()

        if self.r.word_count < VERY_THIN_CONTENT_THRESHOLD:
            self.add_issue("critical", "content", "very_thin_content",
                f"Очень мало контента: {self.r.word_count} слов",
                f"{self.r.word_count} слов", f">{THIN_CONTENT_THRESHOLD} слов")
        elif self.r.word_count < THIN_CONTENT_THRESHOLD and not is_blog_like:
            self.add_issue("warning", "content", "thin_content",
                f"Мало контента: {self.r.word_count} слов",
                f"{self.r.word_count} слов", f">{THIN_CONTENT_THRESHOLD} слов")

        if self.r.text_html_ratio < TEXT_HTML_RATIO_LOW:
            self.add_issue("info", "content", "low_text_ratio",
                f"Низкий текст/HTML: {self.r.text_html_ratio:.1f}%",
                f"{self.r.text_html_ratio:.1f}%", f">{TEXT_HTML_RATIO_LOW}%")

    def _check_canonical(self):
        canonical_tags = self.soup.find_all("link", attrs={"rel": "canonical"})

        if not canonical_tags:
            self.r.canonical_status = "missing"
            self.add_issue("warning", "technical", "missing_canonical",
                "Отсутствует тег Canonical")
            return

        if len(canonical_tags) > 1:
            self.add_issue("critical", "technical", "multiple_canonical",
                f"Найдено {len(canonical_tags)} тегов Canonical",
                f"{len(canonical_tags)} шт.", "1 шт.")

        canonical_href = canonical_tags[0].get("href", "").strip()
        self.r.canonical = canonical_href

        if not canonical_href:
            self.r.canonical_status = "error"
            self.add_issue("warning", "technical", "empty_canonical",
                "Пустой тег Canonical")
            return

        # Check relative
        if not canonical_href.startswith("http"):
            self.add_issue("warning", "technical", "relative_canonical",
                "Canonical содержит относительный URL",
                canonical_href, "https://...")
        absolute_canonical = canonical_href if canonical_href.startswith("http") else urljoin(self.url, canonical_href)
        self.r.canonical_absolute = absolute_canonical

        # Check protocol mismatch
        parsed_page = urlparse(self.url)
        parsed_can = urlparse(absolute_canonical)
        if parsed_page.scheme == "https" and parsed_can.scheme == "http":
            self.add_issue("critical", "technical", "canonical_http",
                "Canonical ссылается на HTTP (страница HTTPS)",
                canonical_href, f"https://{parsed_can.netloc}{parsed_can.path}")

        # Check self-referencing
        norm_page = self.url.rstrip("/")
        norm_can = absolute_canonical.rstrip("/")
        if norm_can and norm_can != norm_page:
            self.r.canonical_status = "other"
            self.add_issue("warning", "technical", "canonical_not_self",
                "Canonical не является self-referencing",
                canonical_href, self.url)
        else:
            self.r.canonical_status = "ok"

    def _check_images(self):
        # Re-parse from original response for images (content was decomposed above)
        try:
            img_soup = BeautifulSoup(self.response.content, "lxml")
        except Exception:
            img_soup = BeautifulSoup(self.response.content, "html.parser")

        images = img_soup.find_all("img")
        self.r.images_total = len(images)
        missing_alt = 0
        empty_alt_non_decorative = 0
        missing_dims = 0
        broken_images = 0
        large_images = 0
        checked = 0

        for img in images:
            alt = img.get("alt")
            src = (img.get("src") or "").strip()

            if alt is None:
                missing_alt += 1
            elif alt.strip() == "":
                is_decorative = any(marker in src.lower() for marker in ["icon", "logo", "sprite", "spacer"])
                if not is_decorative:
                    empty_alt_non_decorative += 1

            if not img.get("width") and not img.get("height"):
                # Check for style attribute
                style = img.get("style", "")
                if "width" not in style and "height" not in style:
                    missing_dims += 1

            if src and checked < 15:
                checked += 1
                abs_img = urljoin(self.url, src)
                status, content_len = self._fetch_resource_info(abs_img)
                if status >= 400:
                    broken_images += 1
                if content_len > LARGE_IMAGE_BYTES:
                    large_images += 1

        self.r.images_missing_alt = missing_alt
        self.r.images_empty_alt = empty_alt_non_decorative
        self.r.images_missing_dimensions = missing_dims
        self.r.images_broken = broken_images
        self.r.images_large = large_images

        if missing_alt > 0:
            self.add_issue("warning", "images", "missing_alt",
                f"{missing_alt} изображений без атрибута ALT",
                f"{missing_alt} шт.", "0 шт.")
        if empty_alt_non_decorative > 0:
            self.add_issue("info", "images", "empty_alt_non_decorative",
                f"{empty_alt_non_decorative} изображений с пустым ALT",
                f"{empty_alt_non_decorative} шт.", "ALT с описанием")

        if missing_dims > 0:
            self.add_issue("warning", "images", "missing_dimensions",
                f"{missing_dims} изображений без width/height (CLS)",
                f"{missing_dims} шт.", "0 шт.")
        if broken_images > 0:
            self.add_issue("warning", "images", "broken_images",
                f"{broken_images} битых изображений (4xx/5xx)",
                f"{broken_images} шт.", "0 шт.")
        if large_images > 0:
            self.add_issue("info", "images", "large_images",
                f"{large_images} тяжёлых изображений (>500KB)",
                f"{large_images} шт.", "0 шт.")

    def _check_schema(self):
        # Re-parse for schema (we decomposed scripts above)
        try:
            schema_soup = BeautifulSoup(self.response.content, "lxml")
        except Exception:
            schema_soup = BeautifulSoup(self.response.content, "html.parser")

        ld_scripts = schema_soup.find_all("script", type="application/ld+json")
        if ld_scripts:
            self.r.has_schema = True
            for script in ld_scripts:
                try:
                    payload = script.string or script.get_text() or ""
                    data = json.loads(payload)
                    if isinstance(data, dict):
                        t = data.get("@type", "")
                        if t:
                            self.r.schema_types.append(t)
                    elif isinstance(data, list):
                        for item in data:
                            if isinstance(item, dict):
                                t = item.get("@type", "")
                                if t:
                                    self.r.schema_types.append(t)
                except (json.JSONDecodeError, TypeError):
                    self.add_issue("warning", "structured_data", "invalid_json_ld",
                        "Невалидный JSON-LD (ошибка парсинга)")
        # Microdata
        if schema_soup.find(attrs={"itemscope": True}):
            self.r.has_microdata = True

    def _check_og(self):
        og_title = self.soup.find("meta", property="og:title")
        og_desc = self.soup.find("meta", property="og:description")
        og_image = self.soup.find("meta", property="og:image")

        if og_title:
            self.r.has_og = True
            self.r.og_tags["title"] = og_title.get("content", "")
        if og_desc:
            self.r.og_tags["description"] = og_desc.get("content", "")
        if og_image:
            self.r.og_tags["image"] = og_image.get("content", "")

        if not og_title:
            self.add_issue("info", "structured_data", "missing_og_title", "Нет og:title")
        if not og_desc:
            self.add_issue("info", "structured_data", "missing_og_desc", "Нет og:description")
        if not og_image:
            self.add_issue("info", "structured_data", "missing_og_image", "Нет og:image")

    def _check_twitter(self):
        tc = self.soup.find("meta", attrs={"name": "twitter:card"})
        if tc:
            self.r.has_twitter_card = True
        else:
            self.add_issue("info", "structured_data", "missing_twitter",
                "Нет Twitter Card мета-тега")

    def _check_viewport(self):
        vp = self.soup.find("meta", attrs={"name": "viewport"})
        if vp:
            self.r.has_viewport = True
        else:
            self.add_issue("critical", "technical", "missing_viewport",
                "Нет мета-тега Viewport (не адаптивно для мобильных)")

    def _check_charset(self):
        charset_meta = self.soup.find("meta", charset=True)
        if charset_meta:
            self.r.has_charset = True
            self.r.charset_value = charset_meta.get("charset", "")
            if self.r.charset_value.lower() not in ("utf-8", "utf8"):
                self.add_issue("warning", "technical", "wrong_charset",
                    f"Кодировка не UTF-8: {self.r.charset_value}",
                    self.r.charset_value, "UTF-8")
        else:
            # Check Content-Type header for charset
            ct = self.r.content_type
            if "charset" in ct.lower():
                self.r.has_charset = True
            else:
                # Check meta http-equiv
                http_equiv = self.soup.find("meta", attrs={"http-equiv": re.compile(r"content-type", re.I)})
                if http_equiv:
                    self.r.has_charset = True
                else:
                    self.add_issue("warning", "technical", "missing_charset",
                        "Не указана кодировка страницы")

    def _check_mixed_content(self):
        """Check for HTTP resources on HTTPS page."""
        if urlparse(self.url).scheme != "https":
            return

        try:
            mc_soup = BeautifulSoup(self.response.content, "lxml")
        except Exception:
            mc_soup = BeautifulSoup(self.response.content, "html.parser")

        mixed = False
        for tag, attr in [("img", "src"), ("script", "src"), ("link", "href"),
                          ("iframe", "src"), ("source", "src"), ("video", "src"),
                          ("audio", "src")]:
            for elem in mc_soup.find_all(tag, attrs={attr: True}):
                src = elem.get(attr, "")
                if src.startswith("http://") and not src.startswith("http://localhost"):
                    mixed = True
                    break
            if mixed:
                break

        if mixed:
            self.r.has_mixed_content = True
            self.add_issue("warning", "security", "mixed_content",
                "Смешанный контент: HTTPS-страница загружает HTTP-ресурсы")

    def _check_lang(self):
        html_tag = self.soup.find("html")
        if html_tag and html_tag.get("lang"):
            self.r.has_lang = True
            self.r.lang_value = html_tag.get("lang", "")
        else:
            self.add_issue("info", "technical", "missing_lang",
                "Не указан атрибут lang у тега <html>")

    def _check_hreflang(self):
        hreflangs = self.soup.find_all("link", attrs={"hreflang": True})
        if hreflangs:
            self.r.has_hreflang = True
            for hl in hreflangs:
                self.r.hreflang_tags.append({
                    "lang": hl.get("hreflang", ""),
                    "href": hl.get("href", ""),
                })
        elif self.r.has_lang and self.r.lang_value.lower().startswith(("en", "ru", "de", "fr", "es")):
            self.add_issue("info", "technical", "missing_hreflang",
                "Не найден hreflang (проверьте, если сайт мультиязычный)")

    def _detect_framework(self):
        html_str = self.response.text[:5000].lower()
        detected = []
        for name, patterns in JS_FRAMEWORKS.items():
            for pat in patterns:
                if pat.lower() in html_str:
                    detected.append(name)
                    break
        if detected:
            self.r.detected_framework = detected[0]

    def _detect_js_render_risk(self):
        script_count = len(self.soup.find_all("script"))
        if script_count > 15 and self.r.word_count < 80:
            self.r.js_render_warning = True
            self.add_issue(
                "info",
                "technical",
                "js_rendering_risk",
                "Похоже, контент формируется через JavaScript. Часть данных может быть недоступна обычному краулеру.",
            )

    def extract_links(self) -> Tuple[List[str], List[str]]:
        """Extract all links from page for crawler."""
        try:
            link_soup = BeautifulSoup(self.response.content, "lxml")
        except Exception:
            link_soup = BeautifulSoup(self.response.content, "html.parser")

        internal_links: List[str] = []
        external_links: List[str] = []
        internal = 0
        external = 0
        nofollow_internal = 0
        empty_href = 0

        for a in link_soup.find_all("a"):
            href = (a.get("href") or "").strip()
            if not href or href == "#":
                empty_href += 1
                continue
            if href.startswith(("javascript:", "mailto:", "tel:")):
                continue

            abs_url = urljoin(self.url, href)
            parsed = urlparse(abs_url)

            if parsed.scheme not in ("http", "https"):
                continue

            is_int = (
                parsed.netloc == self.domain
                or parsed.netloc == ""
                or parsed.netloc.replace("www.", "") == self.domain.replace("www.", "")
            )
            if is_int:
                internal += 1
                internal_links.append(abs_url)
                # Check nofollow on internal
                rel = a.get("rel", [])
                if isinstance(rel, list):
                    if "nofollow" in rel:
                        nofollow_internal += 1
                elif "nofollow" in str(rel):
                    nofollow_internal += 1
            else:
                external += 1
                external_links.append(abs_url)

        self.r.internal_links = internal
        self.r.external_links = external
        self.r.empty_href_links = empty_href
        self.r.internal_links_nofollow = nofollow_internal

        if nofollow_internal > 0:
            self.add_issue("warning", "links", "nofollow_internal",
                f"{nofollow_internal} внутренних ссылок с nofollow",
                f"{nofollow_internal} шт.", "0 шт.")
        if empty_href > 0:
            self.add_issue("info", "links", "empty_href_links",
                f"{empty_href} ссылок с пустым href или #",
                f"{empty_href} шт.", "0 шт.")

        return list(dict.fromkeys(internal_links)), list(dict.fromkeys(external_links))


# === SITE ANALYZER (Cross-page) ===

class SiteAnalyzer:
    """Cross-page analysis after all pages are crawled."""

    def __init__(self, result: SiteAuditResult,
                 internal_link_targets: Dict[str, Set[str]],
                 sitemap_urls: Set[str],
                 outgoing_links: Dict[str, Dict[str, Set[str]]],
                 unresolved_internal_status: Dict[str, int],
                 external_status: Dict[str, int],
                 raw_url_variants: Dict[str, Set[str]],
                 canonical_status_cache: Dict[str, int]):
        self.result = result
        self.link_targets = internal_link_targets
        self.sitemap_urls = sitemap_urls
        self.outgoing_links = outgoing_links
        self.unresolved_internal_status = unresolved_internal_status
        self.external_status = external_status
        self.raw_url_variants = raw_url_variants
        self.canonical_status_cache = canonical_status_cache

    def analyze(self):
        self._find_duplicate_titles()
        self._find_duplicate_descriptions()
        self._find_duplicate_content()
        self._find_orphan_pages()
        self._find_deep_pages()
        self._find_zero_inlinks()
        self._find_noindex_linked()
        self._build_redirect_map()
        self._build_broken_link_map()
        self._find_url_pattern_duplicates()
        self._find_thin_content_clusters()
        self._mark_robots_linked_blocked()
        self._check_no_structured_data()
        self._compare_sitemap()
        self._compute_status_distribution()
        self._compute_issue_stats()
        self._detect_frameworks()

    def _find_duplicate_titles(self):
        title_groups: Dict[str, List[str]] = defaultdict(list)
        for url, page in self.result.pages.items():
            if page.title:
                title_groups[page.title].append(url)

        self.result.duplicate_titles = [
            {"title": title, "urls": urls}
            for title, urls in title_groups.items()
            if len(urls) > 1
        ]
        for group in self.result.duplicate_titles:
            for url in group["urls"]:
                self.result.pages[url].issues.append(PageIssue(
                    "warning",
                    "content",
                    "duplicate_title",
                    "Дублирующийся Title на нескольких страницах",
                    group["title"][:90],
                    "Уникальный Title",
                ))

    def _find_duplicate_descriptions(self):
        desc_groups: Dict[str, List[str]] = defaultdict(list)
        for url, page in self.result.pages.items():
            if page.description:
                desc_groups[page.description].append(url)

        self.result.duplicate_descriptions = [
            {"description": desc, "urls": urls}
            for desc, urls in desc_groups.items()
            if len(urls) > 1
        ]
        for group in self.result.duplicate_descriptions:
            for url in group["urls"]:
                self.result.pages[url].issues.append(PageIssue(
                    "warning",
                    "content",
                    "duplicate_description",
                    "Дублирующийся Meta Description",
                    group["description"][:90],
                    "Уникальный Description",
                ))

    def _find_duplicate_content(self):
        hash_groups: Dict[str, List[str]] = defaultdict(list)
        for url, page in self.result.pages.items():
            if page.content_hash:
                hash_groups[page.content_hash].append(url)

        duplicate_groups = [
            {"urls": urls}
            for h, urls in hash_groups.items()
            if len(urls) > 1
        ]

        # Approximate duplicates (>90%) for non-identical hashes
        text_items = [(u, p.content_text) for u, p in self.result.pages.items() if p.content_text]
        used_pairs = set()
        similar_map: Dict[str, Set[str]] = defaultdict(set)
        for i in range(len(text_items)):
            u1, t1 = text_items[i]
            if len(t1) < 300:
                continue
            for j in range(i + 1, len(text_items)):
                u2, t2 = text_items[j]
                if (u1, u2) in used_pairs:
                    continue
                used_pairs.add((u1, u2))
                if abs(len(t1) - len(t2)) > max(len(t1), len(t2)) * 0.25:
                    continue
                ratio = SequenceMatcher(None, t1[:4000], t2[:4000]).ratio()
                if ratio >= 0.9:
                    similar_map[u1].add(u2)
                    similar_map[u2].add(u1)

        seen = set()
        for url, neighbors in similar_map.items():
            if url in seen:
                continue
            cluster = {url}
            queue = [url]
            while queue:
                node = queue.pop()
                if node in seen:
                    continue
                seen.add(node)
                cluster.add(node)
                for nxt in similar_map.get(node, set()):
                    if nxt not in seen:
                        queue.append(nxt)
            if len(cluster) > 1:
                duplicate_groups.append({"urls": sorted(cluster)})

        self.result.duplicate_content = duplicate_groups
        for group in self.result.duplicate_content:
            for url in group["urls"]:
                self.result.pages[url].issues.append(PageIssue(
                    "warning",
                    "content",
                    "duplicate_content",
                    "Высокое совпадение контента (>90%) с другими страницами",
                ))

    def _find_orphan_pages(self):
        link_targets_norm = {self.normalize_url(u) for u in self.link_targets.keys()}
        base_norm = self.normalize_url(self.result.base_url)
        for sitemap_url in self.sitemap_urls:
            normed = self.normalize_url(sitemap_url)
            if normed == base_norm:
                continue
            if normed not in link_targets_norm:
                self.result.orphan_pages.append(sitemap_url)

    def _find_deep_pages(self):
        for url, page in self.result.pages.items():
            if page.crawl_depth > 3:
                self.result.deep_pages.append({
                    "url": url,
                    "depth": page.crawl_depth,
                })

    def _find_zero_inlinks(self):
        for url in self.result.pages.keys():
            sources = self.link_targets.get(url, set())
            if len(sources) == 0 and self.normalize_url(self.result.base_url) != url:
                self.result.zero_inlink_pages.append(url)
                self.result.pages[url].issues.append(PageIssue(
                    "warning",
                    "links",
                    "zero_inlinks",
                    "На страницу не ведут внутренние ссылки",
                ))

    def _find_noindex_linked(self):
        for url, page in self.result.pages.items():
            if not page.is_indexable and len(self.link_targets.get(url, set())) > 0:
                self.result.noindex_linked_pages.append(url)

    def _build_redirect_map(self):
        for url, page in self.result.pages.items():
            if page.redirect_chain and len(page.redirect_chain) > 1:
                self.result.redirect_map.append({
                    "chain": page.redirect_chain,
                    "hops": len(page.redirect_chain) - 1,
                    "type": page.redirect_type,
                })

    def _build_broken_link_map(self):
        broken_internal_counter: Dict[str, int] = defaultdict(int)
        broken_external_counter: Dict[str, int] = defaultdict(int)

        for source_url, links in self.outgoing_links.items():
            for target in links["internal"]:
                if target in self.result.pages:
                    code = self.result.pages[target].status_code
                else:
                    code = self.unresolved_internal_status.get(target, 0)
                if code >= 400:
                    broken_internal_counter[source_url] += 1
                    self.result.broken_link_map.append({
                        "source": source_url,
                        "brokenUrl": target,
                        "statusCode": code,
                    })

            for ext in links["external"]:
                code = self.external_status.get(ext, 200)
                if self.external_status and code >= 400:
                    broken_external_counter[source_url] += 1

        for source, count in broken_internal_counter.items():
            page = self.result.pages.get(source)
            if not page:
                continue
            page.broken_internal_links = count
            page.issues.append(PageIssue(
                "critical",
                "links",
                "broken_internal_links",
                f"Битые внутренние ссылки: {count} шт.",
                str(count),
                "0",
            ))

        for source, count in broken_external_counter.items():
            page = self.result.pages.get(source)
            if not page or count <= 0:
                continue
            page.broken_external_links = count
            page.issues.append(PageIssue(
                "warning",
                "links",
                "broken_external_links",
                f"Битые внешние ссылки: {count} шт.",
                str(count),
                "0",
            ))

    def _find_url_pattern_duplicates(self):
        for norm, variants in self.raw_url_variants.items():
            cleaned = sorted({v.rstrip("/") for v in variants})
            if len(cleaned) > 1:
                self.result.url_pattern_duplicates.append({
                    "normalized": norm,
                    "variants": cleaned[:10],
                })

    def _find_thin_content_clusters(self):
        clusters: Dict[str, List[str]] = defaultdict(list)
        for url, page in self.result.pages.items():
            if page.word_count < THIN_CONTENT_THRESHOLD:
                path = urlparse(url).path.strip("/")
                root = path.split("/")[0] if path else "/"
                clusters[root].append(url)
        for root, urls in clusters.items():
            if len(urls) >= 2:
                self.result.thin_content_clusters.append({"directory": root, "urls": urls})

    def _mark_robots_linked_blocked(self):
        # Отмечаем как site-wide сигнал в рекомендациях, чтобы не спамить по каждой странице.
        return

    def _check_no_structured_data(self):
        has_any_schema = any(p.has_schema or p.has_microdata for p in self.result.pages.values())
        self.result.no_structured_data = not has_any_schema

    def _compare_sitemap(self):
        crawled_normed = set()
        for url in self.result.pages:
            parsed = urlparse(url)
            normed = urlunparse((parsed.scheme, parsed.netloc, parsed.path.rstrip("/") or "/", "", "", ""))
            crawled_normed.add(normed)

        sitemap_normed = set()
        for url in self.sitemap_urls:
            parsed = urlparse(url)
            normed = urlunparse((parsed.scheme, parsed.netloc, parsed.path.rstrip("/") or "/", "", "", ""))
            sitemap_normed.add(normed)

        only_sitemap = list(sitemap_normed - crawled_normed)
        only_crawled = list(crawled_normed - sitemap_normed)

        self.result.sitemap_vs_crawled = {
            "onlyInSitemap": only_sitemap[:50],
            "onlyInCrawl": only_crawled[:50],
            "sitemapTotal": len(self.sitemap_urls),
            "crawledTotal": len(self.result.pages),
            "overlap": len(sitemap_normed & crawled_normed),
        }

    def _compute_status_distribution(self):
        codes: Dict[str, int] = defaultdict(int)
        for page in self.result.pages.values():
            codes[str(page.status_code)] = codes.get(str(page.status_code), 0) + 1
        self.result.status_codes = dict(codes)

    def _compute_issue_stats(self):
        by_severity: Dict[str, int] = defaultdict(int)
        by_category: Dict[str, Dict[str, int]] = defaultdict(lambda: defaultdict(int))

        for page in self.result.pages.values():
            for issue in page.issues:
                by_severity[issue.severity] += 1
                by_category[issue.category][issue.severity] += 1

        self.result.issues_by_severity = dict(by_severity)
        self.result.issues_by_category = {k: dict(v) for k, v in by_category.items()}

    def _detect_frameworks(self):
        frameworks = set()
        for page in self.result.pages.values():
            if page.detected_framework:
                frameworks.add(page.detected_framework)
        self.result.detected_frameworks = list(frameworks)

    def normalize_url(self, url: str) -> str:
        try:
            parsed = urlparse(url)
            path = parsed.path.rstrip("/") or "/"
            return urlunparse((parsed.scheme.lower(), parsed.netloc.lower(), path, "", parsed.query, ""))
        except Exception:
            return url


# === REPORT GENERATOR (Scoring + Recommendations) ===

class ReportGenerator:
    """Calculates scores and generates recommendations."""

    def __init__(self, result: SiteAuditResult):
        self.result = result

    def calculate_scores(self):
        if not self.result.pages:
            return

        # Category scores + cap category penalty to 30 as requested
        categories = {
            "technical": ["technical", "security"],
            "content": ["content"],
            "images": ["images"],
            "links": ["links"],
            "structured_data": ["structured_data"],
        }

        pages_count = max(1, self.result.total_scanned)
        category_penalties: Dict[str, float] = {}
        for cat_name, cat_keys in categories.items():
            cat_penalty = 0
            for page in self.result.pages.values():
                for issue in page.issues:
                    if issue.category in cat_keys:
                        cat_penalty += PENALTY_WEIGHTS.get(issue.severity, 0)
            # Нормализуем к размеру сайта, чтобы крупные сайты не падали в 0 автоматически.
            normalized = min(MAX_CATEGORY_PENALTY, (cat_penalty / pages_count) * 6)
            category_penalties[cat_name] = normalized
            cat_score = max(0, int(100 - (normalized / MAX_CATEGORY_PENALTY) * 100))
            self.result.category_scores[cat_name] = cat_score

        # Итоговый score считаем как усреднение категорий после cap,
        # иначе крупные сайты всегда получают 0 даже при умеренных проблемах.
        if self.result.category_scores:
            avg_score = sum(self.result.category_scores.values()) / len(self.result.category_scores)
            self.result.health_score = int(max(0, min(100, round(avg_score))))
        else:
            self.result.health_score = 0

    def generate_recommendations(self):
        """Group issues into actionable recommendations."""
        recs: List[Dict] = []
        issue_code_urls: Dict[str, List[str]] = defaultdict(list)

        for url, page in self.result.pages.items():
            for issue in page.issues:
                issue_code_urls[issue.code].append(url)

        # Map issue codes to recommendation templates
        code_to_rec = {
            "client_error": "broken_links",
            "server_error": "broken_links",
            "broken_internal_links": "broken_links",
            "missing_h1": "missing_h1",
            "empty_h1": "missing_h1",
            "multiple_h1": "multiple_h1",
            "missing_title": "missing_title",
            "empty_title": "empty_title",
            "missing_description": "missing_description",
            "empty_description": "missing_description",
            "missing_alt": "missing_alt",
            "missing_canonical": "missing_canonical",
            "slow_ttfb": "slow_pages",
            "no_schema": "no_schema",
            "redirect_chain": "redirect_chains",
            "missing_viewport": "missing_viewport",
            "thin_content": "thin_content",
            "very_thin_content": "thin_content",
            "missing_og_title": "missing_og",
            "missing_og_desc": "missing_og",
            "missing_og_image": "missing_og",
            "missing_charset": "missing_charset",
            "mixed_content": "mixed_content",
            "heading_hierarchy": "heading_hierarchy",
            "canonical_target_error": "missing_canonical",
            "canonical_not_self": "missing_canonical",
            "broken_external_links": "broken_links",
        }

        seen_recs = set()
        for code, urls in issue_code_urls.items():
            rec_key = code_to_rec.get(code)
            if not rec_key or rec_key in seen_recs:
                continue
            seen_recs.add(rec_key)

            template = RECOMMENDATIONS_RU.get(rec_key)
            if not template:
                continue

            # Determine severity from the issues
            severity = "info"
            for page in self.result.pages.values():
                for issue in page.issues:
                    if issue.code == code:
                        if SEVERITY_ORDER.get(issue.severity, 2) < SEVERITY_ORDER.get(severity, 2):
                            severity = issue.severity

            unique_urls = list(set(urls))[:20]
            count = len(set(urls))

            recs.append({
                "key": rec_key,
                "title": template["title"].format(count=count),
                "impact": template["impact"],
                "fix": template["fix"],
                "effort": template["effort"],
                "severity": severity,
                "urls": unique_urls,
                "count": count,
            })

        # Add site-level checks
        if not self.result.http_to_https:
            recs.append({
                "key": "no_https_redirect",
                "title": RECOMMENDATIONS_RU["no_https_redirect"]["title"],
                "impact": RECOMMENDATIONS_RU["no_https_redirect"]["impact"],
                "fix": RECOMMENDATIONS_RU["no_https_redirect"]["fix"],
                "effort": "quick",
                "severity": "critical",
                "urls": [self.result.base_url],
                "count": 1,
            })

        if self.result.orphan_pages:
            count = len(self.result.orphan_pages)
            recs.append({
                "key": "orphan_pages",
                "title": RECOMMENDATIONS_RU["orphan_pages"]["title"].format(count=count),
                "impact": RECOMMENDATIONS_RU["orphan_pages"]["impact"],
                "fix": RECOMMENDATIONS_RU["orphan_pages"]["fix"],
                "effort": "medium",
                "severity": "warning",
                "urls": self.result.orphan_pages[:20],
                "count": count,
            })

        if self.result.duplicate_titles:
            count = len(self.result.duplicate_titles)
            recs.append({
                "key": "duplicate_titles",
                "title": RECOMMENDATIONS_RU["duplicate_titles"]["title"].format(count=count),
                "impact": RECOMMENDATIONS_RU["duplicate_titles"]["impact"],
                "fix": RECOMMENDATIONS_RU["duplicate_titles"]["fix"],
                "effort": "medium",
                "severity": "warning",
                "urls": [u for g in self.result.duplicate_titles for u in g["urls"]][:20],
                "count": count,
            })

        if self.result.duplicate_descriptions:
            count = len(self.result.duplicate_descriptions)
            recs.append({
                "key": "duplicate_descriptions",
                "title": RECOMMENDATIONS_RU["duplicate_descriptions"]["title"].format(count=count),
                "impact": RECOMMENDATIONS_RU["duplicate_descriptions"]["impact"],
                "fix": RECOMMENDATIONS_RU["duplicate_descriptions"]["fix"],
                "effort": "medium",
                "severity": "warning",
                "urls": [u for g in self.result.duplicate_descriptions for u in g["urls"]][:20],
                "count": count,
            })

        if self.result.no_structured_data:
            recs.append({
                "key": "no_schema",
                "title": RECOMMENDATIONS_RU["no_schema"]["title"],
                "impact": RECOMMENDATIONS_RU["no_schema"]["impact"],
                "fix": RECOMMENDATIONS_RU["no_schema"]["fix"],
                "effort": "complex",
                "severity": "warning",
                "urls": [self.result.base_url],
                "count": 1,
            })

        if self.result.noindex_linked_pages:
            count = len(self.result.noindex_linked_pages)
            template = RECOMMENDATIONS_RU["noindex_linked"]
            recs.append({
                "key": "noindex_linked",
                "title": template["title"].format(count=count),
                "impact": template["impact"],
                "fix": template["fix"],
                "effort": template["effort"],
                "severity": "warning",
                "urls": self.result.noindex_linked_pages[:20],
                "count": count,
            })

        if self.result.robots_linked_blocked:
            recs.append({
                "key": "robots_blocked_linked",
                "title": f"Проверить ссылки на URL, закрытые robots.txt ({len(self.result.robots_linked_blocked)} шт.)",
                "impact": "Ссылки на закрытые URL тратят краулинговый бюджет и мешают индексации важных страниц.",
                "fix": "Откройте важные URL в robots.txt или уберите на них внутренние ссылки.",
                "effort": "medium",
                "severity": "warning",
                "urls": self.result.robots_linked_blocked[:20],
                "count": len(self.result.robots_linked_blocked),
            })

        if not self.result.robots_has_clean_param and any(
            p.url for p in self.result.pages.values()
            if "?" in p.url and any(k in p.url for k in ["utm_", "sort=", "filter="])
        ):
            recs.append({
                "key": "yandex_clean_param",
                "title": RECOMMENDATIONS_RU["yandex_clean_param"]["title"],
                "impact": RECOMMENDATIONS_RU["yandex_clean_param"]["impact"],
                "fix": RECOMMENDATIONS_RU["yandex_clean_param"]["fix"],
                "effort": "quick",
                "severity": "info",
                "urls": [],
                "count": 0,
            })

        # Sort by severity
        recs.sort(key=lambda x: SEVERITY_ORDER.get(x["severity"], 2))
        self.result.recommendations = recs

    def to_excel(self) -> bytes:
        output = io.BytesIO()
        with pd.ExcelWriter(output, engine="openpyxl") as writer:
            # Sheet 1: Summary
            summary = pd.DataFrame([{
                "Метрика": "Здоровье сайта",
                "Значение": f"{self.result.health_score}/100",
            }, {
                "Метрика": "Просканировано страниц",
                "Значение": str(self.result.total_scanned),
            }, {
                "Метрика": "Длительность сканирования",
                "Значение": f"{self.result.duration}с",
            }, {
                "Метрика": "Критических ошибок",
                "Значение": str(self.result.issues_by_severity.get("critical", 0)),
            }, {
                "Метрика": "Предупреждений",
                "Значение": str(self.result.issues_by_severity.get("warning", 0)),
            }, {
                "Метрика": "Дата аудита",
                "Значение": datetime.now().strftime("%Y-%m-%d %H:%M"),
            }])
            summary.to_excel(writer, sheet_name="Сводка", index=False)

            # Sheet 2: All pages
            pages_data = []
            for url, page in self.result.pages.items():
                pages_data.append({
                    "URL": url,
                    "Код": page.status_code,
                    "Title": page.title[:80],
                    "Дл. Title": page.title_length,
                    "Описание": page.description[:80],
                    "Дл. Description": page.description_length,
                    "H1 (кол-во)": page.h1_count,
                    "Слов": page.word_count,
                    "Картинки без ALT": page.images_missing_alt,
                    "TTFB (сек)": round(page.ttfb, 2),
                    "Canonical": page.canonical_status,
                    "Ошибок": len(page.issues),
                })
            pd.DataFrame(pages_data).to_excel(writer, sheet_name="Все страницы", index=False)

            # Sheet 3: All issues
            issues_data = []
            for url, page in self.result.pages.items():
                for issue in page.issues:
                    issues_data.append({
                        "URL": url,
                        "Серьёзность": issue.severity,
                        "Категория": issue.category,
                        "Проблема": issue.message,
                        "Текущее значение": issue.current_value,
                        "Норма": issue.expected_value,
                    })
            pd.DataFrame(issues_data).to_excel(writer, sheet_name="Все ошибки", index=False)

            # Sheet 4: Action plan
            plan_data = []
            for rec in self.result.recommendations:
                plan_data.append({
                    "Приоритет": rec["severity"],
                    "Задача": rec["title"],
                    "Влияние": rec["impact"],
                    "Как исправить": rec["fix"],
                    "Сложность": rec["effort"],
                    "Кол-во страниц": rec["count"],
                    "Примеры URL": "; ".join(rec["urls"][:5]),
                })
            pd.DataFrame(plan_data).to_excel(writer, sheet_name="План действий", index=False)

            # Sheet 5: Duplicates
            dupes_data = []
            for group in self.result.duplicate_titles:
                for url in group["urls"]:
                    dupes_data.append({
                        "Тип": "Title",
                        "Значение": group["title"][:80],
                        "URL": url,
                    })
            for group in self.result.duplicate_descriptions:
                for url in group["urls"]:
                    dupes_data.append({
                        "Тип": "Description",
                        "Значение": group["description"][:80],
                        "URL": url,
                    })
            for group in self.result.duplicate_content:
                for url in group["urls"]:
                    dupes_data.append({
                        "Тип": "Контент",
                        "Значение": "(>90% совпадение)",
                        "URL": url,
                    })
            pd.DataFrame(dupes_data).to_excel(writer, sheet_name="Дубли", index=False)

        return output.getvalue()

    def to_csv(self) -> str:
        rows = []
        for url, page in self.result.pages.items():
            rows.append({
                "URL": url,
                "Код": page.status_code,
                "Title": page.title,
                "Дл. Title": page.title_length,
                "Описание": page.description,
                "Дл. Description": page.description_length,
                "H1": "; ".join(page.h1_list),
                "Слов": page.word_count,
                "TTFB": round(page.ttfb, 2),
                "Ошибок": len(page.issues),
            })
        return pd.DataFrame(rows).to_csv(index=False)


# === STREAMLIT UI ===

def inject_custom_css() -> None:
    """Внедряет кастомную тёмную тему интерфейса."""
    st.markdown(
        """
        <style>
            @import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700&family=JetBrains+Mono:wght@400;500&display=swap');
            html, body, [class*="css"] { font-family: 'Inter', sans-serif; }
            #MainMenu, footer, header { visibility: hidden; }

            [data-testid="stAppViewContainer"] {
                background: radial-gradient(1400px 600px at 50% -20%, #1F2A52 0%, #0F172A 48%);
            }
            [data-testid="stSidebar"] {
                background-color: #0F172A;
                border-right: 1px solid #334155;
            }
            .stTabs [data-baseweb="tab-list"] {
                gap: 0px;
                background-color: #1E293B;
                border-radius: 12px;
                padding: 4px;
            }
            .stTabs [data-baseweb="tab"] {
                border-radius: 8px;
                color: #94A3B8;
                font-weight: 500;
                padding: 8px 16px;
            }
            .stTabs [aria-selected="true"] {
                background-color: #6366F1 !important;
                color: #FFFFFF !important;
            }
            .stButton > button[kind="primary"] {
                background-color: #6366F1;
                border: none;
                border-radius: 8px;
                font-weight: 600;
                padding: 10px 20px;
                width: 100%;
            }
            .stButton > button[kind="primary"]:hover {
                background-color: #4338CA;
            }
            .metric-card {
                background: #1E293B;
                border: 1px solid #334155;
                border-radius: 12px;
                padding: 20px;
                text-align: center;
                transition: border-color 0.2s ease;
            }
            .metric-card:hover { border-color: #6366F1; }
            .recommendation-card {
                background: #1E293B;
                border: 1px solid #334155;
                border-left: 4px solid;
                border-radius: 0 12px 12px 0;
                padding: 16px 20px;
                margin-bottom: 12px;
            }
            .scan-log-entry {
                font-family: 'JetBrains Mono', monospace;
                font-size: 13px;
                padding: 4px 8px;
                border-bottom: 1px solid #1E293B;
            }
            .scan-log-entry.ok { color: #10B981; }
            .scan-log-entry.error { color: #EF4444; }
            .scan-log-entry.info { color: #94A3B8; }
            .scan-log-entry.active { color: #F59E0B; background: rgba(245,158,11,0.05); }
            @media (max-width: 768px) {
                .metric-card { padding: 12px; }
                [data-testid="stHorizontalBlock"] { flex-wrap: wrap; }
            }
        </style>
        """,
        unsafe_allow_html=True,
    )


def apply_chart_style(fig: go.Figure, title: str = "") -> None:
    """Применяет единый стиль к Plotly-графикам."""
    fig.update_layout(
        **PLOTLY_LAYOUT,
        title=dict(
            text=title,
            font=dict(size=16, color="#F8FAFC"),
            x=0,
            xanchor="left",
        ),
        legend=dict(
            bgcolor="rgba(0,0,0,0)",
            borderwidth=0,
            font=dict(size=12, color="#94A3B8"),
            orientation="h",
            yanchor="bottom",
            y=-0.2,
            xanchor="center",
            x=0.5,
        ),
        hoverlabel=dict(
            bgcolor="#1E293B",
            bordercolor="#475569",
            font=dict(size=13, color="#F8FAFC"),
        ),
    )


def severity_badge(level: str) -> str:
    """HTML-бейдж серьёзности."""
    config = {
        "critical": ("🔴 Критическая", COLORS["critical"], COLORS["critical_bg"]),
        "warning": ("🟡 Внимание", COLORS["warning"], COLORS["warning_bg"]),
        "info": ("🔵 Информация", COLORS["info"], COLORS["info_bg"]),
    }
    label, text_color, bg_color = config.get(level, config["info"])
    return (
        f'<span style="background:{bg_color}; color:{text_color}; '
        f'padding:2px 8px; border-radius:6px; font-size:12px; font-weight:600;">{label}</span>'
    )


@st.cache_data(show_spinner=False)
def build_pages_dataframe(pages_payload: Dict[str, Dict[str, Any]]) -> pd.DataFrame:
    """Кэшируемая сборка таблицы всех страниц."""
    canonical_map = {
        "ok": "✅ ОК",
        "missing": "⚠️ Нет",
        "error": "🔴 Ошибка",
        "other": "⚠️ На другой URL",
    }
    rows = []
    for url, page in pages_payload.items():
        rows.append({
            "URL": url,
            "Код": page.get("statusCode", 0),
            "Title": (page.get("title") or "")[:50],
            "Дл. Title": page.get("titleLength", 0),
            "Дл. Описания": page.get("descriptionLength", 0),
            "H1 (кол-во)": page.get("h1Count", 0),
            "Слов": page.get("wordCount", 0),
            "Картинки без ALT": page.get("imagesMissingAlt", 0),
            "TTFB (сек)": round(page.get("ttfb", 0.0), 2),
            "Canonical": canonical_map.get(page.get("canonicalStatus", "missing"), "⚠️ Нет"),
            "Ошибок": len(page.get("issues", [])),
            "Битые внутр. ссылки": page.get("brokenInternalLinks", 0),
        })
    return pd.DataFrame(rows)


@st.cache_data(show_spinner=False)
def build_issues_dataframe(pages_payload: Dict[str, Dict[str, Any]]) -> pd.DataFrame:
    """Кэшируемая сборка плоской таблицы ошибок."""
    rows = []
    for url, page in pages_payload.items():
        for issue in page.get("issues", []):
            rows.append({
                "URL": url,
                "Категория": issue.get("category", ""),
                "Серьёзность": issue.get("severity", ""),
                "Проблема": issue.get("message", ""),
                "Текущее значение": issue.get("currentValue", ""),
                "Норма": issue.get("expectedValue", ""),
                "Код": issue.get("code", ""),
            })
    if not rows:
        return pd.DataFrame(columns=["URL", "Категория", "Серьёзность", "Проблема", "Текущее значение", "Норма", "Код"])
    return pd.DataFrame(rows)


class SEOAuditApp:
    """Главный класс Streamlit-приложения."""

    def __init__(self):
        self.setup_page()
        inject_custom_css()
        self.init_session_state()

    def setup_page(self) -> None:
        st.set_page_config(
            page_title="SEO Аудит-Машина",
            page_icon="🔍",
            layout="wide",
            initial_sidebar_state="expanded",
        )

    def init_session_state(self) -> None:
        defaults = {
            "state": "IDLE",
            "results": None,
            "error_message": "",
            "scan_log": [],
            "scan_stats": {"progress": 0.0, "found": 0, "done": 0, "queue": 0, "errors": 0, "elapsed": 0.0},
            "session_id": str(uuid.uuid4()),
            "config": {
                "url": "",
                "max_pages": UI_DEFAULT_MAX_PAGES,
                "max_depth": 5,
                "crawl_delay": 0.3,
                "respect_robots": True,
                "check_external": False,
            },
        }
        for key, value in defaults.items():
            if key not in st.session_state:
                st.session_state[key] = value

    def render(self) -> None:
        self.render_sidebar()
        state = st.session_state["state"]
        if state == "IDLE":
            self.render_welcome_screen()
        elif state == "SCANNING":
            self.render_scanning_screen()
        elif state == "RESULTS":
            self.render_results()
        elif state == "ERROR":
            self.render_error_screen()

    def render_sidebar(self) -> None:
        with st.sidebar:
            st.markdown("## 🔍 SEO Аудит-Машина")
            st.markdown("---")

            cfg = st.session_state["config"]
            cfg["max_pages"] = max(10, min(int(cfg.get("max_pages", UI_DEFAULT_MAX_PAGES)), UI_MAX_PAGES_LIMIT))
            cfg["max_depth"] = max(1, min(int(cfg.get("max_depth", 5)), 10))
            guard = get_runtime_guard()
            url_value = st.text_input(
                "Адрес сайта:",
                value=cfg["url"],
                placeholder="https://example.com",
                help="Введите полный URL сайта для аудита.",
            )
            cfg["url"] = url_value.strip()

            if guard.lock.locked() and guard.active_session_id and guard.active_session_id != st.session_state["session_id"]:
                st.info("⏳ Сейчас выполняется аудит другим пользователем. Запуск временно недоступен.")

            if st.button("🚀 Запустить аудит", type="primary"):
                self.start_scan()

            with st.expander("⚙️ Настройки"):
                cfg["max_pages"] = st.slider(
                    "Макс. страниц",
                    10,
                    UI_MAX_PAGES_LIMIT,
                    int(cfg["max_pages"]),
                    help="Сколько страниц просканировать. Для малого сайта обычно достаточно 50.",
                )
                cfg["max_depth"] = st.slider(
                    "Глубина",
                    1,
                    10,
                    int(cfg["max_depth"]),
                    help="Максимальная глубина переходов по внутренним ссылкам от главной.",
                )
                cfg["crawl_delay"] = st.slider(
                    "Задержка (сек)",
                    0.1,
                    2.0,
                    float(cfg["crawl_delay"]),
                    step=0.1,
                    help="Интервал между батчами запросов. Полезно для уменьшения риска блокировок.",
                )
                cfg["respect_robots"] = st.toggle(
                    "Учитывать robots.txt",
                    value=bool(cfg["respect_robots"]),
                    help="Если включено, аудит пропускает URL, запрещённые в robots.txt.",
                )
                cfg["check_external"] = st.toggle(
                    "Проверять внешние ссылки",
                    value=bool(cfg["check_external"]),
                    help="Дополнительно проверяет внешние URL на 4xx/5xx.",
                )
                if IS_RENDER:
                    st.caption(
                        f"⚙️ Облачный режим: макс. {UI_MAX_PAGES_LIMIT} страниц и до {MAX_WORKERS} параллельных потоков "
                        "для стабильной работы."
                    )

            if st.session_state["state"] == "SCANNING":
                stats = st.session_state["scan_stats"]
                st.markdown("---")
                st.write("**Прогресс:**")
                st.progress(float(stats.get("progress", 0.0)))
                st.caption(f"Найдено: {stats.get('found', 0)} стр.")
                st.caption(f"Проверено: {stats.get('done', 0)}")
                st.caption(f"В очереди: {stats.get('queue', 0)}")
                st.caption(f"Ошибок: {stats.get('errors', 0)}")
                st.caption(f"Время: {stats.get('elapsed', 0):.1f} сек")

            if st.session_state["state"] == "RESULTS" and st.session_state["results"]:
                result: SiteAuditResult = st.session_state["results"]
                report = ReportGenerator(result)
                xlsx_data = report.to_excel()
                csv_data = report.to_csv()
                domain = result.domain.replace(".", "-")
                date_str = datetime.now().strftime("%Y-%m-%d")
                st.markdown("---")
                st.success(f"✅ Аудит завершён за {result.duration} сек")
                st.download_button(
                    "📥 Скачать отчёт (.xlsx)",
                    data=xlsx_data,
                    file_name=f"seo-audit-{domain}-{date_str}.xlsx",
                    mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                    use_container_width=True,
                )
                st.download_button(
                    "📄 Скачать CSV",
                    data=csv_data.encode("utf-8"),
                    file_name=f"seo-audit-{domain}-{date_str}.csv",
                    mime="text/csv",
                    use_container_width=True,
                )

            if LOG_BUFFER:
                with st.expander("⚠️ Системные предупреждения"):
                    for msg in list(LOG_BUFFER)[-8:]:
                        st.caption(msg)

            st.markdown("---")
            st.caption("v1.0 • Python + Streamlit")

    def start_scan(self) -> None:
        cfg = st.session_state["config"]
        guard = get_runtime_guard()
        session_id = st.session_state["session_id"]
        if guard.lock.locked() and guard.active_session_id and guard.active_session_id != session_id:
            st.session_state["state"] = "ERROR"
            st.session_state["error_message"] = ERROR_MESSAGES_RU["busy"]
            st.rerun()

        raw_url = cfg["url"].strip()
        if not raw_url:
            st.session_state["state"] = "ERROR"
            st.session_state["error_message"] = ERROR_MESSAGES_RU["invalid_url"]
            st.rerun()

        if not raw_url.startswith(("http://", "https://")):
            raw_url = "https://" + raw_url
            cfg["url"] = raw_url

        parsed = urlparse(raw_url)
        if not parsed.netloc:
            st.session_state["state"] = "ERROR"
            st.session_state["error_message"] = ERROR_MESSAGES_RU["invalid_url"]
            st.rerun()

        cfg["max_pages"] = max(10, min(int(cfg.get("max_pages", UI_DEFAULT_MAX_PAGES)), UI_MAX_PAGES_LIMIT))

        build_pages_dataframe.clear()
        build_issues_dataframe.clear()
        st.session_state["scan_log"] = []
        st.session_state["scan_stats"] = {"progress": 0.0, "found": 0, "done": 0, "queue": 0, "errors": 0, "elapsed": 0.0}
        st.session_state["results"] = None
        st.session_state["error_message"] = ""
        st.session_state["state"] = "SCANNING"
        st.rerun()

    def render_welcome_screen(self) -> None:
        st.markdown(
            """
            <div style="text-align:center; padding: 20px 0 16px;">
                <h1 style="margin-bottom: 4px;">🔍 SEO Аудит-Машина</h1>
                <p style="color:#94A3B8; font-size:16px;">Автоматический технический аудит любого сайта</p>
            </div>
            """,
            unsafe_allow_html=True,
        )
        st.markdown(
            """
            <div style="background:#1E293B; border:1px solid #334155; border-radius:12px; padding:14px; text-align:center; margin-bottom:18px;">
                🌐 Введите URL сайта и нажмите «Запустить аудит» в боковой панели слева
            </div>
            """,
            unsafe_allow_html=True,
        )

        card_data = [
            ("🔧", "Техника", "Коды ответа • Canonical • SSL"),
            ("📝", "Контент", "Title • Description • H1"),
            ("🖼️", "Картинки", "ALT • Размер • CLS"),
            ("🔗", "Ссылки", "Битые • Nofollow • Глубина"),
            ("📊", "Разметка", "Schema.org • OG • Twitter"),
            ("🔒", "Безопасность", "HTTPS • HSTS • Robots"),
        ]
        cols = st.columns(3)
        for idx, (icon, title, sub) in enumerate(card_data):
            with cols[idx % 3]:
                st.markdown(
                    f"""
                    <div class="metric-card" style="min-height:128px; margin-bottom:10px;">
                        <div style="font-size:28px;">{icon}</div>
                        <div style="font-weight:700; color:#F8FAFC;">{title}</div>
                        <div style="font-size:12px; color:#94A3B8;">{sub}</div>
                    </div>
                    """,
                    unsafe_allow_html=True,
                )

    def render_scanning_screen(self) -> None:
        cfg = st.session_state["config"]
        st.subheader(f"🔍 Сканирование: {urlparse(cfg['url']).netloc}")
        progress_bar = st.progress(0.0)
        stats_container = st.empty()
        log_container = st.empty()
        started = time.time()

        def callback(event: Dict[str, Any]) -> None:
            if event.get("type") == "pre_check":
                st.session_state["scan_log"].append(f"ℹ️ {event.get('message', '')}")
            elif event.get("type") == "page_done":
                done = int(event.get("pagesScanned", 0))
                found = int(event.get("totalDiscovered", 0))
                queue = int(event.get("queueSize", 0))
                errors = int(event.get("errorsCount", 0))
                progress = min(done / max(1, cfg["max_pages"]), 1.0)
                st.session_state["scan_stats"] = {
                    "progress": progress,
                    "found": found,
                    "done": done,
                    "queue": queue,
                    "errors": errors,
                    "elapsed": time.time() - started,
                }
                status = event.get("statusCode", 0)
                icon = "✅" if 200 <= status < 400 else "🔴"
                st.session_state["scan_log"].append(
                    f"{icon} {event.get('url', '')}   {status}   {event.get('ttfb', 0):.2f}с"
                )
            elif event.get("type") == "page_error":
                st.session_state["scan_log"].append(
                    f"🔴 {event.get('url', '')}   ошибка: {event.get('error', '')}"
                )

            st.session_state["scan_log"] = st.session_state["scan_log"][-20:]
            stats = st.session_state["scan_stats"]
            progress_bar.progress(float(stats.get("progress", 0.0)))
            stats_container.markdown(
                f"""
                <div style="display:grid; grid-template-columns: repeat(4, 1fr); gap: 10px; margin: 8px 0 12px;">
                    <div class="metric-card"><div style="font-size:24px;">{stats.get('found',0)}</div><div style="color:#94A3B8;font-size:12px;">Найдено</div></div>
                    <div class="metric-card"><div style="font-size:24px;">{stats.get('done',0)}</div><div style="color:#94A3B8;font-size:12px;">Готово</div></div>
                    <div class="metric-card"><div style="font-size:24px;">{stats.get('queue',0)}</div><div style="color:#94A3B8;font-size:12px;">В очереди</div></div>
                    <div class="metric-card"><div style="font-size:24px;">{stats.get('errors',0)}</div><div style="color:#94A3B8;font-size:12px;">Ошибки</div></div>
                </div>
                """,
                unsafe_allow_html=True,
            )
            log_html = "<div style='border:1px solid #334155; border-radius:12px; padding:8px; background:#0F172A;'>"
            for row in st.session_state["scan_log"][-12:]:
                row_class = "ok" if row.startswith("✅") else "error" if row.startswith("🔴") else "info"
                log_html += f"<div class='scan-log-entry {row_class}'>{row}</div>"
            log_html += "</div>"
            log_container.markdown(log_html, unsafe_allow_html=True)

        guard = get_runtime_guard()
        session_id = st.session_state["session_id"]
        if guard.lock.locked() and guard.active_session_id and guard.active_session_id != session_id:
            st.session_state["state"] = "ERROR"
            st.session_state["error_message"] = ERROR_MESSAGES_RU["busy"]
            st.rerun()

        lock_acquired = False
        try:
            lock_acquired = guard.lock.acquire(blocking=False)
            if not lock_acquired and guard.active_session_id and guard.active_session_id != session_id:
                st.session_state["state"] = "ERROR"
                st.session_state["error_message"] = ERROR_MESSAGES_RU["busy"]
                st.rerun()

            guard.active_session_id = session_id
            guard.started_at = time.time()
            crawler = CrawlerEngine(
                start_url=cfg["url"],
                max_pages=int(cfg["max_pages"]),
                max_depth=int(cfg["max_depth"]),
                crawl_delay=float(cfg["crawl_delay"]),
                respect_robots=bool(cfg["respect_robots"]),
                check_external=bool(cfg["check_external"]),
            )
            result = crawler.crawl(progress_callback=callback)
            if result.total_scanned == 0:
                st.session_state["state"] = "ERROR"
                st.session_state["error_message"] = ERROR_MESSAGES_RU["no_pages"]
            else:
                st.session_state["results"] = result
                st.session_state["state"] = "RESULTS"
        except requests.exceptions.Timeout:
            st.session_state["state"] = "ERROR"
            st.session_state["error_message"] = ERROR_MESSAGES_RU["timeout"]
        except requests.exceptions.SSLError:
            st.session_state["state"] = "ERROR"
            st.session_state["error_message"] = ERROR_MESSAGES_RU["ssl_error"]
        except requests.exceptions.ConnectionError:
            st.session_state["state"] = "ERROR"
            st.session_state["error_message"] = ERROR_MESSAGES_RU["connection_error"]
        except Exception as exc:
            logger.exception("Ошибка сканирования")
            st.session_state["state"] = "ERROR"
            st.session_state["error_message"] = f"❌ Ошибка аудита: {str(exc)[:180]}"
        finally:
            if lock_acquired:
                guard.active_session_id = ""
                guard.started_at = 0.0
                guard.lock.release()

        st.rerun()

    def render_results(self) -> None:
        result: SiteAuditResult = st.session_state["results"]
        pages_payload = {url: page.to_dict() for url, page in result.pages.items()}
        pages_df = build_pages_dataframe(pages_payload)
        issues_df = build_issues_dataframe(pages_payload)

        tab_overview, tab_errors, tab_all_pages, tab_duplicates, tab_plan, tab_tech = st.tabs(
            ["📊 Обзор", "🔴 Ошибки", "📄 Все стр.", "📝 Дубли", "🎯 План", "🔧 Тех."]
        )
        with tab_overview:
            self.render_tab_overview(result, pages_df, issues_df)
        with tab_errors:
            self.render_tab_errors(issues_df)
        with tab_all_pages:
            self.render_tab_all_pages(result, pages_df)
        with tab_duplicates:
            self.render_tab_duplicates(result)
        with tab_plan:
            self.render_tab_action_plan(result)
        with tab_tech:
            self.render_tab_technical(result)

    def render_tab_overview(self, result: SiteAuditResult, pages_df: pd.DataFrame, issues_df: pd.DataFrame) -> None:
        score = result.health_score
        score_color = COLORS["success"] if score >= 80 else COLORS["warning"] if score >= 60 else "#F97316" if score >= 40 else COLORS["critical"]
        score_text = (
            "Отличное состояние" if score >= 80 else
            "Требует внимания" if score >= 60 else
            "Есть серьёзные проблемы" if score >= 40 else
            "Критическое состояние"
        )
        critical_issues = int(result.issues_by_severity.get("critical", 0))
        avg_ttfb = float(pages_df["TTFB (сек)"].mean()) if not pages_df.empty else 0.0

        c1, c2, c3, c4 = st.columns(4)
        with c1:
            self.render_metric_card(ICONS["score"], f"{score}", "Здоровье /100", score_color, score_text)
        with c2:
            self.render_metric_card(ICONS["pages"], f"{result.total_scanned}", "Страниц просканировано", COLORS["info"])
        with c3:
            self.render_metric_card(ICONS["critical"], f"{critical_issues}", "Критических ошибок", COLORS["critical"])
        with c4:
            self.render_metric_card(ICONS["speed"], f"{avg_ttfb:.2f}с", "Средний TTFB", COLORS["warning"] if avg_ttfb > 1.5 else COLORS["success"])

        left, right = st.columns(2)
        with left:
            radar_values = [
                result.category_scores.get("technical", 0),
                result.category_scores.get("content", 0),
                result.category_scores.get("images", 0),
                result.category_scores.get("links", 0),
                result.category_scores.get("structured_data", 0),
            ]
            radar = go.Figure(go.Scatterpolar(
                r=radar_values,
                theta=["Техника", "Контент", "Картинки", "Ссылки", "Разметка"],
                fill="toself",
                fillcolor="rgba(99,102,241,0.2)",
                line=dict(color=COLORS["primary"], width=2),
                marker=dict(size=8, color=COLORS["primary"]),
            ))
            radar.update_layout(
                polar=dict(
                    bgcolor="rgba(0,0,0,0)",
                    radialaxis=dict(visible=True, range=[0, 100], gridcolor="#334155", tickfont=dict(color="#64748B")),
                    angularaxis=dict(gridcolor="#334155", tickfont=dict(color="#E2E8F0")),
                )
            )
            apply_chart_style(radar, "Здоровье по категориям")
            st.plotly_chart(radar, use_container_width=True)

        with right:
            grouped = {"200 ОК": 0, "3xx Редирект": 0, "4xx Не найден": 0, "5xx Сервер": 0}
            for code_str, count in result.status_codes.items():
                try:
                    code = int(code_str)
                except ValueError:
                    continue
                if 200 <= code < 300:
                    grouped["200 ОК"] += count
                elif 300 <= code < 400:
                    grouped["3xx Редирект"] += count
                elif 400 <= code < 500:
                    grouped["4xx Не найден"] += count
                elif 500 <= code < 600:
                    grouped["5xx Сервер"] += count
            donut = go.Figure(go.Pie(
                labels=list(grouped.keys()),
                values=list(grouped.values()),
                hole=0.65,
                marker=dict(colors=[COLORS["success"], COLORS["info"], COLORS["warning"], COLORS["critical"]]),
                textinfo="percent+label",
                hovertemplate="<b>%{label}</b><br>Страниц: %{value}<br>Доля: %{percent}<extra></extra>",
            ))
            donut.add_annotation(
                text=f"<b>{result.total_scanned}</b><br><span style='font-size:12px;color:#94A3B8'>страниц</span>",
                showarrow=False,
                font=dict(size=28, color="#F8FAFC"),
            )
            apply_chart_style(donut, "Коды ответов")
            st.plotly_chart(donut, use_container_width=True)

        slow_df = pages_df.sort_values("TTFB (сек)", ascending=False).head(10)
        if not slow_df.empty:
            slow_fig = px.bar(
                slow_df,
                x="TTFB (сек)",
                y="URL",
                orientation="h",
                color="TTFB (сек)",
                color_continuous_scale=[COLORS["success"], COLORS["warning"], COLORS["critical"]],
            )
            slow_fig.update_layout(yaxis=dict(autorange="reversed"))
            apply_chart_style(slow_fig, "ТОП-10 самых медленных страниц")
            st.plotly_chart(slow_fig, use_container_width=True)

        if not issues_df.empty:
            err = issues_df.groupby(["Категория", "Серьёзность"]).size().reset_index(name="Количество")
            stacked = px.bar(
                err,
                x="Категория",
                y="Количество",
                color="Серьёзность",
                color_discrete_map={"critical": COLORS["critical"], "warning": COLORS["warning"], "info": COLORS["info"]},
            )
            apply_chart_style(stacked, "Распределение ошибок по категориям")
            st.plotly_chart(stacked, use_container_width=True)

    def render_tab_errors(self, issues_df: pd.DataFrame) -> None:
        if issues_df.empty:
            st.success("Проблемы не обнаружены.")
            return

        c1, c2, c3 = st.columns(3)
        with c1:
            category_filter = st.multiselect("Категория", sorted(issues_df["Категория"].dropna().unique().tolist()))
        with c2:
            sev_filter = st.multiselect("Серьёзность", ["critical", "warning", "info"], default=["critical", "warning"])
        with c3:
            code_filter = st.multiselect("Тип", sorted(issues_df["Код"].dropna().unique().tolist()))

        filtered = issues_df.copy()
        if category_filter:
            filtered = filtered[filtered["Категория"].isin(category_filter)]
        if sev_filter:
            filtered = filtered[filtered["Серьёзность"].isin(sev_filter)]
        if code_filter:
            filtered = filtered[filtered["Код"].isin(code_filter)]

        order_map = {"critical": 0, "warning": 1, "info": 2}
        filtered["__sort"] = filtered["Серьёзность"].map(order_map).fillna(9)
        filtered = filtered.sort_values("__sort").drop(columns=["__sort"])

        display_df = filtered[["URL", "Проблема", "Серьёзность", "Текущее значение", "Норма"]].copy()
        display_df["Серьёзность"] = display_df["Серьёзность"].map({
            "critical": "🔴 Критическая",
            "warning": "🟡 Внимание",
            "info": "🔵 Информация",
        })
        st.dataframe(
            display_df,
            use_container_width=True,
            column_config={"URL": st.column_config.LinkColumn("URL")},
            hide_index=True,
        )
        st.caption(f"Показано: {len(display_df)} из {len(issues_df)} проблем")

        st.download_button(
            "📥 Скачать таблицу ошибок (CSV)",
            data=filtered.to_csv(index=False).encode("utf-8"),
            file_name=f"errors-{datetime.now().strftime('%Y-%m-%d')}.csv",
            mime="text/csv",
            use_container_width=False,
        )

    def render_tab_all_pages(self, result: SiteAuditResult, pages_df: pd.DataFrame) -> None:
        if pages_df.empty:
            st.info("Нет данных по страницам.")
            return

        q = st.text_input("🔍 Поиск по URL...", "")
        display_df = pages_df.copy()
        if q:
            display_df = display_df[display_df["URL"].str.contains(q, case=False, na=False)]
        if display_df.empty:
            st.info("По текущему фильтру страницы не найдены.")
            return
        st.dataframe(
            display_df,
            use_container_width=True,
            hide_index=True,
            column_config={"URL": st.column_config.LinkColumn("URL")},
        )

        selected = st.selectbox("Детали страницы:", options=display_df["URL"].tolist()[:200])
        page = result.pages.get(selected)
        if page:
            with st.expander("Показать детали", expanded=False):
                st.write(f"**Title:** {page.title}")
                st.write(f"**Description:** {page.description}")
                st.write(f"**H1:** {', '.join(page.h1_list) if page.h1_list else 'нет'}")
                st.write(f"**Заголовки H1-H6:** {page.headings}")
                for issue in page.issues:
                    st.markdown(f"- `{issue.severity}` {issue.message}")

    def render_tab_duplicates(self, result: SiteAuditResult) -> None:
        title_count = len(result.duplicate_titles)
        desc_count = len(result.duplicate_descriptions)
        content_count = len(result.duplicate_content)
        url_pattern_count = len(result.url_pattern_duplicates)

        with st.expander(f"📝 Дублирующиеся Title ({title_count} групп)", expanded=title_count > 0):
            if not result.duplicate_titles:
                st.caption("Дубли не найдены.")
            for group in result.duplicate_titles:
                st.markdown(f"**Title:** {group['title']}")
                for url in group["urls"]:
                    st.write(f"- {url}")

        with st.expander(f"📝 Дублирующиеся Description ({desc_count} групп)", expanded=desc_count > 0):
            if not result.duplicate_descriptions:
                st.caption("Дубли не найдены.")
            for group in result.duplicate_descriptions:
                st.markdown(f"**Description:** {group['description']}")
                for url in group["urls"]:
                    st.write(f"- {url}")

        with st.expander(f"📝 Дубли контента (>90% совпадение) ({content_count} групп)", expanded=content_count > 0):
            if not result.duplicate_content:
                st.caption("Дубли не найдены.")
            for idx, group in enumerate(result.duplicate_content, 1):
                st.markdown(f"**Группа {idx}:**")
                for url in group["urls"]:
                    st.write(f"- {url}")

        with st.expander(f"📝 Дубли URL-паттернов ({url_pattern_count})", expanded=url_pattern_count > 0):
            if not result.url_pattern_duplicates:
                st.caption("Не найдено.")
            for row in result.url_pattern_duplicates:
                st.write(f"Нормализованный URL: `{row['normalized']}`")
                for variant in row["variants"]:
                    st.write(f"- {variant}")

    def render_tab_action_plan(self, result: SiteAuditResult) -> None:
        recommendations = result.recommendations
        if not recommendations:
            st.success("Критичных задач не обнаружено.")
            return
        st.subheader(f"🎯 План действий — {len(recommendations)} задач")

        for severity, title in [
            ("critical", "🔴 ИСПРАВИТЬ НЕМЕДЛЕННО"),
            ("warning", "🟡 ИСПРАВИТЬ В БЛИЖАЙШЕЕ ВРЕМЯ"),
            ("info", "🔵 УЛУЧШИТЬ ПОЗЖЕ"),
        ]:
            chunk = [r for r in recommendations if r["severity"] == severity]
            if not chunk:
                continue
            st.markdown(f"### {title} ({len(chunk)} задач)")
            for rec in chunk:
                self.render_recommendation_card(rec)

    def render_tab_technical(self, result: SiteAuditResult) -> None:
        st.markdown("### robots.txt")
        st.code(result.robots_txt_content or "robots.txt не найден", language="text")
        if result.robots_rules:
            st.dataframe(pd.DataFrame(result.robots_rules), use_container_width=True, hide_index=True)

        st.markdown("### sitemap.xml")
        sitemap_rows = []
        crawled_set = set(result.pages.keys())
        entries = result.sitemap_entries or [{"url": u, "lastmod": ""} for u in sorted(result.sitemap_urls)]
        for entry in entries[:1000]:
            url = entry.get("url", "")
            sitemap_rows.append({
                "URL": url,
                "Lastmod": entry.get("lastmod", ""),
                "Есть в сканировании": "✅" if url in crawled_set else "❌",
            })
        if sitemap_rows:
            st.dataframe(pd.DataFrame(sitemap_rows), use_container_width=True, hide_index=True)
        svs = result.sitemap_vs_crawled
        if svs:
            st.info(
                f"Всего URL в sitemap: {svs.get('sitemapTotal', 0)} | "
                f"Найдено при сканировании: {svs.get('overlap', 0)} | "
                f"Только в sitemap: {len(svs.get('onlyInSitemap', []))} | "
                f"Только в сканировании: {len(svs.get('onlyInCrawl', []))}"
            )

        st.markdown("### Карта редиректов")
        if result.redirect_map:
            rows = []
            for item in result.redirect_map:
                chain = item.get("chain", [])
                middle = " -> ".join(chain[1:-1]) if len(chain) > 2 else ""
                rows.append({
                    "Исходный URL": chain[0] if chain else "",
                    "Промежуточный": middle,
                    "Конечный URL": chain[-1] if chain else "",
                    "Хопов": item.get("hops", 0),
                    "Тип": item.get("type", 0),
                })
            st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)
        else:
            st.caption("Редиректы не обнаружены.")

        st.markdown("### SSL и безопасность")
        c1, c2, c3, c4, c5 = st.columns(5)
        c1.metric("SSL сертификат", "OK" if result.ssl_valid else "Ошибка")
        c2.metric("TLS", result.tls_version or "n/a")
        c3.metric("HTTP → HTTPS", "Да" if result.http_to_https else "Нет")
        c4.metric("WWW-консистентность", result.www_consistency or "unknown")
        homepage_hsts = any(k.lower() == "strict-transport-security" for k in result.homepage_headers.keys())
        c5.metric("HSTS", "Да" if homepage_hsts else "Нет")

        st.markdown("### HTTP-заголовки главной")
        st.caption(f"Главная: код {result.homepage_status_code or 'n/a'} • TTFB {result.homepage_ttfb:.2f}с")
        headers_text = "\n".join([f"{k}: {v}" for k, v in result.homepage_headers.items()]) or "Нет данных"
        st.code(headers_text, language="text")

        st.markdown("### Обнаружение JS-рендеринга")
        if result.detected_frameworks:
            framework_list = ", ".join(result.detected_frameworks)
            st.warning(
                f"⚠️ Обнаружен JS-фреймворк: {framework_list}\n\n"
                "Часть контента может загружаться через JavaScript.\n"
                "Инструмент анализирует только серверный HTML."
            )
        else:
            st.success("Явные признаки JS-рендеринга не обнаружены.")

        st.markdown("### Дополнительно")
        st.write(f"- llms.txt: {'✅ найден' if result.has_llms_txt else '❌ не найден'}")
        st.write(f"- URL, закрытые robots.txt, но найденные во внутренних ссылках: {len(result.robots_linked_blocked)}")
        st.write(f"- Страницы без входящих внутренних ссылок: {len(result.zero_inlink_pages)}")
        st.write(f"- Noindex-страницы с входящими внутренними ссылками: {len(result.noindex_linked_pages)}")
        st.write(f"- Кластеры thin content: {len(result.thin_content_clusters)}")
        if result.robots_linked_blocked:
            with st.expander("Показать URL, закрытые robots.txt, но найденные во внутренних ссылках"):
                for url in result.robots_linked_blocked[:200]:
                    st.write(f"- {url}")

    def render_error_screen(self) -> None:
        st.error(st.session_state.get("error_message", "Неизвестная ошибка."))
        if st.button("Попробовать снова"):
            st.session_state["state"] = "IDLE"
            st.session_state["error_message"] = ""
            st.rerun()

    def render_metric_card(self, icon: str, value: str, label: str, color: str, sublabel: str = "") -> None:
        st.markdown(
            f"""
            <div class="metric-card">
                <div style="font-size:28px; margin-bottom:4px;">{icon}</div>
                <div style="font-size:34px; font-weight:700; color:{color}; line-height:1.2;">{value}</div>
                <div style="font-size:14px; color:{COLORS['text_secondary']}; margin-top:4px;">{label}</div>
                <div style="font-size:12px; color:{COLORS['text_muted']};">{sublabel}</div>
            </div>
            """,
            unsafe_allow_html=True,
        )

    def render_recommendation_card(self, rec: Dict[str, Any]) -> None:
        sev = rec.get("severity", "info")
        border = COLORS["critical"] if sev == "critical" else COLORS["warning"] if sev == "warning" else COLORS["info"]
        effort = EFFORT_LABELS.get(rec.get("effort", "medium"), EFFORT_LABELS["medium"])
        st.markdown(
            f"""
            <div class="recommendation-card" style="border-left-color:{border};">
                <div style="display:flex; justify-content:space-between; gap:12px;">
                    <div style="font-size:16px; font-weight:700;">{rec.get('title')}</div>
                    <div>{severity_badge(sev)}</div>
                </div>
                <div style="margin-top:8px; color:#CBD5E1;"><b>Влияние:</b> {rec.get('impact')}</div>
                <div style="margin-top:8px; color:#CBD5E1;"><b>Как исправить:</b> {rec.get('fix')}</div>
                <div style="margin-top:8px; color:#94A3B8;"><b>Сложность:</b> {effort}</div>
            </div>
            """,
            unsafe_allow_html=True,
        )
        if rec.get("urls"):
            with st.expander(f"Затронутые страницы ({len(rec['urls'])})"):
                for url in rec["urls"]:
                    st.write(f"- {url}")


# === MAIN ===

if __name__ == "__main__":
    app = SEOAuditApp()
    app.render()

# ============================================
# HOW TO RUN:
# 1. pip install streamlit requests beautifulsoup4 lxml pandas plotly fake-useragent openpyxl
# 2. streamlit run app.py
# 3. Open http://localhost:8501 in your browser
# 4. Enter a URL and click "Start Audit"
# ============================================
