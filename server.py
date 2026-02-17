#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SEO Audit Machine - Backend Server
Full-featured technical SEO audit engine with FastAPI.
Supports real crawling, per-page and cross-page analysis,
scoring, recommendations (in Russian), and XLSX/CSV export.

Requirements:
    pip install fastapi uvicorn requests beautifulsoup4 lxml pandas
    pip install fake-useragent openpyxl aiofiles python-multipart
"""

# === IMPORTS ===
import asyncio
import hashlib
import io
import json
import logging
import re
import ssl
import time
import uuid
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field, asdict
from datetime import datetime
from typing import Any, Dict, List, Optional, Set, Tuple
from urllib.parse import (
    parse_qs, urlencode, urljoin, urlparse, urlunparse, quote
)
from urllib.robotparser import RobotFileParser

import pandas as pd
import requests
from bs4 import BeautifulSoup, Comment
from fastapi import FastAPI, BackgroundTasks, Query
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse, StreamingResponse
import uvicorn

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
MAX_HTML_SIZE = 5 * 1024 * 1024  # 5MB
MAX_REDIRECTS = 5
LARGE_IMAGE_BYTES = 500 * 1024  # 500KB

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
    internal_links_nofollow: int = 0
    broken_links_on_page: List[str] = field(default_factory=list)
    images_total: int = 0
    images_missing_alt: int = 0
    images_missing_dimensions: int = 0
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
            "internalLinksNofollow": self.internal_links_nofollow,
            "brokenLinksOnPage": self.broken_links_on_page,
            "imagesTotal": self.images_total,
            "imagesMissingAlt": self.images_missing_alt,
            "imagesMissingDimensions": self.images_missing_dimensions,
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
        }


@dataclass
class SiteAuditResult:
    base_url: str
    domain: str
    pages: Dict[str, PageResult] = field(default_factory=dict)
    duration: float = 0.0
    total_scanned: int = 0
    sitemap_urls: Set[str] = field(default_factory=set)
    sitemap_raw: str = ""
    robots_txt_content: str = ""
    robots_rules: List[Dict[str, str]] = field(default_factory=list)
    robots_sitemaps: List[str] = field(default_factory=list)
    robots_has_host: bool = False
    robots_host_value: str = ""
    robots_has_clean_param: bool = False
    ssl_valid: bool = True
    ssl_error: str = ""
    http_to_https: bool = False
    www_consistency: str = ""  # "www", "non-www", "inconsistent", "unknown"
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
    redirect_map: List[Dict] = field(default_factory=list)
    broken_link_map: List[Dict] = field(default_factory=list)
    sitemap_vs_crawled: Dict[str, List[str]] = field(default_factory=dict)
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

        self.visited: Set[str] = set()
        self.queue: List[Tuple[str, int]] = []
        self.results: Dict[str, PageResult] = {}
        self.all_discovered_links: Set[str] = set()
        self.internal_link_targets: Dict[str, Set[str]] = defaultdict(set)  # target -> set of source pages
        self.external_links_found: Set[str] = set()

        self.session = requests.Session()
        ua_string = _UA.random if _UA else "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36"
        self.session.headers.update({
            "User-Agent": ua_string,
            "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
            "Accept-Language": "ru-RU,ru;q=0.9,en-US;q=0.8,en;q=0.7",
            "Accept-Encoding": "gzip, deflate",
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
        self.sitemap_raw = ""

        self.ssl_valid = True
        self.ssl_error = ""
        self.http_to_https = False
        self.www_consistency = "unknown"
        self.homepage_headers: Dict[str, str] = {}
        self.has_llms_txt = False
        self.llms_txt_content = ""

        self._progress_callback = None
        self._stop_flag = False
        self._url_param_counts: Dict[str, int] = defaultdict(int)

    def normalize_url(self, url: str) -> str:
        """Normalize URL: strip fragment, trailing slash (except root), sort query params."""
        try:
            parsed = urlparse(url)
            path = parsed.path.rstrip("/") or "/"
            # Sort query params for deduplication
            qs = parse_qs(parsed.query, keep_blank_values=True)
            sorted_qs = urlencode(sorted(qs.items()), doseq=True)
            return urlunparse((parsed.scheme, parsed.netloc, path, "", sorted_qs, ""))
        except Exception:
            return url

    def is_internal(self, url: str) -> bool:
        try:
            parsed = urlparse(url)
            return parsed.netloc == self.domain or parsed.netloc == ""
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
            resp = self.session.get(robots_url, timeout=10)
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
                resp = self.session.get(sitemap_url, timeout=10)
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
                        self.sitemap_urls.add(self.normalize_url(loc.text.strip()))
            except Exception as e:
                logger.warning(f"Failed to parse sitemap {sitemap_url}: {e}")

    def check_ssl(self) -> None:
        """Check SSL certificate validity."""
        try:
            requests.get(f"https://{self.domain}", timeout=10, verify=True)
            self.ssl_valid = True
        except requests.exceptions.SSLError as e:
            self.ssl_valid = False
            self.ssl_error = str(e)[:200]
        except Exception:
            pass

    def check_http_redirect(self) -> None:
        """Check if HTTP redirects to HTTPS."""
        try:
            resp = requests.get(f"http://{self.domain}", timeout=10, allow_redirects=True, verify=False)
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

            resp = requests.get(f"https://{alt_domain}", timeout=10, allow_redirects=True, verify=False)
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
            resp = self.session.get(f"{self.base_origin}/llms.txt", timeout=10)
            if resp.status_code == 200 and len(resp.text) > 0:
                self.has_llms_txt = True
                self.llms_txt_content = resp.text[:2000]
        except Exception:
            pass

    def run_pre_checks(self, callback=None) -> None:
        """Run all pre-crawl checks."""
        steps = [
            ("Проверка robots.txt...", self.fetch_robots_txt),
            ("Загрузка sitemap.xml...", self.fetch_sitemap),
            ("Проверка SSL...", self.check_ssl),
            ("Проверка HTTP -> HTTPS...", self.check_http_redirect),
            ("Проверка www-консистентности...", self.check_www_consistency),
            ("Проверка llms.txt...", self.check_llms_txt),
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

        # Fetch homepage to get headers
        try:
            home_resp = self.session.get(self.start_url, timeout=15, allow_redirects=True)
            self.homepage_headers = dict(home_resp.headers)
        except Exception:
            pass

        # Start BFS
        start_norm = self.normalize_url(self.start_url)
        self.queue.append((self.start_url, 0))
        self.visited.add(start_norm)

        start_time = time.time()

        while self.queue and len(self.results) < self.max_pages and not self._stop_flag:
            # Take batch from queue
            batch = []
            while self.queue and len(batch) < 5 and (len(self.results) + len(batch)) < self.max_pages:
                batch.append(self.queue.pop(0))

            if not batch:
                break

            # Process batch in parallel
            with ThreadPoolExecutor(max_workers=5) as executor:
                futures = {}
                for url, depth in batch:
                    futures[executor.submit(self._fetch_and_analyze, url, depth)] = (url, depth)

                for future in as_completed(futures):
                    url, depth = futures[future]
                    try:
                        page_result, discovered_links = future.result()
                        if page_result:
                            self.results[url] = page_result

                            # Report progress
                            if progress_callback:
                                progress_callback({
                                    "type": "page_done",
                                    "url": url,
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

                            # Enqueue discovered internal links
                            if depth < self.max_depth:
                                for link in discovered_links:
                                    norm = self.normalize_url(link)
                                    if norm not in self.visited and self.is_internal(link):
                                        if self.is_crawlable_url(link) and not self.is_trap_url(link):
                                            if self.respect_robots and self.robots_parser:
                                                if not self.robots_parser.can_fetch("*", link):
                                                    continue
                                            self.visited.add(norm)
                                            self.queue.append((link, depth + 1))

                    except Exception as e:
                        logger.error(f"Error processing {url}: {e}")
                        err_result = PageResult(url=url, error_message=str(e)[:200])
                        err_result.issues.append(PageIssue(
                            "critical", "technical", "crawl_error",
                            f"Ошибка при сканировании: {str(e)[:100]}",
                        ))
                        self.results[url] = err_result
                        if progress_callback:
                            progress_callback({
                                "type": "page_error",
                                "url": url,
                                "error": str(e)[:100],
                                "pagesScanned": len(self.results),
                                "totalDiscovered": len(self.visited),
                                "queueSize": len(self.queue),
                            })

            # Crawl delay
            time.sleep(self.crawl_delay)

        elapsed = time.time() - start_time

        # Build result
        result = SiteAuditResult(
            base_url=self.start_url,
            domain=self.domain,
            pages=self.results,
            duration=round(elapsed, 2),
            total_scanned=len(self.results),
            sitemap_urls=self.sitemap_urls,
            sitemap_raw=self.sitemap_raw,
            robots_txt_content=self.robots_txt_content,
            robots_rules=self.robots_rules,
            robots_sitemaps=self.robots_sitemaps,
            robots_has_host=self.robots_has_host,
            robots_host_value=self.robots_host_value,
            robots_has_clean_param=self.robots_has_clean_param,
            ssl_valid=self.ssl_valid,
            ssl_error=self.ssl_error,
            http_to_https=self.http_to_https,
            www_consistency=self.www_consistency,
            homepage_headers=dict(self.homepage_headers),
            has_llms_txt=self.has_llms_txt,
            llms_txt_content=self.llms_txt_content,
        )

        # Run cross-page analysis
        analyzer = SiteAnalyzer(result, self.internal_link_targets, self.sitemap_urls)
        analyzer.analyze()

        # Scoring
        scorer = ReportGenerator(result)
        scorer.calculate_scores()
        scorer.generate_recommendations()

        return result

    def stop(self):
        self._stop_flag = True

    def _fetch_and_analyze(self, url: str, depth: int) -> Tuple[Optional[PageResult], List[str]]:
        """Fetch a single page and run per-page analysis."""
        result = PageResult(url=url, crawl_depth=depth)
        discovered = []

        try:
            resp = self.session.get(
                url, timeout=15, allow_redirects=True, verify=True,
                stream=False,
            )
        except requests.exceptions.SSLError:
            try:
                resp = self.session.get(url, timeout=15, allow_redirects=True, verify=False)
            except Exception as e:
                result.error_message = f"SSL + fallback error: {str(e)[:100]}"
                result.issues.append(PageIssue("critical", "security", "ssl_error",
                    "Ошибка SSL-сертификата", str(e)[:100], "Валидный сертификат"))
                return result, []
        except requests.exceptions.Timeout:
            result.error_message = "Timeout"
            result.issues.append(PageIssue("critical", "technical", "timeout",
                "Таймаут: сервер не ответил за 15 секунд"))
            return result, []
        except requests.exceptions.ConnectionError as e:
            result.error_message = str(e)[:100]
            result.issues.append(PageIssue("critical", "technical", "connection_error",
                "Ошибка соединения"))
            return result, []
        except requests.exceptions.TooManyRedirects:
            result.error_message = "Too many redirects"
            result.issues.append(PageIssue("critical", "technical", "redirect_loop",
                "Бесконечный цикл редиректов", ">5 хопов", "1-2 хопа"))
            return result, []
        except Exception as e:
            result.error_message = str(e)[:200]
            return result, []

        # Basic response info
        result.status_code = resp.status_code
        result.ttfb = resp.elapsed.total_seconds()
        result.content_type = resp.headers.get("Content-Type", "")
        result.content_length = len(resp.content)
        result.response_headers = {k: v for k, v in resp.headers.items()}

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
            if "noindex" in x_robots.lower():
                result.is_indexable = False

        # Skip non-HTML
        if "text/html" not in result.content_type:
            return result, []

        # Size guard
        if result.content_length > MAX_HTML_SIZE:
            result.issues.append(PageIssue("warning", "technical", "large_page",
                f"Слишком большая HTML-страница: {result.content_length // 1024}KB",
                f"{result.content_length // 1024}KB", "<1MB"))
            return result, []

        # Parse HTML
        try:
            soup = BeautifulSoup(resp.content, "lxml")
        except Exception:
            soup = BeautifulSoup(resp.content, "html.parser")

        # Run all per-page checks
        page_analyzer = PageAnalyzer(url, resp, soup, result, self.domain, self.base_origin)
        page_analyzer.analyze_all()

        # Extract links for crawler
        discovered = page_analyzer.extract_links()

        # Track internal link targets for orphan detection
        for link in discovered:
            if self.is_internal(link):
                norm_link = self.normalize_url(link)
                self.internal_link_targets[norm_link].add(url)

        return result, discovered


# === PAGE ANALYZER ===

class PageAnalyzer:
    """Performs all per-page SEO checks."""

    def __init__(self, url: str, response: requests.Response, soup: BeautifulSoup,
                 result: PageResult, domain: str, base_origin: str):
        self.url = url
        self.response = response
        self.soup = soup
        self.r = result
        self.domain = domain
        self.base_origin = base_origin

    def add_issue(self, severity: str, category: str, code: str, message: str,
                  current: str = "", expected: str = ""):
        self.r.issues.append(PageIssue(severity, category, code, message, current, expected))

    def analyze_all(self):
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

    def _check_headings(self):
        # H1
        h1_tags = self.soup.find_all("h1")
        self.r.h1_list = [h.get_text(strip=True) for h in h1_tags]
        self.r.h1_count = len(h1_tags)

        if not h1_tags:
            self.add_issue("critical", "content", "missing_h1",
                "Отсутствует заголовок H1", "0 шт.", "1 шт.")
        elif len(h1_tags) > 1:
            self.add_issue("warning", "content", "multiple_h1",
                f"Несколько заголовков H1: {len(h1_tags)} шт.",
                f"{len(h1_tags)} шт.", "1 шт.")
        else:
            h1_text = h1_tags[0].get_text(strip=True)
            if not h1_text:
                self.add_issue("critical", "content", "empty_h1",
                    "Пустой заголовок H1", "пусто", "Ключевое слово")
            elif len(h1_text) > H1_MAX_LEN:
                self.add_issue("info", "content", "long_h1",
                    f"H1 слишком длинный: {len(h1_text)} симв.",
                    f"{len(h1_text)} симв.", f"<{H1_MAX_LEN} симв.")

        # H1 vs Title
        if self.r.title and self.r.h1_list:
            if self.r.title.strip().lower() == self.r.h1_list[0].strip().lower():
                self.add_issue("info", "content", "h1_equals_title",
                    "H1 идентичен Title (рекомендуется различать)")

        # Full heading hierarchy
        headings = []
        for level in range(1, 7):
            for h in self.soup.find_all(f"h{level}"):
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
        # Remove script/style/comment content for word count
        for elem in self.soup(["script", "style", "noscript"]):
            elem.decompose()
        # Remove comments
        for comment in self.soup.find_all(string=lambda t: isinstance(t, Comment)):
            comment.extract()

        text = self.soup.get_text(separator=" ", strip=True)
        words = text.split()
        self.r.word_count = len(words)

        # Content hash
        clean_text = re.sub(r"\s+", " ", text.lower().strip())
        self.r.content_hash = hashlib.md5(clean_text.encode("utf-8")).hexdigest()

        # Text to HTML ratio
        html_len = self.r.content_length
        text_len = len(text.encode("utf-8"))
        self.r.text_html_ratio = (text_len / max(1, html_len)) * 100

        # Thin content checks
        if self.r.word_count < VERY_THIN_CONTENT_THRESHOLD:
            self.add_issue("critical", "content", "very_thin_content",
                f"Очень мало контента: {self.r.word_count} слов",
                f"{self.r.word_count} слов", f">{THIN_CONTENT_THRESHOLD} слов")
        elif self.r.word_count < THIN_CONTENT_THRESHOLD:
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

        # Check protocol mismatch
        parsed_page = urlparse(self.url)
        parsed_can = urlparse(canonical_href)
        if parsed_page.scheme == "https" and parsed_can.scheme == "http":
            self.add_issue("critical", "technical", "canonical_http",
                "Canonical ссылается на HTTP (страница HTTPS)",
                canonical_href, f"https://{parsed_can.netloc}{parsed_can.path}")

        # Check self-referencing
        norm_page = self.url.rstrip("/")
        norm_can = canonical_href.rstrip("/")
        if norm_can and norm_can != norm_page:
            # Could be intentional (pointing to primary version)
            self.r.canonical_status = "other"
            self.add_issue("info", "technical", "canonical_different",
                "Canonical указывает на другую страницу",
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
        missing_dims = 0

        for img in images:
            alt = img.get("alt")
            if alt is None:
                missing_alt += 1
            src = img.get("src", "")
            if not img.get("width") and not img.get("height"):
                # Check for style attribute
                style = img.get("style", "")
                if "width" not in style and "height" not in style:
                    missing_dims += 1

        self.r.images_missing_alt = missing_alt
        self.r.images_missing_dimensions = missing_dims

        if missing_alt > 0:
            self.add_issue("warning", "images", "missing_alt",
                f"{missing_alt} изображений без атрибута ALT",
                f"{missing_alt} шт.", "0 шт.")

        if missing_dims > 0:
            self.add_issue("warning", "images", "missing_dimensions",
                f"{missing_dims} изображений без width/height (CLS)",
                f"{missing_dims} шт.", "0 шт.")

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
                    data = json.loads(script.string or "")
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
        else:
            self.add_issue("info", "structured_data", "no_schema",
                "Нет микроразметки Schema.org (JSON-LD)")

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

    def extract_links(self) -> List[str]:
        """Extract all links from page for crawler."""
        try:
            link_soup = BeautifulSoup(self.response.content, "lxml")
        except Exception:
            link_soup = BeautifulSoup(self.response.content, "html.parser")

        links = []
        internal = 0
        external = 0
        nofollow_internal = 0

        for a in link_soup.find_all("a", href=True):
            href = a.get("href", "").strip()
            if not href or href.startswith(("#", "javascript:", "mailto:", "tel:")):
                continue

            abs_url = urljoin(self.url, href)
            parsed = urlparse(abs_url)

            if parsed.scheme not in ("http", "https"):
                continue

            is_int = parsed.netloc == self.domain or parsed.netloc == ""
            if is_int:
                internal += 1
                links.append(abs_url)
                # Check nofollow on internal
                rel = a.get("rel", [])
                if isinstance(rel, list):
                    if "nofollow" in rel:
                        nofollow_internal += 1
                elif "nofollow" in str(rel):
                    nofollow_internal += 1
            else:
                external += 1

        self.r.internal_links = internal
        self.r.external_links = external
        self.r.internal_links_nofollow = nofollow_internal

        if nofollow_internal > 0:
            self.add_issue("warning", "links", "nofollow_internal",
                f"{nofollow_internal} внутренних ссылок с nofollow",
                f"{nofollow_internal} шт.", "0 шт.")

        return links


# === SITE ANALYZER (Cross-page) ===

class SiteAnalyzer:
    """Cross-page analysis after all pages are crawled."""

    def __init__(self, result: SiteAuditResult,
                 internal_link_targets: Dict[str, Set[str]],
                 sitemap_urls: Set[str]):
        self.result = result
        self.link_targets = internal_link_targets
        self.sitemap_urls = sitemap_urls

    def analyze(self):
        self._find_duplicate_titles()
        self._find_duplicate_descriptions()
        self._find_duplicate_content()
        self._find_orphan_pages()
        self._find_deep_pages()
        self._build_redirect_map()
        self._build_broken_link_map()
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

    def _find_duplicate_content(self):
        hash_groups: Dict[str, List[str]] = defaultdict(list)
        for url, page in self.result.pages.items():
            if page.content_hash:
                hash_groups[page.content_hash].append(url)

        self.result.duplicate_content = [
            {"urls": urls}
            for h, urls in hash_groups.items()
            if len(urls) > 1
        ]

    def _find_orphan_pages(self):
        crawled_normed = set()
        normed_to_url: Dict[str, str] = {}
        for url in self.result.pages:
            parsed = urlparse(url)
            normed = urlunparse((parsed.scheme, parsed.netloc, parsed.path.rstrip("/") or "/", "", "", ""))
            crawled_normed.add(normed)
            normed_to_url[normed] = url

        for sitemap_url in self.sitemap_urls:
            parsed = urlparse(sitemap_url)
            normed = urlunparse((parsed.scheme, parsed.netloc, parsed.path.rstrip("/") or "/", "", "", ""))
            if normed in crawled_normed:
                url = normed_to_url[normed]
                # Check if any internal links point to it (not counting self)
                if normed not in self.link_targets or len(self.link_targets.get(normed, set())) == 0:
                    self.result.orphan_pages.append(sitemap_url)

    def _find_deep_pages(self):
        for url, page in self.result.pages.items():
            if page.crawl_depth > 3:
                self.result.deep_pages.append({
                    "url": url,
                    "depth": page.crawl_depth,
                })

    def _build_redirect_map(self):
        for url, page in self.result.pages.items():
            if page.redirect_chain and len(page.redirect_chain) > 1:
                self.result.redirect_map.append({
                    "chain": page.redirect_chain,
                    "hops": len(page.redirect_chain) - 1,
                    "type": page.redirect_type,
                })

    def _build_broken_link_map(self):
        broken_urls = {
            url for url, page in self.result.pages.items()
            if page.status_code >= 400
        }
        for url, page in self.result.pages.items():
            for broken in broken_urls:
                if broken in self.link_targets:
                    if url in self.link_targets[broken]:
                        self.result.broken_link_map.append({
                            "source": url,
                            "brokenUrl": broken,
                            "statusCode": self.result.pages[broken].status_code,
                        })

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
            code_group = f"{page.status_code // 100}xx" if page.status_code else "error"
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


# === REPORT GENERATOR (Scoring + Recommendations) ===

class ReportGenerator:
    """Calculates scores and generates recommendations."""

    def __init__(self, result: SiteAuditResult):
        self.result = result

    def calculate_scores(self):
        if not self.result.pages:
            return

        # Overall score
        total_penalty = 0
        for page in self.result.pages.values():
            for issue in page.issues:
                total_penalty += PENALTY_WEIGHTS.get(issue.severity, 0)

        # Normalize: cap at reasonable level
        n = max(1, self.result.total_scanned)
        # penalty per page, scaled so 10 issues avg = score 0
        normalized_penalty = (total_penalty / n) * 5
        self.result.health_score = max(0, min(100, int(100 - normalized_penalty)))

        # Category scores
        categories = {
            "technical": ["technical", "security"],
            "content": ["content"],
            "images": ["images"],
            "links": ["links"],
            "structured_data": ["structured_data"],
        }

        for cat_name, cat_keys in categories.items():
            cat_penalty = 0
            for page in self.result.pages.values():
                for issue in page.issues:
                    if issue.category in cat_keys:
                        cat_penalty += PENALTY_WEIGHTS.get(issue.severity, 0)
            cat_penalty = min(cat_penalty, MAX_CATEGORY_PENALTY * n)
            cat_score = max(0, min(100, int(100 - (cat_penalty / n) * 8)))
            self.result.category_scores[cat_name] = cat_score

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
                    "Description": page.description[:80],
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
                "Description": page.description,
                "Дл. Description": page.description_length,
                "H1": "; ".join(page.h1_list),
                "Слов": page.word_count,
                "TTFB": round(page.ttfb, 2),
                "Ошибок": len(page.issues),
            })
        return pd.DataFrame(rows).to_csv(index=False)


# === FASTAPI APPLICATION ===

app = FastAPI(title="SEO Audit Machine API", version="1.0.0")

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# In-memory audit storage
audits: Dict[str, dict] = {}


def serialize_result(result: SiteAuditResult) -> dict:
    """Convert SiteAuditResult to JSON-serializable dict."""
    pages = {}
    for url, page in result.pages.items():
        pages[url] = page.to_dict()

    return {
        "baseUrl": result.base_url,
        "domain": result.domain,
        "pages": pages,
        "duration": result.duration,
        "totalScanned": result.total_scanned,
        "sitemapUrls": list(result.sitemap_urls)[:100],
        "robotsTxtContent": result.robots_txt_content[:3000],
        "robotsRules": result.robots_rules,
        "robotsSitemaps": result.robots_sitemaps,
        "robotsHasHost": result.robots_has_host,
        "robotsHostValue": result.robots_host_value,
        "robotsHasCleanParam": result.robots_has_clean_param,
        "sslValid": result.ssl_valid,
        "sslError": result.ssl_error,
        "httpToHttps": result.http_to_https,
        "wwwConsistency": result.www_consistency,
        "homepageHeaders": result.homepage_headers,
        "detectedFrameworks": result.detected_frameworks,
        "hasLlmsTxt": result.has_llms_txt,
        "duplicateTitles": result.duplicate_titles,
        "duplicateDescriptions": result.duplicate_descriptions,
        "duplicateContent": result.duplicate_content,
        "orphanPages": result.orphan_pages[:50],
        "deepPages": result.deep_pages,
        "redirectMap": result.redirect_map,
        "brokenLinkMap": result.broken_link_map,
        "sitemapVsCrawled": result.sitemap_vs_crawled,
        "healthScore": result.health_score,
        "categoryScores": result.category_scores,
        "recommendations": result.recommendations,
        "statusCodes": result.status_codes,
        "issuesBySeverity": result.issues_by_severity,
        "issuesByCategory": result.issues_by_category,
    }


def run_audit(audit_id: str, url: str, max_pages: int, max_depth: int,
              crawl_delay: float, respect_robots: bool, check_external: bool):
    """Run audit in background, storing events for SSE."""
    audits[audit_id]["status"] = "scanning"
    audits[audit_id]["events"] = []

    def progress(event):
        audits[audit_id]["events"].append(event)

    try:
        crawler = CrawlerEngine(
            start_url=url,
            max_pages=max_pages,
            max_depth=max_depth,
            crawl_delay=crawl_delay,
            respect_robots=respect_robots,
            check_external=check_external,
        )
        audits[audit_id]["crawler"] = crawler

        result = crawler.crawl(progress_callback=progress)

        audits[audit_id]["status"] = "done"
        audits[audit_id]["result"] = result
        audits[audit_id]["serialized"] = serialize_result(result)
        audits[audit_id]["events"].append({"type": "done"})

    except Exception as e:
        logger.error(f"Audit {audit_id} failed: {e}")
        audits[audit_id]["status"] = "error"
        audits[audit_id]["error"] = str(e)
        audits[audit_id]["events"].append({"type": "error", "message": str(e)[:200]})


@app.post("/api/audit/start")
async def start_audit(
    background_tasks: BackgroundTasks,
    url: str = Query(...),
    max_pages: int = Query(50, ge=10, le=200),
    max_depth: int = Query(5, ge=1, le=10),
    crawl_delay: float = Query(0.3, ge=0.1, le=2.0),
    respect_robots: bool = Query(True),
    check_external: bool = Query(False),
):
    """Start a new SEO audit."""
    # Validate URL
    if not url.startswith(("http://", "https://")):
        url = "https://" + url

    parsed = urlparse(url)
    if not parsed.netloc:
        return JSONResponse({"error": ERROR_MESSAGES_RU["invalid_url"]}, status_code=400)

    audit_id = str(uuid.uuid4())[:8]
    audits[audit_id] = {
        "id": audit_id,
        "url": url,
        "status": "starting",
        "events": [],
        "result": None,
        "serialized": None,
        "crawler": None,
    }

    background_tasks.add_task(
        run_audit, audit_id, url, max_pages, max_depth,
        crawl_delay, respect_robots, check_external
    )

    return {"auditId": audit_id, "status": "starting"}


@app.get("/api/audit/{audit_id}/events")
async def audit_events(audit_id: str, since: int = Query(0)):
    """SSE-like polling endpoint for crawl progress."""
    if audit_id not in audits:
        return JSONResponse({"error": "Аудит не найден"}, status_code=404)

    audit = audits[audit_id]
    events = audit["events"][since:]
    return {
        "status": audit["status"],
        "events": events,
        "total": len(audit["events"]),
    }


@app.get("/api/audit/{audit_id}/result")
async def audit_result(audit_id: str):
    """Get full audit results."""
    if audit_id not in audits:
        return JSONResponse({"error": "Аудит не найден"}, status_code=404)

    audit = audits[audit_id]
    if audit["status"] != "done":
        return JSONResponse({
            "status": audit["status"],
            "error": audit.get("error", ""),
        }, status_code=202)

    return audit["serialized"]


@app.get("/api/audit/{audit_id}/export/xlsx")
async def export_xlsx(audit_id: str):
    """Export audit as XLSX."""
    if audit_id not in audits or audits[audit_id]["status"] != "done":
        return JSONResponse({"error": "Аудит не завершён"}, status_code=400)

    result = audits[audit_id]["result"]
    gen = ReportGenerator(result)
    xlsx_bytes = gen.to_excel()

    domain = result.domain.replace(".", "-")
    date_str = datetime.now().strftime("%Y-%m-%d")
    filename = f"seo-audit-{domain}-{date_str}.xlsx"

    return StreamingResponse(
        io.BytesIO(xlsx_bytes),
        media_type="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
        headers={"Content-Disposition": f'attachment; filename="{filename}"'},
    )


@app.get("/api/audit/{audit_id}/export/csv")
async def export_csv(audit_id: str):
    """Export audit as CSV."""
    if audit_id not in audits or audits[audit_id]["status"] != "done":
        return JSONResponse({"error": "Аудит не завершён"}, status_code=400)

    result = audits[audit_id]["result"]
    gen = ReportGenerator(result)
    csv_str = gen.to_csv()

    domain = result.domain.replace(".", "-")
    date_str = datetime.now().strftime("%Y-%m-%d")
    filename = f"seo-audit-{domain}-{date_str}.csv"

    return StreamingResponse(
        io.BytesIO(csv_str.encode("utf-8")),
        media_type="text/csv",
        headers={"Content-Disposition": f'attachment; filename="{filename}"'},
    )


@app.post("/api/audit/{audit_id}/stop")
async def stop_audit(audit_id: str):
    """Stop a running audit."""
    if audit_id not in audits:
        return JSONResponse({"error": "Аудит не найден"}, status_code=404)

    crawler = audits[audit_id].get("crawler")
    if crawler:
        crawler.stop()
    return {"status": "stopping"}


@app.get("/api/health")
async def health():
    return {"status": "ok", "version": "1.0.0"}


if __name__ == "__main__":
    uvicorn.run(app, host="0.0.0.0", port=8000)
