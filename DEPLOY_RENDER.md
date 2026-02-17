# Deploy на Render + поддомен `seo.cargoraptor.ru`

## 1) Проверка локально

```bash
cd /Users/a1/Documents/SEO_audit
pip3 install -r requirements.txt
python3 -m streamlit run app.py
```

Проверь в браузере: `http://localhost:8501`

## 2) Подготовить Git-репозиторий (обязательно для Blueprint)

Если репозиторий еще не создан:

```bash
cd /Users/a1/Documents/SEO_audit
git init
git add .
git commit -m "Initial SEO audit app for Render deploy"
git branch -M main
git remote add origin <YOUR_GIT_REMOTE_URL>
git push -u origin main
```

`<YOUR_GIT_REMOTE_URL>` — ссылка на GitHub/GitLab/Bitbucket репозиторий.

## 3) Деплой через Render Blueprint

1. Открой Render Dashboard.
2. Нажми **New +** -> **Blueprint**.
3. Подключи репозиторий.
4. Render автоматически найдёт `render.yaml`.
5. Нажми **Apply**.

Используемая конфигурация:
- `runtime: python`
- `plan: free`
- `startCommand`: Streamlit на `0.0.0.0:$PORT`

## 4) Подключение поддомена `seo.cargoraptor.ru`

1. В Render открой сервис -> **Settings** -> **Custom Domains**.
2. Добавь `seo.cargoraptor.ru`.
3. Render покажет DNS-цель (обычно `...onrender.com`).
4. В Cloudflare -> DNS создай:
   - `Type`: `CNAME`
   - `Name`: `seo`
   - `Target`: значение из Render
5. На время первичной проверки SSL лучше поставить `DNS only` (серое облако).
6. После статуса **Verified/Active** можно включить проксирование Cloudflare при необходимости.

## 5) Ограничить доступ только для своих (опционально)

Если нужен доступ не всем по ссылке:
- В Cloudflare Zero Trust создай Access-приложение для `seo.cargoraptor.ru`.
- Разреши вход только нужным email-доменам или конкретным адресам.

## 6) Проверка после деплоя

Проверь:
- открывается `https://seo.cargoraptor.ru`
- запускается аудит
- доступны скачивания XLSX/CSV
- нет падений в логах Render

