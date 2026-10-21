"""综测雷达：监控学校/重庆市/学会网站上与综测加分相关的通知，有新的就发邮件。

用法：
    python monitor.py                 日常运行：抓取 → 筛选 → 发邮件 → 更新 state/
    python monitor.py --dry-run       只生成 out/digest.html 预览，不发邮件、不改 state/
    python monitor.py --backfill 365  回溯过去 N 天的通知，生成 out/timeline.html（去年各月有哪些机会）
    python monitor.py --timeline      不重新抓取，按当前关键词重新生成时间表

发邮件需要的环境变量（在 GitHub Secrets 里配置）：
    SMTP_USER  发件邮箱，如 12345@qq.com
    SMTP_PASS  邮箱的 SMTP 授权码（不是登录密码）
    MAIL_TO    收件邮箱，不填则发给自己
    SMTP_HOST  默认 smtp.qq.com；163 邮箱填 smtp.163.com
    SMTP_PORT  默认 465（SSL）
"""

import argparse
import html
import json
import os
import re
import smtplib
import sys
import time
from dataclasses import dataclass, field
from datetime import date, datetime, timedelta, timezone
from email.mime.multipart import MIMEMultipart
from email.mime.text import MIMEText
from email.header import Header
from pathlib import Path
from urllib.parse import urljoin

import requests
import yaml
from bs4 import BeautifulSoup

ROOT = Path(__file__).resolve().parent
STATE_DIR = ROOT / "state"
OUT_DIR = ROOT / "out"
SEEN_FILE = STATE_DIR / "seen.json"
HISTORY_FILE = STATE_DIR / "history.json"
META_FILE = STATE_DIR / "meta.json"

BEIJING = timezone(timedelta(hours=8))
UA = {"User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                    "(KHTML, like Gecko) Chrome/130.0 Safari/537.36"}

# 日期格式：优先认数字格式（发布日期一般是 2026-10-18 这种），其次是"20 / 2026-10"这种拆开的，最后才是中文格式
NUM_DATE = re.compile(r"(20\d{2})[-/.](\d{1,2})[-/.](\d{1,2})(?!\d)")
SPLIT_DY = re.compile(r"(?<!\d)(\d{1,2})\s+(20\d{2})[-/.](\d{1,2})(?![-/.\d])")   # "20 2026-10"
SPLIT_YD = re.compile(r"(20\d{2})[-/.](\d{1,2})\s+(\d{1,2})(?!\d)")              # "2026-10 20"
CN_DATE = re.compile(r"(20\d{2})年(\d{1,2})月(\d{1,2})日")
NEXT_PAGE_TEXT = {"下页", "下一页", "下一頁", ">", "›", "»"}
DEADLINE_WORDS = re.compile(r"截止|截至|之前|前报送|前提交|前上交|报名时间|申报时间|提交时间|报名方式|申报时限")
DEADLINE_DATE = re.compile(r"\d{1,2}月\d{1,2}日|20\d{2}[-/.年]\d{1,2}")
DEADLINE_SKIP = re.compile(r"酒店|住宿|预订|会务费|注册费|缴费")


@dataclass
class Item:
    title: str
    url: str
    date: str               # YYYY-MM-DD
    source: str = ""
    cats: list = field(default_factory=list)
    is_result: bool = False
    focus: bool = False
    deadlines: list = field(default_factory=list)


def today_bj() -> date:
    return datetime.now(BEIJING).date()


def annotate(level: str, title: str, msg: str):
    """在 GitHub Actions 里输出注释（notice/warning/error），不登录也能在运行页面看到。"""
    if os.environ.get("GITHUB_ACTIONS") == "true":
        esc = lambda s: s.replace("%", "%25").replace("\r", "%0D").replace("\n", "%0A")
        print(f"::{level} title={esc(title).replace(':', '%3A').replace(',', '%2C')}::{esc(msg)}", flush=True)


# ---------------------------------------------------------------- 抓取与解析

def fetch(url: str, retries: int = 1) -> str:
    last = None
    for i in range(retries + 1):
        try:
            r = requests.get(url, headers=UA, timeout=15)
            r.raise_for_status()
            if not r.encoding or r.encoding.lower() == "iso-8859-1":
                r.encoding = r.apparent_encoding
            return r.text
        except Exception as e:  # 网络抖动时重试
            last = e
            time.sleep(2 * (i + 1))
    raise last


def norm_href(base: str, href: str):
    href = (href or "").strip()
    if not href or href.startswith(("javascript", "#", "mailto")):
        return None
    return urljoin(base, href).split("#")[0]


def to_date(y, m, d):
    try:
        return date(int(y), int(m), int(d))
    except ValueError:
        return None


def find_date(text: str):
    """在一段文字里找发布日期；排除明显是未来的日期（多半是活动举办时间）。"""
    latest_ok = today_bj() + timedelta(days=2)
    for pattern, order in ((NUM_DATE, (1, 2, 3)), (SPLIT_DY, (2, 3, 1)),
                           (SPLIT_YD, (1, 2, 3)), (CN_DATE, (1, 2, 3))):
        for m in pattern.finditer(text):
            d = to_date(*(m.group(i) for i in order))
            if d and d <= latest_ok:
                return d
    return None


def link_title(a) -> str:
    t = (a.get("title") or "").strip()
    if len(t) < 8:
        h = a.find(["h1", "h2", "h3", "h4", "h5"])
        t = h.get_text(" ", strip=True) if h else a.get_text(" ", strip=True)
        t = NUM_DATE.sub("", t)
        t = SPLIT_DY.sub("", t)
        t = re.sub(r"\d{1,2}:\d{2}(:\d{2})?", "", t)
    return re.sub(r"\s+", " ", t).strip(" -|·")


def date_near(a, href: str, base: str):
    """从链接本身往上找日期，碰到包含其他文章链接的容器就停（避免拿到隔壁条目的日期）。"""
    node = a
    for _ in range(6):
        if node is None or node.name in ("body", "html", "[document]"):
            return None
        if node is not a:
            others = {norm_href(base, x["href"]) for x in node.find_all("a", href=True)} - {None, href}
            if others:
                return None
        d = find_date(node.get_text(" ", strip=True))
        if d:
            return d
        node = node.parent
    return None


def extract_items(page_html: str, base: str, source: str):
    soup = BeautifulSoup(page_html, "html.parser")
    items, seen = [], set()
    for a in soup.find_all("a", href=True):
        href = norm_href(base, a["href"])
        if not href or href in seen or href.rstrip("/") == base.rstrip("/"):
            continue
        title = link_title(a)
        if len(title) < 8:
            continue
        d = date_near(a, href, base)
        if not d:
            continue
        seen.add(href)
        items.append(Item(title=title, url=href, date=d.isoformat(), source=source))
    return items, soup


def next_page(soup, base: str):
    for a in soup.find_all("a", href=True):
        if a.get_text(strip=True) in NEXT_PAGE_TEXT:
            u = norm_href(base, a["href"])
            if u and u != base:
                return u
    return None


# ---------------------------------------------------------------- 分类

def classify(item: Item, cfg: dict) -> bool:
    """给通知打上加分类别；返回 False 表示与综测无关、应忽略。"""
    t = item.title
    if any(w in t for w in cfg.get("exclude", [])):
        return False
    if cfg.get("skip_undergrad_only") and "本科" in t and "研究生" not in t:
        return False
    item.cats = [c["id"] for c in cfg["categories"] if any(k in t for k in c["keywords"])]
    item.is_result = any(w in t for w in cfg.get("result_words", []))
    item.focus = any(w.lower() in t.lower() for w in cfg.get("focus_words", []))
    return bool(item.cats)


def find_deadlines(url: str):
    """打开正文，挑出带截止时间的句子（最多两句）。"""
    try:
        soup = BeautifulSoup(fetch(url, retries=1), "html.parser")
    except Exception:
        return []
    for tag in soup(["script", "style", "nav", "header", "footer"]):
        tag.decompose()
    text = soup.get_text("\n", strip=True)
    out = []
    for s in re.split(r"[。；;\n]", text):
        s = s.strip()
        if (6 < len(s) < 160 and DEADLINE_WORDS.search(s) and DEADLINE_DATE.search(s)
                and not DEADLINE_SKIP.search(s)):
            s = s if len(s) <= 90 else s[:88] + "…"
            if s not in out:
                out.append(s)
        if len(out) >= 2:
            break
    return out


# ---------------------------------------------------------------- 状态

def load_json(path: Path, default):
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError):
        return default


def save_json(path: Path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding="utf-8")


# ---------------------------------------------------------------- 邮件内容

def cat_lookup(cfg):
    return {c["id"]: c for c in cfg["categories"]}


def render_items_html(items, cats):
    groups = {}
    for it in items:
        groups.setdefault(it.cats[0], []).append(it)
    order = [c for c in cats if c in groups]
    parts = []
    for cid in order:
        c = cats[cid]
        parts.append(f'<h3 style="margin:18px 0 4px;color:#1f4e79">{html.escape(c["name"])}'
                     f'（{len(groups[cid])}）</h3>'
                     f'<div style="color:#666;font-size:13px;margin-bottom:6px">{html.escape(c["hint"])}</div>')
        for it in sorted(groups[cid], key=lambda x: (x.focus, x.date), reverse=True):
            dl = "".join(f'<div style="color:#b03a2e;font-size:13px">⏰ {html.escape(s)}</div>'
                         for s in it.deadlines)
            star = "⭐ " if it.focus else ""
            parts.append(
                f'<div style="margin:6px 0 10px;padding-left:8px;border-left:3px solid #9cc3e6">'
                f'<a href="{html.escape(it.url)}" style="font-size:15px">{star}{html.escape(it.title)}</a>'
                f'<div style="color:#888;font-size:12px">{it.date} · {html.escape(it.source)}</div>{dl}</div>')
    return "\n".join(parts)


def render_digest(new_items, reminders, last_year, warnings, cfg, today):
    cats = cat_lookup(cfg)
    main = [i for i in new_items if not i.is_result]
    results = [i for i in new_items if i.is_result]
    body = [f'<div style="font-family:-apple-system,Microsoft YaHei,sans-serif;max-width:720px">'
            f'<h2 style="margin-bottom:4px">综测雷达 · {today:%Y年%m月%d日}</h2>']
    if reminders:
        body.append('<h3 style="color:#7d3c98">📌 本期提醒</h3>' +
                    "".join(f"<p>{html.escape(r)}</p>" for r in reminders))
    if main:
        body.append(f"<h2>新通知（{len(main)}）</h2>" + render_items_html(main, cats))
    if last_year:
        body.append(f'<h2 style="color:#555">去年{today.month}月出现过的相关通知（今年可能会再来）</h2>'
                    + render_items_html(last_year, cats))
    if results:
        body.append(f'<h2 style="color:#555">结果公示（{len(results)}，了解进度即可）</h2>'
                    + render_items_html(results, cats))
    if warnings:
        body.append('<h3 style="color:#b03a2e">⚠ 抓取异常</h3>' +
                    "".join(f"<p>{html.escape(w)}</p>" for w in warnings))
    body.append('<p style="color:#999;font-size:12px;margin-top:24px">分值依据《地理科学学院全日制研究生综合考评实施细则》，'
                '最终以学院评审小组认定为准。微信公众号和QQ群里的通知这里抓不到，记得也看一眼。</p></div>')
    return "\n".join(body)


def send_mail(subject: str, html_body: str):
    user, pwd = os.environ.get("SMTP_USER"), os.environ.get("SMTP_PASS")
    if not user or not pwd:
        raise RuntimeError("没有配置 SMTP_USER / SMTP_PASS，无法发邮件")
    to = os.environ.get("MAIL_TO") or user
    host = os.environ.get("SMTP_HOST") or "smtp.qq.com"
    port = int(os.environ.get("SMTP_PORT") or 465)
    msg = MIMEMultipart("alternative")
    msg["Subject"] = Header(subject, "utf-8")
    msg["From"] = user
    msg["To"] = to
    plain = re.sub(r"<[^>]+>", "", html_body.replace("</div>", "\n").replace("</p>", "\n"))
    msg.attach(MIMEText(html.unescape(plain), "plain", "utf-8"))
    msg.attach(MIMEText(html_body, "html", "utf-8"))
    with smtplib.SMTP_SSL(host, port, timeout=30) as s:
        s.login(user, pwd)
        s.sendmail(user, [x.strip() for x in to.split(",")], msg.as_string())


# ---------------------------------------------------------------- 日常运行

def due_reminders(cfg, meta, today):
    """当天或之后14天内的第一次运行推送；每条每年只推一次。"""
    sent = meta.setdefault("reminders_sent", {})
    out = []
    for r in cfg.get("reminders", []):
        m, d = map(int, r["date"].split("-"))
        start = to_date(today.year, m, d)
        key = f"{today.year}-{r['date']}"
        if start and start <= today <= start + timedelta(days=14) and key not in sent:
            out.append(r["text"])
            sent[key] = today.isoformat()
    return out


def last_year_preview(cfg, meta, today):
    """每月第一次运行时，附上去年同月出现过的相关通知。"""
    key = f"{today:%Y-%m}"
    if meta.get("monthly_preview_sent") == key:
        return []
    meta["monthly_preview_sent"] = key
    hist = load_json(HISTORY_FILE, [])
    prefix = f"{today.year - 1}-{today.month:02d}"
    items = [Item(**h) for h in hist if h["date"].startswith(prefix)]
    # 按当前配置重新分类，这样改了关键词也能生效
    return [it for it in items if classify(it, cfg) and not it.is_result]


def run_daily(cfg, dry_run: bool):
    today = today_bj()
    seen = load_json(SEEN_FILE, {})
    meta = load_json(META_FILE, {})
    fails = meta.setdefault("fail_counts", {})
    cutoff = (today - timedelta(days=cfg.get("lookback_days", 21))).isoformat()

    new_items, warnings, ok_sources, titles_seen = [], [], 0, set()
    failed_names = []
    for src in cfg["sources"]:
        name, url = src["name"], src["url"]
        t0 = time.time()
        try:
            items, _ = extract_items(fetch(url), url, name)
        except Exception as e:
            fails[name] = fails.get(name, 0) + 1
            failed_names.append(name)
            print(f"[失败] {name}: {type(e).__name__} {e}", file=sys.stderr)
            annotate("warning", f"抓取失败 {name}", f"{type(e).__name__}（{time.time() - t0:.0f}秒）：{str(e)[:200]}")
            if fails[name] >= 3:
                warnings.append(f"{name} 已连续 {fails[name]} 次抓取失败（{type(e).__name__}），网站可能改版或屏蔽了访问。")
            continue
        ok_sources += 1
        fails[name] = 0
        if not items:
            warnings.append(f"{name} 页面能打开但没解析出任何通知，可能改版了：{url}")
        for it in items:
            if it.url in seen:
                continue
            seen[it.url] = today.isoformat()
            key = re.sub(r"\W", "", it.title)
            if it.date < cutoff or key in titles_seen or not classify(it, cfg):
                continue
            titles_seen.add(key)
            new_items.append(it)
        print(f"[完成] {name}: 解析 {len(items)} 条")
        time.sleep(1)

    if ok_sources == 0:
        warnings.insert(0, "所有网站都抓取失败：运行环境可能访问不了这些网站（例如 GitHub 的海外服务器被屏蔽）。")

    for it in sorted(new_items, key=lambda x: x.date, reverse=True)[: cfg.get("max_detail_fetch", 15)]:
        if not it.is_result:
            it.deadlines = find_deadlines(it.url)

    reminders = due_reminders(cfg, meta, today)
    last_year = last_year_preview(cfg, meta, today)
    has_content = new_items or reminders or warnings or last_year

    summary = (f"网站 {ok_sources}/{len(cfg['sources'])} 个抓取成功；新通知 {len(new_items)} 条，"
               f"提醒 {len(reminders)} 条，去年同月 {len(last_year)} 条，警告 {len(warnings)} 条")
    print(summary)
    annotate("notice", "运行结果", summary + (f"。失败：{'、'.join(failed_names)}" if failed_names else ""))
    digest = render_digest(new_items, reminders, last_year, warnings, cfg, today)
    OUT_DIR.mkdir(exist_ok=True)
    (OUT_DIR / "digest.html").write_text(digest, encoding="utf-8")

    if dry_run:
        print(f"预览已写入 {OUT_DIR / 'digest.html'}（dry-run：未发邮件、未更新状态）")
        return

    if has_content:
        main_n = sum(1 for i in new_items if not i.is_result)
        subject = f"【综测雷达】{today:%m月%d日} · {main_n} 条新通知" if main_n else f"【综测雷达】{today:%m月%d日} · 提醒"
        try:
            send_mail(subject, digest)
        except Exception as e:
            annotate("error", "邮件发送失败", f"{type(e).__name__}: {e}")
            raise
        print("邮件已发送")
        annotate("notice", "邮件已发送", subject)
    else:
        print("没有新内容，不发邮件")

    hist = load_json(HISTORY_FILE, [])
    hist_urls = {h["url"] for h in hist}
    hist += [it.__dict__ for it in new_items if it.url not in hist_urls]
    keep_from = (today - timedelta(days=800)).isoformat()
    save_json(HISTORY_FILE, [h for h in hist if h["date"] >= keep_from])
    save_json(SEEN_FILE, {u: d for u, d in seen.items() if d >= keep_from})
    save_json(META_FILE, meta)


# ---------------------------------------------------------------- 回溯

def run_backfill(cfg, days: int, max_pages: int = 25):
    today = today_bj()
    cutoff = (today - timedelta(days=days)).isoformat()
    found, titles_seen = [], set()
    for src in cfg["sources"]:
        name, url, pages = src["name"], src["url"], 0
        total = 0
        while url and pages < max_pages:
            try:
                items, soup = extract_items(fetch(url), url, name)
            except Exception as e:
                print(f"[失败] {name} 第{pages + 1}页: {e}", file=sys.stderr)
                break
            pages += 1
            total += len(items)
            for it in items:
                key = re.sub(r"\W", "", it.title)
                if it.date >= cutoff and key not in titles_seen and classify(it, cfg):
                    titles_seen.add(key)
                    found.append(it)
            if not items or min(i.date for i in items) < cutoff:
                break
            url = next_page(soup, url)
            time.sleep(1)
        print(f"[完成] {name}: {pages} 页，{total} 条")

    # 存入历史，供"去年同月"提醒使用
    hist = load_json(HISTORY_FILE, [])
    hist_urls = {h["url"] for h in hist}
    hist += [it.__dict__ for it in found if it.url not in hist_urls]
    save_json(HISTORY_FILE, hist)
    print(f"共找到 {len(found)} 条相关通知")
    write_timeline(cfg, days)


def write_timeline(cfg, days: int = 365):
    """用 state/history.json 生成按月排列的时间表（按当前配置重新分类）。"""
    cutoff = (today_bj() - timedelta(days=days)).isoformat()
    cats = cat_lookup(cfg)
    by_month = {}
    for h in load_json(HISTORY_FILE, []):
        it = Item(**h)
        if it.date >= cutoff and classify(it, cfg) and not it.is_result:
            by_month.setdefault(it.date[:7], []).append(it)
    body = [f'<div style="font-family:-apple-system,Microsoft YaHei,sans-serif;max-width:760px">'
            f'<h1>过去 {days} 天的综测相关通知（按月）</h1>'
            f'<p>共 {sum(len(v) for v in by_month.values())} 条（不含结果公示）。很多活动每年时间相近，可以对照着提前准备。'
            f'⭐ 表示和地信方向或研究生相关。</p>']
    for ym in sorted(by_month, reverse=True):
        body.append(f'<h2 style="border-bottom:1px solid #ccc">{ym[:4]}年{int(ym[5:])}月</h2>'
                    + render_items_html(by_month[ym], cats))
    body.append("</div>")
    OUT_DIR.mkdir(exist_ok=True)
    (OUT_DIR / "timeline.html").write_text("\n".join(body), encoding="utf-8")
    print(f"时间表已写入 {OUT_DIR / 'timeline.html'}")


def main():
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
        sys.stderr.reconfigure(encoding="utf-8")
    ap = argparse.ArgumentParser(description="综测雷达")
    ap.add_argument("--dry-run", action="store_true", help="只生成预览，不发邮件、不改状态")
    ap.add_argument("--backfill", type=int, metavar="DAYS", help="回溯过去 DAYS 天，生成时间表")
    ap.add_argument("--timeline", action="store_true", help="不重新抓取，用已有历史重新生成时间表")
    args = ap.parse_args()
    cfg = yaml.safe_load((ROOT / "config.yaml").read_text(encoding="utf-8"))
    if args.backfill:
        run_backfill(cfg, args.backfill)
    elif args.timeline:
        write_timeline(cfg)
    else:
        run_daily(cfg, args.dry_run)


if __name__ == "__main__":
    main()
