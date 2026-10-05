"""
Xavfsiz Telegram moderation boti (asyncio + aiohttp).

Imkoniyatlar:
  - Anti-link / anti-spam (entities + regex + normalizatsiya, adminlar mustasno)
  - Anti-flood (ketma-ket xabarlarni cheklash)
  - Ogohlantirish tizimi (3 ogohlantirish -> 24 soat mute)
  - Captcha (yangi a'zo tugmani bossa yozadi, bosmasa chiqarib yuboriladi)
  - Spam botlarni avtomatik ban qilish (adminlar qo'shmagan bo'lsa)
  - Majburiy obuna (REQUIRED_CHANNEL)
  - Kanal join request'larini avto-qabul + DM

Muhit o'zgaruvchilari (ENV):
  BOT_TOKEN         (majburiy)
  PORT              (Render beradi, default 10000)
  REQUIRED_CHANNEL  (ixtiyoriy, masalan @kanalim)
  ALLOWED_DOMAINS   (ixtiyoriy, vergul bilan: youtube.com,instagram.com)
  BAD_WORDS         (ixtiyoriy, vergul bilan)
  WELCOME_TEXT      (ixtiyoriy)
"""
import asyncio
import html
import logging
import os
import re
import signal
import time
import unicodedata
from collections import defaultdict, deque
from urllib.parse import urlparse

import aiohttp
from aiohttp import web

# ───────────────────────── Sozlamalar ─────────────────────────
TOKEN = os.environ["BOT_TOKEN"]
PORT = int(os.getenv("PORT", "10000"))
REQUIRED_CHANNEL = os.getenv("REQUIRED_CHANNEL", "").strip()
WELCOME_TEXT = os.getenv("WELCOME_TEXT", "Salom! So'rovingiz qabul qilindi ✅")


def _env_set(name: str) -> set[str]:
    return {x.strip().lower() for x in os.getenv(name, "").split(",") if x.strip()}


ALLOWED_DOMAINS = _env_set("ALLOWED_DOMAINS")
BAD_WORDS = _env_set("BAD_WORDS")

CAPTCHA_TIMEOUT = 120      # soniya
MAX_WARNS = 3
MUTE_SECONDS = 24 * 3600
FLOOD_LIMIT, FLOOD_WINDOW = 6, 8   # 8 soniyada 6 tadan ko'p xabar
NOTICE_TTL = 10
MAX_CONCURRENCY = 50
SYSTEM_IDS = {777000, 1087968824}  # Telegram servis / anonim admin

ALLOWED_UPDATES = ["message", "edited_message", "callback_query", "chat_join_request"]


# ───────────────────────── Logging (token yashiriladi) ─────────────────────────
class RedactToken(logging.Filter):
    def filter(self, record: logging.LogRecord) -> bool:
        record.msg = record.getMessage().replace(TOKEN, "***")
        record.args = ()
        return True


handler = logging.StreamHandler()
handler.addFilter(RedactToken())
logging.basicConfig(level=logging.INFO, handlers=[handler],
                    format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("defensy")


# ───────────────────────── Telegram API ─────────────────────────
class TG:
    def __init__(self, token: str):
        self.base = f"https://api.telegram.org/bot{token}/"
        self.session: aiohttp.ClientSession | None = None

    async def start(self):
        self.session = aiohttp.ClientSession(timeout=aiohttp.ClientTimeout(total=65))

    async def close(self):
        if self.session:
            await self.session.close()

    async def call(self, method: str, **params):
        """Natija yoki None qaytaradi. 429 va tarmoq xatolarida qayta urinadi."""
        for attempt in range(4):
            try:
                async with self.session.post(self.base + method, json=params) as r:
                    data = await r.json(content_type=None)
            except (aiohttp.ClientError, asyncio.TimeoutError) as e:
                log.warning("%s tarmoq xatosi: %s", method, type(e).__name__)
                await asyncio.sleep(2 ** attempt)
                continue
            if data.get("ok"):
                return data["result"]
            if data.get("error_code") == 429:
                wait = data.get("parameters", {}).get("retry_after", 1)
                await asyncio.sleep(wait + 1)
                continue
            log.info("%s xato: %s", method, data.get("description"))
            return None
        return None


# ───────────────────────── Matn tekshiruvlari ─────────────────────────
URL_RE = re.compile(
    r"(?:https?://|www\.|tg://|telegram\.(?:me|dog)/|\bt\s*\.\s*me\s*/)"
    r"|\b[a-z0-9-]+\.(?:com|ru|uz|org|net|me|io|xyz|info|ly|cc|top|site|online|club|link)\b",
    re.I,
)
ZERO_WIDTH = re.compile(r"[\u200b-\u200f\u202a-\u202e\u2060\ufeff]")


def normalize(text: str) -> str:
    text = unicodedata.normalize("NFKC", text)
    return ZERO_WIDTH.sub("", text).lower()


def host_allowed(host: str) -> bool:
    host = host.lower().removeprefix("www.")
    return any(host == d or host.endswith("." + d) for d in ALLOWED_DOMAINS)


def entity_text(text: str, e: dict) -> str:
    raw = text.encode("utf-16-le")  # Telegram offsetlari UTF-16 bo'yicha
    return raw[2 * e["offset"]: 2 * (e["offset"] + e["length"])].decode("utf-16-le", "ignore")


def has_forbidden_link(msg: dict) -> bool:
    text = msg.get("text") or msg.get("caption") or ""
    ents = msg.get("entities") or msg.get("caption_entities") or []
    for e in ents:
        if e["type"] == "text_link":
            if not host_allowed(urlparse(e.get("url", "")).hostname or ""):
                return True
        elif e["type"] == "url":
            u = entity_text(text, e)
            host = urlparse(u if "//" in u else "//" + u).hostname or ""
            if not host_allowed(host):
                return True
        elif e["type"] == "email":
            return True
    norm = normalize(text)
    for d in ALLOWED_DOMAINS:
        norm = norm.replace(d, "")
    return bool(URL_RE.search(norm))


def has_bad_word(text: str) -> bool:
    norm = normalize(text)
    return any(w in norm for w in BAD_WORDS)


# ───────────────────────── Bot ─────────────────────────
class Bot:
    def __init__(self):
        self.tg = TG(TOKEN)
        self.stop = asyncio.Event()
        self.sem = asyncio.Semaphore(MAX_CONCURRENCY)
        self.tasks: set[asyncio.Task] = set()
        self.me_id = 0
        self.admin_cache: dict[tuple, tuple] = {}
        self.flood: dict[tuple, deque] = defaultdict(deque)
        self.warns: dict[tuple, tuple] = {}            # (chat,user) -> (soni, vaqt)
        self.pending: dict[tuple, asyncio.Task] = {}   # captcha kutayotganlar

    # ---- yordamchilar ----
    def spawn(self, coro) -> asyncio.Task:
        t = asyncio.create_task(coro)
        self.tasks.add(t)
        t.add_done_callback(self.tasks.discard)
        return t

    async def safe(self, coro):
        async with self.sem:
            try:
                await coro
            except Exception:
                log.exception("Handler xatosi")

    async def is_admin(self, chat_id: int, user_id: int) -> bool:
        key, now = (chat_id, user_id), time.monotonic()
        hit = self.admin_cache.get(key)
        if hit and now - hit[1] < 300:
            return hit[0]
        m = await self.tg.call("getChatMember", chat_id=chat_id, user_id=user_id)
        ok = bool(m) and m["status"] in ("creator", "administrator")
        self.admin_cache[key] = (ok, now)
        return ok

    async def is_subscribed(self, user_id: int) -> bool:
        m = await self.tg.call("getChatMember", chat_id=REQUIRED_CHANNEL, user_id=user_id)
        if m is None:
            return True  # bot kanalda admin emas bo'lsa hammani bloklab qo'ymaymiz
        return m["status"] in ("creator", "administrator", "member") or (
            m["status"] == "restricted" and m.get("is_member"))

    async def notify(self, chat_id: int, text: str, ttl: int = NOTICE_TTL, **extra):
        m = await self.tg.call("sendMessage", chat_id=chat_id, text=text,
                               parse_mode="HTML", **extra)
        if m and ttl:
            async def _del():
                await asyncio.sleep(ttl)
                await self.tg.call("deleteMessage", chat_id=chat_id, message_id=m["message_id"])
            self.spawn(_del())

    @staticmethod
    def mention(u: dict) -> str:
        name = html.escape(u.get("first_name") or "Foydalanuvchi")
        return f'<a href="tg://user?id={u["id"]}">{name}</a>'

    # ---- jazo tizimi ----
    async def punish(self, msg: dict, reason: str):
        chat_id, user = msg["chat"]["id"], msg["from"]
        await self.tg.call("deleteMessage", chat_id=chat_id, message_id=msg["message_id"])
        key, now = (chat_id, user["id"]), time.time()
        count, ts = self.warns.get(key, (0, now))
        count = count + 1 if now - ts < 86400 else 1
        if count >= MAX_WARNS:
            self.warns.pop(key, None)
            await self.tg.call("restrictChatMember", chat_id=chat_id, user_id=user["id"],
                               permissions={"can_send_messages": False},
                               until_date=int(now) + MUTE_SECONDS)
            await self.notify(chat_id, f"🔇 {self.mention(user)} 24 soatga cheklandi ({reason}).")
        else:
            self.warns[key] = (count, now)
            await self.notify(chat_id, f"⚠️ {self.mention(user)}, {reason}. Ogohlantirish {count}/{MAX_WARNS}.")

    def is_flood(self, key: tuple) -> bool:
        now, dq = time.monotonic(), self.flood[key]
        dq.append(now)
        while dq and now - dq[0] > FLOOD_WINDOW:
            dq.popleft()
        return len(dq) > FLOOD_LIMIT

    # ---- update'larni yo'naltirish ----
    async def dispatch(self, u: dict):
        if "message" in u or "edited_message" in u:
            await self.on_message(u.get("message") or u["edited_message"])
        elif "callback_query" in u:
            await self.on_callback(u["callback_query"])
        elif "chat_join_request" in u:
            await self.on_join_request(u["chat_join_request"])

    async def on_message(self, msg: dict):
        chat = msg["chat"]
        if chat["type"] == "private":
            if (msg.get("text") or "").startswith("/start"):
                await self.tg.call("sendMessage", chat_id=chat["id"],
                                   text="👋 Men guruh va kanallarni himoya qiluvchi botman.\n"
                                        "Meni guruhga admin qilib qo'shing.")
            return
        if chat["type"] not in ("group", "supergroup"):
            return

        if msg.get("new_chat_members"):
            return await self.on_new_members(msg)
        if msg.get("left_chat_member"):
            t = self.pending.pop((chat["id"], msg["left_chat_member"]["id"]), None)
            if t:
                t.cancel()
            await self.tg.call("deleteMessage", chat_id=chat["id"], message_id=msg["message_id"])
            return

        user = msg.get("from")
        if not user or user["id"] in SYSTEM_IDS or user.get("is_bot"):
            return
        chat_id, uid = chat["id"], user["id"]
        if await self.is_admin(chat_id, uid):
            return

        if (chat_id, uid) in self.pending:  # captcha o'tmagan
            await self.tg.call("deleteMessage", chat_id=chat_id, message_id=msg["message_id"])
            return
        if REQUIRED_CHANNEL and not await self.is_subscribed(uid):
            await self.tg.call("deleteMessage", chat_id=chat_id, message_id=msg["message_id"])
            await self.notify(
                chat_id, f"{self.mention(user)}, yozish uchun avval {html.escape(REQUIRED_CHANNEL)} kanaliga obuna bo'ling.",
                reply_markup={"inline_keyboard": [[{
                    "text": "📢 Kanalga o'tish",
                    "url": f"https://t.me/{REQUIRED_CHANNEL.lstrip('@')}"}]]})
            return
        if self.is_flood((chat_id, uid)):
            return await self.punish(msg, "spam/flood")
        if has_forbidden_link(msg):
            return await self.punish(msg, "havola yuborish taqiqlangan")
        if has_bad_word(msg.get("text") or msg.get("caption") or ""):
            return await self.punish(msg, "so'kinish taqiqlangan")

    # ---- captcha ----
    async def on_new_members(self, msg: dict):
        chat_id = msg["chat"]["id"]
        adder = msg.get("from") or {}
        await self.tg.call("deleteMessage", chat_id=chat_id, message_id=msg["message_id"])
        adder_admin = await self.is_admin(chat_id, adder.get("id", 0))
        for u in msg["new_chat_members"]:
            if u.get("is_bot"):
                if u["id"] != self.me_id and not adder_admin:
                    await self.tg.call("banChatMember", chat_id=chat_id, user_id=u["id"])
                continue
            if adder_admin and adder.get("id") != u["id"]:
                continue  # admin o'zi qo'shgan
            await self.start_captcha(chat_id, u)

    async def start_captcha(self, chat_id: int, user: dict):
        uid = user["id"]
        await self.tg.call("restrictChatMember", chat_id=chat_id, user_id=uid,
                           permissions={"can_send_messages": False})
        m = await self.tg.call(
            "sendMessage", chat_id=chat_id, parse_mode="HTML",
            text=f"👋 {self.mention(user)}, robot emasligingizni tasdiqlang.\n"
                 f"{CAPTCHA_TIMEOUT} soniya ichida tugmani bosing.",
            reply_markup={"inline_keyboard": [[{"text": "✅ Men robot emasman",
                                                "callback_data": f"cap:{uid}"}]]})
        if not m:
            return
        self.pending[(chat_id, uid)] = self.spawn(
            self.captcha_timeout(chat_id, uid, m["message_id"]))

    async def captcha_timeout(self, chat_id: int, uid: int, mid: int):
        await asyncio.sleep(CAPTCHA_TIMEOUT)
        self.pending.pop((chat_id, uid), None)
        # 60 soniyalik ban = chiqarib yuborish, keyin qayta qo'shilishi mumkin
        await self.tg.call("banChatMember", chat_id=chat_id, user_id=uid,
                           until_date=int(time.time()) + 60)
        await self.tg.call("deleteMessage", chat_id=chat_id, message_id=mid)

    async def on_callback(self, cb: dict):
        data = cb.get("data") or ""
        if not data.startswith("cap:") or not data[4:].isdigit() or "message" not in cb:
            return await self.tg.call("answerCallbackQuery", callback_query_id=cb["id"])
        uid, chat_id = int(data[4:]), cb["message"]["chat"]["id"]
        if cb["from"]["id"] != uid:
            return await self.tg.call("answerCallbackQuery", callback_query_id=cb["id"],
                                      text="Bu tugma siz uchun emas.", show_alert=True)
        task = self.pending.pop((chat_id, uid), None)
        if task:
            task.cancel()
        chat = await self.tg.call("getChat", chat_id=chat_id) or {}
        perms = chat.get("permissions") or {"can_send_messages": True}
        await self.tg.call("restrictChatMember", chat_id=chat_id, user_id=uid, permissions=perms)
        await self.tg.call("deleteMessage", chat_id=chat_id, message_id=cb["message"]["message_id"])
        await self.tg.call("answerCallbackQuery", callback_query_id=cb["id"], text="Tasdiqlandi ✅")

    # ---- kanal join request ----
    async def on_join_request(self, jr: dict):
        chat_id, user = jr["chat"]["id"], jr["from"]
        if user.get("is_bot"):
            return await self.tg.call("declineChatJoinRequest", chat_id=chat_id, user_id=user["id"])
        if await self.tg.call("approveChatJoinRequest", chat_id=chat_id, user_id=user["id"]):
            await self.tg.call("sendMessage", chat_id=jr["user_chat_id"], text=WELCOME_TEXT)

    # ---- xotirani tozalash ----
    async def janitor(self):
        while not self.stop.is_set():
            await asyncio.sleep(600)
            now_m, now = time.monotonic(), time.time()
            self.admin_cache = {k: v for k, v in self.admin_cache.items() if now_m - v[1] < 300}
            self.warns = {k: v for k, v in self.warns.items() if now - v[1] < 86400}
            for k in [k for k, dq in self.flood.items() if not dq or now_m - dq[-1] > FLOOD_WINDOW]:
                del self.flood[k]

    # ---- ishga tushirish ----
    async def poll(self):
        await self.tg.call("deleteWebhook", drop_pending_updates=False)
        offset = 0
        while not self.stop.is_set():
            updates = await self.tg.call("getUpdates", offset=offset, timeout=50,
                                         allowed_updates=ALLOWED_UPDATES)
            if updates is None:
                await asyncio.sleep(3)
                continue
            for u in updates:
                offset = u["update_id"] + 1
                self.spawn(self.safe(self.dispatch(u)))

    async def run(self):
        await self.tg.start()
        me = await self.tg.call("getMe")
        if not me:
            raise SystemExit("BOT_TOKEN noto'g'ri yoki Telegram'ga ulanib bo'lmadi")
        self.me_id = me["id"]
        log.info("Bot ishga tushdi: @%s", me.get("username"))

        # Render uchun health-check (faqat "ok" qaytaradi, boshqa ma'lumot bermaydi)
        app = web.Application()
        app.router.add_get("/", lambda r: web.Response(text="ok"))
        runner = web.AppRunner(app)
        await runner.setup()
        await web.TCPSite(runner, "0.0.0.0", PORT).start()

        loop = asyncio.get_running_loop()
        for sig in (signal.SIGINT, signal.SIGTERM):
            try:
                loop.add_signal_handler(sig, self.stop.set)
            except NotImplementedError:
                pass

        bg = [self.spawn(self.poll()), self.spawn(self.janitor())]
        await self.stop.wait()
        for t in bg + list(self.pending.values()):
            t.cancel()
        await runner.cleanup()
        await self.tg.close()


if __name__ == "__main__":
    asyncio.run(Bot().run())
