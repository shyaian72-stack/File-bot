#!/usr/bin/env python3
# =============================================================================
#  Shyaian FILE STORE BOT — Production Telegram File Store Bot
#  Single-file implementation (main.py) — SQLite, fully async
#  Framework: python-telegram-bot v22+, aiosqlite
# =============================================================================

from __future__ import annotations

import asyncio
import html
import json
import logging
import os
import re
import time
from datetime import datetime, timedelta

import aiosqlite
from telegram import (
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    KeyboardButton,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
    Update,
)
from telegram.constants import ParseMode
from telegram.error import BadRequest, RetryAfter, TelegramError
from telegram.request import HTTPXRequest
from telegram.ext import (
    Application,
    ApplicationBuilder,
    ApplicationHandlerStop,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    ConversationHandler,
    MessageHandler,
    filters,
)

# =============================================================================
# CONFIG
# =============================================================================
# NOTE: put your token in an environment variable BOT_TOKEN, or create a file
# called "token.txt" next to main.py containing only the token. Never paste
# your live token into chat logs or public repos — if it has ever been
# exposed, revoke it via @BotFather (/revoke) and generate a new one.

def _load_token() -> str:
    token = os.environ.get("BOT_TOKEN")
    if token:
        return token.strip()
    token_file = os.path.join(os.path.dirname(os.path.abspath(__file__)), "token.txt")
    if os.path.exists(token_file):
        with open(token_file, "r", encoding="utf-8") as f:
            t = f.read().strip()
            if t:
                return t
    raise RuntimeError(
        "No bot token found. Set BOT_TOKEN env var, or create a token.txt "
        "file next to main.py containing your bot token."
    )


BOT_TOKEN = _load_token()
OWNER_ID = int(os.environ.get("OWNER_ID", "0"))
BOT_USERNAME = os.environ.get("BOT_USERNAME", "FILE_STORE_42_BOT")

DB_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "database.db")

logging.basicConfig(
    format="%(asctime)s | %(levelname)s | %(name)s | %(message)s",
    level=logging.INFO,
)
logging.getLogger("httpx").setLevel(logging.WARNING)
log = logging.getLogger("FILE_STORE_42_BOT")

DEFAULT_SETTINGS = {
    "bot_name": "Shyaian FILE STORE",
    "referral_reward": "5",
    "daily_bonus": "5",
    "premium_daily_bonus_multiplier": "1",
    "premium_daily_bonus": "15",
    "support_username": "Shyaian",
    "payment_username": "Shyaian",
    "force_join": "1",
    "maintenance": "0",
    "star_rate": "30",  # coins per star baseline reference (500 coins = 15 stars => ~33.3 coins/star)
    "coin_packages": json.dumps([
        {"coins": 100, "stars": 3},
        {"coins": 500, "stars": 15},
        {"coins": 1000, "stars": 28},
        {"coins": 2500, "stars": 65},
        {"coins": 5000, "stars": 120},
    ]),
    # Self-serve Premium pricing (paid with in-wallet coins) — fully editable from
    # Admin Settings, no code changes needed.
    "premium_pricing": json.dumps([
        {"days": 7, "price": 300},
        {"days": 30, "price": 900},
        {"days": 90, "price": 2200},
        {"days": 0, "price": 6000},  # days: 0 == Lifetime
    ]),
    # Buy Coins with real money (BDT). 1 Taka -> this many coins.
    "coin_rate_bdt": "5",
    "bdt_payment_details": "bKash (Send Money): 01864689035\nNagad (Send Money): 01864689035",
}

FILE_TYPE_ICON = {
    "document": "📄", "video": "🎬", "audio": "🎵", "photo": "🖼",
    "voice": "🎙", "animation": "🎞", "video_note": "🎥",
}

# =============================================================================
# PREMIUM UI / CUSTOM EMOJI
# =============================================================================
# Telegram "Premium custom emoji" only render for real emoji-set IDs owned by
# Telegram Premium — a bot cannot invent working IDs, and sending a fake one
# causes Telegram to reject the message. To stay 100% functional out of the
# box we render with regular Unicode emoji everywhere (which display in a
# clean, modern way on every account, Premium or not). If you DO have real
# custom_emoji_id values (e.g. from your own Premium account's emoji-status
# picker or `getCustomEmojiStickers`), drop them in CUSTOM_EMOJI below and
# set USE_CUSTOM_EMOJI = True — the helper `emoji()` will then wrap them as
# MessageEntity(type="custom_emoji") automatically wherever it's used.
USE_CUSTOM_EMOJI = False
CUSTOM_EMOJI: dict[str, str] = {
    # "💎": "5289791376234131725",  # example — replace with a real custom_emoji_id
}

DIVIDER = "───────────────────"

# =============================================================================
# DATABASE LAYER
# =============================================================================

_db_lock = asyncio.Lock()

# =============================================================================
# ANTI-SPAM / FLOOD PROTECTION
# =============================================================================
# Three layers, working together:
#
# 1) DUPLICATE-ACTION dedup — keyed on (user, exact button/text pressed), not
#    just user. Pressing the SAME button twice within DUPLICATE_COOLDOWN gets
#    silently absorbed (this is what stops double-tap purchase/bonus races).
#    Pressing something DIFFERENT — browsing to another menu, a different
#    button — is never delayed, so normal fast use never feels blocked.
#
# 2) TRUE-FLOOD rate limiter — if a user fires more than FLOOD_MAX_ACTIONS
#    *distinct* actions within FLOOD_WINDOW_SECONDS (genuine spam, not just a
#    quick double-tap), further actions are dropped until the window rolls
#    off. This is what actually protects the bot/DB under real abuse, without
#    layer 1's tight per-action cooldown getting in the way of normal use.
#
# Both run as a group=-1 handler — before anything else — and use
# ApplicationHandlerStop to keep dropped updates from reaching real handlers,
# the DB, or the Telegram API at all.
#
# 3) A per-user asyncio.Lock for money-moving actions (daily bonus, buying a
#    file, redeeming a code, buying premium) so that even two requests that
#    DO slip through close together (e.g. from two devices at once) are still
#    processed one at a time for that specific user — preventing double-claim
#    / double-spend races now that concurrent_updates lets different users
#    run fully in parallel. Locks are per-user, so this never blocks others.

DUPLICATE_COOLDOWN_SECONDS = 0.6
FLOOD_WINDOW_SECONDS = 3.0
FLOOD_MAX_ACTIONS = 12

_last_action_by_key: dict[tuple[int, str], float] = {}
_recent_action_times: dict[int, list[float]] = {}

_user_action_locks: dict[int, asyncio.Lock] = {}
_user_action_locks_guard = asyncio.Lock()


async def get_user_action_lock(user_id: int) -> asyncio.Lock:
    async with _user_action_locks_guard:
        lock = _user_action_locks.get(user_id)
        if lock is None:
            lock = asyncio.Lock()
            _user_action_locks[user_id] = lock
        return lock


async def flood_guard(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    if user is None:
        return

    if update.callback_query:
        action_id = update.callback_query.data or ""
    elif update.message and update.message.text:
        action_id = update.message.text
    else:
        return  # non-text, non-callback updates (media, etc.) aren't the abuse vector here

    now = time.monotonic()

    # Layer 1 — exact duplicate of the same action, too soon after itself.
    key = (user.id, action_id)
    last_same = _last_action_by_key.get(key, 0.0)
    _last_action_by_key[key] = now
    if now - last_same < DUPLICATE_COOLDOWN_SECONDS:
        if update.callback_query:
            try:
                await update.callback_query.answer()  # silent — just absorb the duplicate tap
            except TelegramError:
                pass
        raise ApplicationHandlerStop

    # Layer 2 — too many actions overall in a short rolling window.
    history = _recent_action_times.setdefault(user.id, [])
    history[:] = [t for t in history if now - t < FLOOD_WINDOW_SECONDS]
    history.append(now)
    if len(history) > FLOOD_MAX_ACTIONS:
        if update.callback_query:
            try:
                await update.callback_query.answer("⏳ Please slow down a little.", show_alert=False)
            except TelegramError:
                pass
        raise ApplicationHandlerStop


# =============================================================================
# OUTBOUND RATE LIMITER (broadcast / bulk sends)
# =============================================================================
# A correct token-bucket: `acquire()` never lets calls start more than `rate`
# times per second in aggregate, no matter how many tasks call it at once.
# This is NOT the same as bounding concurrency with a Semaphore — a semaphore
# only limits how many are in-flight simultaneously, not how often NEW ones
# are allowed to start, so pairing it with a fixed per-call sleep can still
# blow past Telegram's real ~30 msg/s ceiling (and then everything gets much
# slower from repeated RetryAfter throttling). This class paces the *start*
# of each send against a shared clock instead, which is what actually caps
# real throughput at the target rate while letting network I/O overlap.
class RateLimiter:
    def __init__(self, rate: float):
        self.interval = 1.0 / rate
        self._lock = asyncio.Lock()
        self._next_time = time.monotonic()

    async def acquire(self) -> None:
        async with self._lock:
            now = time.monotonic()
            wait = self._next_time - now
            if wait > 0:
                await asyncio.sleep(wait)
                now = time.monotonic()
            self._next_time = now + self.interval


# Telegram's hard ceiling for a bot sending to many different chats is ~30
# messages/second (core.telegram.org/bots/faq) — no bot can exceed that.
# 25/s leaves a safety margin.
TELEGRAM_SEND_LIMITER = RateLimiter(25)

# ---- connection pool ---------------------------------------------------------
# Opening a brand-new SQLite connection for every single query (the old
# approach) means aiosqlite spins up a fresh background thread per call —
# under heavy concurrent load (many users hitting the bot at once) that
# thread churn becomes the actual bottleneck, not SQLite itself. A small
# pool of long-lived, pre-configured connections removes that overhead:
# handlers borrow a connection, use it, and return it instead of paying
# connection-setup cost on every query.
DB_POOL_SIZE = int(os.environ.get("DB_POOL_SIZE", "64"))
_db_pool: "asyncio.Queue[aiosqlite.Connection]" = None


async def init_db_pool() -> None:
    global _db_pool
    _db_pool = asyncio.Queue(maxsize=DB_POOL_SIZE)
    for _ in range(DB_POOL_SIZE):
        conn = await aiosqlite.connect(DB_PATH)
        conn.row_factory = aiosqlite.Row
        await conn.execute("PRAGMA journal_mode = WAL;")
        await conn.execute("PRAGMA synchronous = NORMAL;")   # safe with WAL, much faster
        await conn.execute("PRAGMA busy_timeout = 8000;")     # wait instead of erroring under write contention
        await conn.execute("PRAGMA foreign_keys = ON;")
        await _db_pool.put(conn)
    log.info("DB connection pool ready (%d connections)", DB_POOL_SIZE)


async def close_db_pool() -> None:
    if _db_pool is None:
        return
    while not _db_pool.empty():
        conn = await _db_pool.get()
        await conn.close()


class _PooledConnection:
    """Async context manager — borrows a connection from the shared pool
    instead of opening a new one. Drop-in replacement for
    `aiosqlite.connect(DB_PATH)` at every call site."""

    async def __aenter__(self) -> aiosqlite.Connection:
        self.conn = await _db_pool.get()
        return self.conn

    async def __aexit__(self, exc_type, exc, tb) -> None:
        await _db_pool.put(self.conn)


def db_conn() -> _PooledConnection:
    return _PooledConnection()


async def init_db() -> None:
    async with aiosqlite.connect(DB_PATH) as db:
        await db.executescript(
            """
            CREATE TABLE IF NOT EXISTS users (
                user_id INTEGER PRIMARY KEY,
                username TEXT,
                first_name TEXT,
                join_date TEXT,
                is_banned INTEGER DEFAULT 0,
                referred_by INTEGER,
                last_bonus_time TEXT,
                last_seen TEXT
            );

            CREATE TABLE IF NOT EXISTS files (
                file_pk INTEGER PRIMARY KEY AUTOINCREMENT,
                tg_file_id TEXT NOT NULL,
                tg_file_unique_id TEXT,
                file_kind TEXT NOT NULL,
                file_name TEXT NOT NULL,
                file_size INTEGER DEFAULT 0,
                description TEXT DEFAULT '',
                price INTEGER DEFAULT 0,
                upload_date TEXT,
                downloads_count INTEGER DEFAULT 0,
                uploaded_by INTEGER,
                premium_only INTEGER DEFAULT 0,
                is_deleted INTEGER DEFAULT 0
            );

            CREATE TABLE IF NOT EXISTS wallet (
                user_id INTEGER PRIMARY KEY,
                coins INTEGER DEFAULT 0
            );

            CREATE TABLE IF NOT EXISTS transactions (
                tx_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                tx_type TEXT,
                amount INTEGER,
                description TEXT,
                timestamp TEXT
            );

            CREATE TABLE IF NOT EXISTS payments (
                payment_id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                stars INTEGER,
                coins INTEGER,
                screenshot_file_id TEXT,
                status TEXT DEFAULT 'pending',
                admin_id INTEGER,
                reason TEXT,
                timestamp TEXT,
                payment_method TEXT DEFAULT 'stars',
                amount_bdt INTEGER
            );

            CREATE TABLE IF NOT EXISTS redeems (
                code TEXT PRIMARY KEY,
                coin_reward INTEGER DEFAULT 0,
                premium_days INTEGER DEFAULT 0,
                usage_limit INTEGER DEFAULT 0,
                used_count INTEGER DEFAULT 0,
                expiry_date TEXT,
                status TEXT DEFAULT 'active',
                created_by INTEGER,
                created_at TEXT
            );

            CREATE TABLE IF NOT EXISTS redeem_uses (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                code TEXT,
                user_id INTEGER,
                timestamp TEXT,
                UNIQUE(code, user_id)
            );

            CREATE TABLE IF NOT EXISTS referrals (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                referrer_id INTEGER,
                new_user_id INTEGER UNIQUE,
                date TEXT,
                reward INTEGER
            );

            CREATE TABLE IF NOT EXISTS force_channels (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT UNIQUE,
                chat_id INTEGER,
                title TEXT,
                invite_link TEXT,
                chat_type TEXT,
                added_date TEXT
            );

            CREATE TABLE IF NOT EXISTS admins (
                user_id INTEGER PRIMARY KEY,
                added_date TEXT
            );

            CREATE TABLE IF NOT EXISTS settings (
                key TEXT PRIMARY KEY,
                value TEXT
            );

            CREATE TABLE IF NOT EXISTS downloads (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                file_pk INTEGER,
                timestamp TEXT
            );

            CREATE TABLE IF NOT EXISTS premium (
                user_id INTEGER PRIMARY KEY,
                expiry_date TEXT,
                is_lifetime INTEGER DEFAULT 0,
                granted_by INTEGER,
                granted_at TEXT
            );

            CREATE TABLE IF NOT EXISTS purchases (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER,
                file_pk INTEGER,
                price INTEGER,
                timestamp TEXT
            );

            CREATE INDEX IF NOT EXISTS idx_files_deleted ON files(is_deleted);
            CREATE INDEX IF NOT EXISTS idx_tx_user ON transactions(user_id);
            CREATE INDEX IF NOT EXISTS idx_purchases_user_file ON purchases(user_id, file_pk);
            CREATE INDEX IF NOT EXISTS idx_downloads_user ON downloads(user_id);
            """
        )
        await db.commit()

        # Safe column migrations — CREATE TABLE IF NOT EXISTS above only helps
        # brand-new databases; existing ones need columns added explicitly.
        # Each ALTER is tried independently and ignored if the column already
        # exists, so this is always safe to re-run on every startup.
        migrations = [
            ("files", "premium_only", "INTEGER DEFAULT 0"),
            ("payments", "payment_method", "TEXT DEFAULT 'stars'"),
            ("payments", "amount_bdt", "INTEGER"),
        ]
        for table, column, coltype in migrations:
            try:
                await db.execute(f"ALTER TABLE {table} ADD COLUMN {column} {coltype}")
                await db.commit()
                log.info("Migrated: added %s.%s", table, column)
            except aiosqlite.OperationalError:
                pass  # column already exists — nothing to do

        # seed default settings
        for k, v in DEFAULT_SETTINGS.items():
            await db.execute(
                "INSERT OR IGNORE INTO settings (key, value) VALUES (?, ?)", (k, v)
            )
        # If OWNER_ID is explicitly configured, seed it as admin. Otherwise,
        # the first person to run /setup becomes the initial admin.
        if OWNER_ID > 0:
            await db.execute(
                "INSERT OR IGNORE INTO admins (user_id, added_date) VALUES (?, ?)",
                (OWNER_ID, datetime.utcnow().isoformat()),
            )
        await db.commit()
    log.info("Database ready at %s", DB_PATH)


# ---- settings helpers -------------------------------------------------------

async def get_setting(key: str, default: str = "") -> str:
    async with db_conn() as db:
        cur = await db.execute("SELECT value FROM settings WHERE key=?", (key,))
        row = await cur.fetchone()
        return row[0] if row else default


async def set_setting(key: str, value: str) -> None:
    async with db_conn() as db:
        await db.execute(
            "INSERT INTO settings (key, value) VALUES (?, ?) "
            "ON CONFLICT(key) DO UPDATE SET value=excluded.value",
            (key, value),
        )
        await db.commit()


# ---- user / admin helpers ---------------------------------------------------

async def ensure_user(user_id: int, username: str | None, first_name: str | None,
                       referred_by: int | None = None) -> bool:
    """Returns True if this is a newly created user."""
    async with db_conn() as db:
        cur = await db.execute("SELECT user_id FROM users WHERE user_id=?", (user_id,))
        exists = await cur.fetchone()
        now = datetime.utcnow().isoformat()
        if exists:
            await db.execute(
                "UPDATE users SET username=?, first_name=?, last_seen=? WHERE user_id=?",
                (username, first_name, now, user_id),
            )
            await db.commit()
            return False
        await db.execute(
            "INSERT INTO users (user_id, username, first_name, join_date, referred_by, last_seen) "
            "VALUES (?, ?, ?, ?, ?, ?)",
            (user_id, username, first_name, now, referred_by, now),
        )
        await db.execute(
            "INSERT OR IGNORE INTO wallet (user_id, coins) VALUES (?, 0)", (user_id,)
        )
        await db.commit()
        return True


async def is_admin(user_id: int) -> bool:
    if user_id == OWNER_ID:
        return True
    async with db_conn() as db:
        cur = await db.execute("SELECT 1 FROM admins WHERE user_id=?", (user_id,))
        return (await cur.fetchone()) is not None


async def is_banned(user_id: int) -> bool:
    async with db_conn() as db:
        cur = await db.execute("SELECT is_banned FROM users WHERE user_id=?", (user_id,))
        row = await cur.fetchone()
        return bool(row and row[0])


async def get_user_row(user_id: int):
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM users WHERE user_id=?", (user_id,))
        return await cur.fetchone()


# ---- wallet helpers ----------------------------------------------------------

async def get_balance(user_id: int) -> int:
    async with db_conn() as db:
        cur = await db.execute("SELECT coins FROM wallet WHERE user_id=?", (user_id,))
        row = await cur.fetchone()
        if row is None:
            await db.execute("INSERT OR IGNORE INTO wallet (user_id, coins) VALUES (?, 0)", (user_id,))
            await db.commit()
            return 0
        return row[0]


async def add_coins(user_id: int, amount: int, tx_type: str, description: str = "") -> int:
    async with _db_lock:
        async with db_conn() as db:
            await db.execute(
                "INSERT INTO wallet (user_id, coins) VALUES (?, 0) "
                "ON CONFLICT(user_id) DO NOTHING", (user_id,)
            )
            await db.execute(
                "UPDATE wallet SET coins = coins + ? WHERE user_id=?", (amount, user_id)
            )
            await db.execute(
                "INSERT INTO transactions (user_id, tx_type, amount, description, timestamp) "
                "VALUES (?, ?, ?, ?, ?)",
                (user_id, tx_type, amount, description, datetime.utcnow().isoformat()),
            )
            await db.commit()
            cur = await db.execute("SELECT coins FROM wallet WHERE user_id=?", (user_id,))
            row = await cur.fetchone()
            return row[0]


async def remove_coins(user_id: int, amount: int, tx_type: str, description: str = "") -> bool:
    """Returns False if insufficient balance."""
    async with _db_lock:
        async with db_conn() as db:
            cur = await db.execute("SELECT coins FROM wallet WHERE user_id=?", (user_id,))
            row = await cur.fetchone()
            bal = row[0] if row else 0
            if bal < amount:
                return False
            await db.execute(
                "UPDATE wallet SET coins = coins - ? WHERE user_id=?", (amount, user_id)
            )
            await db.execute(
                "INSERT INTO transactions (user_id, tx_type, amount, description, timestamp) "
                "VALUES (?, ?, ?, ?, ?)",
                (user_id, tx_type, -amount, description, datetime.utcnow().isoformat()),
            )
            await db.commit()
            return True


# ---- premium helpers ----------------------------------------------------------

async def get_premium(user_id: int):
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM premium WHERE user_id=?", (user_id,))
        return await cur.fetchone()


async def is_premium_active(user_id: int) -> bool:
    row = await get_premium(user_id)
    if not row:
        return False
    if row["is_lifetime"]:
        return True
    if row["expiry_date"] and datetime.fromisoformat(row["expiry_date"]) > datetime.utcnow():
        return True
    return False


async def grant_premium(user_id: int, days: int | None, admin_id: int) -> None:
    async with db_conn() as db:
        if days is None:  # lifetime
            await db.execute(
                "INSERT INTO premium (user_id, expiry_date, is_lifetime, granted_by, granted_at) "
                "VALUES (?, NULL, 1, ?, ?) ON CONFLICT(user_id) DO UPDATE SET "
                "expiry_date=NULL, is_lifetime=1, granted_by=excluded.granted_by, granted_at=excluded.granted_at",
                (user_id, admin_id, datetime.utcnow().isoformat()),
            )
        else:
            expiry = (datetime.utcnow() + timedelta(days=days)).isoformat()
            await db.execute(
                "INSERT INTO premium (user_id, expiry_date, is_lifetime, granted_by, granted_at) "
                "VALUES (?, ?, 0, ?, ?) ON CONFLICT(user_id) DO UPDATE SET "
                "expiry_date=excluded.expiry_date, is_lifetime=0, granted_by=excluded.granted_by, granted_at=excluded.granted_at",
                (user_id, expiry, admin_id, datetime.utcnow().isoformat()),
            )
        await db.commit()


async def remove_premium(user_id: int) -> None:
    async with db_conn() as db:
        await db.execute("DELETE FROM premium WHERE user_id=?", (user_id,))
        await db.commit()


# =============================================================================
# UI: KEYBOARDS
# =============================================================================

def user_reply_keyboard(admin: bool) -> ReplyKeyboardMarkup:
    rows = [
        [KeyboardButton("📁 Buy Files", style="primary"), KeyboardButton("💎 My Wallet", style="primary")],
        [KeyboardButton("💵 Buy Coins (৳)", style="success"), KeyboardButton("🎁 Daily Bonus", style="primary")],
        [KeyboardButton("🚀 Invite Friends", style="primary"), KeyboardButton("🎟️ Redeem Code", style="primary")],
        [KeyboardButton("📊 My Stats", style="primary"), KeyboardButton("🏆 Leaderboard", style="primary")],
        [KeyboardButton("💬 Support", style="primary")],
    ]
    if admin:
        rows.append([KeyboardButton("👑 Admin Panel", style="primary")])
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)


def admin_reply_keyboard() -> ReplyKeyboardMarkup:
    """Full admin control keyboard — replaces the user keyboard entirely while
    the admin is inside the Admin Panel. Requires python-telegram-bot >= 22.7
    (Bot API 9.4+) for the `style` field to render as colored buttons in
    Telegram; see requirements.txt."""
    rows = [
        [KeyboardButton("📤 Upload File", style="primary"), KeyboardButton("📂 Manage Files", style="primary")],
        [KeyboardButton("💰 Wallet Manager", style="primary"), KeyboardButton("🎟 Redeem Manager", style="primary")],
        [KeyboardButton("📡 Force Channels", style="primary"), KeyboardButton("📢 Broadcast", style="primary")],
        [KeyboardButton("👥 User Manager", style="primary"), KeyboardButton("👤 All Users", style="primary")],
        [KeyboardButton("👑 Premium Manager", style="primary"), KeyboardButton("📊 Statistics", style="primary")],
        [KeyboardButton("🛠 Maintenance", style="primary"), KeyboardButton("⚙ Settings", style="primary")],
        [KeyboardButton("⬅️ Back to Main", style="primary")],
    ]
    return ReplyKeyboardMarkup(rows, resize_keyboard=True)


def admin_panel_keyboard() -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton("📤 Upload File", callback_data="ad:upload"),
         InlineKeyboardButton("📂 Manage Files", callback_data="ad:managefiles")],
        [InlineKeyboardButton("💰 Wallet Manager", callback_data="ad:walletmgr"),
         InlineKeyboardButton("🎟 Redeem Manager", callback_data="ad:redeemmgr")],
        [InlineKeyboardButton("📡 Force Channels", callback_data="ad:fcmgr"),
         InlineKeyboardButton("📢 Broadcast", callback_data="ad:broadcast")],
        [InlineKeyboardButton("👥 User Manager", callback_data="ad:usermgr"),
         InlineKeyboardButton("👑 Premium Manager", callback_data="ad:premiummgr")],
        [InlineKeyboardButton("📊 Statistics", callback_data="ad:stats"),
         InlineKeyboardButton("🛠 Maintenance", callback_data="ad:maintenance")],
        [InlineKeyboardButton("⚙ Settings", callback_data="ad:settings")],
    ]
    return InlineKeyboardMarkup(rows)


def back_button(cb: str = "ad:home") -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([[InlineKeyboardButton("⬅ Back", callback_data=cb)]])


# =============================================================================
# FORCE JOIN SYSTEM
# =============================================================================

async def list_force_channels():
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM force_channels ORDER BY id")
        return await cur.fetchall()


async def check_force_join(bot, user_id: int) -> list[dict]:
    """Returns list of channels the user has NOT joined."""
    if (await get_setting("force_join", "1")) != "1":
        return []
    channels = await list_force_channels()
    missing = []
    for ch in channels:
        try:
            member = await bot.get_chat_member(chat_id=ch["chat_id"], user_id=user_id)
            # Telegram may return `restricted` for a user who is still a member.
            # Only treat restricted as joined when Telegram explicitly says
            # is_member=True.  This avoids both false positives and false negatives.
            if member.status in ("left", "kicked"):
                missing.append(dict(ch))
            elif member.status == "restricted" and not getattr(member, "is_member", False):
                missing.append(dict(ch))
        except TelegramError as e:
            # If Telegram cannot inspect membership (most commonly because the
            # bot is not an administrator in the channel), fail closed and show
            # the channel as missing instead of accidentally granting access.
            log.warning("Force-join check failed for chat %s/user %s: %s", ch["chat_id"], user_id, e)
            missing.append(dict(ch))
    return missing


async def send_force_join_prompt(update: Update, missing: list[dict]) -> None:
    buttons = []
    for ch in missing:
        if ch.get("username"):
            url = f"https://t.me/{ch['username'].lstrip('@')}"
        elif ch.get("invite_link"):
            url = ch["invite_link"]
        else:
            continue  # no usable join link on file — skip rather than crash
        buttons.append([InlineKeyboardButton(f"📢 {ch['title']}", url=url)])
    buttons.append([InlineKeyboardButton("✅ Verify", callback_data="verify_join")])
    text = (
        "🔒 <b>Access Restricted</b>\n\n"
        "To use this bot, please join all required channels below, "
        "then tap <b>✅ Verify</b>.\n\n"
        "⚠️ If you already joined but verification fails, make sure the bot "
        "is an <b>administrator</b> in the required channel/group."
    )
    if update.callback_query:
        await update.callback_query.message.reply_text(
            text, reply_markup=InlineKeyboardMarkup(buttons), parse_mode=ParseMode.HTML
        )
    else:
        await update.effective_message.reply_text(
            text, reply_markup=InlineKeyboardMarkup(buttons), parse_mode=ParseMode.HTML
        )


# =============================================================================
# CONVERSATION STATES
# =============================================================================

(UP_FILE, UP_NAME, UP_DESC, UP_PRICE, UP_PREVIEW) = range(5)
(BC_PKG, BC_STARS, BC_SCREENSHOT) = range(10, 13)
(RD_CODE,) = range(20, 21)
(FC_ADD, FC_INVITE_LINK) = range(30, 32)
(UM_SEARCH, UM_AMOUNT) = range(40, 42)
(RM_CODE, RM_COINS, RM_PREMIUM, RM_LIMIT, RM_EXPIRY) = range(50, 55)
(BR_CONTENT,) = range(60, 61)
(ST_VALUE,) = range(70, 71)
(EF_FIELD,) = range(80, 81)
(WB_IDS, WB_ACTION, WB_AMOUNT, WB_PREMIUM) = range(90, 94)
(BDT_AMOUNT, BDT_PROOF) = range(94, 96)

ADMIN_ONLY_MSG = "🚫 This action is for admins only."


def fmt_size(num: int) -> str:
    step = 1024.0
    for unit in ["B", "KB", "MB", "GB", "TB"]:
        if num < step:
            return f"{num:.1f} {unit}" if unit != "B" else f"{int(num)} {unit}"
        num /= step
    return f"{num:.1f} PB"


def fmt_date(iso: str | None) -> str:
    if not iso:
        return "—"
    try:
        return datetime.fromisoformat(iso).strftime("%d %b %Y, %H:%M")
    except Exception:
        return iso


# =============================================================================
# GLOBAL GUARDS (maintenance / ban / force join)
# =============================================================================

async def guard_user(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    """Returns True if the update should proceed normally."""
    user = update.effective_user
    if user is None:
        return False

    admin = await is_admin(user.id)

    maintenance = (await get_setting("maintenance", "0")) == "1"
    if maintenance and not admin:
        await update.effective_message.reply_text(
            "🚧 <b>Bot is under maintenance.</b>\nPlease try again later.",
            parse_mode=ParseMode.HTML,
        )
        return False

    if await is_banned(user.id):
        await update.effective_message.reply_text(
            "🚫 You have been banned from using this bot. Contact support if you think this is a mistake."
        )
        return False

    if not admin:
        missing = await check_force_join(context.bot, user.id)
        if missing:
            await send_force_join_prompt(update, missing)
            return False

    return True


# =============================================================================
# START COMMAND
# =============================================================================

async def cmd_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    args = context.args

    maintenance = (await get_setting("maintenance", "0")) == "1"
    admin = await is_admin(user.id)
    if maintenance and not admin:
        await update.effective_message.reply_text(
            "🚧 <b>Bot is under maintenance.</b>\nPlease try again later.",
            parse_mode=ParseMode.HTML,
        )
        return

    if await is_banned(user.id):
        await update.effective_message.reply_text("🚫 You have been banned from using this bot.")
        return

    referred_by = None
    if args and args[0].isdigit():
        ref_id = int(args[0])
        if ref_id != user.id:
            existing = await get_user_row(user.id)
            if existing is None:
                referred_by = ref_id

    is_new = await ensure_user(user.id, user.username, user.first_name, referred_by)

    if not admin:
        missing = await check_force_join(context.bot, user.id)
        if missing:
            await send_force_join_prompt(update, missing)
            return

    await maybe_process_referral(context.bot, user.id)

    await show_main_menu(update, context)


async def maybe_process_referral(bot, user_id: int) -> None:
    """Grants the referral reward once the referred user actually reaches the
    bot (i.e. after passing force-join, or immediately if none is required).
    Safe to call repeatedly — process_referral() is idempotent."""
    row = await get_user_row(user_id)
    if row and row["referred_by"]:
        await process_referral(bot, row["referred_by"], user_id)


async def process_referral(bot, referrer_id: int, new_user_id: int) -> None:
    async with db_conn() as db:
        cur = await db.execute("SELECT 1 FROM users WHERE user_id=?", (referrer_id,))
        if not await cur.fetchone():
            return
        cur = await db.execute("SELECT 1 FROM referrals WHERE new_user_id=?", (new_user_id,))
        if await cur.fetchone():
            return
        reward = int(await get_setting("referral_reward", "20"))
        await db.execute(
            "INSERT INTO referrals (referrer_id, new_user_id, date, reward) VALUES (?, ?, ?, ?)",
            (referrer_id, new_user_id, datetime.utcnow().isoformat(), reward),
        )
        await db.commit()

    new_balance = await add_coins(referrer_id, reward, "referral", f"Referral bonus for inviting user {new_user_id}")

    new_user_row = await get_user_row(new_user_id)
    if new_user_row and new_user_row["username"]:
        uname = f"@{new_user_row['username']}"
    elif new_user_row and new_user_row["first_name"]:
        uname = new_user_row["first_name"]
    else:
        uname = f"User {new_user_id}"

    try:
        await bot.send_message(
            referrer_id,
            "🎉 <b>New Referral Alert!</b> 🎉\n\n"
            f"👤 <b>User:</b> {html.escape(uname)}\n"
            f"🪙 <b>You earned:</b> +{reward} coins\n"
            f"💰 <b>Your new balance:</b> {new_balance} coins",
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        pass


async def show_main_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    user = update.effective_user
    admin = await is_admin(user.id)
    bot_name = await get_setting("bot_name", "TAHMID FILE STORE")
    balance = await get_balance(user.id)

    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (user.id,))
        ref_count = (await cur.fetchone())[0]

    is_premium = await is_premium_active(user.id)
    premium_line = "👑 <b>Premium — Active</b>" if is_premium else "⭐ Premium: <i>Not Active</i>"
    name_tag = f"👑 {html.escape(user.first_name or 'Friend')}" if is_premium else html.escape(user.first_name or "Friend")

    text = (
        f"👋 <b>Welcome, {name_tag}!</b>\n\n"
        f"🏷 <b>{html.escape(bot_name)}</b>\n"
        f"{DIVIDER}\n"
        f"🪙 <b>Wallet:</b> {balance} Coins\n"
        f"👥 <b>Referrals:</b> {ref_count}\n"
        f"{premium_line}\n"
        f"{DIVIDER}\n\n"
        f"Use the menu below to get started 👇"
    )
    await update.effective_message.reply_text(
        text, parse_mode=ParseMode.HTML, reply_markup=user_reply_keyboard(admin)
    )


async def cb_verify_join(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    user = update.effective_user
    missing = await check_force_join(context.bot, user.id)
    if missing:
        await query.answer("❌ You haven't joined all channels yet.", show_alert=True)
        return
    await query.answer("✅ Verified!")
    try:
        await query.message.delete()
    except BadRequest:
        pass
    await ensure_user(user.id, user.username, user.first_name)
    await maybe_process_referral(context.bot, user.id)
    await show_main_menu(update, context)


# =============================================================================
# HELP / SUPPORT
# =============================================================================

async def cmd_setup(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Allow the first person to run /setup to claim initial admin access."""
    user = update.effective_user
    message = update.effective_message
    if user is None or message is None:
        return

    async with db_conn() as db:
        # Lock the write transaction so two users cannot both claim first setup.
        await db.execute("BEGIN IMMEDIATE")
        cur = await db.execute("SELECT user_id FROM admins")
        rows = await cur.fetchall()

        # Older deployments may have seeded the old fallback OWNER_ID. If no
        # OWNER_ID was explicitly set in Render, treat that default as unclaimed.
        if "OWNER_ID" not in os.environ and rows and all(int(r[0]) == 7350349936 for r in rows):
            await db.execute("DELETE FROM admins WHERE user_id=?", (7350349936,))
            cur = await db.execute("SELECT user_id FROM admins")
            rows = await cur.fetchall()

        if rows:
            await db.rollback()
            if await is_admin(user.id):
                await message.reply_text("✅ You are already an admin. Send /admin to open the Admin Panel.")
            else:
                await message.reply_text("⚠️ Setup has already been completed. Only an existing admin can manage admins.")
            return

        await db.execute(
            "INSERT INTO admins (user_id, added_date) VALUES (?, ?)",
            (user.id, datetime.utcnow().isoformat()),
        )
        await db.commit()

    await message.reply_text(
        "✅ Setup complete! You are now the bot's first admin. Send /start or /admin to continue."
    )


async def cmd_myid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Show the caller's Telegram numeric ID to help configure OWNER_ID."""
    user = update.effective_user
    if user is None:
        return
    await update.effective_message.reply_text(
        f"🆔 Your Telegram Numeric ID: {user.id}\n\n"
        "If the Admin Panel button is missing, set this number as OWNER_ID "
        "in Render → Environment, save, redeploy, then send /start again."
    )


async def cmd_admin(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Open the admin keyboard for authorized admins; otherwise show their ID."""
    user = update.effective_user
    if user is None:
        return
    if not await is_admin(user.id):
        await update.effective_message.reply_text(
            f"🚫 You are not configured as an admin.\n"
            f"🆔 Your Telegram Numeric ID: {user.id}\n\n"
            "Set this number as OWNER_ID in Render → Environment, save, "
            "redeploy, then send /start again."
        )
        return
    await update.effective_message.reply_text(
        "👑 <b>Admin Panel</b>\n\nAdmin controls are available on the keyboard below.",
        parse_mode=ParseMode.HTML,
        reply_markup=admin_reply_keyboard(),
    )


async def cmd_help(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    text = (
        "📖 <b>Help & Guide</b>\n\n"
        "📁 <b>Buy Files</b> — Browse and purchase files with coins.\n"
        "🪙 <b>Coins</b> — Buy coins with Telegram Stars, or earn them free via "
        "Daily Bonus, Referrals, and Redeem Codes.\n"
        "👥 <b>Referral</b> — Share your personal link, earn coins per new user.\n"
        "🎟️ <b>Redeem</b> — Enter a code from the admin to instantly get coins.\n"
        "💬 <b>Support</b> — Reach out any time via the Support menu.\n"
    )
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)


async def handle_support(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    support_username = "Shyaian"
    text = (
        "💬 <b>Support</b>\n\n"
        f"👤 Contact: @{html.escape(support_username)}\n"
        "🕒 Business Hours: 10:00 AM – 10:00 PM (IST)\n\n"
        "We usually reply within a few hours."
    )
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)


# =============================================================================
# WALLET
# =============================================================================

async def handle_my_wallet(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    await send_wallet_view(update, context)


async def send_wallet_view(update: Update, context: ContextTypes.DEFAULT_TYPE, edit: bool = False) -> None:
    user = update.effective_user
    balance = await get_balance(user.id)
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (user.id,))
        ref_count = (await cur.fetchone())[0]
    daily_status = await bonus_status_text(user.id)
    is_premium = await is_premium_active(user.id)
    premium_line = "👑 <b>Premium — Active</b>" if is_premium else "⭐ Premium: <i>Not Active</i>"

    text = (
        "💎 <b>My Wallet</b>\n"
        f"{DIVIDER}\n"
        f"🪙 <b>Coins:</b> {balance}\n"
        f"👥 <b>Total Referrals:</b> {ref_count}\n"
        f"🎁 <b>Daily Bonus:</b> {daily_status}\n"
        f"{premium_line}\n"
        f"{DIVIDER}"
    )
    buttons = [
        [InlineKeyboardButton("⭐ Buy Coins", callback_data="wallet:buycoins")],
        [InlineKeyboardButton("📜 Transactions", callback_data="wallet:tx:0")],
    ]
    if not is_premium:
        buttons.append([InlineKeyboardButton("👑 Buy Premium with Coins", callback_data="wallet:buypremium")])
    kb = InlineKeyboardMarkup(buttons)
    if edit and update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_wallet_buy_premium(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    if await is_premium_active(update.effective_user.id):
        await query.answer("✅ You already have Premium active.", show_alert=True)
        return
    pricing = json.loads(await get_setting("premium_pricing", "[]"))
    balance = await get_balance(update.effective_user.id)
    lines = [f"👑 <b>Buy Premium with Coins</b>\n{DIVIDER}", f"🪙 Your balance: <b>{balance}</b>\n"]
    buttons = []
    for p in pricing:
        label = "Lifetime" if p["days"] == 0 else f"{p['days']} Days"
        lines.append(f"• {label} — 🪙 {p['price']}")
        buttons.append([InlineKeyboardButton(f"👑 {label} — {p['price']} coins", callback_data=f"premium:buy:{p['days']}:{p['price']}")])
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="wallet:home")])
    await query.edit_message_text("\n".join(lines), parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_premium_purchase(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    user = update.effective_user
    _, _, days, price = query.data.split(":")
    days, price = int(days), int(price)

    lock = await get_user_action_lock(user.id)
    async with lock:
        if await is_premium_active(user.id):
            await query.answer("✅ You already have Premium active.", show_alert=True)
            return
        ok = await remove_coins(user.id, price, "premium_purchase", f"Bought Premium ({'Lifetime' if days == 0 else f'{days} days'})")
        if not ok:
            await query.answer("❌ Not enough Coins for this plan.", show_alert=True)
            return
        await grant_premium(user.id, None if days == 0 else days, admin_id=0)

    await query.answer("👑 Premium activated!")
    label = "Lifetime" if days == 0 else f"{days} Days"
    await query.edit_message_text(
        f"🎉 <b>Premium Activated!</b>\n\n👑 Plan: <b>{label}</b>\n🪙 Paid: <b>{price} coins</b>\n\n"
        "Enjoy your Premium badge, bonus multiplier, and priority support!",
        parse_mode=ParseMode.HTML,
    )


async def bonus_status_text(user_id: int) -> str:
    row = await get_user_row(user_id)
    if row and row["last_bonus_time"]:
        last = datetime.fromisoformat(row["last_bonus_time"])
        elapsed = datetime.utcnow() - last
        if elapsed < timedelta(hours=24):
            remaining = timedelta(hours=24) - elapsed
            h, rem = divmod(int(remaining.total_seconds()), 3600)
            m = rem // 60
            return f"⏳ Available in {h}h {m}m"
    return "✅ Available now"


async def cb_wallet_tx(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    user = update.effective_user
    page = int(query.data.split(":")[2])
    per_page = 8
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT * FROM transactions WHERE user_id=? ORDER BY tx_id DESC LIMIT ? OFFSET ?",
            (user.id, per_page, page * per_page),
        )
        rows = await cur.fetchall()

    if not rows and page == 0:
        text = "📜 <b>Transactions</b>\n\nNo transactions yet."
    else:
        lines = ["📜 <b>Transactions</b>\n"]
        for r in rows:
            sign = "+" if r["amount"] >= 0 else ""
            lines.append(
                f"{'🟢' if r['amount']>=0 else '🔴'} {sign}{r['amount']} 🪙 — {html.escape(r['tx_type'])} "
                f"<i>({fmt_date(r['timestamp'])})</i>"
            )
        text = "\n".join(lines)

    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"wallet:tx:{page-1}"))
    if len(rows) == per_page:
        nav.append(InlineKeyboardButton("Next ➡", callback_data=f"wallet:tx:{page+1}"))
    buttons = [nav] if nav else []
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="wallet:home")])
    await query.answer()
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_wallet_home(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    await update.callback_query.answer()
    await send_wallet_view(update, context, edit=True)


# ---- buy coins conversation -------------------------------------------------

async def cb_buycoins_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    packages = json.loads(await get_setting("coin_packages", "[]"))
    payment_username = await get_setting("payment_username", "tahmid_hi")
    lines = ["⭐ <b>Buy Coins — Manual Stars Payment</b>\n"]
    for i, p in enumerate(packages):
        lines.append(f"🪙 {p['coins']} Coins = ⭐ {p['stars']} Stars")
    lines.append(f"\nSend Stars To: <b>@{html.escape(payment_username)}</b>")
    lines.append("\nAfter sending, tap <b>⭐ I Have Paid</b> below.")
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("⭐ I Have Paid", callback_data="buycoins:paid")],
        [InlineKeyboardButton("⬅ Back", callback_data="wallet:home")],
    ])
    await query.edit_message_text("\n".join(lines), parse_mode=ParseMode.HTML, reply_markup=kb)
    return ConversationHandler.END


async def cb_buycoins_paid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.message.reply_text(
        "⭐ How many Stars did you send? (numbers only)",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="buycoins:cancel")]]),
    )
    return BC_STARS


async def conv_buycoins_stars(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit() or int(text) <= 0:
        await update.message.reply_text("❌ Please send a valid number of Stars.")
        return BC_STARS
    context.user_data["bc_stars"] = int(text)
    await update.message.reply_text("📷 Please send your payment screenshot now.")
    return BC_SCREENSHOT


async def conv_buycoins_screenshot(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not update.message.photo and not update.message.document:
        await update.message.reply_text("❌ Please send a screenshot as a photo or document.")
        return BC_SCREENSHOT

    file_id = update.message.photo[-1].file_id if update.message.photo else update.message.document.file_id
    stars = context.user_data.pop("bc_stars")
    user = update.effective_user

    # prevent duplicate pending requests
    async with db_conn() as db:
        cur = await db.execute(
            "SELECT 1 FROM payments WHERE user_id=? AND status='pending'", (user.id,)
        )
        if await cur.fetchone():
            await update.message.reply_text(
                "⚠️ You already have a pending payment request. Please wait for admin review."
            )
            return ConversationHandler.END

        # estimate coins from packages, fallback to star_rate
        packages = json.loads(await get_setting("coin_packages", "[]"))
        coins = 0
        for p in packages:
            if p["stars"] == stars:
                coins = p["coins"]
                break
        if coins == 0:
            rate = float(await get_setting("star_rate", "30"))
            coins = int(stars * rate / 30 * 100)  # fallback approx; admin can adjust on accept

        await db.execute(
            "INSERT INTO payments (user_id, stars, coins, screenshot_file_id, status, timestamp) "
            "VALUES (?, ?, ?, ?, 'pending', ?)",
            (user.id, stars, coins, file_id, datetime.utcnow().isoformat()),
        )
        await db.commit()
        cur = await db.execute("SELECT last_insert_rowid()")
        payment_id = (await cur.fetchone())[0]

    await update.message.reply_text(
        "✅ Your payment request has been submitted. You'll be notified once reviewed."
    )

    uname = f"@{user.username}" if user.username else "—"
    caption = (
        "💰 <b>New Payment Request</b>\n\n"
        f"👤 Username: {html.escape(uname)}\n"
        f"🆔 User ID: <code>{user.id}</code>\n"
        f"⭐ Stars: <b>{stars}</b>\n"
        f"🪙 Coins: <b>{coins}</b>\n"
        f"📅 Time: {fmt_date(datetime.utcnow().isoformat())}"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Accept", callback_data=f"pay:accept:{payment_id}"),
         InlineKeyboardButton("❌ Reject", callback_data=f"pay:reject:{payment_id}")]
    ])
    admin_ids = await get_all_admin_ids()
    for admin_id in admin_ids:
        try:
            if update.message.photo:
                await context.bot.send_photo(admin_id, file_id, caption=caption, parse_mode=ParseMode.HTML, reply_markup=kb)
            else:
                await context.bot.send_document(admin_id, file_id, caption=caption, parse_mode=ParseMode.HTML, reply_markup=kb)
        except TelegramError:
            pass
    return ConversationHandler.END


async def cb_buycoins_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    await update.callback_query.answer()
    await update.callback_query.message.reply_text("❌ Cancelled.")
    context.user_data.pop("bc_stars", None)
    return ConversationHandler.END


# ---- Buy Coins with Taka (BDT) — manual bKash/Nagad payment ----------------

async def handle_buy_coins_bdt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    rate = await get_setting("coin_rate_bdt", "5")
    details = await get_setting("bdt_payment_details", "")
    text = (
        "💵 <b>Buy Coins with Taka (৳)</b>\n"
        f"{DIVIDER}\n"
        f"💱 Rate: <b>1 ৳ = {html.escape(rate)} Coins</b>\n\n"
        f"{html.escape(details)}\n\n"
        "Send the amount via bKash/Nagad (Send Money), then tap <b>💵 I Have Paid</b> below."
    )
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("💵 I Have Paid", callback_data="buybdt:paid")]])
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_buybdt_paid(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.message.reply_text(
        "💵 How many Taka (৳) did you send? (numbers only)",
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ Cancel", callback_data="buybdt:cancel")]]),
    )
    return BDT_AMOUNT


async def conv_buybdt_amount(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit() or int(text) <= 0:
        await update.message.reply_text("❌ Please send a valid Taka amount.")
        return BDT_AMOUNT
    context.user_data["bdt_amount"] = int(text)
    await update.message.reply_text(
        "📷 Please send your payment screenshot now — or type your bKash/Nagad Transaction ID as text."
    )
    return BDT_PROOF


async def conv_buybdt_proof(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    amount = context.user_data.pop("bdt_amount", None)
    if amount is None:
        await update.message.reply_text("❌ Something went wrong — please start again from 💵 Buy Coins (৳).")
        return ConversationHandler.END

    file_id = None
    is_photo = False
    txn_text = None
    if update.message.photo:
        file_id = update.message.photo[-1].file_id
        is_photo = True
    elif update.message.document:
        file_id = update.message.document.file_id
    elif update.message.text:
        txn_text = update.message.text.strip()
    else:
        await update.message.reply_text("❌ Please send a screenshot, or type your Transaction ID as text.")
        return BDT_PROOF

    user = update.effective_user

    async with db_conn() as db:
        cur = await db.execute("SELECT 1 FROM payments WHERE user_id=? AND status='pending'", (user.id,))
        if await cur.fetchone():
            await update.message.reply_text("⚠️ You already have a pending payment request. Please wait for admin review.")
            return ConversationHandler.END

        rate = float(await get_setting("coin_rate_bdt", "5"))
        coins = int(amount * rate)

        await db.execute(
            "INSERT INTO payments (user_id, coins, screenshot_file_id, status, timestamp, payment_method, amount_bdt) "
            "VALUES (?, ?, ?, 'pending', ?, 'bdt', ?)",
            (user.id, coins, file_id, datetime.utcnow().isoformat(), amount),
        )
        await db.commit()
        cur = await db.execute("SELECT last_insert_rowid()")
        payment_id = (await cur.fetchone())[0]

    await update.message.reply_text("✅ Your payment request has been submitted. You'll be notified once reviewed.")

    uname = f"@{user.username}" if user.username else "—"
    txn_note = f"\n🧾 Transaction ID: <code>{html.escape(txn_text)}</code>" if txn_text else ""
    caption = (
        "💵 <b>New BDT Payment Request</b>\n\n"
        f"👤 Username: {html.escape(uname)}\n"
        f"🆔 User ID: <code>{user.id}</code>\n"
        f"💵 Amount: <b>৳{amount}</b>\n"
        f"🪙 Coins: <b>{coins}</b>{txn_note}\n"
        f"📅 Time: {fmt_date(datetime.utcnow().isoformat())}"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Accept", callback_data=f"pay:accept:{payment_id}"),
         InlineKeyboardButton("❌ Reject", callback_data=f"pay:reject:{payment_id}")]
    ])
    admin_ids = await get_all_admin_ids()
    for admin_id in admin_ids:
        try:
            if file_id and is_photo:
                await context.bot.send_photo(admin_id, file_id, caption=caption, parse_mode=ParseMode.HTML, reply_markup=kb)
            elif file_id:
                await context.bot.send_document(admin_id, file_id, caption=caption, parse_mode=ParseMode.HTML, reply_markup=kb)
            else:
                await context.bot.send_message(admin_id, caption, parse_mode=ParseMode.HTML, reply_markup=kb)
        except TelegramError:
            pass
    return ConversationHandler.END


async def cb_buybdt_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    await update.callback_query.answer()
    await update.callback_query.message.reply_text("❌ Cancelled.")
    context.user_data.pop("bdt_amount", None)
    return ConversationHandler.END


async def get_all_admin_ids() -> list[int]:
    ids = {OWNER_ID}
    async with db_conn() as db:
        cur = await db.execute("SELECT user_id FROM admins")
        rows = await cur.fetchall()
        for r in rows:
            ids.add(r[0])
    return list(ids)


async def cb_payment_accept(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    admin = update.effective_user
    if not await is_admin(admin.id):
        await query.answer(ADMIN_ONLY_MSG, show_alert=True)
        return
    payment_id = int(query.data.split(":")[2])
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM payments WHERE payment_id=?", (payment_id,))
        payment = await cur.fetchone()
        if not payment or payment["status"] != "pending":
            await query.answer("⚠️ Already processed.", show_alert=True)
            return
        await db.execute(
            "UPDATE payments SET status='accepted', admin_id=? WHERE payment_id=?",
            (admin.id, payment_id),
        )
        await db.commit()

    method_note = f"({payment['stars']} stars)" if payment["payment_method"] != "bdt" else f"(৳{payment['amount_bdt']})"
    await add_coins(payment["user_id"], payment["coins"], "payment", f"Payment accepted {method_note}")
    await query.answer("✅ Accepted")
    try:
        await query.edit_message_caption(
            caption=query.message.caption + "\n\n✅ <b>ACCEPTED</b>", parse_mode=ParseMode.HTML
        )
    except BadRequest:
        pass
    try:
        await context.bot.send_message(
            payment["user_id"],
            f"✅ <b>Payment Accepted!</b>\n🪙 {payment['coins']} Coins have been added to your wallet.",
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        pass


async def cb_payment_reject(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    admin = update.effective_user
    if not await is_admin(admin.id):
        await query.answer(ADMIN_ONLY_MSG, show_alert=True)
        return
    payment_id = int(query.data.split(":")[2])
    context.user_data["reject_payment_id"] = payment_id
    context.user_data["reject_chat_msg"] = (query.message.chat_id, query.message.message_id)
    await query.answer()
    await query.message.reply_text(
        "✏️ Enter rejection reason (or send - to skip):"
    )
    context.user_data["awaiting_reject_reason"] = True


async def handle_reject_reason(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not context.user_data.get("awaiting_reject_reason"):
        return
    context.user_data["awaiting_reject_reason"] = False
    reason = update.message.text.strip()
    reason = "" if reason == "-" else reason
    payment_id = context.user_data.pop("reject_payment_id")

    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM payments WHERE payment_id=?", (payment_id,))
        payment = await cur.fetchone()
        if not payment or payment["status"] != "pending":
            await update.message.reply_text("⚠️ Already processed.")
            return
        await db.execute(
            "UPDATE payments SET status='rejected', admin_id=?, reason=? WHERE payment_id=?",
            (update.effective_user.id, reason, payment_id),
        )
        await db.commit()

    await update.message.reply_text("❌ Payment rejected and user notified.")
    try:
        msg = "❌ <b>Payment Rejected</b>"
        if reason:
            msg += f"\nReason: {html.escape(reason)}"
        await context.bot.send_message(payment["user_id"], msg, parse_mode=ParseMode.HTML)
    except TelegramError:
        pass


# =============================================================================
# DAILY BONUS
# =============================================================================

async def handle_daily_bonus(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    user = update.effective_user
    lock = await get_user_action_lock(user.id)
    async with lock:
        row = await get_user_row(user.id)
        if row and row["last_bonus_time"]:
            last = datetime.fromisoformat(row["last_bonus_time"])
            elapsed = datetime.utcnow() - last
            if elapsed < timedelta(hours=24):
                remaining = timedelta(hours=24) - elapsed
                h, rem = divmod(int(remaining.total_seconds()), 3600)
                m = rem // 60
                await update.effective_message.reply_text(
                    f"⏳ <b>Daily Bonus Already Claimed</b>\nCome back in <b>{h}h {m}m</b>.",
                    parse_mode=ParseMode.HTML,
                )
                return

        premium = await is_premium_active(user.id)
        if premium:
            reward = int(await get_setting("premium_daily_bonus", "40"))
            tx_label = "Premium daily bonus claim"
        else:
            reward = int(await get_setting("daily_bonus", "25"))
            tx_label = "Daily bonus claim"
        await add_coins(user.id, reward, "daily_bonus", tx_label)
        async with db_conn() as db:
            await db.execute(
                "UPDATE users SET last_bonus_time=? WHERE user_id=?",
                (datetime.utcnow().isoformat(), user.id),
            )
            await db.commit()
    badge = "\n👑 <i>Premium Daily Bonus</i>" if premium else ""
    await update.effective_message.reply_text(
        f"🎁 <b>Daily Bonus Claimed!</b>\n🪙 You received <b>{reward} Coins</b>.{badge}",
        parse_mode=ParseMode.HTML,
    )


# =============================================================================
# REFERRAL / LEADERBOARD
# =============================================================================

async def handle_invite_friends(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    user = update.effective_user
    reward = await get_setting("referral_reward", "20")
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (user.id,))
        count = (await cur.fetchone())[0]
    link = f"https://t.me/{BOT_USERNAME}?start={user.id}"
    text = (
        "🚀 <b>Invite Friends</b>\n\n"
        f"Earn <b>{reward} Coins</b> for every friend who joins using your link!\n\n"
        f"🔗 <code>{link}</code>\n\n"
        f"👥 Total Referrals: <b>{count}</b>"
    )
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)


async def handle_leaderboard(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT referrer_id, COUNT(*) as cnt FROM referrals GROUP BY referrer_id "
            "ORDER BY cnt DESC LIMIT 10"
        )
        rows = await cur.fetchall()

    if not rows:
        await update.effective_message.reply_text("🏆 <b>Leaderboard</b>\n\nNo referrals yet.", parse_mode=ParseMode.HTML)
        return

    medals = ["🥇", "🥈", "🥉"]
    lines = ["🏆 <b>Top 10 Referrals</b>\n"]
    for i, r in enumerate(rows):
        u = await get_user_row(r["referrer_id"])
        name = html.escape(u["first_name"] or "Unknown") if u else "Unknown"
        rank = medals[i] if i < 3 else f"{i+1}."
        lines.append(f"{rank} {name} — <b>{r['cnt']}</b> referrals")
    await update.effective_message.reply_text("\n".join(lines), parse_mode=ParseMode.HTML)


# =============================================================================
# REDEEM CODE
# =============================================================================

async def handle_redeem_prompt(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await guard_user(update, context):
        return ConversationHandler.END
    await update.effective_message.reply_text(
        "🎟️ Please enter your redeem code:",
        reply_markup=ReplyKeyboardMarkup([["❌ Cancel"]], resize_keyboard=True),
    )
    return RD_CODE


async def handle_redeem_code(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if update.message.text.strip() == "❌ Cancel":
        admin = await is_admin(update.effective_user.id)
        await update.message.reply_text("Cancelled.", reply_markup=user_reply_keyboard(admin))
        return ConversationHandler.END

    code = update.message.text.strip().upper()
    user = update.effective_user
    lock = await get_user_action_lock(user.id)

    async with lock:
        async with db_conn() as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM redeems WHERE code=?", (code,))
            redeem = await cur.fetchone()

            admin = await is_admin(user.id)
            if not redeem:
                await update.message.reply_text("❌ Invalid Redeem Code.", reply_markup=user_reply_keyboard(admin))
                return ConversationHandler.END

            if redeem["status"] != "active":
                await update.message.reply_text("❌ This code is no longer active.", reply_markup=user_reply_keyboard(admin))
                return ConversationHandler.END

            if redeem["expiry_date"]:
                try:
                    if datetime.fromisoformat(redeem["expiry_date"]) < datetime.utcnow():
                        await db.execute("UPDATE redeems SET status='expired' WHERE code=?", (code,))
                        await db.commit()
                        await update.message.reply_text("❌ This code has expired.", reply_markup=user_reply_keyboard(admin))
                        return ConversationHandler.END
                except ValueError:
                    pass

            if redeem["usage_limit"] and redeem["used_count"] >= redeem["usage_limit"]:
                await update.message.reply_text("❌ This code has reached its usage limit.", reply_markup=user_reply_keyboard(admin))
                return ConversationHandler.END

            cur = await db.execute(
                "SELECT 1 FROM redeem_uses WHERE code=? AND user_id=?", (code, user.id)
            )
            if await cur.fetchone():
                await update.message.reply_text("❌ You have already redeemed this code.", reply_markup=user_reply_keyboard(admin))
                return ConversationHandler.END

            await db.execute(
                "INSERT INTO redeem_uses (code, user_id, timestamp) VALUES (?, ?, ?)",
                (code, user.id, datetime.utcnow().isoformat()),
            )
            await db.execute("UPDATE redeems SET used_count = used_count + 1 WHERE code=?", (code,))
            await db.commit()

        if redeem["coin_reward"]:
            await add_coins(user.id, redeem["coin_reward"], "redeem", f"Redeem code {code}")
        if redeem["premium_days"]:
            await grant_premium(user.id, redeem["premium_days"], admin_id=0)

    msg = f"✅ <b>Redeem Successful!</b>\n🪙 +{redeem['coin_reward']} Coins"
    if redeem["premium_days"]:
        msg += f"\n⭐ +{redeem['premium_days']} Days Premium"
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=user_reply_keyboard(admin))
    return ConversationHandler.END


# =============================================================================
# MY STATS
# =============================================================================

async def handle_my_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    user = update.effective_user
    row = await get_user_row(user.id)
    balance = await get_balance(user.id)
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM purchases WHERE user_id=?", (user.id,))
        purchased = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (user.id,))
        refs = (await cur.fetchone())[0]
        cur = await db.execute("SELECT COUNT(*) FROM redeem_uses WHERE user_id=?", (user.id,))
        redeems = (await cur.fetchone())[0]

    is_premium = await is_premium_active(user.id)
    premium_line = "👑 <b>Premium — Active</b>" if is_premium else "⭐ Premium: <i>Not Active</i>"
    text = (
        "📊 <b>My Stats</b>\n"
        f"{DIVIDER}\n"
        f"👤 <b>User ID:</b> <code>{user.id}</code>\n"
        f"📅 <b>Join Date:</b> {fmt_date(row['join_date']) if row else '—'}\n"
        f"🪙 <b>Coins:</b> {balance}\n"
        f"📁 <b>Purchased Files:</b> {purchased}\n"
        f"👥 <b>Referrals:</b> {refs}\n"
        f"🎁 <b>Redeem Count:</b> {redeems}\n"
        f"{premium_line}\n"
        f"{DIVIDER}"
    )
    await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)


# =============================================================================
# FILE STORE — USER SIDE (BROWSE / VIEW / BUY / DOWNLOAD)
# =============================================================================

async def handle_buy_files(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await guard_user(update, context):
        return
    await send_file_list(update, context, page=0)


async def send_file_list(update: Update, context: ContextTypes.DEFAULT_TYPE, page: int, edit: bool = False) -> None:
    per_page = 8
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT file_pk, file_name, price FROM files WHERE is_deleted=0 "
            "ORDER BY file_pk DESC LIMIT ? OFFSET ?",
            (per_page, page * per_page),
        )
        rows = await cur.fetchall()

    if not rows:
        text = "📁 <b>Buy Files</b>\n\nNo files available right now."
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("📁 My Purchases", callback_data="purchases:0")]])
    else:
        text = "📁 <b>Buy Files</b>\n\nSelect a file to view details:"
        buttons = []
        for r in rows:
            tag = "🟢 FREE" if r["price"] == 0 else f"🪙 {r['price']}"
            buttons.append([InlineKeyboardButton(f"📄 {r['file_name']} — {tag}", callback_data=f"file:view:{r['file_pk']}")])
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"files:list:{page-1}"))
        if len(rows) == per_page:
            nav.append(InlineKeyboardButton("Next ➡", callback_data=f"files:list:{page+1}"))
        if nav:
            buttons.append(nav)
        buttons.append([InlineKeyboardButton("📁 My Purchases", callback_data="purchases:0")])
        kb = InlineKeyboardMarkup(buttons)

    if edit and update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_files_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    page = int(query.data.split(":")[2])
    await send_file_list(update, context, page, edit=True)


async def cb_file_view(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    file_pk = int(query.data.split(":")[2])
    user = update.effective_user

    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM files WHERE file_pk=? AND is_deleted=0", (file_pk,))
        f = await cur.fetchone()
        if not f:
            await query.answer("❌ File not found.", show_alert=True)
            return
        cur = await db.execute(
            "SELECT 1 FROM purchases WHERE user_id=? AND file_pk=?", (user.id, file_pk)
        )
        owned = bool(await cur.fetchone())

    await query.answer()
    icon = FILE_TYPE_ICON.get(f["file_kind"], "📄")
    text = (
        f"{icon} <b>{html.escape(f['file_name'])}</b>\n\n"
        f"📦 Size: <b>{fmt_size(f['file_size'])}</b>\n"
        f"📄 Description: {html.escape(f['description']) if f['description'] else '—'}\n"
    )
    if f["price"] == 0 or owned:
        text += "\n🟢 <b>FREE</b>" if f["price"] == 0 and not owned else "\n✅ <b>You own this file</b>"
        buttons = [[InlineKeyboardButton("⬇ Download", callback_data=f"file:dl:{file_pk}")]]
    else:
        text += f"\n🪙 <b>{f['price']} Coins</b>"
        buttons = [[InlineKeyboardButton("🛒 Buy Now", callback_data=f"file:buy:{file_pk}")]]
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="files:list:0")])
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_file_buy(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    file_pk = int(query.data.split(":")[2])
    user = update.effective_user
    lock = await get_user_action_lock(user.id)
    async with lock:
        async with db_conn() as db:
            db.row_factory = aiosqlite.Row
            cur = await db.execute("SELECT * FROM files WHERE file_pk=? AND is_deleted=0", (file_pk,))
            f = await cur.fetchone()
            if not f:
                await query.answer("❌ File not found.", show_alert=True)
                return
            cur = await db.execute("SELECT 1 FROM purchases WHERE user_id=? AND file_pk=?", (user.id, file_pk))
            if await cur.fetchone():
                await query.answer("✅ You already own this file.", show_alert=True)
                return

        if f["price"] > 0:
            ok = await remove_coins(user.id, f["price"], "purchase", f"Purchased file: {f['file_name']}")
            if not ok:
                await query.answer("❌ Not enough Coins.", show_alert=True)
                await query.edit_message_text(
                    "❌ <b>Not enough Coins.</b>\n\nPlease top up your wallet to continue.",
                    parse_mode=ParseMode.HTML,
                    reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("💎 Open Wallet", callback_data="wallet:home")]]),
                )
                return

        async with db_conn() as db:
            await db.execute(
                "INSERT INTO purchases (user_id, file_pk, price, timestamp) VALUES (?, ?, ?, ?)",
                (user.id, file_pk, f["price"], datetime.utcnow().isoformat()),
            )
            await db.commit()

    await query.answer("✅ Purchased!")
    await query.edit_message_text(
        f"✅ <b>Purchase Successful!</b>\n\nYou now own <b>{html.escape(f['file_name'])}</b> forever.",
        parse_mode=ParseMode.HTML,
        reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("⬇ Download Now", callback_data=f"file:dl:{file_pk}")]]),
    )


async def cb_file_download(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    file_pk = int(query.data.split(":")[2])
    user = update.effective_user

    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM files WHERE file_pk=? AND is_deleted=0", (file_pk,))
        f = await cur.fetchone()
        if not f:
            await query.answer("❌ File not found.", show_alert=True)
            return
        if f["price"] > 0:
            cur = await db.execute("SELECT 1 FROM purchases WHERE user_id=? AND file_pk=?", (user.id, file_pk))
            if not await cur.fetchone():
                await query.answer("❌ You need to purchase this file first.", show_alert=True)
                return

    await query.answer("⬇ Sending file...")
    try:
        await context.bot.send_document(
            chat_id=user.id, document=f["tg_file_id"], caption=f"📄 {html.escape(f['file_name'])}", parse_mode=ParseMode.HTML
        )
    except (BadRequest, TelegramError):
        # some kinds (video/audio/photo) are better sent via copy_message using original message
        try:
            await context.bot.send_message(user.id, "⚠️ Could not deliver file, please contact support.")
        except TelegramError:
            pass
        return

    async with db_conn() as db:
        await db.execute(
            "INSERT INTO downloads (user_id, file_pk, timestamp) VALUES (?, ?, ?)",
            (user.id, file_pk, datetime.utcnow().isoformat()),
        )
        await db.execute("UPDATE files SET downloads_count = downloads_count + 1 WHERE file_pk=?", (file_pk,))
        await db.commit()


async def cb_my_purchases(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    page = int(query.data.split(":")[1])
    per_page = 8
    user = update.effective_user
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT p.*, f.file_name FROM purchases p JOIN files f ON p.file_pk=f.file_pk "
            "WHERE p.user_id=? ORDER BY p.id DESC LIMIT ? OFFSET ?",
            (user.id, per_page, page * per_page),
        )
        rows = await cur.fetchall()

    if not rows:
        text = "📁 <b>My Purchases</b>\n\nYou haven't purchased any files yet."
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("⬅ Back", callback_data="files:list:0")]])
    else:
        text = "📁 <b>My Purchases</b>\n\n"
        buttons = []
        for r in rows:
            buttons.append([InlineKeyboardButton(f"⬇ {r['file_name']}", callback_data=f"file:dl:{r['file_pk']}")])
        buttons.append([InlineKeyboardButton("⬅ Back", callback_data="files:list:0")])
        kb = InlineKeyboardMarkup(buttons)

    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


# =============================================================================
# ADMIN: UPLOAD WIZARD
# =============================================================================

async def cb_admin_upload_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return ConversationHandler.END
    if update.callback_query:
        await update.callback_query.answer()
    await update.effective_message.reply_text(
        "📤 <b>Upload File</b>\n\nSend me the file you want to add to the store.",
        parse_mode=ParseMode.HTML,
    )
    return UP_FILE


async def conv_upload_file(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    msg = update.message
    kind = None
    tg_file = None
    file_name = None
    file_size = 0

    if msg.document:
        kind, tg_file = "document", msg.document
        file_name, file_size = tg_file.file_name or "file", tg_file.file_size or 0
    elif msg.video:
        kind, tg_file = "video", msg.video
        file_name = tg_file.file_name or f"video_{tg_file.file_unique_id}.mp4"
        file_size = tg_file.file_size or 0
    elif msg.audio:
        kind, tg_file = "audio", msg.audio
        file_name = tg_file.file_name or f"audio_{tg_file.file_unique_id}.mp3"
        file_size = tg_file.file_size or 0
    elif msg.photo:
        tg_file = msg.photo[-1]
        kind = "photo"
        file_name = f"photo_{tg_file.file_unique_id}.jpg"
        file_size = tg_file.file_size or 0
    elif msg.voice:
        kind, tg_file = "voice", msg.voice
        file_name = f"voice_{tg_file.file_unique_id}.ogg"
        file_size = tg_file.file_size or 0
    elif msg.animation:
        kind, tg_file = "animation", msg.animation
        file_name = tg_file.file_name or f"gif_{tg_file.file_unique_id}.mp4"
        file_size = tg_file.file_size or 0
    else:
        await msg.reply_text("❌ Unsupported file type. Please send a valid file.")
        return UP_FILE

    context.user_data["up_kind"] = kind
    context.user_data["up_file_id"] = tg_file.file_id
    context.user_data["up_unique_id"] = tg_file.file_unique_id
    context.user_data["up_orig_name"] = file_name
    context.user_data["up_size"] = file_size

    await msg.reply_text(
        f"✅ File received ({fmt_size(file_size)}).\n\n📝 Enter File Name (or send - to use original filename):"
    )
    return UP_NAME


async def conv_upload_name(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    name = context.user_data["up_orig_name"] if text == "-" else text
    context.user_data["up_name"] = name
    await update.message.reply_text("📄 Enter Description (or send - to skip):")
    return UP_DESC


async def conv_upload_desc(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    context.user_data["up_desc"] = "" if text == "-" else text
    await update.message.reply_text("💰 Enter Coin Price (0 = FREE):\n\nExample: 0, 50, 100, 250, 500, 1000")
    return UP_PRICE


async def conv_upload_price(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please enter a valid number.")
        return UP_PRICE
    context.user_data["up_price"] = int(text)
    return await show_upload_preview(update, context)


async def show_upload_preview(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    d = context.user_data
    text = (
        "👀 <b>Preview</b>\n\n"
        f"📁 File Name: {html.escape(d['up_name'])}\n"
        f"📦 File Size: {fmt_size(d['up_size'])}\n"
        f"📄 Description: {html.escape(d['up_desc']) if d['up_desc'] else '—'}\n"
        f"💰 Coin Price: {d['up_price']}\n"
        f"📅 Upload Date: {fmt_date(datetime.utcnow().isoformat())}"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Publish", callback_data="up:publish"),
         InlineKeyboardButton("✏ Edit", callback_data="up:edit")],
        [InlineKeyboardButton("❌ Cancel", callback_data="up:cancel")],
    ])
    await update.message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    return UP_PREVIEW


async def cb_upload_publish(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    d = context.user_data
    user = update.effective_user
    async with db_conn() as db:
        await db.execute(
            "INSERT INTO files (tg_file_id, tg_file_unique_id, file_kind, file_name, file_size, "
            "description, price, upload_date, uploaded_by) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (d["up_file_id"], d["up_unique_id"], d["up_kind"], d["up_name"], d["up_size"],
             d["up_desc"], d["up_price"], datetime.utcnow().isoformat(), user.id),
        )
        await db.commit()
    await query.edit_message_text("✅ <b>File Published Successfully!</b>", parse_mode=ParseMode.HTML)
    for key in ["up_kind", "up_file_id", "up_unique_id", "up_orig_name", "up_size", "up_name", "up_desc", "up_price"]:
        context.user_data.pop(key, None)
    return ConversationHandler.END


async def cb_upload_edit(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.message.reply_text("📝 Enter File Name (or send - to use original filename):")
    return UP_NAME


async def cb_upload_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.edit_message_text("❌ Upload cancelled.")
    for key in ["up_kind", "up_file_id", "up_unique_id", "up_orig_name", "up_size", "up_name", "up_desc", "up_price"]:
        context.user_data.pop(key, None)
    return ConversationHandler.END


# =============================================================================
# ADMIN: MANAGE FILES
# =============================================================================

async def cb_admin_managefiles(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    if update.callback_query:
        await update.callback_query.answer()
    await send_manage_files_list(update, context, page=0)


async def send_manage_files_list(update: Update, context: ContextTypes.DEFAULT_TYPE, page: int) -> None:
    per_page = 8
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT file_pk, file_name, price, downloads_count FROM files WHERE is_deleted=0 "
            "ORDER BY file_pk DESC LIMIT ? OFFSET ?",
            (per_page, page * per_page),
        )
        rows = await cur.fetchall()

    text = "📂 <b>Manage Files</b>\n\nSelect a file to edit or delete:"
    buttons = []
    for r in rows:
        buttons.append([InlineKeyboardButton(
            f"📄 {r['file_name']} ({r['downloads_count']}⬇)", callback_data=f"mf:view:{r['file_pk']}:{page}"
        )])
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"mf:list:{page-1}"))
    if len(rows) == per_page:
        nav.append(InlineKeyboardButton("Next ➡", callback_data=f"mf:list:{page+1}"))
    if nav:
        buttons.append(nav)
    buttons.append([InlineKeyboardButton("⬅ Back to Admin Panel", callback_data="ad:home")])

    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_mf_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    page = int(query.data.split(":")[2])
    await send_manage_files_list(update, context, page)


async def cb_mf_view(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    _, _, file_pk, page = query.data.split(":")
    file_pk = int(file_pk)
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM files WHERE file_pk=?", (file_pk,))
        f = await cur.fetchone()
    if not f:
        await query.answer("❌ Not found.", show_alert=True)
        return
    await query.answer()
    text = (
        f"📄 <b>{html.escape(f['file_name'])}</b>\n\n"
        f"📦 Size: {fmt_size(f['file_size'])}\n"
        f"📄 Description: {html.escape(f['description']) if f['description'] else '—'}\n"
        f"💰 Price: {f['price']} coins\n"
        f"⬇ Downloads: {f['downloads_count']}\n"
        f"📅 Uploaded: {fmt_date(f['upload_date'])}"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Edit Name", callback_data=f"mf:ename:{file_pk}"),
         InlineKeyboardButton("✏️ Edit Desc", callback_data=f"mf:edesc:{file_pk}")],
        [InlineKeyboardButton("✏️ Edit Price", callback_data=f"mf:eprice:{file_pk}")],
        [InlineKeyboardButton("🗑 Delete File", callback_data=f"mf:delete:{file_pk}")],
        [InlineKeyboardButton("⬅ Back", callback_data=f"mf:list:{page}")],
    ])
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_mf_edit_field(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    _, field, file_pk = query.data.split(":")
    context.user_data["ef_file_pk"] = int(file_pk)
    context.user_data["ef_field"] = field
    prompts = {
        "ename": "📝 Enter new File Name:",
        "edesc": "📄 Enter new Description:",
        "eprice": "💰 Enter new Coin Price:",
    }
    await query.message.reply_text(prompts[field])
    return EF_FIELD


async def conv_edit_field_value(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    field = context.user_data.pop("ef_field")
    file_pk = context.user_data.pop("ef_file_pk")
    value = update.message.text.strip()

    column_map = {"ename": "file_name", "edesc": "description", "eprice": "price"}
    column = column_map[field]

    if field == "eprice":
        if not value.isdigit():
            await update.message.reply_text("❌ Please enter a valid number.")
            context.user_data["ef_field"] = field
            context.user_data["ef_file_pk"] = file_pk
            return EF_FIELD
        value = int(value)

    async with db_conn() as db:
        await db.execute(f"UPDATE files SET {column}=? WHERE file_pk=?", (value, file_pk))
        await db.commit()

    await update.message.reply_text("✅ File updated successfully.")
    return ConversationHandler.END


async def cb_mf_delete(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    file_pk = int(query.data.split(":")[2])
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Yes, Delete", callback_data=f"mf:delconfirm:{file_pk}"),
         InlineKeyboardButton("❌ No", callback_data=f"mf:view:{file_pk}:0")],
    ])
    await query.edit_message_text("⚠️ Are you sure you want to delete this file?", reply_markup=kb)


async def cb_mf_delete_confirm(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    file_pk = int(query.data.split(":")[2])
    async with db_conn() as db:
        await db.execute("UPDATE files SET is_deleted=1 WHERE file_pk=?", (file_pk,))
        await db.commit()
    await query.answer("🗑 Deleted")
    await query.edit_message_text("🗑 <b>File deleted successfully.</b>", parse_mode=ParseMode.HTML)


# =============================================================================
# ADMIN: FORCE CHANNEL MANAGER
# =============================================================================

async def cb_admin_fcmgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Add Channel", callback_data="fc:add"),
         InlineKeyboardButton("➖ Remove Channel", callback_data="fc:remove")],
        [InlineKeyboardButton("📋 Channel List", callback_data="fc:list")],
        [InlineKeyboardButton("⬅ Back", callback_data="ad:home")],
    ])
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.edit_message_text("📡 <b>Force Channel Manager</b>", parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text("📡 <b>Force Channel Manager</b>", parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_fc_add_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.message.reply_text(
        "➕ <b>Add Force-Join Channel/Group</b>\n\n"
        "Send any one of these:\n"
        "• A public <b>@username</b>\n"
        "• A numeric <b>chat ID</b> (e.g. <code>-1001234567890</code>)\n"
        "• Or just <b>forward</b> any message from that channel/group here\n\n"
        "I only need to already be a <b>member</b> of it — admin rights aren't required "
        "(they're only used to auto-generate a join link for private chats).",
        parse_mode=ParseMode.HTML,
    )
    return FC_ADD


async def conv_fc_add(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    msg = update.message
    try:
        chat_ref = None

        forward_chat = getattr(msg, "forward_from_chat", None)
        if forward_chat is None:
            origin = getattr(msg, "forward_origin", None)
            forward_chat = getattr(origin, "chat", None) if origin else None

        if forward_chat is not None:
            chat_ref = forward_chat.id
        else:
            text = (msg.text or "").strip()
            if text.startswith("@"):
                chat_ref = text
            elif text.lstrip("-").isdigit():
                chat_ref = int(text)
            else:
                await msg.reply_text(
                    "❌ Please send a valid @username, a numeric chat ID, or forward a message from the channel/group."
                )
                return FC_ADD

        try:
            chat = await context.bot.get_chat(chat_ref)
        except TelegramError as e:
            await msg.reply_text(
                f"❌ Couldn't find that chat ({html.escape(str(e))}).\n"
                "Make sure I've already been added to it, then try again.",
                parse_mode=ParseMode.HTML,
            )
            return FC_ADD

        try:
            me = await context.bot.get_me()
            member = await context.bot.get_chat_member(chat.id, me.id)
            if member.status in ("left", "kicked"):
                await msg.reply_text("❌ I'm not currently a member of that chat. Please add me first, then try again.")
                return FC_ADD
            is_bot_admin = member.status in ("administrator", "creator")
        except TelegramError as e:
            await msg.reply_text(
                f"❌ I can't access that chat's member list ({html.escape(str(e))}).\n"
                "Please make sure I've been added to it.",
                parse_mode=ParseMode.HTML,
            )
            return FC_ADD

        username = f"@{chat.username}" if chat.username else None
        invite_link = None

        if not username:
            # Private chat with no public username — try to auto-generate a join
            # link (requires the bot to have admin + "invite users" rights).
            if is_bot_admin:
                try:
                    invite_link = await context.bot.export_chat_invite_link(chat.id)
                except TelegramError:
                    invite_link = None
            if not invite_link:
                context.user_data["fc_pending"] = {
                    "chat_id": chat.id, "title": chat.title, "chat_type": str(chat.type),
                }
                await msg.reply_text(
                    "⚠️ This is a private chat and I couldn't auto-generate a join link "
                    "(that needs admin rights with 'Invite Users' permission here).\n\n"
                    "Please paste an invite link for it now (e.g. https://t.me/+AbCdEfGh...):"
                )
                return FC_INVITE_LINK

        await _save_force_channel(chat.id, username, chat.title, str(chat.type), invite_link)
        await msg.reply_text(f"✅ Added: <b>{html.escape(chat.title)}</b>", parse_mode=ParseMode.HTML)
        return ConversationHandler.END

    except Exception as e:
        log.exception("Unexpected error in conv_fc_add")
        await msg.reply_text(
            f"⚠️ <b>Something went wrong adding this channel.</b>\n<code>{html.escape(str(e))}</code>\n\n"
            "This has been logged — please share this exact message so it can be fixed.",
            parse_mode=ParseMode.HTML,
        )
        return ConversationHandler.END


async def conv_fc_invite_link(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    link = update.message.text.strip()
    if not (link.startswith("https://t.me/") or link.startswith("http://t.me/")):
        await update.message.reply_text("❌ Please send a valid t.me invite link.")
        return FC_INVITE_LINK
    pending = context.user_data.pop("fc_pending", None)
    if not pending:
        await update.message.reply_text("❌ Something went wrong — please start again from Force Channels.")
        return ConversationHandler.END
    await _save_force_channel(pending["chat_id"], None, pending["title"], pending["chat_type"], link)
    await update.message.reply_text(f"✅ Added: <b>{html.escape(pending['title'])}</b>", parse_mode=ParseMode.HTML)
    return ConversationHandler.END


async def _save_force_channel(chat_id: int, username: str | None, title: str, chat_type: str, invite_link: str | None) -> None:
    async with db_conn() as db:
        if username:
            await db.execute(
                "INSERT INTO force_channels (username, chat_id, title, invite_link, chat_type, added_date) "
                "VALUES (?, ?, ?, ?, ?, ?) ON CONFLICT(username) DO UPDATE SET "
                "chat_id=excluded.chat_id, title=excluded.title, invite_link=excluded.invite_link, "
                "chat_type=excluded.chat_type",
                (username, chat_id, title, invite_link, chat_type, datetime.utcnow().isoformat()),
            )
        else:
            # No username to key on (private chat) — replace any prior entry for this chat_id.
            await db.execute("DELETE FROM force_channels WHERE chat_id=? AND username IS NULL", (chat_id,))
            await db.execute(
                "INSERT INTO force_channels (username, chat_id, title, invite_link, chat_type, added_date) "
                "VALUES (NULL, ?, ?, ?, ?, ?)",
                (chat_id, title, invite_link, chat_type, datetime.utcnow().isoformat()),
            )
        await db.commit()


async def cb_fc_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    channels = await list_force_channels()
    if not channels:
        text = "📋 <b>Channel List</b>\n\nNo channels added yet."
    else:
        lines = ["📋 <b>Channel List</b>\n"]
        for ch in channels:
            lines.append(f"• <b>{html.escape(ch['title'])}</b> — added {fmt_date(ch['added_date'])}")
        text = "\n".join(lines)
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=back_button("ad:fcmgr"))


async def cb_fc_remove_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    channels = await list_force_channels()
    if not channels:
        await query.edit_message_text("No channels to remove.", reply_markup=back_button("ad:fcmgr"))
        return
    buttons = [[InlineKeyboardButton(f"➖ {ch['title']}", callback_data=f"fc:rm:{ch['id']}")] for ch in channels]
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="ad:fcmgr")])
    await query.edit_message_text("➖ Select a channel to remove:", reply_markup=InlineKeyboardMarkup(buttons))


async def cb_fc_remove_confirm(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    ch_id = int(query.data.split(":")[2])
    async with db_conn() as db:
        await db.execute("DELETE FROM force_channels WHERE id=?", (ch_id,))
        await db.commit()
    await query.answer("➖ Removed")
    await cb_fc_remove_menu(update, context)


# =============================================================================
# ADMIN: WALLET MANAGER
# =============================================================================

async def cb_admin_walletmgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Add Coins", callback_data="wm:add"),
         InlineKeyboardButton("➖ Remove Coins", callback_data="wm:remove")],
        [InlineKeyboardButton("♻ Reset Coins", callback_data="wm:reset")],
        [InlineKeyboardButton("👥 Bulk Manage Users", callback_data="wm:bulk")],
        [InlineKeyboardButton("📋 Pending Payments", callback_data="pp:list:0")],
        [InlineKeyboardButton("📜 Wallet History", callback_data="wm:history")],
        [InlineKeyboardButton("⬅ Back", callback_data="ad:home")],
    ])
    text = "💰 <b>Wallet Manager</b>\n\nEnter a User ID to manage their wallet, or view recent history."
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_wm_action_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    action = query.data.split(":")[1]  # add / remove / reset
    context.user_data["wm_action"] = action
    await query.message.reply_text("👤 Enter the target User ID:")
    return UM_SEARCH


async def conv_wm_user_id(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please send a valid numeric User ID.")
        return UM_SEARCH
    target_id = int(text)
    row = await get_user_row(target_id)
    if not row:
        await update.message.reply_text("❌ User not found.")
        return ConversationHandler.END
    context.user_data["wm_target"] = target_id
    action = context.user_data["wm_action"]
    if action == "reset":
        async with db_conn() as db:
            await db.execute("UPDATE wallet SET coins=0 WHERE user_id=?", (target_id,))
            await db.execute(
                "INSERT INTO transactions (user_id, tx_type, amount, description, timestamp) VALUES (?, ?, ?, ?, ?)",
                (target_id, "admin_reset", 0, "Admin reset wallet to 0", datetime.utcnow().isoformat()),
            )
            await db.commit()
        await update.message.reply_text(f"♻ Wallet reset to 0 for user {target_id}.")
        return ConversationHandler.END

    await update.message.reply_text("🪙 Enter the amount:")
    return UM_AMOUNT


async def conv_wm_amount(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit() or int(text) <= 0:
        await update.message.reply_text("❌ Please enter a valid positive number.")
        return UM_AMOUNT
    amount = int(text)
    target_id = context.user_data.pop("wm_target")
    action = context.user_data.pop("wm_action")

    if action == "add":
        new_bal = await add_coins(target_id, amount, "admin_gift", f"Admin added {amount} coins")
        await update.message.reply_text(f"✅ Added {amount} coins. New balance: {new_bal}")
        try:
            await context.bot.send_message(target_id, f"🎁 <b>{amount} Coins</b> have been added to your wallet by admin!", parse_mode=ParseMode.HTML)
        except TelegramError:
            pass
    else:
        ok = await remove_coins(target_id, amount, "admin_deduct", f"Admin removed {amount} coins")
        if ok:
            await update.message.reply_text(f"✅ Removed {amount} coins.")
        else:
            await update.message.reply_text("❌ User doesn't have enough coins to remove that amount.")
    return ConversationHandler.END


async def cb_wm_bulk_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.message.reply_text(
        "👥 <b>Bulk Manage Users</b>\n\n"
        "Send the target users separated by space, comma, or a new line — "
        "numeric User IDs, @usernames, or a mix of both:\n"
        "<code>111 222 @alice @bob</code>",
        parse_mode=ParseMode.HTML,
    )
    return WB_IDS


async def conv_wm_bulk_ids(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    raw = update.message.text.strip()
    tokens = [tok for tok in re.split(r"[\s,]+", raw) if tok]
    if not tokens:
        await update.message.reply_text("❌ Please send at least one User ID or @username.")
        return WB_IDS

    resolved: list[int] = []
    not_found: list[str] = []

    async with db_conn() as db:
        for tok in tokens:
            if tok.startswith("@"):
                uname = tok.lstrip("@")
                cur = await db.execute("SELECT user_id FROM users WHERE username=?", (uname,))
                row = await cur.fetchone()
                if row:
                    resolved.append(row[0])
        for tok in tokens:
            if tok.startswith("@"):
                uname = tok.lstrip("@")
                cur = await db.execute(
                    "SELECT user_id FROM users WHERE username=?",
                    (uname,),
                )
                row = await cur.fetchone()
                if row:
                    resolved.append(row[0])
                else:
                    not_found.append(tok)
            elif tok.isdigit() and int(tok) <= 9223372036854775807:
                resolved.append(int(tok))
            else:
                not_found.append(tok)

    context.user_data["wb_ids"] = resolved
    msg = f"✅ Resolved <b>{len(resolved)}</b> users.\n\nWhat should be applied to all of them?"
    if not_found:
        msg += f"\n\n⚠️ Not found (skipped): {', '.join(not_found[:15])}"
        if len(not_found) > 15:
            msg += f" (+{len(not_found) - 15} more)"
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Add Coins", callback_data="wb:add"),
         InlineKeyboardButton("➖ Remove Coins", callback_data="wb:remove")],
        [InlineKeyboardButton("🚫 Ban All", callback_data="wb:ban"),
         InlineKeyboardButton("✅ Unban All", callback_data="wb:unban")],
        [InlineKeyboardButton("👑 Give Premium", callback_data="wb:premium")],
        [InlineKeyboardButton("❌ Cancel", callback_data="wb:cancel")],
    ])
    await update.message.reply_text(msg, parse_mode=ParseMode.HTML, reply_markup=kb)
    return WB_ACTION


async def cb_wb_action_coins(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    context.user_data["wb_coin_action"] = "add" if query.data == "wb:add" else "remove"
    verb = "add to" if query.data == "wb:add" else "remove from"
    await query.message.reply_text(f"🪙 Enter the coin amount to {verb} all {len(context.user_data['wb_ids'])} users:")
    return WB_AMOUNT


async def conv_wm_bulk_amount(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit() or int(text) <= 0:
        await update.message.reply_text("❌ Please enter a valid positive number.")
        return WB_AMOUNT
    amount = int(text)
    target_ids = context.user_data.pop("wb_ids")
    action = context.user_data.pop("wb_coin_action")
    is_add = action == "add"

    verb = "Adding" if is_add else "Removing"
    status_msg = await update.message.reply_text(f"⏳ {verb} {amount} coins for {len(target_ids)} users...")
    ok_list: list[int] = []
    skipped: list[int] = []

    async def process_one(uid: int) -> None:
        row = await get_user_row(uid)
        if not row:
            skipped.append(uid)
            return
        if is_add:
            await add_coins(uid, amount, "admin_gift", f"Bulk admin gift: {amount} coins")
            success = True
        else:
            success = await remove_coins(uid, amount, "admin_deduct", f"Bulk admin deduct: {amount} coins")
        if not success:
            skipped.append(uid)
            return
        ok_list.append(uid)
        await TELEGRAM_SEND_LIMITER.acquire()
        try:
            verb_msg = f"🎁 <b>{amount} Coins</b> have been added to your wallet by admin!" if is_add \
                else f"⚠️ <b>{amount} Coins</b> have been deducted from your wallet by admin."
            await context.bot.send_message(uid, verb_msg, parse_mode=ParseMode.HTML)
        except TelegramError:
            pass

    await asyncio.gather(*(process_one(uid) for uid in target_ids))

    past_verb = "Added" if is_add else "Removed"
    result = f"✅ <b>Bulk {past_verb} Complete</b>\n\n🪙 {past_verb} {amount} coins for <b>{len(ok_list)}</b> users."
    if skipped:
        result += f"\n⚠️ Skipped (not found or insufficient balance): {', '.join(str(u) for u in skipped[:20])}"
        if len(skipped) > 20:
            result += f" (+{len(skipped) - 20} more)"
    await status_msg.edit_text(result, parse_mode=ParseMode.HTML)
    return ConversationHandler.END


async def cb_wb_action_ban(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    target_ids = context.user_data.pop("wb_ids")
    banned = 1 if query.data == "wb:ban" else 0
    async with db_conn() as db:
        for uid in target_ids:
            await db.execute("UPDATE users SET is_banned=? WHERE user_id=?", (banned, uid))
        await db.commit()
    action_word = "Banned" if banned else "Unbanned"
    await query.message.reply_text(f"✅ <b>{action_word}</b> {len(target_ids)} users.", parse_mode=ParseMode.HTML)
    return ConversationHandler.END


async def cb_wb_action_premium_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("7 Days", callback_data="wb:pset:7"),
         InlineKeyboardButton("30 Days", callback_data="wb:pset:30")],
        [InlineKeyboardButton("90 Days", callback_data="wb:pset:90"),
         InlineKeyboardButton("Lifetime", callback_data="wb:pset:0")],
    ])
    await query.message.reply_text("👑 Select Premium duration to grant to all selected users:", reply_markup=kb)
    return WB_PREMIUM


async def cb_wb_action_premium_set(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    days = int(query.data.split(":")[2])
    target_ids = context.user_data.pop("wb_ids")
    for uid in target_ids:
        await grant_premium(uid, None if days == 0 else days, update.effective_user.id)
        await TELEGRAM_SEND_LIMITER.acquire()
        try:
            label = "Lifetime" if days == 0 else f"{days} days"
            await context.bot.send_message(
                uid, f"👑 <b>You've been granted Premium!</b>\nDuration: {label}", parse_mode=ParseMode.HTML
            )
        except TelegramError:
            pass
    label = "Lifetime" if days == 0 else f"{days} Days"
    await query.message.reply_text(f"✅ Granted <b>{label}</b> Premium to {len(target_ids)} users.", parse_mode=ParseMode.HTML)
    return ConversationHandler.END


async def cb_wb_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    context.user_data.pop("wb_ids", None)
    context.user_data.pop("wb_coin_action", None)
    await query.message.reply_text("❌ Cancelled.")
    return ConversationHandler.END


# =============================================================================
# ADMIN: PENDING PAYMENTS (all at once, paginated)
# =============================================================================

async def cb_pending_payments_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not await is_admin(update.effective_user.id):
        await query.answer(ADMIN_ONLY_MSG, show_alert=True)
        return
    await query.answer()
    page = int(query.data.split(":")[2])
    per_page = 10
    async with db_conn() as db:
        total = (await (await db.execute("SELECT COUNT(*) FROM payments WHERE status='pending'")).fetchone())[0]
        cur = await db.execute(
            "SELECT * FROM payments WHERE status='pending' ORDER BY payment_id ASC LIMIT ? OFFSET ?",
            (per_page, page * per_page),
        )
        rows = await cur.fetchall()

    if not rows and page == 0:
        text = "📋 <b>Pending Payments</b>\n\nNothing pending right now — all caught up! ✅"
        buttons = [[InlineKeyboardButton("⬅ Back", callback_data="ad:walletmgr")]]
    else:
        text = f"📋 <b>Pending Payments</b>  —  Total: <b>{total}</b>\n\nTap Accept/Reject on any request below:\n"
        buttons = []
        for r in rows:
            urow = await get_user_row(r["user_id"])
            uname = f"@{urow['username']}" if urow and urow["username"] else (urow["first_name"] if urow else f"ID {r['user_id']}")
            text += f"\n👤 <b>{html.escape(uname or str(r['user_id']))}</b> — ⭐{r['stars']} → 🪙{r['coins']} <i>({fmt_date(r['timestamp'])})</i>"
            buttons.append([
                InlineKeyboardButton(f"✅ Accept #{r['payment_id']}", callback_data=f"pay:accept:{r['payment_id']}"),
                InlineKeyboardButton(f"❌ Reject #{r['payment_id']}", callback_data=f"pay:reject:{r['payment_id']}"),
            ])
        nav = []
        if page > 0:
            nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"pp:list:{page-1}"))
        if (page + 1) * per_page < total:
            nav.append(InlineKeyboardButton("Next ➡", callback_data=f"pp:list:{page+1}"))
        if nav:
            buttons.append(nav)
        buttons.append([InlineKeyboardButton("⬅ Back", callback_data="ad:walletmgr")])

    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_wm_history(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM transactions ORDER BY tx_id DESC LIMIT 15")
        rows = await cur.fetchall()
    if not rows:
        text = "📜 No transactions yet."
    else:
        lines = ["📜 <b>Recent Wallet History</b>\n"]
        for r in rows:
            lines.append(f"👤 <code>{r['user_id']}</code> {'+' if r['amount']>=0 else ''}{r['amount']} — {html.escape(r['tx_type'])}")
        text = "\n".join(lines)
    await query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=back_button("ad:walletmgr"))


# =============================================================================
# ADMIN: REDEEM MANAGER
# =============================================================================

async def cb_admin_redeemmgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Create Code", callback_data="rm:create")],
        [InlineKeyboardButton("📋 List Codes", callback_data="rm:list")],
        [InlineKeyboardButton("⬅ Back", callback_data="ad:home")],
    ])
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.edit_message_text("🎟 <b>Redeem Manager</b>", parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text("🎟 <b>Redeem Manager</b>", parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_rm_create_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    await query.message.reply_text("🎟 Enter the redeem code (e.g. WELCOME500):")
    return RM_CODE


async def conv_rm_code(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    code = update.message.text.strip().upper()
    if not re.match(r"^[A-Z0-9_\-]{3,32}$", code):
        await update.message.reply_text("❌ Invalid code format. Use letters/numbers only (3-32 chars).")
        return RM_CODE
    async with db_conn() as db:
        cur = await db.execute("SELECT 1 FROM redeems WHERE code=?", (code,))
        if await cur.fetchone():
            await update.message.reply_text("❌ This code already exists. Try another.")
            return RM_CODE
    context.user_data["rm_code"] = code
    await update.message.reply_text("💰 Enter Coin Reward (e.g. 500):")
    return RM_COINS


async def conv_rm_coins(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please enter a valid number.")
        return RM_COINS
    context.user_data["rm_coins"] = int(text)
    await update.message.reply_text("⭐ Enter Premium Reward in days (0 for none):")
    return RM_PREMIUM


async def conv_rm_premium(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please enter a valid number.")
        return RM_PREMIUM
    context.user_data["rm_premium"] = int(text)
    await update.message.reply_text("🔢 Enter Usage Limit (0 for unlimited):")
    return RM_LIMIT


async def conv_rm_limit(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit():
        await update.message.reply_text("❌ Please enter a valid number.")
        return RM_LIMIT
    context.user_data["rm_limit"] = int(text)
    await update.message.reply_text("📅 Enter Expiry Date (DD-MM-YYYY) or send - for no expiry:")
    return RM_EXPIRY


async def conv_rm_expiry(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    expiry_iso = None

    if text != "-":
        try:
            expiry_iso = datetime.strptime(
                text, "%d-%m-%Y"
            ).isoformat()
        except ValueError:
            await update.message.reply_text(
                "❌ Invalid date format. Use DD-MM-YYYY or send -."
            )
            return RM_EXPIRY

    d = context.user_data
    required_keys = (
        "rm_code", "rm_coins", "rm_premium", "rm_limit"
    )

    missing_keys = [key for key in required_keys if key not in d]

    if missing_keys:
        log.warning(
            "Redeem Manager state missing for user %s: %s",
            update.effective_user.id,
            ", ".join(missing_keys),
        )

        for key in required_keys:
            context.user_data.pop(key, None)

        await update.message.reply_text(
            "⚠️ Redeem setup data was lost. "
            "Please open Admin Panel → Redeem Manager → "
            "Create again and complete all steps."
        )
        return ConversationHandler.END

    async with db_conn() as db:
        await db.execute(
            "INSERT INTO redeems "
            "(code, coin_reward, premium_days, usage_limit, "
            "expiry_date, status, created_by, created_at) "
            "VALUES (?, ?, ?, ?, ?, 'active', ?, ?)",
            (
                d["rm_code"],
                d["rm_coins"],
                d["rm_premium"],
                d["rm_limit"],
                expiry_iso,
                update.effective_user.id,
                datetime.utcnow().isoformat(),
            ),
        )
        await db.commit()

    await update.message.reply_text(
        f"✅ <b>Redeem Code Created!</b>\n\n"
        f"🎟 Code: <code>{d['rm_code']}</code>\n"
        f"💰 Coins: {d['rm_coins']}\n"
        f"⭐ Premium Days: {d['rm_premium']}\n"
        f"🔢 Usage Limit: {d['rm_limit'] or 'Unlimited'}\n"
        f"📅 Expiry: {text if text != '-' else 'Never'}",
        parse_mode=ParseMode.HTML,
    )

    for key in required_keys:
        context.user_data.pop(key, None)

    return ConversationHandler.END

async def cb_rm_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()

    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute(
            "SELECT * FROM redeems ORDER BY created_at DESC LIMIT 15"
        )
        rows = await cur.fetchall()

    if not rows:
        text = "📋 No redeem codes yet."
    else:
        lines = ["📋 <b>Redeem Codes</b>\n"]
        for r in rows:
            lines.append(
                f"🎟 <code>{r['code']}</code> — "
                f"{r['coin_reward']}🪙 | "
                f"{r['used_count']}/{r['usage_limit'] or '∞'} used | "
                f"{r['status']}"
            )
        text = "\n".join(lines)

    await query.edit_message_text(
        text,
        parse_mode=ParseMode.HTML,
        reply_markup=back_button("ad:redeem"),
    )
# =============================================================================
# ADMIN: USER MANAGER
# =============================================================================

async def cb_admin_usermgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return ConversationHandler.END
    if update.callback_query:
        await update.callback_query.answer()
    await update.effective_message.reply_text("🔍 Enter User ID or @username to search:")
    return UM_SEARCH


async def conv_um_search(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        if text.isdigit():
            cur = await db.execute("SELECT * FROM users WHERE user_id=?", (int(text),))
        else:
            uname = text.lstrip("@")
            cur = await db.execute("SELECT * FROM users WHERE username=?", (uname,))
        row = await cur.fetchone()

    if not row:
        await update.message.reply_text("❌ User not found.")
        return ConversationHandler.END

    await send_user_profile(update.message, row["user_id"])
    return ConversationHandler.END


async def send_user_profile(message_or_query, target_id: int, edit: bool = False):
    row = await get_user_row(target_id)
    if not row:
        return
    balance = await get_balance(target_id)
    async with db_conn() as db:
        cur = await db.execute("SELECT COUNT(*) FROM referrals WHERE referrer_id=?", (target_id,))
        refs = (await cur.fetchone())[0]
    premium = "⭐ Active" if await is_premium_active(target_id) else "❌ None"
    banned = "🚫 Banned" if row["is_banned"] else "✅ Active"

    text = (
        f"👤 <b>User Profile</b>\n\n"
        f"🆔 ID: <code>{target_id}</code>\n"
        f"📛 Name: {html.escape(row['first_name'] or '—')}\n"
        f"🔗 Username: @{html.escape(row['username']) if row['username'] else '—'}\n"
        f"📅 Joined: {fmt_date(row['join_date'])}\n"
        f"🪙 Wallet: {balance}\n"
        f"👥 Referrals: {refs}\n"
        f"⭐ Premium: {premium}\n"
        f"🔒 Status: {banned}"
    )
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ Add Coins", callback_data=f"um:addc:{target_id}"),
         InlineKeyboardButton("➖ Remove Coins", callback_data=f"um:remc:{target_id}")],
        [InlineKeyboardButton("🚫 Ban", callback_data=f"um:ban:{target_id}"),
         InlineKeyboardButton("✅ Unban", callback_data=f"um:unban:{target_id}")],
        [InlineKeyboardButton("👑 Give Premium", callback_data=f"um:givep:{target_id}"),
         InlineKeyboardButton("❌ Remove Premium", callback_data=f"um:remp:{target_id}")],
    ])
    if hasattr(message_or_query, "edit_message_text") and edit:
        await message_or_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await message_or_query.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


# =============================================================================
# ADMIN: ALL USERS (paginated directory)
# =============================================================================

async def cb_admin_all_users(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    if update.callback_query:
        await update.callback_query.answer()
    await send_all_users_list(update, context, page=0)


async def send_all_users_list(update: Update, context: ContextTypes.DEFAULT_TYPE, page: int) -> None:
    per_page = 10
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        total = (await (await db.execute("SELECT COUNT(*) FROM users")).fetchone())[0]
        cur = await db.execute(
            "SELECT user_id, username, first_name, is_banned FROM users "
            "ORDER BY join_date DESC LIMIT ? OFFSET ?",
            (per_page, page * per_page),
        )
        rows = await cur.fetchall()

    text = f"👤 <b>All Users</b>\n\n👥 Total Registered: <b>{total}</b>\n\nTap a user to view or manage their profile:"
    buttons = []
    for r in rows:
        label = f"@{r['username']}" if r["username"] else (r["first_name"] or f"ID {r['user_id']}")
        tag = "🚫 " if r["is_banned"] else "👤 "
        buttons.append([InlineKeyboardButton(f"{tag}{label}", callback_data=f"au:view:{r['user_id']}:{page}")])
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton("⬅ Prev", callback_data=f"au:list:{page-1}"))
    if (page + 1) * per_page < total:
        nav.append(InlineKeyboardButton("Next ➡", callback_data=f"au:list:{page+1}"))
    if nav:
        buttons.append(nav)

    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_au_list(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    page = int(query.data.split(":")[2])
    await send_all_users_list(update, context, page)


async def cb_au_view(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    target_id = int(query.data.split(":")[2])
    await send_user_profile(query, target_id, edit=True)


async def cb_um_ban(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    action, target_id = query.data.split(":")[1], int(query.data.split(":")[2])
    banned = 1 if action == "ban" else 0
    async with db_conn() as db:
        await db.execute("UPDATE users SET is_banned=? WHERE user_id=?", (banned, target_id))
        await db.commit()
    await query.answer("✅ Updated")
    await send_user_profile(query, target_id, edit=True)


async def cb_um_premium(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    action, target_id = query.data.split(":")[1], int(query.data.split(":")[2])
    if action == "remp":
        await remove_premium(target_id)
        await query.answer("✅ Premium removed")
        await send_user_profile(query, target_id, edit=True)
        return
    # givep -> show duration options
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("7 Days", callback_data=f"um:pset:{target_id}:7"),
         InlineKeyboardButton("30 Days", callback_data=f"um:pset:{target_id}:30")],
        [InlineKeyboardButton("90 Days", callback_data=f"um:pset:{target_id}:90"),
         InlineKeyboardButton("Lifetime", callback_data=f"um:pset:{target_id}:0")],
        [InlineKeyboardButton("⬅ Back", callback_data=f"um:back:{target_id}")],
    ])
    await query.answer()
    await query.edit_message_text("👑 Select Premium Duration:", reply_markup=kb)


async def cb_um_pset(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    _, _, target_id, days = query.data.split(":")
    target_id, days = int(target_id), int(days)
    await grant_premium(target_id, None if days == 0 else days, update.effective_user.id)
    await query.answer("✅ Premium granted")
    try:
        await context.bot.send_message(
            target_id,
            f"👑 <b>You've been granted Premium!</b>\nDuration: {'Lifetime' if days==0 else f'{days} days'}",
            parse_mode=ParseMode.HTML,
        )
    except TelegramError:
        pass
    await send_user_profile(query, target_id, edit=True)


async def cb_um_back(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    target_id = int(query.data.split(":")[2])
    await query.answer()
    await send_user_profile(query, target_id, edit=True)


async def cb_um_coins_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    action, target_id = query.data.split(":")[1], int(query.data.split(":")[2])
    context.user_data["um_action"] = "add" if action == "addc" else "remove"
    context.user_data["um_target"] = target_id
    await query.message.reply_text("🪙 Enter the coin amount:")
    return UM_AMOUNT


async def conv_um_coins_amount(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    text = update.message.text.strip()
    if not text.isdigit() or int(text) <= 0:
        await update.message.reply_text("❌ Please enter a valid positive number.")
        return UM_AMOUNT
    amount = int(text)
    target_id = context.user_data.pop("um_target")
    action = context.user_data.pop("um_action")
    if action == "add":
        await add_coins(target_id, amount, "admin_gift", "Admin added coins via User Manager")
        await update.message.reply_text(f"✅ Added {amount} coins to user {target_id}.")
    else:
        ok = await remove_coins(target_id, amount, "admin_deduct", "Admin removed coins via User Manager")
        await update.message.reply_text(
            f"✅ Removed {amount} coins from user {target_id}." if ok else "❌ Insufficient balance to remove that amount."
        )
    return ConversationHandler.END


# =============================================================================
# ADMIN: PREMIUM MANAGER (bulk view)
# =============================================================================

async def cb_admin_premiummgr(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    if update.callback_query:
        await update.callback_query.answer()
    async with db_conn() as db:
        db.row_factory = aiosqlite.Row
        cur = await db.execute("SELECT * FROM premium ORDER BY granted_at DESC LIMIT 20")
        rows = await cur.fetchall()
    if not rows:
        text = "👑 <b>Premium Manager</b>\n\nNo premium users yet.\n\nUse 👥 User Manager to grant premium to a specific user."
    else:
        lines = ["👑 <b>Premium Users</b>\n"]
        for r in rows:
            status = "Lifetime" if r["is_lifetime"] else fmt_date(r["expiry_date"])
            lines.append(f"🆔 <code>{r['user_id']}</code> — {status}")
        text = "\n".join(lines)
    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=back_button("ad:home"))
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)


# =============================================================================
# ADMIN: BROADCAST
# =============================================================================

async def cb_admin_broadcast_start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return ConversationHandler.END
    if update.callback_query:
        await update.callback_query.answer()
    await update.effective_message.reply_text(
        "📢 Send the message you want to broadcast (text, photo, video, animation, sticker, document, voice, or audio).\n\n"
        "Send /cancel to abort."
    )
    return BR_CONTENT


async def conv_broadcast_content(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    msg = update.message
    async with db_conn() as db:
        cur = await db.execute("SELECT user_id FROM users")
        all_users = [r[0] for r in await cur.fetchall()]

    status_msg = await msg.reply_text(f"📢 Broadcasting to {len(all_users)} users...")
    counters = {"done": 0, "failed": 0}
    counters_lock = asyncio.Lock()

    async def send_one(uid: int) -> None:
        await TELEGRAM_SEND_LIMITER.acquire()
        try:
            await context.bot.copy_message(chat_id=uid, from_chat_id=msg.chat_id, message_id=msg.message_id)
            async with counters_lock:
                counters["done"] += 1
        except RetryAfter as e:
            await asyncio.sleep(e.retry_after + 0.5)
            try:
                await context.bot.copy_message(chat_id=uid, from_chat_id=msg.chat_id, message_id=msg.message_id)
                async with counters_lock:
                    counters["done"] += 1
            except TelegramError:
                async with counters_lock:
                    counters["failed"] += 1
        except TelegramError:
            async with counters_lock:
                counters["failed"] += 1

    await asyncio.gather(*(send_one(uid) for uid in all_users))

    await status_msg.edit_text(
        f"✅ <b>Broadcast Complete</b>\n\n✅ Sent: {counters['done']}\n❌ Failed: {counters['failed']}",
        parse_mode=ParseMode.HTML,
    )
    return ConversationHandler.END


async def cmd_cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    admin = await is_admin(update.effective_user.id)
    await update.message.reply_text("❌ Cancelled.", reply_markup=user_reply_keyboard(admin))
    context.user_data.clear()
    return ConversationHandler.END


# =============================================================================
# ADMIN: STATISTICS
# =============================================================================

async def cb_admin_stats(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    if update.callback_query:
        await update.callback_query.answer()

    async with db_conn() as db:
        total_users = (await (await db.execute("SELECT COUNT(*) FROM users")).fetchone())[0]
        active_users = (await (await db.execute(
            "SELECT COUNT(*) FROM users WHERE last_seen > ?",
            ((datetime.utcnow() - timedelta(days=7)).isoformat(),)
        )).fetchone())[0]
        premium_users = (await (await db.execute(
            "SELECT COUNT(*) FROM premium WHERE is_lifetime=1 OR expiry_date > ?",
            (datetime.utcnow().isoformat(),)
        )).fetchone())[0]
        total_files = (await (await db.execute("SELECT COUNT(*) FROM files WHERE is_deleted=0")).fetchone())[0]
        total_downloads = (await (await db.execute("SELECT COUNT(*) FROM downloads")).fetchone())[0]
        coins_distributed = (await (await db.execute(
            "SELECT COALESCE(SUM(amount),0) FROM transactions WHERE amount > 0"
        )).fetchone())[0]
        redeem_count = (await (await db.execute("SELECT COUNT(*) FROM redeem_uses")).fetchone())[0]
        referral_count = (await (await db.execute("SELECT COUNT(*) FROM referrals")).fetchone())[0]
        revenue_stars = (await (await db.execute(
            "SELECT COALESCE(SUM(stars),0) FROM payments WHERE status='accepted'"
        )).fetchone())[0]
        pending_payments = (await (await db.execute(
            "SELECT COUNT(*) FROM payments WHERE status='pending'"
        )).fetchone())[0]

    text = (
        "📊 <b>Statistics</b>\n\n"
        f"👥 Total Users: <b>{total_users}</b>\n"
        f"🟢 Active (7d): <b>{active_users}</b>\n"
        f"⭐ Premium Users: <b>{premium_users}</b>\n"
        f"📁 Total Files: <b>{total_files}</b>\n"
        f"⬇ Downloads: <b>{total_downloads}</b>\n"
        f"🪙 Coins Distributed: <b>{coins_distributed}</b>\n"
        f"🎟 Redeem Count: <b>{redeem_count}</b>\n"
        f"🚀 Referral Count: <b>{referral_count}</b>\n"
        f"💰 Revenue: <b>{revenue_stars} ⭐</b>\n"
        f"⏳ Pending Payments: <b>{pending_payments}</b>"
    )
    if update.callback_query:
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=back_button("ad:home"))
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML)


# =============================================================================
# ADMIN: MAINTENANCE
# =============================================================================

async def cb_admin_maintenance(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    current = await get_setting("maintenance", "0")
    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("✅ Enable", callback_data="mt:on"),
         InlineKeyboardButton("❌ Disable", callback_data="mt:off")],
        [InlineKeyboardButton("⬅ Back", callback_data="ad:home")],
    ])
    status = "🚧 ENABLED" if current == "1" else "✅ DISABLED"
    text = f"🛠 <b>Maintenance Mode</b>\n\nCurrent status: <b>{status}</b>"
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=kb)


async def cb_mt_toggle(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    val = "1" if query.data == "mt:on" else "0"
    await set_setting("maintenance", val)
    await query.answer("✅ Updated")
    await cb_admin_maintenance(update, context)


# =============================================================================
# ADMIN: SETTINGS
# =============================================================================

SETTINGS_FIELDS = {
    "referral_reward": "🚀 Referral Reward (coins)",
    "daily_bonus": "🎁 Daily Bonus (coins)",
    "premium_daily_bonus": "👑 Premium Daily Bonus (coins)",
    "coin_packages": "🪙 Coin Packages (JSON list)",
    "premium_pricing": "👑 Premium Pricing (JSON list)",
    "coin_rate_bdt": "💵 Coins per 1 Taka",
    "bdt_payment_details": "💵 BDT Payment Details (bKash/Nagad)",
    "star_rate": "⭐ Star Rate",
    "support_username": "💬 Support Username",
    "payment_username": "💰 Payment Username (Stars)",
    "bot_name": "🏷 Bot Name",
    "force_join": "📡 Force Join (1/0)",
}


async def cb_admin_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        if update.callback_query:
            await update.callback_query.answer(ADMIN_ONLY_MSG, show_alert=True)
        else:
            await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    buttons = [[InlineKeyboardButton(label, callback_data=f"set:{key}")] for key, label in SETTINGS_FIELDS.items()]
    buttons.append([InlineKeyboardButton("⬅ Back", callback_data="ad:home")])
    text = "⚙ <b>Settings</b>\n\nSelect a setting to edit:"
    if update.callback_query:
        await update.callback_query.answer()
        await update.callback_query.edit_message_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))
    else:
        await update.effective_message.reply_text(text, parse_mode=ParseMode.HTML, reply_markup=InlineKeyboardMarkup(buttons))


async def cb_settings_field(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer()
    key = query.data.split(":")[1]
    current = await get_setting(key, "")
    context.user_data["st_key"] = key
    await query.message.reply_text(
        f"✏️ Current value of <b>{SETTINGS_FIELDS.get(key, key)}</b>:\n<code>{html.escape(current)}</code>\n\n"
        f"Send the new value:",
        parse_mode=ParseMode.HTML,
    )
    return ST_VALUE


async def conv_settings_value(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    key = context.user_data.pop("st_key")
    value = update.message.text.strip()
async def conv_settings_value(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    key = context.user_data.pop("st_key", None)

    if key not in SETTINGS_FIELDS:
        await update.message.reply_text(
            "⚠️ Settings session expired. "
            "Please open Admin Panel → Settings and try again."
        )
        return ConversationHandler.END

    value = update.message.text.strip()

    if key == "coin_packages":
        try:
            parsed = json.loads(value)
            assert isinstance(parsed, list)
        except Exception:
            await update.message.reply_text(
                '❌ Invalid JSON. Example: [{"coins": 100, "stars": 3}, {"coins": 500, "stars": 15}]'
            )
            context.user_data["st_key"] = key
            return ST_VALUE

    await set_setting(key, value)
    await update.message.reply_text("✅ Setting updated successfully.")
    return ConversationHandler.END
    await set_setting(key, value)
    await update.message.reply_text("✅ Setting updated successfully.")
    return ConversationHandler.END


# =============================================================================
# ADMIN PANEL ROOT / DISPATCH
# =============================================================================

async def handle_admin_panel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        await update.effective_message.reply_text(ADMIN_ONLY_MSG)
        return
    await update.effective_message.reply_text(
        "👑 <b>Admin Panel</b>\n\nAll admin controls are now available on your keyboard below.\n"
        "Tap <b>⬅️ Back to Main</b> anytime to return to the normal menu.",
        parse_mode=ParseMode.HTML,
        reply_markup=admin_reply_keyboard(),
    )


async def handle_admin_back_to_main(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not await is_admin(update.effective_user.id):
        return
    await update.effective_message.reply_text(
        "🏠 <b>Main Menu</b>", parse_mode=ParseMode.HTML, reply_markup=user_reply_keyboard(True)
    )


async def cb_admin_home(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    await query.answer()
    await query.edit_message_text("👑 <b>Admin Panel</b>\n\nSelect an option below:", parse_mode=ParseMode.HTML, reply_markup=admin_panel_keyboard())


# =============================================================================
# PERIODIC JOBS
# =============================================================================

async def job_expire_premium(context: ContextTypes.DEFAULT_TYPE) -> None:
    async with db_conn() as db:
        await db.execute(
            "DELETE FROM premium WHERE is_lifetime=0 AND expiry_date IS NOT NULL AND expiry_date < ?",
            (datetime.utcnow().isoformat(),),
        )
        await db.commit()


# =============================================================================
# ERROR HANDLER
# =============================================================================

async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    log.error("Exception while handling update:", exc_info=context.error)
    try:
        admin_ids = await get_all_admin_ids()
        err_text = f"⚠️ <b>Bot Error</b>\n<code>{html.escape(str(context.error))[:800]}</code>"
        for admin_id in admin_ids:
            try:
                await context.bot.send_message(admin_id, err_text, parse_mode=ParseMode.HTML)
            except TelegramError:
                pass
    except Exception:
        pass


# =============================================================================
# TEXT ROUTER (reply-keyboard buttons)
# =============================================================================

TEXT_ROUTES = {
    "📁 Buy Files": handle_buy_files,
    "💎 My Wallet": handle_my_wallet,
    "💵 Buy Coins (৳)": handle_buy_coins_bdt,
    "🎁 Daily Bonus": handle_daily_bonus,
    "🚀 Invite Friends": handle_invite_friends,
    "📊 My Stats": handle_my_stats,
    "🏆 Leaderboard": handle_leaderboard,
    "💬 Support": handle_support,
    "👑 Admin Panel": handle_admin_panel,
    # Admin reply-keyboard controls (only ever shown to admins; handlers below
    # each re-check is_admin themselves as defense in depth)
    "📂 Manage Files": cb_admin_managefiles,
    "💰 Wallet Manager": cb_admin_walletmgr,
    "🎟 Redeem Manager": cb_admin_redeemmgr,
    "📡 Force Channels": cb_admin_fcmgr,
    "👤 All Users": cb_admin_all_users,
    "👑 Premium Manager": cb_admin_premiummgr,
    "📊 Statistics": cb_admin_stats,
    "🛠 Maintenance": cb_admin_maintenance,
    "⚙ Settings": cb_admin_settings,
    "⬅️ Back to Main": handle_admin_back_to_main,
}


async def text_router(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if update.effective_user is None or update.message is None or update.message.text is None:
        return  # not a normal user text message (e.g. channel post, edit) — ignore safely
    if context.user_data is not None and context.user_data.get("awaiting_reject_reason"):
        await handle_reject_reason(update, context)
        return
    text = update.message.text
    handler = TEXT_ROUTES.get(text)
    if handler:
        await handler(update, context)


# =============================================================================
# MAIN
# =============================================================================

def build_application() -> Application:
    # concurrent_updates lets PTB process many users' messages/clicks in
    # parallel (asyncio tasks) instead of one-at-a-time — this is the single
    # biggest lever for handling a large burst of simultaneous users.
    # The larger HTTPXRequest connection pools let that many concurrent
    # handlers actually make outbound Telegram API calls at once instead of
    # queueing behind a small default pool.
    concurrent_updates = int(os.environ.get("CONCURRENT_UPDATES", "512"))
    app = (
        ApplicationBuilder()
        .token(BOT_TOKEN)
        .concurrent_updates(concurrent_updates)
        .request(HTTPXRequest(
            connection_pool_size=concurrent_updates,
            pool_timeout=20.0,
            connect_timeout=15.0,
            read_timeout=20.0,
            write_timeout=20.0,
        ))
        .get_updates_request(HTTPXRequest(connection_pool_size=64, pool_timeout=20.0))
        .post_init(post_init)
        .post_shutdown(post_shutdown)
        .build()
    )

    # Flood guard runs first, in its own group, ahead of everything else —
    # excess rapid-fire taps/messages never reach real handlers at all.
    app.add_handler(MessageHandler(filters.ALL, flood_guard), group=-1)
    app.add_handler(CallbackQueryHandler(flood_guard), group=-1)

    app.add_handler(CommandHandler("setup", cmd_setup))
    app.add_handler(CommandHandler("start", cmd_start))
    app.add_handler(CommandHandler("help", cmd_help))
    app.add_handler(CommandHandler("myid", cmd_myid))
    app.add_handler(CommandHandler("admin", cmd_admin))
    app.add_handler(CommandHandler("cancel", cmd_cancel))

    app.add_handler(CallbackQueryHandler(cb_verify_join, pattern="^verify_join$"))

    # Wallet
    app.add_handler(CallbackQueryHandler(cb_wallet_home, pattern="^wallet:home$"))
    app.add_handler(CallbackQueryHandler(cb_wallet_tx, pattern="^wallet:tx:"))
    app.add_handler(CallbackQueryHandler(cb_wallet_buy_premium, pattern="^wallet:buypremium$"))
    app.add_handler(CallbackQueryHandler(cb_premium_purchase, pattern=r"^premium:buy:\d+:\d+$"))

    # Buy coins conversation
    buycoins_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_buycoins_paid, pattern="^buycoins:paid$")],
        states={
            BC_STARS: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_buycoins_stars)],
            BC_SCREENSHOT: [MessageHandler((filters.PHOTO | filters.Document.ALL) & ~filters.COMMAND, conv_buycoins_screenshot)],
        },
        fallbacks=[CallbackQueryHandler(cb_buycoins_cancel, pattern="^buycoins:cancel$"), CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(CallbackQueryHandler(cb_buycoins_start, pattern="^wallet:buycoins$"))
    app.add_handler(buycoins_conv)
    app.add_handler(CallbackQueryHandler(cb_payment_accept, pattern=r"^pay:accept:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_payment_reject, pattern=r"^pay:reject:\d+$"))

    buybdt_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_buybdt_paid, pattern="^buybdt:paid$")],
        states={
            BDT_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_buybdt_amount)],
            BDT_PROOF: [MessageHandler((filters.PHOTO | filters.Document.ALL | filters.TEXT) & ~filters.COMMAND, conv_buybdt_proof)],
        },
        fallbacks=[CallbackQueryHandler(cb_buybdt_cancel, pattern="^buybdt:cancel$"), CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(buybdt_conv)

    # Redeem
    redeem_conv = ConversationHandler(
        entry_points=[MessageHandler(filters.Regex("^🎟️ Redeem Code$"), handle_redeem_prompt)],
        states={RD_CODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, handle_redeem_code)]},
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(redeem_conv)

    # Files
    app.add_handler(CallbackQueryHandler(cb_files_list, pattern=r"^files:list:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_file_view, pattern=r"^file:view:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_file_buy, pattern=r"^file:buy:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_file_download, pattern=r"^file:dl:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_my_purchases, pattern=r"^purchases:\d+$"))

    # Admin root
    app.add_handler(CallbackQueryHandler(cb_admin_home, pattern="^ad:home$"))
    app.add_handler(CallbackQueryHandler(cb_admin_managefiles, pattern="^ad:managefiles$"))
    app.add_handler(CallbackQueryHandler(cb_admin_walletmgr, pattern="^ad:walletmgr$"))
    app.add_handler(CallbackQueryHandler(cb_admin_redeemmgr, pattern="^ad:redeemmgr$"))
    app.add_handler(CallbackQueryHandler(cb_admin_fcmgr, pattern="^ad:fcmgr$"))
    app.add_handler(CallbackQueryHandler(cb_admin_premiummgr, pattern="^ad:premiummgr$"))
    app.add_handler(CallbackQueryHandler(cb_admin_stats, pattern="^ad:stats$"))
    app.add_handler(CallbackQueryHandler(cb_admin_maintenance, pattern="^ad:maintenance$"))
    app.add_handler(CallbackQueryHandler(cb_mt_toggle, pattern="^mt:(on|off)$"))
    app.add_handler(CallbackQueryHandler(cb_admin_settings, pattern="^ad:settings$"))

    # Upload wizard
    upload_conv = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(cb_admin_upload_start, pattern="^ad:upload$"),
            MessageHandler(filters.Regex("^📤 Upload File$"), cb_admin_upload_start),
        ],
        states={
            UP_FILE: [MessageHandler(
                (filters.Document.ALL | filters.VIDEO | filters.AUDIO | filters.PHOTO | filters.VOICE | filters.ANIMATION) & ~filters.COMMAND,
                conv_upload_file
            )],
            UP_NAME: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_upload_name)],
            UP_DESC: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_upload_desc)],
            UP_PRICE: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_upload_price)],
            UP_PREVIEW: [
                CallbackQueryHandler(cb_upload_publish, pattern="^up:publish$"),
                CallbackQueryHandler(cb_upload_edit, pattern="^up:edit$"),
                CallbackQueryHandler(cb_upload_cancel, pattern="^up:cancel$"),
            ],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(upload_conv)

    # Manage files
    app.add_handler(CallbackQueryHandler(cb_mf_list, pattern=r"^mf:list:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_mf_view, pattern=r"^mf:view:\d+:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_mf_delete, pattern=r"^mf:delete:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_mf_delete_confirm, pattern=r"^mf:delconfirm:\d+$"))

    edit_field_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_mf_edit_field, pattern=r"^mf:(ename|edesc|eprice):\d+$")],
        states={EF_FIELD: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_edit_field_value)]},
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(edit_field_conv)

    # Force channel manager
    fc_add_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_fc_add_start, pattern="^fc:add$")],
        states={
            FC_ADD: [MessageHandler(~filters.COMMAND, conv_fc_add)],  # text OR a forwarded message
            FC_INVITE_LINK: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_fc_invite_link)],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(fc_add_conv)
    app.add_handler(CallbackQueryHandler(cb_fc_list, pattern="^fc:list$"))
    app.add_handler(CallbackQueryHandler(cb_fc_remove_menu, pattern="^fc:remove$"))
    app.add_handler(CallbackQueryHandler(cb_fc_remove_confirm, pattern=r"^fc:rm:\d+$"))

    # Wallet manager (admin)
    wm_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_wm_action_start, pattern="^wm:(add|remove|reset)$")],
        states={
            UM_SEARCH: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_wm_user_id)],
            UM_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_wm_amount)],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(wm_conv)
    app.add_handler(CallbackQueryHandler(cb_wm_history, pattern="^wm:history$"))

    # Bulk manage users (admin): add/remove coins, ban/unban, grant premium
    wb_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_wm_bulk_start, pattern="^wm:bulk$")],
        states={
            WB_IDS: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_wm_bulk_ids)],
            WB_ACTION: [
                CallbackQueryHandler(cb_wb_action_coins, pattern="^wb:(add|remove)$"),
                CallbackQueryHandler(cb_wb_action_ban, pattern="^wb:(ban|unban)$"),
                CallbackQueryHandler(cb_wb_action_premium_menu, pattern="^wb:premium$"),
                CallbackQueryHandler(cb_wb_cancel, pattern="^wb:cancel$"),
            ],
            WB_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_wm_bulk_amount)],
            WB_PREMIUM: [CallbackQueryHandler(cb_wb_action_premium_set, pattern=r"^wb:pset:\d+$")],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(wb_conv)

    # Pending payments — view/act on all pending requests together (admin)
    app.add_handler(CallbackQueryHandler(cb_pending_payments_list, pattern=r"^pp:list:\d+$"))

    # Redeem manager (admin)
    rm_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_rm_create_start, pattern="^rm:create$")],
        states={
            RM_CODE: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_code)],
            RM_COINS: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_coins)],
            RM_PREMIUM: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_premium)],
            RM_LIMIT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_limit)],
            RM_EXPIRY: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_rm_expiry)],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(rm_conv)
    app.add_handler(CallbackQueryHandler(cb_rm_list, pattern="^rm:list$"))

    # User manager (admin)
    um_conv = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(cb_admin_usermgr, pattern="^ad:usermgr$"),
            MessageHandler(filters.Regex("^👥 User Manager$"), cb_admin_usermgr),
            CallbackQueryHandler(cb_um_coins_start, pattern=r"^um:(addc|remc):\d+$"),
        ],
        states={
            UM_SEARCH: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_um_search)],
            UM_AMOUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_um_coins_amount)],
        },
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(um_conv)
    app.add_handler(CallbackQueryHandler(cb_um_ban, pattern=r"^um:(ban|unban):\d+$"))
    app.add_handler(CallbackQueryHandler(cb_um_premium, pattern=r"^um:(givep|remp):\d+$"))
    app.add_handler(CallbackQueryHandler(cb_um_pset, pattern=r"^um:pset:\d+:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_um_back, pattern=r"^um:back:\d+$"))

    # All Users directory (admin)
    app.add_handler(CallbackQueryHandler(cb_au_list, pattern=r"^au:list:\d+$"))
    app.add_handler(CallbackQueryHandler(cb_au_view, pattern=r"^au:view:\d+:\d+$"))

    # Broadcast
    broadcast_conv = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(cb_admin_broadcast_start, pattern="^ad:broadcast$"),
            MessageHandler(filters.Regex("^📢 Broadcast$"), cb_admin_broadcast_start),
        ],
        states={BR_CONTENT: [MessageHandler(
            (filters.TEXT | filters.PHOTO | filters.VIDEO | filters.ANIMATION | filters.Sticker.ALL |
             filters.Document.ALL | filters.VOICE | filters.AUDIO) & ~filters.COMMAND,
            conv_broadcast_content
        )]},
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(broadcast_conv)

    # Settings
    settings_conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(cb_settings_field, pattern=r"^set:\w+$")],
        states={ST_VALUE: [MessageHandler(filters.TEXT & ~filters.COMMAND, conv_settings_value)]},
        fallbacks=[CommandHandler("cancel", cmd_cancel)],
        per_message=False,
    )
    app.add_handler(settings_conv)

    # Reply-keyboard text router (must be after conversation handlers so states take priority)
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, text_router))

    app.add_error_handler(error_handler)
    return app


async def post_init(app: Application) -> None:
    await init_db()
    await init_db_pool()
    if app.job_queue:
        app.job_queue.run_repeating(job_expire_premium, interval=3600, first=10)
    log.info("Bot initialized and ready.")


async def post_shutdown(app: Application) -> None:
    await close_db_pool()

from flask import Flask
from threading import Thread

web = Flask(__name__)

@web.route("/")
def home():
    return "SHYAIAN FILE STORE BOT IS LIVE!"

def run_web():
    port = int(os.environ.get("PORT", 10000))
    web.run(host="0.0.0.0", port=port)

Thread(target=run_web, daemon=True).start()
def main() -> None:
    app = build_application()
    log.info("Starting TAHMID FILE STORE BOT...")
    app.run_polling(
        allowed_updates=["message", "callback_query"],
        drop_pending_updates=True,
    )


if __name__ == "__main__":
    main()
