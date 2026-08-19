import io
import asyncio
import sys
import os
import re
import json
import certifi
import ssl
import bip32utils
import hashlib
import hmac
import base64
import time
import requests
import uuid
import threading
import solders
import logging
import aiosqlite
import struct
import matplotlib.pyplot as plt
import matplotlib.font_manager as fm
import numpy as np
import urllib.parse
import tempfile
from aiogram.types import Message
from collections import defaultdict

from aiogram import F
import unicodedata
from mnemonic import Mnemonic
from aiogram import types
from functools import wraps
from aiogram.exceptions import TelegramNetworkError 
from aiogram.exceptions import TelegramBadRequest
from aiogram.types import ErrorEvent
from aiogram.types import BufferedInputFile
from io import BytesIO
from typing import Union
from PIL import Image, ImageDraw, ImageFont
from pathlib import Path
from decimal import Decimal
from typing import Dict, List, Tuple, Optional
from dotenv import load_dotenv
from datetime import datetime, timedelta
from datetime import datetime, timezone
from solana.rpc.types import MemcmpOpts
from typing import Tuple
from selenium import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.support import expected_conditions as EC
from PIL import Image
from selenium.webdriver.chrome.service import Service
from webdriver_manager.chrome import ChromeDriverManager
from selenium.webdriver.support.ui import WebDriverWait
from webdriver_manager.core.os_manager import ChromeType

import sqlite3
import contextlib
from contextlib import asynccontextmanager
from threading import Lock

from aiogram import Dispatcher
from aiogram import BaseMiddleware
from aiogram.client.session.aiohttp import AiohttpSession
from aiogram import Bot, Dispatcher, Router, F
from aiogram.enums import ParseMode
from aiogram.client.default import DefaultBotProperties
from aiogram.types import Message, CallbackQuery, InlineKeyboardButton, InlineKeyboardMarkup
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.utils.keyboard import InlineKeyboardBuilder
from aiogram.fsm.context import FSMContext
from aiogram.fsm.state import State, StatesGroup
from aiogram.filters import Command
from aiogram.types import ReplyKeyboardRemove
from typing import Optional, Dict, Any
from aiogram.types import BotCommand, BotCommandScopeDefault
from aiogram.types import MenuButtonCommands

from solders.keypair import Keypair
from solders.pubkey import Pubkey
from solana.rpc.async_api import AsyncClient
from solana.rpc.commitment import Confirmed, Processed
from solana.rpc.types import TxOpts
from solana.rpc.commitment import Processed
from solders.transaction import Transaction
from solders.transaction import Transaction as LegacyTransaction
from solders.system_program import TransferParams, transfer
from solana.rpc.types import TokenAccountOpts
from solana.rpc.api import Client
from solders.signature import Signature as SoldersSignature
from solders.message import Message as SoldersMessage, MessageV0
from solders.transaction import VersionedTransaction
from solders.transaction import VersionedTransaction as SoldersVersionedTransaction
from solders.keypair import Keypair as SoldersKeypair
from solders.compute_budget import set_compute_unit_limit, set_compute_unit_price
from spl.token.constants import TOKEN_PROGRAM_ID, ASSOCIATED_TOKEN_PROGRAM_ID
from spl.token.async_client import AsyncToken
from solders.pubkey import Pubkey as SolanaPublicKey
from solders.message import VersionedMessage as SoldersVersionedMessage
from spl.token.core import MintInfo, AccountInfo
from solders.message import to_bytes_versioned

from spl.token.instructions import (
    get_associated_token_address, 
    create_associated_token_account, 
    transfer_checked, 
    TransferCheckedParams,
    close_account,
    CloseAccountParams
)

import socket
socket.setdefaulttimeout(10)
socket.has_ipv6 = False

if sys.platform == 'win32':
    asyncio.set_event_loop_policy(asyncio.WindowsSelectorEventLoopPolicy())
    
    import socket
    socket.setdefaulttimeout(30)
    
load_dotenv('.env.omegtradingbot')
db_lock = Lock()
SELL_TOKEN_CACHE = {}

# Configuration
BOT_TOKEN = "8873771351:AAE3YeSiwFK-AQneIv_ydEIOM0NiucT46Hc"
ADMIN_IDS = []
admin_ids_str = os.getenv("ADMIN_IDS", "")
if admin_ids_str:
    try:
        ADMIN_IDS = [int(id_str.strip()) for id_str in admin_ids_str.split(",") if id_str.strip().isdigit()]
    except:
        print(f"⚠️ Error parsing ADMIN_IDS: {admin_ids_str}")
        ADMIN_IDS = []

ADMIN_ID = ADMIN_IDS[0] if ADMIN_IDS else 0
RPC_URL = os.getenv("RPC_URL", "https://api.mainnet-beta.solana.com")
HELIUS_RPC = os.getenv("HELIUS_RPC", RPC_URL)
DATABASE_NAME = "omegtradingbot.db"

pnl_card_cache = {}
CACHE_DURATION = 300

JUPITER_QUOTE_URL = "https://lite-api.jup.ag/swap/v1/quote"
JUPITER_SWAP_URL = "https://lite-api.jup.ag/swap/v1/swap"

SOLANA_RPC_ENDPOINTS = [
    "https://api.mainnet-beta.solana.com",
    "https://solana.publicnode.com",
]
session: aiohttp.ClientSession | None = None

def create_ssl_context():
    """Secure SSL context"""
    ssl_context = ssl.create_default_context(cafile=certifi.where())
    ssl_context.check_hostname = True
    ssl_context.verify_mode = ssl.CERT_REQUIRED
    return ssl_context

ssl_context = create_ssl_context()

session = AiohttpSession(timeout=60)
bot = Bot(
    token=BOT_TOKEN, 
    default=DefaultBotProperties(parse_mode=ParseMode.HTML),
    session=session
)
storage = MemoryStorage()
dp = Dispatcher(storage=storage)
router = Router()
dp.include_router(router)

_orig_init = aiohttp.TCPConnector.__init__

def _patched_init(self, *args, **kwargs):
    if "ssl" not in kwargs:
        kwargs["ssl"] = ssl_context
    return _orig_init(self, *args, **kwargs)

aiohttp.TCPConnector.__init__ = _patched_init

class DatabaseManager:
    def __init__(self, db_path: str):
        self.db_path = db_path
        self._lock = asyncio.Lock()
        self._write_lock = asyncio.Lock()
        self._connection_pool = []
        self._max_pool_size = 10  # Increased from 5 to 10
        self._pool_lock = asyncio.Lock()
        self._retry_count = 3
        self._retry_delay = 0.5
        
    async def get_connection(self):
        """Get a connection from pool or create new one with retry logic"""
        for attempt in range(self._retry_count):
            try:
                async with self._pool_lock:
                    if self._connection_pool:
                        return self._connection_pool.pop()
                
                conn = await aiosqlite.connect(
                    self.db_path,
                    timeout=30.0, 
                    check_same_thread=False,
                    isolation_level=None
                )
                
                await conn.execute("PRAGMA journal_mode=WAL")
                await conn.execute("PRAGMA synchronous=NORMAL")
                await conn.execute("PRAGMA cache_size=-4000")  
                await conn.execute("PRAGMA busy_timeout=30000") 
                await conn.execute("PRAGMA foreign_keys=ON")
                await conn.execute("PRAGMA temp_store=MEMORY")
                await conn.execute("PRAGMA mmap_size=30000000000")
                
                return conn
                
            except aiosqlite.OperationalError as e:
                if "database is locked" in str(e) and attempt < self._retry_count - 1:
                    logging.warning(f"Database locked on connection, retrying {attempt + 1}/{self._retry_count}")
                    await asyncio.sleep(self._retry_delay * (attempt + 1))
                    continue
                else:
                    raise e
    
    async def return_connection(self, conn):
        """Return connection to pool"""
        async with self._pool_lock:
            if len(self._connection_pool) < self._max_pool_size:
                self._connection_pool.append(conn)
            else:
                await conn.close()
