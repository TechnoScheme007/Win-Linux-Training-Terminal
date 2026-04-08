#!/usr/bin/env python3
"""
Custom Linux Terminal Simulator
A training environment that emulates a Linux shell on Windows.
Features a virtual filesystem persisted to disk, pipes, redirection,
environment variables, globbing, and 80+ standard Linux commands.
"""

import os
import re
import sys
import json
import time
import shlex
import fnmatch
import getpass
import platform
import random
import hashlib
import base64
import io
import tarfile
import gzip as gzlib
import zipfile
import urllib.request
import urllib.error
import ssl
import threading
from datetime import datetime
from pathlib import Path

# Optional readline (tab completion + arrow-key history)
_HAS_READLINE = False
try:
    if os.name == "nt":
        import pyreadline3 as _pyreadline  # noqa: F401
        import readline
    else:
        import readline
    _HAS_READLINE = True
except ImportError:
    try:
        import readline  # may exist on some Windows pythons
        _HAS_READLINE = True
    except ImportError:
        readline = None

# ---------------------------------------------------------------------------
# Persistence
# ---------------------------------------------------------------------------
BASE_DIR = Path(__file__).parent.resolve()
STATE_DIR = BASE_DIR / "vfs_state"
STATE_DIR.mkdir(exist_ok=True)
FS_FILE = STATE_DIR / "filesystem.json"
HIST_FILE = STATE_DIR / "history.txt"
ENV_FILE = STATE_DIR / "env.json"
MOUNTS_FILE = STATE_DIR / "mounts.json"

# ---------------------------------------------------------------------------
# Sandbox safety policy for Windows mounts
# ---------------------------------------------------------------------------
MOUNT_MAX_FILE_SIZE = 10 * 1024 * 1024   # 10 MB hard cap on writes via mounts
MOUNT_BLOCKED_EXTS = {".exe", ".bat", ".cmd", ".com", ".dll", ".sys",
                       ".msi", ".ps1", ".vbs", ".scr", ".lnk"}
# Real Windows directories that may NEVER be mounted (catastrophic if wiped)
MOUNT_FORBIDDEN_REAL = [
    "c:\\", "c:\\windows", "c:\\program files", "c:\\program files (x86)",
    "c:\\users", "c:\\programdata",
]

NOW = lambda: time.time()
USER = "user"
HOST = "linux-trainer"


# ---------------------------------------------------------------------------
# Virtual Filesystem
# ---------------------------------------------------------------------------
def _node(kind, content=None, perms=None, binary=False):
    n = {
        "type": kind,
        "perms": perms or ("rwxr-xr-x" if kind == "dir" else "rw-r--r--"),
        "owner": "root",
        "group": "root",
        "mtime": NOW(),
    }
    if kind == "dir":
        n["children"] = {}
    else:
        n["content"] = content if content is not None else ""
        n["binary"] = binary
    return n


def node_bytes(node):
    """Return the file node's content as bytes (decoding base64 if binary)."""
    if node is None or node.get("type") != "file":
        return b""
    c = node.get("content", "")
    if node.get("binary"):
        try:
            return base64.b64decode(c)
        except Exception:
            return b""
    return c.encode("utf-8", errors="replace")


def node_set_bytes(node, data):
    """Store bytes into a file node (auto-detects binary vs text)."""
    if node is None:
        return
    try:
        node["content"] = data.decode("utf-8")
        node["binary"] = False
    except UnicodeDecodeError:
        node["content"] = base64.b64encode(data).decode("ascii")
        node["binary"] = True
    node["mtime"] = NOW()


def node_text(node):
    """Return file content as text. Binary files become a placeholder string."""
    if node is None:
        return ""
    if node.get("binary"):
        return f"<binary data, {len(node_bytes(node))} bytes>"
    return node.get("content", "")


def _default_fs():
    root = _node("dir")
    c = root["children"]

    def mkdir(parent, name):
        parent[name] = _node("dir")
        return parent[name]["children"]

    def mkfile(parent, name, content):
        parent[name] = _node("file", content)

    bin_ = mkdir(c, "bin")
    etc = mkdir(c, "etc")
    home = mkdir(c, "home")
    tmp = mkdir(c, "tmp")
    var = mkdir(c, "var")
    rootd = mkdir(c, "root")
    usr = mkdir(c, "usr")
    opt = mkdir(c, "opt")
    mnt = mkdir(c, "mnt")
    media = mkdir(c, "media")
    proc = mkdir(c, "proc")
    dev = mkdir(c, "dev")

    mkfile(etc, "hostname", HOST + "\n")
    mkfile(etc, "os-release",
           'NAME="Ubuntu"\nVERSION="22.04 LTS (Jammy Jellyfish)"\n'
           'ID=ubuntu\nPRETTY_NAME="Ubuntu 22.04 LTS"\n')
    mkfile(etc, "passwd",
           "root:x:0:0:root:/root:/bin/bash\n"
           f"{USER}:x:1000:1000:{USER}:/home/{USER}:/bin/bash\n")
    mkfile(etc, "group", "root:x:0:\nuser:x:1000:\n")
    mkfile(etc, "shells", "/bin/sh\n/bin/bash\n/bin/dash\n")
    mkfile(etc, "motd", "Welcome to the Linux Training Terminal!\n")

    user_home = mkdir(home, USER)
    mkfile(user_home, ".bashrc",
           "# ~/.bashrc\nexport PS1='\\u@\\h:\\w$ '\nalias ll='ls -la'\nalias la='ls -A'\n")
    mkfile(user_home, ".profile", "# ~/.profile\n")
    mkfile(user_home, "welcome.txt",
           "Welcome to your Linux training terminal!\n\n"
           "Try: ls, pwd, cd, cat, echo, grep, find, help\n"
           "Pipes work: cat welcome.txt | wc -l\n"
           "Redirection works: echo hello > test.txt\n"
           "Type 'help' for the full list of commands.\n")
    mkdir(user_home, "Documents")
    mkdir(user_home, "Downloads")
    mkdir(user_home, "Pictures")
    docs = user_home["Documents"]["children"]
    mkfile(docs, "notes.txt", "Linux notes\n-----------\n1. Everything is a file\n2. Pipes are powerful\n3. Practice daily\n")
    mkfile(docs, "todo.md", "# TODO\n- [ ] Learn vim\n- [ ] Master grep\n- [ ] Understand permissions\n")

    log = mkdir(var, "log")
    mkfile(log, "syslog", "[boot] system started\n[boot] training mode active\n")
    mkdir(var, "tmp")
    mkdir(usr, "bin")
    mkdir(usr, "local")
    mkdir(usr, "share")
    mkdir(usr, "lib")

    return root


class VFS:
    def __init__(self):
        if FS_FILE.exists():
            try:
                self.root = json.loads(FS_FILE.read_text())
            except Exception:
                self.root = _default_fs()
        else:
            self.root = _default_fs()
            self.save()
        # Ensure /mnt exists for Windows mounts
        if "mnt" not in self.root["children"]:
            self.root["children"]["mnt"] = _node("dir")
        self.mounts = {}  # virtual_path -> {"real_root": str, "readonly": bool}
        self._load_mounts()

    def save(self):
        FS_FILE.write_text(json.dumps(self.root))

    def reset(self):
        self.root = _default_fs()
        if "mnt" not in self.root["children"]:
            self.root["children"]["mnt"] = _node("dir")
        self.save()

    # ---------- Mounts ----------
    def _load_mounts(self):
        if MOUNTS_FILE.exists():
            try:
                self.mounts = json.loads(MOUNTS_FILE.read_text())
            except Exception:
                self.mounts = {}
        for mp in self.mounts:
            self._ensure_mount_dir(mp)

    def _save_mounts(self):
        MOUNTS_FILE.write_text(json.dumps(self.mounts, indent=2))

    def _ensure_mount_dir(self, mp):
        """Create the virtual mount-point directory if missing."""
        parts = self.split(mp)
        node = self.root
        for p in parts:
            if p not in node["children"]:
                node["children"][p] = _node("dir")
            node = node["children"][p]

    def add_mount(self, virtual_path, real_root, readonly=False):
        virtual_path = self.normalize("/", virtual_path)
        real_root = os.path.abspath(real_root)
        if not os.path.isdir(real_root):
            return False, f"real path does not exist or is not a directory: {real_root}"
        rl = real_root.lower().rstrip("\\/")
        # Reject drive roots (c:, c:\, d:, etc.)
        if re.match(r"^[a-z]:$", rl):
            return False, "refused: cannot mount a drive root"
        # Reject critical system dirs and any nested path under them
        forbidden_exact = ["c:\\windows", "c:\\program files",
                           "c:\\program files (x86)", "c:\\programdata"]
        for f in forbidden_exact:
            if rl == f or rl.startswith(f + "\\"):
                return False, f"refused: {f} is a protected system directory"
        # Refuse to mount the user profile root itself, but allow folders under it
        m = re.match(r"^(c:\\users\\[^\\]+)$", rl)
        if m:
            return False, "refused: cannot mount the user profile root directly"
        self.mounts[virtual_path] = {"real_root": real_root, "readonly": readonly}
        self._ensure_mount_dir(virtual_path)
        self._save_mounts()
        return True, ""

    def remove_mount(self, virtual_path):
        virtual_path = self.normalize("/", virtual_path)
        if virtual_path not in self.mounts:
            return False, f"not mounted: {virtual_path}"
        del self.mounts[virtual_path]
        self._save_mounts()
        return True, ""

    def find_mount(self, abs_path):
        """If abs_path falls inside a mount, return (mount_point, info, real_path) or None."""
        for mp in sorted(self.mounts.keys(), key=len, reverse=True):
            if abs_path == mp or abs_path.startswith(mp.rstrip("/") + "/"):
                rel = abs_path[len(mp):].lstrip("/")
                info = self.mounts[mp]
                real_root = os.path.abspath(info["real_root"])
                real = os.path.abspath(os.path.join(real_root, rel))
                # Jail check: real must be inside real_root after resolving
                try:
                    real_resolved = os.path.realpath(real)
                    root_resolved = os.path.realpath(real_root)
                except OSError:
                    return None
                if not (real_resolved == root_resolved or
                        real_resolved.startswith(root_resolved + os.sep)):
                    return None  # escape attempt
                return (mp, info, real_resolved)
        return None

    def _real_to_node(self, real_path, mount_info):
        """Build a synthesized VFS node from a real disk path. Single level."""
        try:
            st = os.stat(real_path)
        except (OSError, PermissionError):
            return None
        if os.path.isdir(real_path):
            children = {}
            try:
                for name in sorted(os.listdir(real_path)):
                    rc = os.path.join(real_path, name)
                    try:
                        is_dir = os.path.isdir(rc)
                        cst = os.stat(rc)
                    except (OSError, PermissionError):
                        continue
                    children[name] = {
                        "type": "dir" if is_dir else "file",
                        "perms": "rwxr-xr-x" if is_dir else "rw-r--r--",
                        "owner": "windows",
                        "group": "windows",
                        "mtime": cst.st_mtime,
                        "children": {} if is_dir else None,
                        "content": "" if is_dir else "",
                        "binary": False,
                        "_real": rc,
                        "_lazy": True,
                    }
            except (OSError, PermissionError):
                pass
            return {
                "type": "dir",
                "perms": "rwxr-xr-x",
                "owner": "windows",
                "group": "windows",
                "mtime": st.st_mtime,
                "children": children,
                "_real": real_path,
                "_mount_info": mount_info,
            }
        else:
            try:
                if st.st_size > MOUNT_MAX_FILE_SIZE:
                    data = b"<file too large to read in trainer>"
                else:
                    with open(real_path, "rb") as f:
                        data = f.read()
            except (OSError, PermissionError):
                return None
            try:
                content = data.decode("utf-8")
                binary = False
            except UnicodeDecodeError:
                content = base64.b64encode(data).decode("ascii")
                binary = True
            return {
                "type": "file",
                "perms": "rw-r--r--",
                "owner": "windows",
                "group": "windows",
                "mtime": st.st_mtime,
                "content": content,
                "binary": binary,
                "_real": real_path,
                "_mount_info": mount_info,
            }

    # ---------- path helpers ----------
    @staticmethod
    def split(path):
        path = path.replace("\\", "/")
        parts = [p for p in path.split("/") if p]
        return parts

    @staticmethod
    def normalize(cwd, path):
        if not path:
            return cwd
        if path.startswith("/"):
            parts = []
        else:
            parts = VFS.split(cwd)
        for p in VFS.split(path):
            if p == ".":
                continue
            elif p == "..":
                if parts:
                    parts.pop()
            elif p == "~":
                parts = ["home", USER]
            else:
                parts.append(p)
        return "/" + "/".join(parts)

    def resolve(self, cwd, path):
        """Return (node, absolute_path) or (None, abs_path) if missing."""
        abs_path = self.normalize(cwd, path)
        # Mount routing
        m = self.find_mount(abs_path)
        if m is not None:
            mp, info, real = m
            if not os.path.exists(real):
                return None, abs_path
            return self._real_to_node(real, info), abs_path
        # Pure virtual FS
        parts = self.split(abs_path)
        node = self.root
        for p in parts:
            if node["type"] != "dir":
                return None, abs_path
            if p not in node["children"]:
                return None, abs_path
            node = node["children"][p]
        return node, abs_path

    def list_children(self, abs_path):
        """Return a fresh dict {name: node} for the directory at abs_path.
        Use this in commands that recurse, so mount data stays live."""
        node, _ = self.resolve("/", abs_path)
        if node is None or node["type"] != "dir":
            return {}
        children = node.get("children", {}) or {}
        # For mount lazy entries, prefer re-resolving via abs path
        result = {}
        for name, child in children.items():
            if child and child.get("_lazy"):
                child_path = abs_path.rstrip("/") + "/" + name
                fresh, _ = self.resolve("/", child_path)
                result[name] = fresh if fresh is not None else child
            else:
                result[name] = child
        return result

    def parent_of(self, abs_path):
        parts = self.split(abs_path)
        if not parts:
            return None, ""
        parent_path = "/" + "/".join(parts[:-1])
        parent, _ = self.resolve("/", parent_path)
        return parent, parts[-1]

    def _check_mount_write(self, real_path, info, is_file=True):
        """Apply sandbox rules before any real-disk write."""
        if info.get("readonly"):
            return False, "read-only mount"
        if is_file:
            ext = os.path.splitext(real_path)[1].lower()
            if ext in MOUNT_BLOCKED_EXTS:
                return False, f"refused: extension {ext} is blocked in mounts"
        return True, ""

    def mkfile(self, cwd, path, content="", overwrite=True, binary=False):
        abs_path = self.normalize(cwd, path)
        # Mount route?
        m = self.find_mount(abs_path)
        if m is not None:
            mp, info, real = m
            ok_w, msg = self._check_mount_write(real, info, is_file=True)
            if not ok_w:
                return False, f"cannot write '{path}': {msg}"
            if binary:
                try:
                    data = base64.b64decode(content)
                except Exception:
                    data = b""
            else:
                data = content.encode("utf-8", errors="replace") if isinstance(content, str) else content
            if len(data) > MOUNT_MAX_FILE_SIZE:
                return False, f"cannot write '{path}': exceeds {MOUNT_MAX_FILE_SIZE} byte cap"
            try:
                os.makedirs(os.path.dirname(real), exist_ok=True)
                with open(real, "wb") as f:
                    f.write(data)
            except (OSError, PermissionError) as e:
                return False, f"cannot write '{path}': {e}"
            return True, ""
        # Pure virtual
        parent, name = self.parent_of(abs_path)
        if parent is None or parent["type"] != "dir":
            return False, f"cannot create '{path}': No such file or directory"
        if name in parent["children"]:
            existing = parent["children"][name]
            if existing["type"] == "dir":
                return False, f"cannot write '{path}': Is a directory"
            if not overwrite:
                return True, ""
            existing["content"] = content
            existing["binary"] = binary
            existing["mtime"] = NOW()
        else:
            parent["children"][name] = _node("file", content, binary=binary)
        return True, ""

    def mkdir(self, cwd, path, parents=False):
        abs_path = self.normalize(cwd, path)
        # Mount route?
        m = self.find_mount(abs_path)
        if m is not None:
            mp, info, real = m
            ok_w, msg = self._check_mount_write(real, info, is_file=False)
            if not ok_w:
                return False, f"cannot mkdir '{path}': {msg}"
            try:
                if parents:
                    os.makedirs(real, exist_ok=True)
                else:
                    os.mkdir(real)
            except FileExistsError:
                if not parents:
                    return False, f"cannot create directory '{path}': File exists"
            except (OSError, PermissionError) as e:
                return False, f"cannot create directory '{path}': {e}"
            return True, ""
        parts = self.split(abs_path)
        node = self.root
        for i, p in enumerate(parts):
            if node["type"] != "dir":
                return False, f"cannot create directory '{path}': Not a directory"
            if p not in node["children"]:
                if parents or i == len(parts) - 1:
                    node["children"][p] = _node("dir")
                else:
                    return False, f"cannot create directory '{path}': No such file or directory"
            elif i == len(parts) - 1 and not parents:
                return False, f"cannot create directory '{path}': File exists"
            node = node["children"][p]
        return True, ""

    def remove(self, cwd, path, recursive=False):
        abs_path = self.normalize(cwd, path)
        if abs_path == "/":
            return False, "refusing to remove '/'"
        # Refuse to remove a mount point itself
        if abs_path in self.mounts:
            return False, f"cannot remove '{path}': is a mount point (use umount)"
        # Mount route?
        m = self.find_mount(abs_path)
        if m is not None:
            mp, info, real = m
            if info.get("readonly"):
                return False, f"cannot remove '{path}': read-only mount"
            if not os.path.exists(real):
                return False, f"cannot remove '{path}': No such file or directory"
            try:
                if os.path.isdir(real):
                    if not recursive:
                        if os.listdir(real):
                            return False, f"cannot remove '{path}': Directory not empty"
                        os.rmdir(real)
                    else:
                        import shutil
                        shutil.rmtree(real)
                else:
                    os.remove(real)
            except (OSError, PermissionError) as e:
                return False, f"cannot remove '{path}': {e}"
            return True, ""
        # Pure virtual
        parent, name = self.parent_of(abs_path)
        if parent is None or name not in parent["children"]:
            return False, f"cannot remove '{path}': No such file or directory"
        node = parent["children"][name]
        if node["type"] == "dir":
            if not recursive:
                return False, f"cannot remove '{path}': Is a directory"
            if node["children"] and not recursive:
                return False, f"cannot remove '{path}': Directory not empty"
        del parent["children"][name]
        return True, ""


# ---------------------------------------------------------------------------
# Shell state
# ---------------------------------------------------------------------------
class Shell:
    def __init__(self):
        self.vfs = VFS()
        self.cwd = f"/home/{USER}"
        self.prev_cwd = self.cwd
        self.env = {
            "USER": USER,
            "HOME": f"/home/{USER}",
            "SHELL": "/bin/bash",
            "PATH": "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
            "PWD": self.cwd,
            "LANG": "en_US.UTF-8",
            "TERM": "xterm-256color",
            "HOSTNAME": HOST,
            "PS1": "\\u@\\h:\\w$ ",
            "?": "0",
        }
        if ENV_FILE.exists():
            try:
                self.env.update(json.loads(ENV_FILE.read_text()))
            except Exception:
                pass
        self.aliases = {"ll": "ls -la", "la": "ls -A", "l": "ls -CF", "..": "cd ..", "...": "cd ../.."}
        self.functions = {}  # name -> list of body statements
        self.history = []
        if HIST_FILE.exists():
            self.history = HIST_FILE.read_text(errors="ignore").splitlines()
        self.running = True
        self.last_status = 0

    def save_state(self):
        self.vfs.save()
        try:
            HIST_FILE.write_text("\n".join(self.history[-1000:]))
            ENV_FILE.write_text(json.dumps(self.env))
        except Exception:
            pass

    def prompt(self):
        cwd = self.cwd
        home = self.env["HOME"]
        if cwd == home:
            disp = "~"
        elif cwd.startswith(home + "/"):
            disp = "~" + cwd[len(home):]
        else:
            disp = cwd
        return f"\033[1;32m{USER}@{HOST}\033[0m:\033[1;34m{disp}\033[0m$ "


# ---------------------------------------------------------------------------
# Command implementations
# Each command takes (shell, args, stdin) and returns (stdout, stderr, status)
# ---------------------------------------------------------------------------
COMMANDS = {}


def cmd(name, *aliases):
    def deco(fn):
        COMMANDS[name] = fn
        for a in aliases:
            COMMANDS[a] = fn
        fn._cmdname = name
        return fn
    return deco


def ok(out=""):
    return (out, "", 0)


def err(name, msg, status=1):
    return ("", f"{name}: {msg}\n", status)


# ---------- Filesystem ----------
@cmd("pwd")
def c_pwd(sh, args, stdin):
    return ok(sh.cwd + "\n")


@cmd("cd")
def c_cd(sh, args, stdin):
    target = args[0] if args else sh.env["HOME"]
    if target == "-":
        target = sh.prev_cwd
    node, abs_path = sh.vfs.resolve(sh.cwd, target)
    if node is None:
        return err("cd", f"{target}: No such file or directory")
    if node["type"] != "dir":
        return err("cd", f"{target}: Not a directory")
    sh.prev_cwd = sh.cwd
    sh.cwd = abs_path
    sh.env["PWD"] = abs_path
    return ok()


@cmd("ls", "dir")
def c_ls(sh, args, stdin):
    flags = set()
    paths = []
    for a in args:
        if a.startswith("-") and len(a) > 1:
            for ch in a[1:]:
                flags.add(ch)
        else:
            paths.append(a)
    if not paths:
        paths = [sh.cwd]
    show_hidden = "a" in flags or "A" in flags
    long_fmt = "l" in flags
    one_per = "1" in flags
    recursive = "R" in flags
    out_lines = []

    def list_dir(p):
        node, abs_path = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            return [f"ls: cannot access '{p}': No such file or directory"]
        if node["type"] != "dir":
            if long_fmt:
                return [_format_long(p, node)]
            return [p]
        kids = sh.vfs.list_children(abs_path)
        names = sorted(kids.keys())
        if not show_hidden:
            names = [n for n in names if not n.startswith(".")]
        if "A" not in flags and "a" in flags:
            names = [".", ".."] + names
        result = []
        if long_fmt:
            result.append(f"total {len(names)}")
            for n in names:
                child = kids.get(n) if n not in (".", "..") else node
                result.append(_format_long(n, child))
        elif one_per:
            for n in names:
                result.append(_color_name(n, kids.get(n)))
        else:
            result.append("  ".join(_color_name(n, kids.get(n)) for n in names))
        if recursive:
            for n in names:
                child = kids.get(n)
                if child and child["type"] == "dir":
                    sub = (abs_path.rstrip("/") + "/" + n)
                    result.append("")
                    result.append(f"{sub}:")
                    result.extend(list_dir(sub))
        return result

    def _color_name(name, node):
        if node and node["type"] == "dir":
            return f"\033[1;34m{name}\033[0m"
        return name

    def _format_long(name, node):
        if not node:
            return name
        t = "d" if node["type"] == "dir" else "-"
        perms = node.get("perms", "rwxr-xr-x")
        owner = node.get("owner", "root")
        group = node.get("group", "root")
        if node["type"] == "file":
            size = len(node_bytes(node))
        else:
            size = 4096
        mtime = datetime.fromtimestamp(node.get("mtime", NOW())).strftime("%b %d %H:%M")
        nm = _color_name(name, node)
        return f"{t}{perms} 1 {owner} {group} {size:>6} {mtime} {nm}"

    for i, p in enumerate(paths):
        if len(paths) > 1:
            out_lines.append(f"{p}:")
        out_lines.extend(list_dir(p))
        if i < len(paths) - 1:
            out_lines.append("")
    return ok("\n".join(out_lines) + "\n")


@cmd("mkdir")
def c_mkdir(sh, args, stdin):
    parents = False
    paths = []
    for a in args:
        if a == "-p":
            parents = True
        elif a.startswith("-"):
            pass
        else:
            paths.append(a)
    if not paths:
        return err("mkdir", "missing operand")
    out = ""
    for p in paths:
        success, msg = sh.vfs.mkdir(sh.cwd, p, parents=parents)
        if not success:
            out += f"mkdir: {msg}\n"
    return (out, "", 0 if not out else 1) if out else ok()


@cmd("rmdir")
def c_rmdir(sh, args, stdin):
    if not args:
        return err("rmdir", "missing operand")
    for p in args:
        node, _ = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            return err("rmdir", f"failed to remove '{p}': No such file or directory")
        if node["type"] != "dir":
            return err("rmdir", f"failed to remove '{p}': Not a directory")
        if node["children"]:
            return err("rmdir", f"failed to remove '{p}': Directory not empty")
        sh.vfs.remove(sh.cwd, p, recursive=True)
    return ok()


@cmd("rm", "del")
def c_rm(sh, args, stdin):
    recursive = False
    force = False
    paths = []
    for a in args:
        if a.startswith("-") and len(a) > 1:
            for ch in a[1:]:
                if ch in ("r", "R"):
                    recursive = True
                elif ch == "f":
                    force = True
        else:
            paths.append(a)
    if not paths and not force:
        return err("rm", "missing operand")
    out = ""
    for p in paths:
        success, msg = sh.vfs.remove(sh.cwd, p, recursive=recursive)
        if not success and not force:
            out += f"rm: {msg}\n"
    return (out, "", 1 if out else 0) if out else ok()


@cmd("touch")
def c_touch(sh, args, stdin):
    if not args:
        return err("touch", "missing file operand")
    for p in args:
        if p.startswith("-"):
            continue
        node, abs_path = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            success, msg = sh.vfs.mkfile(sh.cwd, p, "")
            if not success:
                return err("touch", msg)
        else:
            node["mtime"] = NOW()
    return ok()


@cmd("cat")
def c_cat(sh, args, stdin):
    if not args:
        return ok(stdin or "")
    out = ""
    number = False
    paths = []
    for a in args:
        if a == "-n":
            number = True
        elif a.startswith("-"):
            pass
        else:
            paths.append(a)
    for p in paths:
        node, _ = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            return err("cat", f"{p}: No such file or directory")
        if node["type"] == "dir":
            return err("cat", f"{p}: Is a directory")
        out += node_text(node)
    if number:
        lines = out.splitlines()
        out = "\n".join(f"{i+1:>6}\t{l}" for i, l in enumerate(lines)) + ("\n" if out.endswith("\n") else "")
    return ok(out)


@cmd("tac")
def c_tac(sh, args, stdin):
    text = ""
    if args:
        for p in args:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("tac", f"{p}: No such file or directory")
            text += node_text(node)
    else:
        text = stdin or ""
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return ok("\n".join(reversed(lines)) + "\n")


@cmd("head")
def c_head(sh, args, stdin):
    n = 10
    paths = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "-n" and i + 1 < len(args):
            n = int(args[i+1]); i += 2; continue
        if a.startswith("-") and a[1:].isdigit():
            n = int(a[1:]); i += 1; continue
        paths.append(a); i += 1
    if not paths:
        text = stdin or ""
    else:
        text = ""
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("head", f"{p}: No such file or directory")
            text += node_text(node)
    lines = text.splitlines()
    return ok("\n".join(lines[:n]) + "\n")


@cmd("tail")
def c_tail(sh, args, stdin):
    n = 10
    paths = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "-n" and i + 1 < len(args):
            n = int(args[i+1]); i += 2; continue
        if a.startswith("-") and a[1:].isdigit():
            n = int(a[1:]); i += 1; continue
        paths.append(a); i += 1
    if not paths:
        text = stdin or ""
    else:
        text = ""
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("tail", f"{p}: No such file or directory")
            text += node_text(node)
    lines = text.splitlines()
    return ok("\n".join(lines[-n:]) + "\n")


@cmd("cp", "copy")
def c_cp(sh, args, stdin):
    recursive = False
    files = []
    for a in args:
        if a in ("-r", "-R", "-rf", "-fr"):
            recursive = True
        elif a.startswith("-"):
            pass
        else:
            files.append(a)
    if len(files) < 2:
        return err("cp", "missing destination file operand")
    *srcs, dst = files
    dst_node, dst_abs = sh.vfs.resolve(sh.cwd, dst)
    dst_is_dir = dst_node is not None and dst_node["type"] == "dir"
    for s in srcs:
        sn, s_abs = sh.vfs.resolve(sh.cwd, s)
        if sn is None:
            return err("cp", f"cannot stat '{s}': No such file or directory")
        if sn["type"] == "dir" and not recursive:
            return err("cp", f"-r not specified; omitting directory '{s}'")
        target = dst_abs + "/" + os.path.basename(s_abs) if dst_is_dir else dst_abs
        _copy_node(sh, sn, target, s_abs)
    return ok()


def _copy_node(sh, src_node, dst_path, src_path=None):
    if src_node["type"] == "file":
        sh.vfs.mkfile("/", dst_path,
                      src_node.get("content", ""),
                      binary=src_node.get("binary", False))
    else:
        sh.vfs.mkdir("/", dst_path, parents=True)
        if src_path:
            kids = sh.vfs.list_children(src_path)
        else:
            kids = src_node.get("children", {}) or {}
        for name, child in kids.items():
            if child is None:
                continue
            _copy_node(sh, child,
                       dst_path.rstrip("/") + "/" + name,
                       (src_path.rstrip("/") + "/" + name) if src_path else None)


@cmd("mv", "move")
def c_mv(sh, args, stdin):
    files = [a for a in args if not a.startswith("-")]
    if len(files) < 2:
        return err("mv", "missing destination file operand")
    *srcs, dst = files
    dst_node, dst_abs = sh.vfs.resolve(sh.cwd, dst)
    dst_is_dir = dst_node is not None and dst_node["type"] == "dir"
    for s in srcs:
        sn, s_abs = sh.vfs.resolve(sh.cwd, s)
        if sn is None:
            return err("mv", f"cannot stat '{s}': No such file or directory")
        target = dst_abs + "/" + os.path.basename(s_abs) if dst_is_dir else dst_abs
        _copy_node(sh, sn, target, s_abs)
        sh.vfs.remove("/", s_abs, recursive=True)
    return ok()


@cmd("ln")
def c_ln(sh, args, stdin):
    files = [a for a in args if not a.startswith("-")]
    if len(files) < 2:
        return err("ln", "missing operand")
    src, dst = files[0], files[1]
    sn, _ = sh.vfs.resolve(sh.cwd, src)
    if sn is None:
        return err("ln", f"failed to access '{src}': No such file or directory")
    if sn["type"] == "file":
        sh.vfs.mkfile(sh.cwd, dst, sn.get("content", ""), binary=sn.get("binary", False))
    return ok()


@cmd("find")
def c_find(sh, args, stdin):
    start = "."
    name_pat = None
    type_filter = None
    i = 0
    pos_args = []
    while i < len(args):
        a = args[i]
        if a == "-name" and i + 1 < len(args):
            name_pat = args[i+1]; i += 2; continue
        if a == "-type" and i + 1 < len(args):
            type_filter = args[i+1]; i += 2; continue
        pos_args.append(a); i += 1
    if pos_args:
        start = pos_args[0]
    node, abs_path = sh.vfs.resolve(sh.cwd, start)
    if node is None:
        return err("find", f"'{start}': No such file or directory")
    out = []

    def walk(n, p):
        match = True
        if name_pat and not fnmatch.fnmatch(os.path.basename(p) or "/", name_pat):
            match = False
        if type_filter == "f" and n["type"] != "file":
            match = False
        if type_filter == "d" and n["type"] != "dir":
            match = False
        if match:
            out.append(p)
        if n["type"] == "dir":
            for name, child in sorted(sh.vfs.list_children(p).items()):
                walk(child, p.rstrip("/") + "/" + name)

    walk(node, abs_path)
    return ok("\n".join(out) + "\n")


@cmd("tree")
def c_tree(sh, args, stdin):
    start = args[0] if args else "."
    node, abs_path = sh.vfs.resolve(sh.cwd, start)
    if node is None:
        return err("tree", f"{start}: No such file or directory")
    out = [abs_path]
    files = [0]; dirs = [0]

    def walk(n, p, prefix=""):
        if n["type"] != "dir":
            return
        kids = sh.vfs.list_children(p)
        names = sorted(kids.keys())
        for i, name in enumerate(names):
            child = kids[name]
            connector = "└── " if i == len(names) - 1 else "├── "
            out.append(prefix + connector + name)
            if child and child["type"] == "dir":
                dirs[0] += 1
                ext = "    " if i == len(names) - 1 else "│   "
                walk(child, p.rstrip("/") + "/" + name, prefix + ext)
            else:
                files[0] += 1

    walk(node, abs_path)
    out.append(f"\n{dirs[0]} directories, {files[0]} files")
    return ok("\n".join(out) + "\n")


@cmd("stat")
def c_stat(sh, args, stdin):
    if not args:
        return err("stat", "missing operand")
    out = ""
    for p in args:
        node, abs_path = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            return err("stat", f"cannot stat '{p}': No such file or directory")
        size = len(node.get("content", "")) if node["type"] == "file" else 4096
        mtime = datetime.fromtimestamp(node.get("mtime", NOW())).strftime("%Y-%m-%d %H:%M:%S")
        kind = "directory" if node["type"] == "dir" else "regular file"
        out += (f"  File: {abs_path}\n"
                f"  Size: {size}\tBlocks: 8\tIO Block: 4096   {kind}\n"
                f"Access: ({node.get('perms','rwxr-xr-x')})  Uid: ({node.get('owner','root')})   Gid: ({node.get('group','root')})\n"
                f"Modify: {mtime}\n")
    return ok(out)


@cmd("file")
def c_file(sh, args, stdin):
    out = ""
    for p in args:
        node, _ = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            out += f"{p}: cannot open (No such file or directory)\n"
        elif node["type"] == "dir":
            out += f"{p}: directory\n"
        else:
            if node.get("binary"):
                out += f"{p}: data\n"
            else:
                content = node.get("content", "")
                if not content:
                    out += f"{p}: empty\n"
                elif all(c.isprintable() or c in "\n\r\t" for c in content[:200]):
                    out += f"{p}: ASCII text\n"
                else:
                    out += f"{p}: data\n"
    return ok(out)


@cmd("du")
def c_du(sh, args, stdin):
    paths = [a for a in args if not a.startswith("-")] or ["."]
    out = ""

    def size_of(n, p):
        if n["type"] == "file":
            return len(node_bytes(n))
        total = 0
        for name, c in sh.vfs.list_children(p).items():
            if c is None:
                continue
            total += size_of(c, p.rstrip("/") + "/" + name)
        return total

    for p in paths:
        node, abs_path = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            return err("du", f"cannot access '{p}': No such file or directory")
        out += f"{size_of(node, abs_path)}\t{abs_path}\n"
    return ok(out)


@cmd("df")
def c_df(sh, args, stdin):
    out = ("Filesystem     1K-blocks      Used Available Use% Mounted on\n"
           "/dev/vda1       20480000   5120000  15360000  25% /\n"
           "tmpfs            1024000         0   1024000   0% /tmp\n"
           "tmpfs             204800        12    204788   1% /run\n")
    return ok(out)


@cmd("chmod")
def c_chmod(sh, args, stdin):
    if len(args) < 2:
        return err("chmod", "missing operand")
    mode, *paths = args
    for p in paths:
        node, _ = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            return err("chmod", f"cannot access '{p}': No such file or directory")
        if mode.isdigit() and len(mode) == 3:
            m = ""
            for d in mode:
                d = int(d)
                m += ("r" if d & 4 else "-")
                m += ("w" if d & 2 else "-")
                m += ("x" if d & 1 else "-")
            node["perms"] = m
        else:
            node["perms"] = mode
    return ok()


@cmd("chown")
def c_chown(sh, args, stdin):
    if len(args) < 2:
        return err("chown", "missing operand")
    spec, *paths = args
    if ":" in spec:
        owner, group = spec.split(":", 1)
    else:
        owner, group = spec, None
    for p in paths:
        node, _ = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            return err("chown", f"cannot access '{p}': No such file or directory")
        node["owner"] = owner
        if group:
            node["group"] = group
    return ok()


# ---------- Text processing ----------
@cmd("echo")
def c_echo(sh, args, stdin):
    no_newline = False
    interpret = False
    real_args = []
    for a in args:
        if a == "-n":
            no_newline = True
        elif a == "-e":
            interpret = True
        else:
            real_args.append(a)
    text = " ".join(real_args)
    if interpret:
        text = text.encode().decode("unicode_escape")
    return ok(text + ("" if no_newline else "\n"))


@cmd("printf")
def c_printf(sh, args, stdin):
    if not args:
        return err("printf", "missing operand")
    fmt = args[0].encode().decode("unicode_escape")
    rest = args[1:]
    try:
        out = fmt % tuple(rest) if "%" in fmt else fmt
    except Exception:
        out = fmt
    return ok(out)


@cmd("grep", "egrep", "fgrep")
def c_grep(sh, args, stdin):
    flags = {"i": False, "v": False, "n": False, "c": False, "r": False, "l": False}
    pattern = None
    paths = []
    i = 0
    while i < len(args):
        a = args[i]
        if a.startswith("-") and len(a) > 1 and not a[1:].isdigit():
            for ch in a[1:]:
                if ch in flags:
                    flags[ch] = True
            i += 1; continue
        if pattern is None:
            pattern = a
        else:
            paths.append(a)
        i += 1
    if pattern is None:
        return err("grep", "no pattern")
    try:
        flagsi = re.IGNORECASE if flags["i"] else 0
        rx = re.compile(pattern, flagsi)
    except re.error as e:
        return err("grep", str(e))

    def grep_text(text, label=None):
        results = []
        count = 0
        for ln, line in enumerate(text.splitlines(), 1):
            m = rx.search(line)
            if (m and not flags["v"]) or (not m and flags["v"]):
                count += 1
                if flags["l"]:
                    if label: return [label]
                    return ["(stdin)"]
                prefix = ""
                if label and len(paths) > 1:
                    prefix = f"{label}:"
                if flags["n"]:
                    prefix += f"{ln}:"
                results.append(prefix + line)
        if flags["c"]:
            return [f"{label+':' if label and len(paths)>1 else ''}{count}"]
        return results

    out = []
    if not paths:
        out.extend(grep_text(stdin or ""))
    else:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                out.append(f"grep: {p}: No such file or directory")
                continue
            if node["type"] == "dir":
                if flags["r"]:
                    def walk(n, base, abs_p):
                        if n["type"] == "file":
                            out.extend(grep_text(node_text(n), base))
                        else:
                            for nm, ch in sh.vfs.list_children(abs_p).items():
                                if ch is None:
                                    continue
                                walk(ch, base + "/" + nm, abs_p.rstrip("/") + "/" + nm)
                    _, abs_p = sh.vfs.resolve(sh.cwd, p)
                    walk(node, p, abs_p)
                else:
                    out.append(f"grep: {p}: Is a directory")
                continue
            out.extend(grep_text(node_text(node), p))
    text = "\n".join(out)
    if text and not text.endswith("\n"):
        text += "\n"
    return (text, "", 0 if out else 1)


@cmd("sed")
def c_sed(sh, args, stdin):
    if not args:
        return err("sed", "missing script")
    script = args[0]
    paths = args[1:]
    text = ""
    if paths:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("sed", f"can't read {p}: No such file or directory")
            text += node_text(node)
    else:
        text = stdin or ""
    # Support s/old/new/[g] only
    m = re.match(r"^s(.)(.*?)\1(.*?)\1([gi]*)$", script)
    if not m:
        return err("sed", f"unsupported script: {script}")
    _, old, new, mods = m.groups()
    flags_re = re.IGNORECASE if "i" in mods else 0
    count = 0 if "g" in mods else 1
    out_lines = []
    for line in text.splitlines():
        out_lines.append(re.sub(old, new, line, count=count, flags=flags_re))
    return ok("\n".join(out_lines) + ("\n" if text.endswith("\n") else ""))


@cmd("awk")
def c_awk(sh, args, stdin):
    """Minimal awk: supports '{print $N}' and '{print}' patterns."""
    if not args:
        return err("awk", "missing program")
    prog = args[0]
    paths = args[1:]
    text = ""
    if paths:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("awk", f"can't open {p}")
            text += node_text(node)
    else:
        text = stdin or ""
    sep = None
    m = re.match(r"^\{print\s*(.*)\}$", prog.strip())
    if not m:
        return err("awk", f"unsupported program: {prog}")
    expr = m.group(1).strip()
    out = []
    for line in text.splitlines():
        fields = line.split(sep)
        if not expr:
            out.append(line)
        else:
            parts = [p.strip() for p in expr.split(",")]
            vals = []
            for part in parts:
                if part == "$0":
                    vals.append(line)
                elif part.startswith("$"):
                    try:
                        idx = int(part[1:])
                        vals.append(fields[idx-1] if 0 < idx <= len(fields) else "")
                    except ValueError:
                        vals.append(part)
                else:
                    vals.append(part.strip('"'))
            out.append(" ".join(vals))
    return ok("\n".join(out) + "\n")


@cmd("wc")
def c_wc(sh, args, stdin):
    flags = set()
    paths = []
    for a in args:
        if a.startswith("-"):
            for ch in a[1:]:
                flags.add(ch)
        else:
            paths.append(a)
    show_l = "l" in flags
    show_w = "w" in flags
    show_c = "c" in flags
    if not (show_l or show_w or show_c):
        show_l = show_w = show_c = True

    def stats(t):
        return (len(t.splitlines()), len(t.split()), len(t))

    out = ""
    total = [0, 0, 0]
    if not paths:
        l, w, c = stats(stdin or "")
        parts = []
        if show_l: parts.append(f"{l:>7}")
        if show_w: parts.append(f"{w:>7}")
        if show_c: parts.append(f"{c:>7}")
        out = " ".join(parts) + "\n"
    else:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                out += f"wc: {p}: No such file or directory\n"
                continue
            if node["type"] == "dir":
                out += f"wc: {p}: Is a directory\n"
                continue
            l, w, c = stats(node_text(node))
            total[0] += l; total[1] += w; total[2] += c
            parts = []
            if show_l: parts.append(f"{l:>7}")
            if show_w: parts.append(f"{w:>7}")
            if show_c: parts.append(f"{c:>7}")
            out += " ".join(parts) + f" {p}\n"
        if len(paths) > 1:
            parts = []
            if show_l: parts.append(f"{total[0]:>7}")
            if show_w: parts.append(f"{total[1]:>7}")
            if show_c: parts.append(f"{total[2]:>7}")
            out += " ".join(parts) + " total\n"
    return ok(out)


@cmd("sort")
def c_sort(sh, args, stdin):
    reverse = False
    numeric = False
    unique = False
    paths = []
    for a in args:
        if a == "-r": reverse = True
        elif a == "-n": numeric = True
        elif a == "-u": unique = True
        elif a.startswith("-"): pass
        else: paths.append(a)
    text = ""
    if paths:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("sort", f"cannot read: {p}")
            text += node_text(node)
    else:
        text = stdin or ""
    lines = text.splitlines()
    key = (lambda s: float(re.match(r"\s*(-?\d+\.?\d*)", s).group(1)) if re.match(r"\s*-?\d", s) else 0) if numeric else None
    try:
        lines.sort(key=key, reverse=reverse)
    except Exception:
        lines.sort(reverse=reverse)
    if unique:
        seen = set()
        new = []
        for l in lines:
            if l not in seen:
                seen.add(l); new.append(l)
        lines = new
    return ok("\n".join(lines) + "\n")


@cmd("uniq")
def c_uniq(sh, args, stdin):
    count = "-c" in args
    paths = [a for a in args if not a.startswith("-")]
    text = ""
    if paths:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("uniq", f"cannot read: {p}")
            text += node_text(node)
    else:
        text = stdin or ""
    out = []
    prev = None
    cnt = 0
    for line in text.splitlines():
        if line == prev:
            cnt += 1
        else:
            if prev is not None:
                out.append(f"{cnt:>7} {prev}" if count else prev)
            prev = line
            cnt = 1
    if prev is not None:
        out.append(f"{cnt:>7} {prev}" if count else prev)
    return ok("\n".join(out) + "\n")


@cmd("cut")
def c_cut(sh, args, stdin):
    delim = "\t"
    fields = None
    chars = None
    paths = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "-d" and i + 1 < len(args):
            delim = args[i+1]; i += 2; continue
        if a.startswith("-d"):
            delim = a[2:]; i += 1; continue
        if a == "-f" and i + 1 < len(args):
            fields = args[i+1]; i += 2; continue
        if a.startswith("-f"):
            fields = a[2:]; i += 1; continue
        if a == "-c" and i + 1 < len(args):
            chars = args[i+1]; i += 2; continue
        if a.startswith("-c"):
            chars = a[2:]; i += 1; continue
        paths.append(a); i += 1
    text = ""
    if paths:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("cut", f"{p}: No such file or directory")
            text += node_text(node)
    else:
        text = stdin or ""

    def parse_range(spec, max_n):
        result = set()
        for part in spec.split(","):
            if "-" in part:
                a, b = part.split("-", 1)
                a = int(a) if a else 1
                b = int(b) if b else max_n
                result.update(range(a, b + 1))
            else:
                result.add(int(part))
        return sorted(result)

    out = []
    for line in text.splitlines():
        if fields is not None:
            parts = line.split(delim)
            idxs = parse_range(fields, len(parts))
            out.append(delim.join(parts[i-1] for i in idxs if 0 < i <= len(parts)))
        elif chars is not None:
            idxs = parse_range(chars, len(line))
            out.append("".join(line[i-1] for i in idxs if 0 < i <= len(line)))
        else:
            out.append(line)
    return ok("\n".join(out) + "\n")


@cmd("tr")
def c_tr(sh, args, stdin):
    if len(args) < 1:
        return err("tr", "missing operand")
    delete = "-d" in args
    args2 = [a for a in args if a != "-d"]
    text = stdin or ""
    if delete:
        chars = args2[0] if args2 else ""
        return ok("".join(c for c in text if c not in chars))
    if len(args2) < 2:
        return err("tr", "missing operand")
    src, dst = args2[0], args2[1]
    table = str.maketrans(src, dst[:len(src)].ljust(len(src), dst[-1] if dst else " "))
    return ok(text.translate(table))


@cmd("tee")
def c_tee(sh, args, stdin):
    append = "-a" in args
    paths = [a for a in args if not a.startswith("-")]
    text = stdin or ""
    for p in paths:
        if append:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            existing = node_text(node) if node and node["type"] == "file" else ""
            sh.vfs.mkfile(sh.cwd, p, existing + text)
        else:
            sh.vfs.mkfile(sh.cwd, p, text)
    return ok(text)


@cmd("rev")
def c_rev(sh, args, stdin):
    text = ""
    if args:
        for p in args:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("rev", f"{p}: No such file or directory")
            text += node_text(node)
    else:
        text = stdin or ""
    return ok("\n".join(line[::-1] for line in text.splitlines()) + "\n")


@cmd("nl")
def c_nl(sh, args, stdin):
    text = ""
    if args:
        for p in args:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("nl", f"{p}: No such file or directory")
            text += node_text(node)
    else:
        text = stdin or ""
    out = []
    n = 1
    for line in text.splitlines():
        if line.strip():
            out.append(f"{n:>6}\t{line}")
            n += 1
        else:
            out.append("\t" + line)
    return ok("\n".join(out) + "\n")


@cmd("basename")
def c_basename(sh, args, stdin):
    if not args:
        return err("basename", "missing operand")
    p = args[0]
    suffix = args[1] if len(args) > 1 else ""
    name = p.rstrip("/").split("/")[-1]
    if suffix and name.endswith(suffix):
        name = name[:-len(suffix)]
    return ok(name + "\n")


@cmd("dirname")
def c_dirname(sh, args, stdin):
    if not args:
        return err("dirname", "missing operand")
    p = args[0].rstrip("/")
    if "/" not in p:
        return ok(".\n")
    return ok(p.rsplit("/", 1)[0] + "\n" if p.rsplit("/", 1)[0] else "/\n")


@cmd("diff")
def c_diff(sh, args, stdin):
    if len(args) < 2:
        return err("diff", "missing operand")
    a, b = args[0], args[1]
    na, _ = sh.vfs.resolve(sh.cwd, a)
    nb, _ = sh.vfs.resolve(sh.cwd, b)
    if na is None: return err("diff", f"{a}: No such file or directory")
    if nb is None: return err("diff", f"{b}: No such file or directory")
    la = node_text(na).splitlines()
    lb = node_text(nb).splitlines()
    import difflib
    diff = list(difflib.unified_diff(la, lb, lineterm="", fromfile=a, tofile=b))
    return ok("\n".join(diff) + ("\n" if diff else ""))


@cmd("seq")
def c_seq(sh, args, stdin):
    if not args:
        return err("seq", "missing operand")
    nums = [int(a) for a in args]
    if len(nums) == 1:
        rng = range(1, nums[0] + 1)
    elif len(nums) == 2:
        rng = range(nums[0], nums[1] + 1)
    else:
        rng = range(nums[0], nums[2] + 1, nums[1])
    return ok("\n".join(str(i) for i in rng) + "\n")


@cmd("yes")
def c_yes(sh, args, stdin):
    text = " ".join(args) if args else "y"
    return ok((text + "\n") * 10)  # cap to 10 to avoid runaway


@cmd("true")
def c_true(sh, args, stdin):
    return ok()


@cmd("false")
def c_false(sh, args, stdin):
    return ("", "", 1)


# ---------- System info ----------
@cmd("whoami")
def c_whoami(sh, args, stdin):
    return ok(USER + "\n")


@cmd("id")
def c_id(sh, args, stdin):
    return ok(f"uid=1000({USER}) gid=1000({USER}) groups=1000({USER}),27(sudo)\n")


@cmd("hostname")
def c_hostname(sh, args, stdin):
    return ok(HOST + "\n")


@cmd("uname")
def c_uname(sh, args, stdin):
    if "-a" in args:
        return ok(f"Linux {HOST} 5.15.0-trainer #1 SMP x86_64 GNU/Linux\n")
    if "-r" in args: return ok("5.15.0-trainer\n")
    if "-m" in args: return ok("x86_64\n")
    if "-n" in args: return ok(HOST + "\n")
    return ok("Linux\n")


@cmd("date")
def c_date(sh, args, stdin):
    return ok(datetime.now().strftime("%a %b %d %H:%M:%S %Z %Y") + "\n")


@cmd("cal")
def c_cal(sh, args, stdin):
    import calendar
    now = datetime.now()
    return ok(calendar.month(now.year, now.month) + "\n")


@cmd("uptime")
def c_uptime(sh, args, stdin):
    return ok(f" {datetime.now().strftime('%H:%M:%S')} up 1 day,  3:42,  1 user,  load average: 0.15, 0.10, 0.09\n")


@cmd("ps")
def c_ps(sh, args, stdin):
    out = ("  PID TTY          TIME CMD\n"
           " 1234 pts/0    00:00:00 bash\n"
           " 5678 pts/0    00:00:00 ps\n")
    return ok(out)


@cmd("top")
def c_top(sh, args, stdin):
    out = ("top - " + datetime.now().strftime("%H:%M:%S") + " up 1 day, 1 user, load average: 0.10, 0.08, 0.05\n"
           "Tasks:   2 total,   1 running,   1 sleeping\n"
           "%Cpu(s):  1.0 us,  0.5 sy, 98.5 id\n"
           "MiB Mem :   8192.0 total,   4096.0 free,   2048.0 used\n\n"
           "  PID USER      PR  NI    VIRT    RES    SHR S  %CPU  %MEM   TIME+ COMMAND\n"
           " 1234 user      20   0   12345   2345    789 S   0.3   0.0   0:00.10 bash\n")
    return ok(out)


@cmd("free")
def c_free(sh, args, stdin):
    out = ("              total        used        free      shared  buff/cache   available\n"
           "Mem:        8192000     2048000     4096000      102400     2048000     5836800\n"
           "Swap:       2048000           0     2048000\n")
    return ok(out)


@cmd("kill")
def c_kill(sh, args, stdin):
    return ok()


@cmd("killall")
def c_killall(sh, args, stdin):
    return ok()


@cmd("env", "printenv")
def c_env(sh, args, stdin):
    if args:
        out = ""
        for a in args:
            if a in sh.env:
                out += sh.env[a] + "\n"
        return ok(out)
    return ok("\n".join(f"{k}={v}" for k, v in sh.env.items() if k != "?") + "\n")


@cmd("export")
def c_export(sh, args, stdin):
    if not args:
        return c_env(sh, [], stdin)
    for a in args:
        if "=" in a:
            k, v = a.split("=", 1)
            sh.env[k] = v
        else:
            if a not in sh.env:
                sh.env[a] = ""
    return ok()


@cmd("unset")
def c_unset(sh, args, stdin):
    for a in args:
        sh.env.pop(a, None)
    return ok()


@cmd("set")
def c_set(sh, args, stdin):
    return ok("\n".join(f"{k}={v}" for k, v in sorted(sh.env.items())) + "\n")


@cmd("alias")
def c_alias(sh, args, stdin):
    if not args:
        return ok("\n".join(f"alias {k}='{v}'" for k, v in sh.aliases.items()) + "\n")
    for a in args:
        if "=" in a:
            k, v = a.split("=", 1)
            sh.aliases[k] = v.strip("'\"")
    return ok()


@cmd("unalias")
def c_unalias(sh, args, stdin):
    for a in args:
        sh.aliases.pop(a, None)
    return ok()


@cmd("history")
def c_history(sh, args, stdin):
    out = "\n".join(f"{i+1:>5}  {h}" for i, h in enumerate(sh.history))
    return ok(out + "\n")


@cmd("which")
def c_which(sh, args, stdin):
    out = ""
    for a in args:
        if a in COMMANDS or a in sh.aliases:
            out += f"/usr/bin/{a}\n"
        else:
            return ("", f"which: no {a}\n", 1)
    return ok(out)


@cmd("whereis")
def c_whereis(sh, args, stdin):
    out = ""
    for a in args:
        if a in COMMANDS:
            out += f"{a}: /usr/bin/{a} /usr/share/man/man1/{a}.1.gz\n"
        else:
            out += f"{a}:\n"
    return ok(out)


@cmd("type")
def c_type(sh, args, stdin):
    out = ""
    for a in args:
        if a in sh.aliases:
            out += f"{a} is aliased to '{sh.aliases[a]}'\n"
        elif a in COMMANDS:
            out += f"{a} is a shell builtin\n"
        else:
            out += f"{a}: not found\n"
    return ok(out)


@cmd("clear", "cls")
def c_clear(sh, args, stdin):
    os.system("cls" if os.name == "nt" else "clear")
    return ok()


@cmd("exit", "logout", "quit")
def c_exit(sh, args, stdin):
    sh.running = False
    return ok()


@cmd("sudo")
def c_sudo(sh, args, stdin):
    if not args:
        return err("sudo", "usage: sudo command")
    return execute_command(sh, args, stdin)


@cmd("man")
def c_man(sh, args, stdin):
    if not args:
        return err("man", "what manual page do you want?")
    name = args[0]
    if name not in COMMANDS:
        return err("man", f"no manual entry for {name}")
    doc = MANPAGES.get(name, f"NAME\n    {name} - (training stub)\n\nDESCRIPTION\n    See 'help' for the full command list.\n")
    return ok(doc + "\n")


@cmd("help")
def c_help(sh, args, stdin):
    names = sorted(set(COMMANDS.keys()))
    out = "Available commands (" + str(len(names)) + "):\n\n"
    for i, n in enumerate(names):
        out += f"{n:<14}"
        if (i + 1) % 6 == 0:
            out += "\n"
    out += "\n\n"
    out += ("Shell features:\n"
            "  Pipes:        cmd1 | cmd2\n"
            "  Redirect:     cmd > file, cmd >> file, cmd < file\n"
            "  Chains:       cmd1 && cmd2, cmd1 || cmd2, cmd1 ; cmd2\n"
            "  Variables:    export VAR=value ; echo $VAR\n"
            "  Globbing:     ls *.txt\n"
            "  History:      history\n"
            "  Reset FS:     reset-fs (custom command)\n")
    return ok(out)


@cmd("reset-fs")
def c_reset(sh, args, stdin):
    sh.vfs.reset()
    sh.cwd = f"/home/{USER}"
    return ok("filesystem reset to defaults\n")


# ---------- Math / Utilities ----------
@cmd("expr")
def c_expr(sh, args, stdin):
    expr = " ".join(args)
    try:
        # SAFE evaluator: digits and operators only
        if not re.match(r"^[\d\s+\-*/%().]+$", expr):
            return err("expr", "syntax error")
        return ok(str(eval(expr)) + "\n")
    except Exception as e:
        return err("expr", str(e))


@cmd("bc")
def c_bc(sh, args, stdin):
    text = stdin or ""
    out = []
    for line in text.splitlines():
        try:
            if not re.match(r"^[\d\s+\-*/%().]+$", line):
                continue
            out.append(str(eval(line)))
        except Exception:
            pass
    return ok("\n".join(out) + ("\n" if out else ""))


@cmd("test", "[")
def c_test(sh, args, stdin):
    if args and args[-1] == "]":
        args = args[:-1]
    if not args:
        return ("", "", 1)
    if len(args) == 2:
        op, val = args
        if op == "-z": return ("", "", 0 if val == "" else 1)
        if op == "-n": return ("", "", 0 if val != "" else 1)
        if op == "-e":
            n, _ = sh.vfs.resolve(sh.cwd, val); return ("", "", 0 if n else 1)
        if op == "-f":
            n, _ = sh.vfs.resolve(sh.cwd, val); return ("", "", 0 if n and n["type"] == "file" else 1)
        if op == "-d":
            n, _ = sh.vfs.resolve(sh.cwd, val); return ("", "", 0 if n and n["type"] == "dir" else 1)
    if len(args) == 3:
        a, op, b = args
        if op == "=": return ("", "", 0 if a == b else 1)
        if op == "!=": return ("", "", 0 if a != b else 1)
        try:
            ai, bi = int(a), int(b)
            if op == "-eq": return ("", "", 0 if ai == bi else 1)
            if op == "-ne": return ("", "", 0 if ai != bi else 1)
            if op == "-lt": return ("", "", 0 if ai < bi else 1)
            if op == "-le": return ("", "", 0 if ai <= bi else 1)
            if op == "-gt": return ("", "", 0 if ai > bi else 1)
            if op == "-ge": return ("", "", 0 if ai >= bi else 1)
        except ValueError:
            pass
    return ("", "", 1)


@cmd("sleep")
def c_sleep(sh, args, stdin):
    if args:
        try:
            time.sleep(min(float(args[0]), 10))
        except Exception:
            pass
    return ok()


@cmd("md5sum")
def c_md5sum(sh, args, stdin):
    out = ""
    if args:
        for p in args:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("md5sum", f"{p}: No such file or directory")
            out += hashlib.md5(node_bytes(node)).hexdigest() + f"  {p}\n"
    else:
        out = hashlib.md5((stdin or "").encode()).hexdigest() + "  -\n"
    return ok(out)


@cmd("sha1sum")
def c_sha1sum(sh, args, stdin):
    out = ""
    if args:
        for p in args:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("sha1sum", f"{p}: No such file or directory")
            out += hashlib.sha1(node_bytes(node)).hexdigest() + f"  {p}\n"
    else:
        out = hashlib.sha1((stdin or "").encode()).hexdigest() + "  -\n"
    return ok(out)


@cmd("sha256sum")
def c_sha256sum(sh, args, stdin):
    out = ""
    if args:
        for p in args:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("sha256sum", f"{p}: No such file or directory")
            out += hashlib.sha256(node_bytes(node)).hexdigest() + f"  {p}\n"
    else:
        out = hashlib.sha256((stdin or "").encode()).hexdigest() + "  -\n"
    return ok(out)


@cmd("base64")
def c_base64(sh, args, stdin):
    decode = "-d" in args
    paths = [a for a in args if not a.startswith("-")]
    data = b""
    if paths:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("base64", f"{p}: No such file or directory")
            data += node_bytes(node)
    else:
        data = (stdin or "").encode("utf-8", errors="replace")
    try:
        if decode:
            return ok(base64.b64decode(data).decode(errors="replace"))
        return ok(base64.b64encode(data).decode() + "\n")
    except Exception as e:
        return err("base64", str(e))


# ---------- Network (mocked) ----------
@cmd("ping")
def c_ping(sh, args, stdin):
    if not args:
        return err("ping", "usage: ping host")
    host = args[-1]
    out = f"PING {host} (127.0.0.1) 56(84) bytes of data.\n"
    for i in range(4):
        out += f"64 bytes from {host}: icmp_seq={i+1} ttl=64 time=0.0{random.randint(1,9)}{random.randint(0,9)} ms\n"
    out += f"\n--- {host} ping statistics ---\n4 packets transmitted, 4 received, 0% packet loss, time 3050ms\n"
    return ok(out)


@cmd("curl")
def c_curl(sh, args, stdin):
    if not args:
        return err("curl", "no URL specified")
    output_path = None
    use_remote_name = False
    show_headers = False
    silent = False
    method = "GET"
    headers = {}
    url = None
    i = 0
    while i < len(args):
        a = args[i]
        if a == "-o" and i + 1 < len(args):
            output_path = args[i+1]; i += 2; continue
        if a == "-O":
            use_remote_name = True; i += 1; continue
        if a in ("-I", "--head"):
            show_headers = True; method = "HEAD"; i += 1; continue
        if a in ("-s", "--silent"):
            silent = True; i += 1; continue
        if a == "-X" and i + 1 < len(args):
            method = args[i+1]; i += 2; continue
        if a == "-H" and i + 1 < len(args):
            h = args[i+1]
            if ":" in h:
                k, v = h.split(":", 1)
                headers[k.strip()] = v.strip()
            i += 2; continue
        if a.startswith("-"):
            i += 1; continue
        url = a; i += 1
    if url is None:
        return err("curl", "no URL specified")
    if not re.match(r"^https?://", url):
        url = "http://" + url
    try:
        ctx = ssl.create_default_context()
        try:
            ctx.check_hostname = False
            ctx.verify_mode = ssl.CERT_NONE
        except Exception:
            pass
        req = urllib.request.Request(url, method=method, headers=headers or {})
        with urllib.request.urlopen(req, timeout=15, context=ctx) as resp:
            hdr_text = ""
            if show_headers:
                hdr_text = f"HTTP/1.1 {resp.status} {resp.reason}\n"
                for k, v in resp.headers.items():
                    hdr_text += f"{k}: {v}\n"
                hdr_text += "\n"
            data = resp.read(MOUNT_MAX_FILE_SIZE) if not show_headers else b""
    except urllib.error.HTTPError as e:
        return ("", f"curl: HTTP {e.code} {e.reason}\n", 22)
    except (urllib.error.URLError, OSError, ValueError) as e:
        return ("", f"curl: ({type(e).__name__}) {e}\n", 6)
    if use_remote_name:
        output_path = url.rstrip("/").rsplit("/", 1)[-1] or "index.html"
    if output_path:
        try:
            text = data.decode("utf-8")
            sh.vfs.mkfile(sh.cwd, output_path, text, binary=False)
        except UnicodeDecodeError:
            sh.vfs.mkfile(sh.cwd, output_path,
                          base64.b64encode(data).decode("ascii"), binary=True)
        return ok("" if silent else f"[saved {output_path}, {len(data)} bytes]\n")
    if show_headers:
        return ok(hdr_text)
    try:
        return ok(data.decode("utf-8"))
    except UnicodeDecodeError:
        return ok(f"<binary response, {len(data)} bytes — use -o file>\n")


@cmd("wget")
def c_wget(sh, args, stdin):
    if not args:
        return err("wget", "no URL specified")
    quiet = "-q" in args
    output_path = None
    i = 0
    urls = []
    while i < len(args):
        a = args[i]
        if a == "-O" and i + 1 < len(args):
            output_path = args[i+1]; i += 2; continue
        if a.startswith("-"):
            i += 1; continue
        urls.append(a); i += 1
    if not urls:
        return err("wget", "no URL specified")
    url = urls[0]
    if not re.match(r"^https?://", url):
        url = "http://" + url
    target = output_path or (url.rstrip("/").rsplit("/", 1)[-1] or "index.html")
    try:
        ctx = ssl.create_default_context()
        try:
            ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
        except Exception:
            pass
        with urllib.request.urlopen(url, timeout=15, context=ctx) as resp:
            data = resp.read(MOUNT_MAX_FILE_SIZE)
    except urllib.error.HTTPError as e:
        return ("", f"wget: HTTP {e.code} {e.reason}\n", 8)
    except (urllib.error.URLError, OSError, ValueError) as e:
        return ("", f"wget: ({type(e).__name__}) {e}\n", 4)
    try:
        sh.vfs.mkfile(sh.cwd, target, data.decode("utf-8"), binary=False)
    except UnicodeDecodeError:
        sh.vfs.mkfile(sh.cwd, target,
                      base64.b64encode(data).decode("ascii"), binary=True)
    if quiet:
        return ok()
    return ok(f"--{datetime.now().strftime('%Y-%m-%d %H:%M:%S')}--  {url}\n"
              f"Saving to: '{target}'\n"
              f"'{target}' saved [{len(data)}]\n")


# ---------- Mounts ----------
@cmd("mount")
def c_mount(sh, args, stdin):
    if not args:
        if not sh.vfs.mounts:
            return ok("(no mounts)\n")
        out = ""
        for mp, info in sh.vfs.mounts.items():
            ro = " (ro)" if info.get("readonly") else ""
            out += f"{info['real_root']} on {mp} type winbridge{ro}\n"
        return ok(out)
    readonly = False
    pos = []
    for a in args:
        if a in ("-r", "--readonly", "-o" "ro"):
            readonly = True
        elif a.startswith("-"):
            pass
        else:
            pos.append(a)
    if len(pos) < 2:
        return err("mount", "usage: mount [-r] <real_windows_path> <virtual_path>")
    real, virt = pos[0], pos[1]
    success, msg = sh.vfs.add_mount(virt, real, readonly=readonly)
    if not success:
        return err("mount", msg)
    return ok(f"mounted {real} -> {virt}{' (read-only)' if readonly else ''}\n")


@cmd("umount", "unmount")
def c_umount(sh, args, stdin):
    if not args:
        return err("umount", "usage: umount <virtual_path>")
    success, msg = sh.vfs.remove_mount(args[0])
    if not success:
        return err("umount", msg)
    return ok(f"unmounted {args[0]}\n")


# ---------- Archive tools ----------
def _vfs_walk(sh, abs_path, base=""):
    """Yield (arc_name, node) pairs for files+dirs under abs_path."""
    node, _ = sh.vfs.resolve("/", abs_path)
    if node is None:
        return
    name = base or os.path.basename(abs_path) or ""
    yield (name or ".", node, abs_path)
    if node["type"] == "dir":
        for cname, child in sorted(sh.vfs.list_children(abs_path).items()):
            if child is None:
                continue
            sub_arc = (name + "/" + cname) if name else cname
            yield from _vfs_walk(sh, abs_path.rstrip("/") + "/" + cname, sub_arc)


@cmd("tar")
def c_tar(sh, args, stdin):
    if not args:
        return err("tar", "missing operands")
    create = extract = listing = False
    use_gzip = use_bzip = False
    archive = None
    paths = []
    flag_consumed = False
    i = 0
    while i < len(args):
        a = args[i]
        if not flag_consumed and a.startswith("-"):
            for ch in a.lstrip("-"):
                if ch == "c": create = True
                elif ch == "x": extract = True
                elif ch == "t": listing = True
                elif ch == "z": use_gzip = True
                elif ch == "j": use_bzip = True
                elif ch == "v": pass
                elif ch == "f":
                    if i + 1 < len(args):
                        archive = args[i+1]; i += 1
            flag_consumed = True
            i += 1; continue
        if not flag_consumed and len(a) >= 2 and a[0] in "cxt":
            for ch in a:
                if ch == "c": create = True
                elif ch == "x": extract = True
                elif ch == "t": listing = True
                elif ch == "z": use_gzip = True
                elif ch == "j": use_bzip = True
                elif ch == "f":
                    if i + 1 < len(args):
                        archive = args[i+1]; i += 1
            flag_consumed = True
            i += 1; continue
        paths.append(a); i += 1
    if archive is None:
        return err("tar", "missing -f archive")
    mode_w = ("w:gz" if use_gzip else "w:bz2" if use_bzip else "w")
    mode_r = ("r:gz" if use_gzip else "r:bz2" if use_bzip else "r:*")
    if create:
        buf = io.BytesIO()
        try:
            with tarfile.open(fileobj=buf, mode=mode_w) as tf:
                for src in paths:
                    src_node, src_abs = sh.vfs.resolve(sh.cwd, src)
                    if src_node is None:
                        return err("tar", f"{src}: Cannot stat: No such file or directory")
                    base = os.path.basename(src_abs) or src
                    for arc, node, abs_p in _vfs_walk(sh, src_abs, base):
                        ti = tarfile.TarInfo(name=arc)
                        if node["type"] == "dir":
                            ti.type = tarfile.DIRTYPE
                            ti.mode = 0o755
                            tf.addfile(ti)
                        else:
                            data = node_bytes(node)
                            ti.size = len(data)
                            ti.mode = 0o644
                            tf.addfile(ti, io.BytesIO(data))
        except Exception as e:
            return err("tar", str(e))
        sh.vfs.mkfile(sh.cwd, archive,
                      base64.b64encode(buf.getvalue()).decode("ascii"),
                      binary=True)
        return ok()
    if extract or listing:
        node, _ = sh.vfs.resolve(sh.cwd, archive)
        if node is None:
            return err("tar", f"{archive}: Cannot open: No such file or directory")
        data = node_bytes(node)
        out = ""
        try:
            with tarfile.open(fileobj=io.BytesIO(data), mode=mode_r) as tf:
                for member in tf.getmembers():
                    if listing:
                        out += member.name + "\n"
                        continue
                    if member.isdir():
                        sh.vfs.mkdir(sh.cwd, member.name, parents=True)
                    elif member.isfile():
                        f = tf.extractfile(member)
                        if f is None:
                            continue
                        content = f.read()
                        try:
                            sh.vfs.mkfile(sh.cwd, member.name, content.decode("utf-8"))
                        except UnicodeDecodeError:
                            sh.vfs.mkfile(sh.cwd, member.name,
                                          base64.b64encode(content).decode("ascii"),
                                          binary=True)
        except Exception as e:
            return err("tar", str(e))
        return ok(out)
    return err("tar", "specify -c, -x, or -t")


@cmd("gzip")
def c_gzip(sh, args, stdin):
    keep = "-k" in args
    paths = [a for a in args if not a.startswith("-")]
    if not paths:
        return err("gzip", "missing file")
    for p in paths:
        node, abs_p = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            return err("gzip", f"{p}: No such file or directory")
        if node["type"] != "file":
            return err("gzip", f"{p}: Is a directory")
        data = node_bytes(node)
        compressed = gzlib.compress(data)
        sh.vfs.mkfile(sh.cwd, p + ".gz",
                      base64.b64encode(compressed).decode("ascii"), binary=True)
        if not keep:
            sh.vfs.remove(sh.cwd, p)
    return ok()


@cmd("gunzip")
def c_gunzip(sh, args, stdin):
    keep = "-k" in args
    paths = [a for a in args if not a.startswith("-")]
    if not paths:
        return err("gunzip", "missing file")
    for p in paths:
        node, _ = sh.vfs.resolve(sh.cwd, p)
        if node is None:
            return err("gunzip", f"{p}: No such file or directory")
        try:
            data = gzlib.decompress(node_bytes(node))
        except Exception as e:
            return err("gunzip", str(e))
        out_name = p[:-3] if p.endswith(".gz") else p + ".out"
        try:
            sh.vfs.mkfile(sh.cwd, out_name, data.decode("utf-8"))
        except UnicodeDecodeError:
            sh.vfs.mkfile(sh.cwd, out_name,
                          base64.b64encode(data).decode("ascii"), binary=True)
        if not keep:
            sh.vfs.remove(sh.cwd, p)
    return ok()


@cmd("zip")
def c_zip(sh, args, stdin):
    if len(args) < 2:
        return err("zip", "usage: zip <archive.zip> <files...>")
    archive = args[0]
    paths = args[1:]
    buf = io.BytesIO()
    try:
        with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
            for src in paths:
                src_node, src_abs = sh.vfs.resolve(sh.cwd, src)
                if src_node is None:
                    return err("zip", f"{src}: No such file or directory")
                base = os.path.basename(src_abs) or src
                for arc, node, abs_p in _vfs_walk(sh, src_abs, base):
                    if node["type"] == "file":
                        zf.writestr(arc, node_bytes(node))
                    else:
                        zf.writestr(arc + "/", b"")
    except Exception as e:
        return err("zip", str(e))
    sh.vfs.mkfile(sh.cwd, archive,
                  base64.b64encode(buf.getvalue()).decode("ascii"), binary=True)
    return ok(f"  adding: {len(paths)} item(s) to {archive}\n")


@cmd("unzip")
def c_unzip(sh, args, stdin):
    listing = "-l" in args
    paths = [a for a in args if not a.startswith("-")]
    if not paths:
        return err("unzip", "missing archive")
    archive = paths[0]
    node, _ = sh.vfs.resolve(sh.cwd, archive)
    if node is None:
        return err("unzip", f"{archive}: No such file or directory")
    out = ""
    try:
        with zipfile.ZipFile(io.BytesIO(node_bytes(node))) as zf:
            for info in zf.infolist():
                if listing:
                    out += f"{info.file_size:>9}  {info.filename}\n"
                    continue
                if info.is_dir():
                    sh.vfs.mkdir(sh.cwd, info.filename, parents=True)
                else:
                    data = zf.read(info.filename)
                    try:
                        sh.vfs.mkfile(sh.cwd, info.filename, data.decode("utf-8"))
                    except UnicodeDecodeError:
                        sh.vfs.mkfile(sh.cwd, info.filename,
                                      base64.b64encode(data).decode("ascii"), binary=True)
                    out += f"  inflating: {info.filename}\n"
    except Exception as e:
        return err("unzip", str(e))
    return ok(out)


# ---------- Scripting builtins ----------
@cmd("read")
def c_read(sh, args, stdin):
    """Read a line from stdin (or interactively) into variable(s)."""
    prompt = ""
    var_names = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "-p" and i + 1 < len(args):
            prompt = args[i+1]; i += 2; continue
        var_names.append(a); i += 1
    if not var_names:
        var_names = ["REPLY"]
    if stdin:
        line = stdin.split("\n", 1)[0]
    else:
        try:
            line = input(prompt)
        except (EOFError, KeyboardInterrupt):
            return ("", "", 1)
    parts = line.split()
    for i, v in enumerate(var_names):
        if i == len(var_names) - 1:
            sh.env[v] = " ".join(parts[i:]) if i < len(parts) else ""
        else:
            sh.env[v] = parts[i] if i < len(parts) else ""
    return ok()


@cmd("source", ".")
def c_source(sh, args, stdin):
    if not args:
        return err("source", "filename argument required")
    p = args[0]
    node, _ = sh.vfs.resolve(sh.cwd, p)
    if node is None:
        return err("source", f"{p}: No such file or directory")
    if node["type"] != "file":
        return err("source", f"{p}: Is a directory")
    return run_script(sh, node_text(node))


@cmd("bash", "sh")
def c_bash(sh, args, stdin):
    if not args:
        return ok("(bash trainer — pass a script file to execute)\n")
    if args[0] == "-c" and len(args) > 1:
        return run_script(sh, args[1])
    return c_source(sh, args, stdin)


@cmd("ifconfig")
def c_ifconfig(sh, args, stdin):
    out = ("eth0: flags=4163<UP,BROADCAST,RUNNING,MULTICAST>  mtu 1500\n"
           "        inet 192.168.1.42  netmask 255.255.255.0  broadcast 192.168.1.255\n"
           "        ether 00:1a:2b:3c:4d:5e  txqueuelen 1000  (Ethernet)\n"
           "lo: flags=73<UP,LOOPBACK,RUNNING>  mtu 65536\n"
           "        inet 127.0.0.1  netmask 255.0.0.0\n")
    return ok(out)


@cmd("ip")
def c_ip(sh, args, stdin):
    if args and args[0] == "a":
        return c_ifconfig(sh, [], stdin)
    return ok("Usage: ip a\n")


@cmd("netstat", "ss")
def c_netstat(sh, args, stdin):
    return ok("Active Internet connections\nProto Local Address           Foreign Address         State\ntcp   0.0.0.0:22              0.0.0.0:*               LISTEN\n")


@cmd("ssh")
def c_ssh(sh, args, stdin):
    return ok("[mocked] ssh is disabled in training terminal.\n")


# ---------- Editors ----------
@cmd("nano", "vim", "vi", "edit")
def c_edit(sh, args, stdin):
    if not args:
        return err("edit", "usage: nano FILE")
    p = args[0]
    node, _ = sh.vfs.resolve(sh.cwd, p)
    existing = node_text(node) if node and node["type"] == "file" else ""
    print(f"\n--- Editing {p} (end input with a line containing only ':wq') ---")
    if existing:
        print(existing)
    lines = existing.splitlines()
    try:
        while True:
            line = input()
            if line.strip() == ":wq":
                break
            if line.strip() == ":q!":
                return ok()
            lines.append(line)
    except (EOFError, KeyboardInterrupt):
        pass
    sh.vfs.mkfile(sh.cwd, p, "\n".join(lines) + "\n")
    return ok(f"[saved {p}]\n")


@cmd("less", "more")
def c_less(sh, args, stdin):
    return c_cat(sh, args, stdin)


# ===========================================================================
# KALI / SECURITY-TRAINING COMMANDS
# ===========================================================================
# Pure-python implementations and safely-bounded real-network tools.
# All real-network tools honor the KALI_OFFLINE env var (set to "1" to block).
# ---------------------------------------------------------------------------

import socket as _socket  # used by network tools below

_KALI_NET_NOTICE_SHOWN = {"v": False}


def _net_allowed(sh):
    """Check if real-network ops are permitted in this session."""
    if sh.env.get("KALI_OFFLINE") == "1":
        return False, "real network disabled (KALI_OFFLINE=1)"
    if not _KALI_NET_NOTICE_SHOWN["v"]:
        _KALI_NET_NOTICE_SHOWN["v"] = True
        sys.stderr.write(
            "[real network] outbound traffic is enabled. "
            "Set KALI_OFFLINE=1 to disable.\n")
    return True, ""


# ---------- crunch: wordlist generator ----------
@cmd("crunch")
def c_crunch(sh, args, stdin):
    """crunch <min> <max> [charset] [-t pattern] [-o file]
       Pattern chars: @=lower , =upper %=digit ^=symbol"""
    if len(args) < 2:
        return err("crunch", "usage: crunch <min> <max> [charset] [-t pattern] [-o file]")
    try:
        min_len = int(args[0])
        max_len = int(args[1])
    except ValueError:
        return err("crunch", "min/max must be integers")
    charset = "abcdefghijklmnopqrstuvwxyz"
    pattern = None
    out_file = None
    i = 2
    if i < len(args) and not args[i].startswith("-"):
        charset = args[i]; i += 1
    while i < len(args):
        a = args[i]
        if a == "-t" and i + 1 < len(args):
            pattern = args[i+1]; i += 2; continue
        if a == "-o" and i + 1 < len(args):
            out_file = args[i+1]; i += 2; continue
        i += 1
    HARD_CAP = 100_000
    results = []
    if pattern:
        # Pattern: @ lower, , upper, % digit, ^ symbol; literal otherwise
        from itertools import product
        sets = []
        for ch in pattern:
            if ch == "@": sets.append("abcdefghijklmnopqrstuvwxyz")
            elif ch == ",": sets.append("ABCDEFGHIJKLMNOPQRSTUVWXYZ")
            elif ch == "%": sets.append("0123456789")
            elif ch == "^": sets.append("!@#$%^&*()-_=+[]{};:,.<>?")
            else: sets.append(ch)
        total = 1
        for s in sets:
            total *= len(s)
        if total > HARD_CAP:
            return err("crunch", f"refusing: would generate {total} entries (cap {HARD_CAP})")
        for combo in product(*sets):
            results.append("".join(combo))
    else:
        from itertools import product
        total = 0
        for length in range(min_len, max_len + 1):
            total += len(charset) ** length
        if total > HARD_CAP:
            return err("crunch", f"refusing: would generate {total} entries (cap {HARD_CAP})")
        for length in range(min_len, max_len + 1):
            for combo in product(charset, repeat=length):
                results.append("".join(combo))
    text = "\n".join(results) + "\n"
    if out_file:
        sh.vfs.mkfile(sh.cwd, out_file, text)
        return ok(f"Crunch will now generate the following amount of data: {len(text)} bytes\n"
                  f"Crunch will now generate the following number of lines: {len(results)}\n"
                  f"[wrote {out_file}]\n")
    return ok(text)


# ---------- hashid: identify hash type ----------
HASH_SIGNATURES = [
    (r"^[a-f0-9]{32}$", ["MD5", "MD4", "NTLM", "LM", "RIPEMD-128"]),
    (r"^[a-f0-9]{40}$", ["SHA-1", "RIPEMD-160", "MySQL5"]),
    (r"^[a-f0-9]{56}$", ["SHA-224", "Keccak-224"]),
    (r"^[a-f0-9]{64}$", ["SHA-256", "Keccak-256", "BLAKE2s-256"]),
    (r"^[a-f0-9]{96}$", ["SHA-384", "Keccak-384"]),
    (r"^[a-f0-9]{128}$", ["SHA-512", "Whirlpool", "BLAKE2b-512"]),
    (r"^\$2[aby]\$\d{2}\$.{53}$", ["bcrypt"]),
    (r"^\$1\$.{0,8}\$.{22}$", ["MD5 Crypt"]),
    (r"^\$5\$.{0,16}\$.{43}$", ["SHA-256 Crypt"]),
    (r"^\$6\$.{0,16}\$.{86}$", ["SHA-512 Crypt"]),
    (r"^\$argon2(id|i|d)\$", ["Argon2"]),
    (r"^[A-Za-z0-9+/]{27}=$", ["MD5 (base64)"]),
    (r"^[A-Za-z0-9+/]{43}=$", ["SHA-256 (base64)"]),
]


@cmd("hashid", "hash-identifier")
def c_hashid(sh, args, stdin):
    if not args and not stdin:
        return err("hashid", "usage: hashid <hash> | hashid -f <file>")
    hashes = []
    if "-f" in args:
        idx = args.index("-f")
        if idx + 1 < len(args):
            node, _ = sh.vfs.resolve(sh.cwd, args[idx+1])
            if node is None:
                return err("hashid", f"{args[idx+1]}: No such file or directory")
            hashes = [l.strip() for l in node_text(node).splitlines() if l.strip()]
    elif args:
        hashes = [a for a in args if not a.startswith("-")]
    else:
        hashes = [l.strip() for l in (stdin or "").splitlines() if l.strip()]
    out = ""
    for h in hashes:
        out += f"--\nAnalyzing '{h}'\n"
        matches = []
        for rx, names in HASH_SIGNATURES:
            if re.match(rx, h, re.IGNORECASE):
                matches.extend(names)
        if matches:
            for m in matches:
                out += f"[+] {m}\n"
        else:
            out += "[-] Unknown hash format\n"
    return ok(out)


# ---------- john / hashcat: wordlist attack (limited) ----------
def _hash_word(word, algo):
    b = word.encode("utf-8", errors="replace")
    if algo == "md5":
        return hashlib.md5(b).hexdigest()
    if algo == "sha1":
        return hashlib.sha1(b).hexdigest()
    if algo == "sha224":
        return hashlib.sha224(b).hexdigest()
    if algo == "sha256":
        return hashlib.sha256(b).hexdigest()
    if algo == "sha384":
        return hashlib.sha384(b).hexdigest()
    if algo == "sha512":
        return hashlib.sha512(b).hexdigest()
    if algo == "ntlm":
        return hashlib.new("md4", word.encode("utf-16le")).hexdigest()
    return ""


def _detect_hash_algo(h):
    h = h.strip()
    L = len(h)
    if L == 32: return "md5"
    if L == 40: return "sha1"
    if L == 56: return "sha224"
    if L == 64: return "sha256"
    if L == 96: return "sha384"
    if L == 128: return "sha512"
    return None


@cmd("john", "hashcat")
def c_john(sh, args, stdin):
    """john --wordlist=words.txt [--format=md5] [-h hash] hashfile
       Limited training mode: only wordlist attack against md5/sha1/sha224/
       sha256/sha384/sha512/ntlm. No brute force, no rules."""
    wordlist_path = None
    fmt = None
    inline_hash = None
    hash_file = None
    show = False
    i = 0
    while i < len(args):
        a = args[i]
        if a.startswith("--wordlist="):
            wordlist_path = a.split("=", 1)[1]
        elif a in ("-w", "--wordlist") and i + 1 < len(args):
            wordlist_path = args[i+1]; i += 1
        elif a.startswith("--format="):
            fmt = a.split("=", 1)[1].lower()
        elif a == "-m" and i + 1 < len(args):
            # hashcat-style mode codes (subset)
            mode_map = {"0": "md5", "100": "sha1", "1300": "sha224",
                        "1400": "sha256", "10800": "sha384",
                        "1700": "sha512", "1000": "ntlm"}
            fmt = mode_map.get(args[i+1], None); i += 1
        elif a == "-a" and i + 1 < len(args):
            i += 1  # ignore attack mode
        elif a == "--show":
            show = True
        elif a == "-h" and i + 1 < len(args):
            inline_hash = args[i+1]; i += 1
        elif not a.startswith("-"):
            if hash_file is None:
                hash_file = a
        i += 1
    targets = []
    if inline_hash:
        targets.append(inline_hash.strip())
    if hash_file:
        node, _ = sh.vfs.resolve(sh.cwd, hash_file)
        if node is None:
            return err("john", f"{hash_file}: No such file or directory")
        for line in node_text(node).splitlines():
            line = line.strip()
            if line:
                targets.append(line)
    if not targets:
        return err("john", "no hashes provided")
    if not wordlist_path:
        return err("john", "--wordlist=FILE required (training mode is wordlist-only)")
    wnode, _ = sh.vfs.resolve(sh.cwd, wordlist_path)
    if wnode is None:
        return err("john", f"{wordlist_path}: No such file or directory")
    words = node_text(wnode).splitlines()
    out = f"Loaded {len(targets)} password hash(es)\n"
    out += f"Will run wordlist attack with {len(words)} candidates\n\n"
    cracked = []
    for h in targets:
        algo = fmt or _detect_hash_algo(h)
        if algo is None:
            out += f"[!] {h}: cannot detect format\n"
            continue
        h_low = h.lower()
        found = None
        for w in words:
            w = w.rstrip("\r\n")
            if _hash_word(w, algo) == h_low:
                found = w; break
        if found is not None:
            out += f"{found}\t({algo}: {h})\n"
            cracked.append((h, found, algo))
        else:
            out += f"[-] {h} ({algo}): not found in wordlist\n"
    out += f"\nSession completed: {len(cracked)}/{len(targets)} cracked\n"
    return ok(out)


# ---------- xxd / hexdump ----------
def _hex_dump(data, group=2):
    out = []
    for off in range(0, len(data), 16):
        chunk = data[off:off+16]
        hex_part = ""
        for i, b in enumerate(chunk):
            hex_part += f"{b:02x}"
            if (i + 1) % group == 0:
                hex_part += " "
        hex_part = hex_part.ljust(40)
        ascii_part = "".join(chr(b) if 32 <= b < 127 else "." for b in chunk)
        out.append(f"{off:08x}: {hex_part} {ascii_part}")
    return "\n".join(out) + "\n"


@cmd("xxd")
def c_xxd(sh, args, stdin):
    reverse = False
    paths = []
    for a in args:
        if a == "-r":
            reverse = True
        elif not a.startswith("-"):
            paths.append(a)
    if reverse:
        text = ""
        if paths:
            for p in paths:
                node, _ = sh.vfs.resolve(sh.cwd, p)
                if node is None:
                    return err("xxd", f"{p}: No such file or directory")
                text += node_text(node)
        else:
            text = stdin or ""
        out = bytearray()
        for line in text.splitlines():
            m = re.match(r"^[0-9a-fA-F]+:?\s*([0-9a-fA-F\s]+)", line)
            if not m:
                continue
            hex_str = re.sub(r"\s+", "", m.group(1))
            try:
                out.extend(bytes.fromhex(hex_str))
            except ValueError:
                pass
        try:
            return ok(out.decode("utf-8"))
        except UnicodeDecodeError:
            return ok(out.decode("latin-1"))
    data = b""
    if paths:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("xxd", f"{p}: No such file or directory")
            data += node_bytes(node)
    else:
        data = (stdin or "").encode("utf-8", errors="replace")
    return ok(_hex_dump(data))


@cmd("hexdump", "hd")
def c_hexdump(sh, args, stdin):
    return c_xxd(sh, [a for a in args if a not in ("-C",)], stdin)


# ---------- strings ----------
@cmd("strings")
def c_strings(sh, args, stdin):
    min_len = 4
    paths = []
    i = 0
    while i < len(args):
        a = args[i]
        if a == "-n" and i + 1 < len(args):
            try: min_len = int(args[i+1])
            except ValueError: pass
            i += 2; continue
        if a.startswith("-n"):
            try: min_len = int(a[2:])
            except ValueError: pass
            i += 1; continue
        if not a.startswith("-"):
            paths.append(a)
        i += 1
    data = b""
    if paths:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("strings", f"{p}: No such file or directory")
            data += node_bytes(node)
    else:
        data = (stdin or "").encode("utf-8", errors="replace")
    out = []
    cur = bytearray()
    for b in data:
        if 32 <= b < 127:
            cur.append(b)
        else:
            if len(cur) >= min_len:
                out.append(cur.decode("ascii"))
            cur = bytearray()
    if len(cur) >= min_len:
        out.append(cur.decode("ascii"))
    return ok("\n".join(out) + "\n")


# ---------- binwalk: signature scan ----------
BINWALK_SIGS = [
    (b"\x89PNG\r\n\x1a\n", "PNG image"),
    (b"\xff\xd8\xff", "JPEG image data"),
    (b"GIF87a", "GIF image data, version 87a"),
    (b"GIF89a", "GIF image data, version 89a"),
    (b"PK\x03\x04", "Zip archive data"),
    (b"PK\x05\x06", "Zip archive (empty)"),
    (b"Rar!\x1a\x07\x00", "RAR archive data v1.5"),
    (b"Rar!\x1a\x07\x01\x00", "RAR archive data v5"),
    (b"7z\xbc\xaf\x27\x1c", "7-zip archive data"),
    (b"\x1f\x8b\x08", "gzip compressed data"),
    (b"BZh", "bzip2 compressed data"),
    (b"\x7fELF", "ELF executable"),
    (b"MZ", "PE executable (MS-DOS/Windows)"),
    (b"%PDF-", "PDF document"),
    (b"\xca\xfe\xba\xbe", "Java class file / Mach-O fat binary"),
    (b"\xfe\xed\xfa\xce", "Mach-O 32-bit"),
    (b"\xfe\xed\xfa\xcf", "Mach-O 64-bit"),
    (b"OggS", "Ogg container"),
    (b"ID3", "MP3 audio (with ID3v2)"),
    (b"RIFF", "RIFF container (WAV/AVI)"),
    (b"SQLite format 3\x00", "SQLite 3 database"),
    (b"BM", "BMP image (possibly)"),
    (b"\x00\x00\x01\x00", "Windows icon (.ico)"),
    (b"-----BEGIN ", "PEM-encoded data / certificate"),
    (b"#!/", "Script (shebang)"),
]


@cmd("binwalk")
def c_binwalk(sh, args, stdin):
    if not args:
        return err("binwalk", "usage: binwalk <file>")
    node, _ = sh.vfs.resolve(sh.cwd, args[0])
    if node is None:
        return err("binwalk", f"{args[0]}: No such file or directory")
    data = node_bytes(node)
    out = "DECIMAL       HEXADECIMAL     DESCRIPTION\n"
    out += "-" * 70 + "\n"
    found_any = False
    for sig, desc in BINWALK_SIGS:
        offset = 0
        while True:
            idx = data.find(sig, offset)
            if idx == -1:
                break
            out += f"{idx:<14}0x{idx:<14X}{desc}\n"
            found_any = True
            offset = idx + 1
            if offset > 1024 * 1024:  # cap scan at 1MB per signature
                break
    if not found_any:
        out += "(no recognized signatures)\n"
    return ok(out)


# ---------- rot13 / caesar ----------
def _caesar(text, shift):
    out = []
    for c in text:
        if "a" <= c <= "z":
            out.append(chr((ord(c) - ord("a") + shift) % 26 + ord("a")))
        elif "A" <= c <= "Z":
            out.append(chr((ord(c) - ord("A") + shift) % 26 + ord("A")))
        else:
            out.append(c)
    return "".join(out)


@cmd("rot13")
def c_rot13(sh, args, stdin):
    text = ""
    if args:
        for p in args:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return ok(_caesar(" ".join(args), 13) + "\n")
            text += node_text(node)
    else:
        text = stdin or ""
    return ok(_caesar(text, 13))


@cmd("caesar")
def c_caesar(sh, args, stdin):
    if not args:
        return err("caesar", "usage: caesar <shift> [text...]")
    try:
        shift = int(args[0])
    except ValueError:
        return err("caesar", "shift must be integer")
    if len(args) > 1:
        text = " ".join(args[1:])
    else:
        text = stdin or ""
    return ok(_caesar(text, shift) + ("\n" if not text.endswith("\n") else ""))


# ---------- cowsay / figlet ----------
@cmd("cowsay")
def c_cowsay(sh, args, stdin):
    msg = " ".join(args) if args else (stdin or "Moo!").strip()
    width = max(4, min(60, len(msg)))
    bar = " " + "_" * (width + 2)
    out = bar + "\n"
    out += f"< {msg.ljust(width)} >\n"
    out += " " + "-" * (width + 2) + "\n"
    out += "        \\   ^__^\n"
    out += "         \\  (oo)\\_______\n"
    out += "            (__)\\       )\\/\\\n"
    out += "                ||----w |\n"
    out += "                ||     ||\n"
    return ok(out)


# Simple 5-line block font for figlet (uppercase letters + digits + space)
_FIGLET_FONT = {
    "A": [" █████ ", "██   ██", "███████", "██   ██", "██   ██"],
    "B": ["██████ ", "██   ██", "██████ ", "██   ██", "██████ "],
    "C": [" ██████", "██     ", "██     ", "██     ", " ██████"],
    "D": ["██████ ", "██   ██", "██   ██", "██   ██", "██████ "],
    "E": ["███████", "██     ", "█████  ", "██     ", "███████"],
    "F": ["███████", "██     ", "█████  ", "██     ", "██     "],
    "G": [" ██████", "██     ", "██  ███", "██   ██", " ██████"],
    "H": ["██   ██", "██   ██", "███████", "██   ██", "██   ██"],
    "I": ["██", "██", "██", "██", "██"],
    "J": ["     ██", "     ██", "     ██", "██   ██", " █████ "],
    "K": ["██  ██ ", "██ ██  ", "████   ", "██ ██  ", "██  ██ "],
    "L": ["██     ", "██     ", "██     ", "██     ", "███████"],
    "M": ["███    ███", "████  ████", "██ ████ ██", "██  ██  ██", "██      ██"],
    "N": ["███    ██", "████   ██", "██ ██  ██", "██  ██ ██", "██   ████"],
    "O": [" ██████ ", "██    ██", "██    ██", "██    ██", " ██████ "],
    "P": ["██████ ", "██   ██", "██████ ", "██     ", "██     "],
    "Q": [" ██████ ", "██    ██", "██    ██", "██  █ ██", " ███████"],
    "R": ["██████ ", "██   ██", "██████ ", "██   ██", "██   ██"],
    "S": [" ██████", "██     ", " █████ ", "     ██", "██████ "],
    "T": ["████████", "   ██   ", "   ██   ", "   ██   ", "   ██   "],
    "U": ["██   ██", "██   ██", "██   ██", "██   ██", " █████ "],
    "V": ["██    ██", "██    ██", "██    ██", " ██  ██ ", "  ████  "],
    "W": ["██     ██", "██     ██", "██  █  ██", "██ ███ ██", " ███ ███ "],
    "X": ["██   ██", " ██ ██ ", "  ███  ", " ██ ██ ", "██   ██"],
    "Y": ["██  ██", " ████ ", "  ██  ", "  ██  ", "  ██  "],
    "Z": ["███████", "    ██ ", "   ██  ", "  ██   ", "███████"],
    "0": [" █████ ", "██   ██", "██   ██", "██   ██", " █████ "],
    "1": ["  ██ ", "  ██ ", "  ██ ", "  ██ ", "  ██ "],
    "2": ["██████ ", "     ██", " █████ ", "██     ", "███████"],
    "3": ["██████ ", "     ██", " █████ ", "     ██", "██████ "],
    "4": ["██   ██", "██   ██", "███████", "     ██", "     ██"],
    "5": ["███████", "██     ", "███████", "     ██", "███████"],
    "6": [" ██████", "██     ", "███████", "██   ██", " █████ "],
    "7": ["███████", "     ██", "    ██ ", "   ██  ", "  ██   "],
    "8": [" █████ ", "██   ██", " █████ ", "██   ██", " █████ "],
    "9": [" █████ ", "██   ██", " ██████", "     ██", " █████ "],
    " ": ["    ", "    ", "    ", "    ", "    "],
    "!": ["██", "██", "██", "  ", "██"],
    "?": ["██████ ", "     ██", "  ████ ", "       ", "  ██   "],
}


@cmd("figlet")
def c_figlet(sh, args, stdin):
    msg = " ".join(args) if args else (stdin or "").strip()
    if not msg:
        return err("figlet", "usage: figlet <text>")
    msg = msg.upper()
    rows = ["", "", "", "", ""]
    for ch in msg:
        glyph = _FIGLET_FONT.get(ch, _FIGLET_FONT["?"])
        for i in range(5):
            rows[i] += glyph[i] + "  "
    return ok("\n".join(rows) + "\n")


# ---------- base32 ----------
@cmd("base32")
def c_base32(sh, args, stdin):
    decode = "-d" in args
    paths = [a for a in args if not a.startswith("-")]
    data = b""
    if paths:
        for p in paths:
            node, _ = sh.vfs.resolve(sh.cwd, p)
            if node is None:
                return err("base32", f"{p}: No such file or directory")
            data += node_bytes(node)
    else:
        data = (stdin or "").encode("utf-8", errors="replace")
    try:
        if decode:
            return ok(base64.b32decode(data.strip().upper()).decode(errors="replace"))
        return ok(base64.b32encode(data).decode() + "\n")
    except Exception as e:
        return err("base32", str(e))


# ---------- DNS lookups ----------
@cmd("dig", "nslookup", "host")
def c_dig(sh, args, stdin):
    allowed, msg = _net_allowed(sh)
    if not allowed:
        return err("dig", msg)
    if not args:
        return err("dig", "usage: dig <hostname> [A|AAAA|PTR]")
    host = args[0]
    rtype = args[1].upper() if len(args) > 1 else "A"
    out = f";; {rtype} record lookup for {host}\n"
    try:
        if rtype == "PTR" or re.match(r"^\d+\.\d+\.\d+\.\d+$", host):
            try:
                name, _, _ = _socket.gethostbyaddr(host)
                out += f"{host}\tPTR\t{name}\n"
            except _socket.herror as e:
                out += f";; reverse lookup failed: {e}\n"
                return ("", out, 1)
        else:
            try:
                infos = _socket.getaddrinfo(host, None,
                    _socket.AF_INET6 if rtype == "AAAA" else _socket.AF_INET)
                seen = set()
                for info in infos:
                    addr = info[4][0]
                    if addr in seen: continue
                    seen.add(addr)
                    out += f"{host}\t{rtype}\t{addr}\n"
                if not seen:
                    out += ";; no results\n"
                    return ("", out, 1)
            except _socket.gaierror as e:
                out += f";; lookup failed: {e}\n"
                return ("", out, 1)
    except Exception as e:
        return err("dig", str(e))
    return ok(out)


# ---------- whois ----------
@cmd("whois")
def c_whois(sh, args, stdin):
    allowed, msg = _net_allowed(sh)
    if not allowed:
        return err("whois", msg)
    if not args:
        return err("whois", "usage: whois <domain>")
    domain = args[0]
    server = "whois.iana.org"
    out = ""
    for hop in range(2):  # at most one referral
        try:
            with _socket.create_connection((server, 43), timeout=10) as s:
                s.sendall((domain + "\r\n").encode())
                buf = b""
                s.settimeout(10)
                while True:
                    try:
                        chunk = s.recv(4096)
                    except _socket.timeout:
                        break
                    if not chunk:
                        break
                    buf += chunk
                    if len(buf) > 100_000:
                        break
        except Exception as e:
            return err("whois", f"{server}: {e}")
        text = buf.decode("utf-8", errors="replace")
        out += f";; query to {server}\n{text}\n"
        m = re.search(r"^refer:\s*(\S+)", text, re.MULTILINE | re.IGNORECASE)
        if m and hop == 0:
            server = m.group(1).strip()
            continue
        break
    return ok(out)


# ---------- nmap (TCP-connect, capped) ----------
NMAP_TOP_PORTS = [21, 22, 23, 25, 53, 80, 110, 111, 135, 139,
                  143, 443, 445, 993, 995, 1723, 3306, 3389, 5900, 8080]


def _parse_ports(spec):
    ports = set()
    for part in spec.split(","):
        part = part.strip()
        if "-" in part:
            try:
                a, b = part.split("-", 1)
                a, b = int(a), int(b)
                ports.update(range(a, b + 1))
            except ValueError:
                pass
        else:
            try:
                ports.add(int(part))
            except ValueError:
                pass
    return sorted(p for p in ports if 1 <= p <= 65535)


@cmd("nmap")
def c_nmap(sh, args, stdin):
    allowed, msg = _net_allowed(sh)
    if not allowed:
        return err("nmap", msg)
    ports = NMAP_TOP_PORTS
    host = None
    i = 0
    while i < len(args):
        a = args[i]
        if a == "-p" and i + 1 < len(args):
            ports = _parse_ports(args[i+1]); i += 2; continue
        if a.startswith("-p"):
            ports = _parse_ports(a[2:]); i += 1; continue
        if a.startswith("-"):
            i += 1; continue
        host = a; i += 1
    if host is None:
        return err("nmap", "usage: nmap [-p ports] <host>")
    if "/" in host:
        return err("nmap", "refused: CIDR ranges not supported (single host only)")
    if len(ports) > 200:
        return err("nmap", f"refused: {len(ports)} ports exceeds cap of 200")
    try:
        ip = _socket.gethostbyname(host)
    except _socket.gaierror as e:
        return err("nmap", f"failed to resolve {host}: {e}")
    out = f"Starting nmap-trainer scan\nNmap scan report for {host} ({ip})\n"
    open_ports = []
    closed = 0
    for p in ports:
        s = _socket.socket(_socket.AF_INET, _socket.SOCK_STREAM)
        s.settimeout(0.5)
        try:
            r = s.connect_ex((ip, p))
            if r == 0:
                open_ports.append(p)
        except Exception:
            closed += 1
        finally:
            s.close()
    out += f"Not shown: {len(ports) - len(open_ports)} closed/filtered ports\n"
    if open_ports:
        out += "PORT     STATE  SERVICE\n"
        for p in open_ports:
            try:
                svc = _socket.getservbyport(p, "tcp")
            except OSError:
                svc = "unknown"
            out += f"{p}/tcp   open   {svc}\n"
    out += f"\nNmap done: 1 host up, {len(open_ports)} open\n"
    return ok(out)


# ---------- nc / netcat (client only) ----------
@cmd("nc", "netcat", "ncat")
def c_nc(sh, args, stdin):
    allowed, msg = _net_allowed(sh)
    if not allowed:
        return err("nc", msg)
    if "-l" in args or "--listen" in args:
        return err("nc", "refused: listen mode disabled in trainer")
    zcheck = "-z" in args
    pos = [a for a in args if not a.startswith("-")]
    if len(pos) < 2:
        return err("nc", "usage: nc [-z] <host> <port>")
    host, port = pos[0], pos[1]
    try:
        port = int(port)
    except ValueError:
        return err("nc", "port must be integer")
    if zcheck:
        s = _socket.socket(_socket.AF_INET, _socket.SOCK_STREAM)
        s.settimeout(5)
        try:
            r = s.connect_ex((host, port))
        except Exception as e:
            return err("nc", str(e))
        finally:
            s.close()
        if r == 0:
            return ok(f"Connection to {host} {port} port [tcp/*] succeeded!\n")
        return ("", f"nc: connect to {host} port {port} (tcp) failed\n", 1)
    try:
        s = _socket.create_connection((host, port), timeout=5)
    except Exception as e:
        return err("nc", str(e))
    try:
        if stdin:
            s.sendall(stdin.encode("utf-8", errors="replace"))
        s.shutdown(_socket.SHUT_WR)
        s.settimeout(5)
        chunks = []
        while True:
            try:
                data = s.recv(4096)
            except _socket.timeout:
                break
            if not data:
                break
            chunks.append(data)
            if sum(len(c) for c in chunks) > MOUNT_MAX_FILE_SIZE:
                break
    finally:
        s.close()
    raw = b"".join(chunks)
    try:
        return ok(raw.decode("utf-8"))
    except UnicodeDecodeError:
        return ok(f"<binary, {len(raw)} bytes>\n")


# ---------- dirb / gobuster ----------
@cmd("dirb", "gobuster")
def c_dirb(sh, args, stdin):
    allowed, msg = _net_allowed(sh)
    if not allowed:
        return err("dirb", msg)
    url = None
    wordlist = None
    # Support both:
    #   dirb URL WORDLIST
    #   gobuster dir -u URL -w WORDLIST
    i = 0
    while i < len(args):
        a = args[i]
        if a == "-u" and i + 1 < len(args):
            url = args[i+1]; i += 2; continue
        if a == "-w" and i + 1 < len(args):
            wordlist = args[i+1]; i += 2; continue
        if a == "dir":
            i += 1; continue
        if a.startswith("-"):
            i += 1; continue
        if url is None:
            url = a
        elif wordlist is None:
            wordlist = a
        i += 1
    if not url or not wordlist:
        return err("dirb", "usage: dirb <url> <wordlist>  (or gobuster dir -u URL -w LIST)")
    if not url.startswith("http"):
        url = "http://" + url
    if not url.endswith("/"):
        url = url + "/"
    wnode, _ = sh.vfs.resolve(sh.cwd, wordlist)
    if wnode is None:
        return err("dirb", f"{wordlist}: No such file or directory")
    words = [w.strip() for w in node_text(wnode).splitlines() if w.strip() and not w.startswith("#")]
    MAX_REQ = 500
    if len(words) > MAX_REQ:
        words = words[:MAX_REQ]
    out = f"\n--- Scanning URL: {url} ---\n"
    out += f"--- Wordlist size: {len(words)} ---\n\n"
    ctx = ssl.create_default_context()
    try:
        ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
    except Exception:
        pass
    found = 0
    for w in words:
        target = url + w
        req = urllib.request.Request(target, method="GET",
                                     headers={"User-Agent": "dirb-trainer/1.0"})
        try:
            with urllib.request.urlopen(req, timeout=5, context=ctx) as resp:
                code = resp.status
                size = len(resp.read(8192))
                if code < 400:
                    out += f"==> DIRECTORY: {target}  (CODE:{code}|SIZE:{size})\n"
                    found += 1
        except urllib.error.HTTPError as e:
            if e.code in (301, 302, 401, 403):
                out += f"  (CODE:{e.code}) {target}\n"
                found += 1
        except Exception:
            pass
        time.sleep(0.05)
    out += f"\n--- {found} hits in {len(words)} requests ---\n"
    return ok(out)


# ---------- cewl: word extractor ----------
@cmd("cewl")
def c_cewl(sh, args, stdin):
    allowed, msg = _net_allowed(sh)
    if not allowed:
        return err("cewl", msg)
    min_len = 5
    out_file = None
    url = None
    i = 0
    while i < len(args):
        a = args[i]
        if a == "-m" and i + 1 < len(args):
            try: min_len = int(args[i+1])
            except ValueError: pass
            i += 2; continue
        if a in ("-w", "--write") and i + 1 < len(args):
            out_file = args[i+1]; i += 2; continue
        if not a.startswith("-"):
            url = a
        i += 1
    if url is None:
        return err("cewl", "usage: cewl [-m N] [-w outfile] <url>")
    if not url.startswith("http"):
        url = "http://" + url
    try:
        ctx = ssl.create_default_context()
        try:
            ctx.check_hostname = False; ctx.verify_mode = ssl.CERT_NONE
        except Exception:
            pass
        with urllib.request.urlopen(url, timeout=15, context=ctx) as resp:
            data = resp.read(MOUNT_MAX_FILE_SIZE)
    except Exception as e:
        return err("cewl", str(e))
    text = data.decode("utf-8", errors="replace")
    text = re.sub(r"<script[^>]*>.*?</script>", " ", text, flags=re.DOTALL | re.IGNORECASE)
    text = re.sub(r"<style[^>]*>.*?</style>", " ", text, flags=re.DOTALL | re.IGNORECASE)
    text = re.sub(r"<[^>]+>", " ", text)
    text = re.sub(r"&\w+;", " ", text)
    words = re.findall(r"[A-Za-z][A-Za-z0-9'-]{" + str(min_len-1) + r",}", text)
    seen = set()
    uniq = []
    for w in words:
        if w not in seen:
            seen.add(w); uniq.append(w)
    result = "\n".join(uniq) + "\n"
    if out_file:
        sh.vfs.mkfile(sh.cwd, out_file, result)
        return ok(f"[wrote {len(uniq)} words to {out_file}]\n")
    return ok(result)


# Manpages content (just a few interesting ones)
MANPAGES = {
    "ls": "NAME\n    ls - list directory contents\n\nSYNOPSIS\n    ls [OPTION]... [FILE]...\n\nOPTIONS\n    -a   show hidden files\n    -l   long listing\n    -R   recursive\n    -1   one per line\n",
    "cd": "NAME\n    cd - change the working directory\n\nSYNOPSIS\n    cd [DIR]\n",
    "grep": "NAME\n    grep - print lines matching a pattern\n\nOPTIONS\n    -i  ignore case\n    -v  invert\n    -n  show line numbers\n    -r  recursive\n    -c  count\n    -l  files with matches\n",
    "echo": "NAME\n    echo - display a line of text\n",
}


# ---------------------------------------------------------------------------
# Script parser & executor (multi-line if/for/while/functions)
# ---------------------------------------------------------------------------
def _strip_comment(line):
    out = ""
    in_q = None
    i = 0
    while i < len(line):
        c = line[i]
        if in_q:
            out += c
            if c == in_q: in_q = None
        elif c in ("'", '"'):
            in_q = c; out += c
        elif c == "#":
            break
        else:
            out += c
        i += 1
    return out


def script_open_close_delta(line):
    """Block depth contribution of a line. Used for interactive multi-line."""
    line = _strip_comment(line).strip()
    if not line:
        return 0
    delta = 0
    # Strip strings to avoid counting keywords inside them
    cleaned = re.sub(r"'[^']*'|\"[^\"]*\"", "", line)
    # Tokens
    tokens = re.findall(r"[A-Za-z_][\w]*|[{}]", cleaned)
    for t in tokens:
        if t in ("if", "for", "while", "case", "select"):
            delta += 1
        elif t in ("fi", "done", "esac"):
            delta -= 1
        elif t == "{":
            delta += 1
        elif t == "}":
            delta -= 1
    # function NAME() {  - the { handles the open
    return delta


def split_script_lines(text):
    """Split script text into logical lines, splitting on ';' but respecting quotes,
    and peeling leading control keywords (do/then/else) onto their own lines."""
    raw_parts = []
    for raw in text.splitlines():
        raw = _strip_comment(raw)
        cur = ""; q = None
        for c in raw:
            if q:
                cur += c
                if c == q: q = None
            elif c in ("'", '"'):
                q = c; cur += c
            elif c == ";":
                if cur.strip():
                    raw_parts.append(cur.strip())
                cur = ""
            elif c == "{":
                # Attach { to the preceding token, then break
                cur += c
                if cur.strip():
                    raw_parts.append(cur.strip())
                cur = ""
            elif c == "}":
                if cur.strip():
                    raw_parts.append(cur.strip())
                raw_parts.append("}")
                cur = ""
            else:
                cur += c
        if cur.strip():
            raw_parts.append(cur.strip())

    lines = []
    for p in raw_parts:
        # Peel leading do/then/else keywords onto their own line
        while True:
            m = re.match(r"^(do|then|else)\b\s*(.*)$", p)
            if not m:
                break
            kw, rest = m.group(1), m.group(2).strip()
            lines.append(kw)
            if not rest:
                p = ""
                break
            p = rest
        if p:
            lines.append(p)
    return lines


def parse_statements(lines, i, end_kw):
    stmts = []
    while i < len(lines):
        line = lines[i].strip()
        if not line:
            i += 1; continue
        first = line.split()[0]
        if first in end_kw:
            return stmts, i
        if first == "if":
            stmt, i = parse_if(lines, i)
            stmts.append(stmt)
        elif first == "for":
            stmt, i = parse_for(lines, i)
            stmts.append(stmt)
        elif first == "while":
            stmt, i = parse_while(lines, i)
            stmts.append(stmt)
        elif first == "function" or re.match(r"^[A-Za-z_]\w*\s*\(\s*\)", line):
            stmt, i = parse_func(lines, i)
            stmts.append(stmt)
        else:
            stmts.append(("cmd", line))
            i += 1
    return stmts, i


def parse_if(lines, i):
    # Line: "if COND" optionally followed by "then" on same logical line was already split
    line = lines[i].strip()
    cond = line[2:].strip()
    if cond.endswith("then"):
        cond = cond[:-4].strip()
    i += 1
    # Skip a bare 'then' line
    if i < len(lines) and lines[i].strip() == "then":
        i += 1
    then_stmts, i = parse_statements(lines, i, {"elif", "else", "fi"})
    elifs = []
    else_stmts = None
    while i < len(lines) and lines[i].strip().startswith("elif"):
        elif_cond = lines[i].strip()[4:].strip()
        if elif_cond.endswith("then"):
            elif_cond = elif_cond[:-4].strip()
        i += 1
        if i < len(lines) and lines[i].strip() == "then":
            i += 1
        elif_body, i = parse_statements(lines, i, {"elif", "else", "fi"})
        elifs.append((elif_cond, elif_body))
    if i < len(lines) and lines[i].strip() == "else":
        i += 1
        else_stmts, i = parse_statements(lines, i, {"fi"})
    if i < len(lines) and lines[i].strip() == "fi":
        i += 1
    return ("if", cond, then_stmts, elifs, else_stmts), i


def parse_for(lines, i):
    line = lines[i].strip()
    m = re.match(r"^for\s+(\w+)\s+in\s+(.+?)(?:\s+do)?$", line)
    if not m:
        # bash C-style not supported; treat as cmd
        return ("cmd", line), i + 1
    var, items = m.group(1), m.group(2)
    i += 1
    if i < len(lines) and lines[i].strip() == "do":
        i += 1
    body, i = parse_statements(lines, i, {"done"})
    if i < len(lines) and lines[i].strip() == "done":
        i += 1
    return ("for", var, items, body), i


def parse_while(lines, i):
    line = lines[i].strip()
    cond = line[5:].strip()
    if cond.endswith("do"):
        cond = cond[:-2].strip()
    i += 1
    if i < len(lines) and lines[i].strip() == "do":
        i += 1
    body, i = parse_statements(lines, i, {"done"})
    if i < len(lines) and lines[i].strip() == "done":
        i += 1
    return ("while", cond, body), i


def parse_func(lines, i):
    line = lines[i].strip()
    m = re.match(r"^(?:function\s+)?([A-Za-z_]\w*)\s*\(\s*\)\s*\{?", line)
    if not m:
        return ("cmd", line), i + 1
    name = m.group(1)
    has_open_brace = "{" in line
    i += 1
    if not has_open_brace and i < len(lines) and lines[i].strip() == "{":
        i += 1
    body, i = parse_statements(lines, i, {"}"})
    if i < len(lines) and lines[i].strip() == "}":
        i += 1
    return ("func", name, body), i


def execute_statements(sh, stmts):
    last = sh.last_status
    for stmt in stmts:
        kind = stmt[0]
        if kind == "cmd":
            run_line(sh, stmt[1], from_script=True)
            last = sh.last_status
        elif kind == "if":
            _, cond, then_b, elifs, else_b = stmt
            run_line(sh, cond, from_script=True)
            if sh.last_status == 0:
                execute_statements(sh, then_b)
            else:
                done = False
                for ec, eb in elifs:
                    run_line(sh, ec, from_script=True)
                    if sh.last_status == 0:
                        execute_statements(sh, eb)
                        done = True
                        break
                if not done and else_b is not None:
                    execute_statements(sh, else_b)
            last = sh.last_status
        elif kind == "for":
            _, var, items_str, body = stmt
            items_tokens, _ = tokenize(items_str, sh)
            for item in items_tokens or []:
                sh.env[var] = item
                execute_statements(sh, body)
            last = sh.last_status
        elif kind == "while":
            _, cond, body = stmt
            guard = 0
            while True:
                run_line(sh, cond, from_script=True)
                if sh.last_status != 0:
                    break
                execute_statements(sh, body)
                guard += 1
                if guard > 10000:
                    sys.stderr.write("while: iteration limit reached\n")
                    break
            last = sh.last_status
        elif kind == "func":
            _, name, body = stmt
            sh.functions[name] = body
            last = 0
            sh.last_status = 0
    return last


def run_script(sh, text):
    lines = split_script_lines(text)
    stmts, _ = parse_statements(lines, 0, set())
    try:
        execute_statements(sh, stmts)
    except Exception as e:
        sys.stderr.write(f"script error: {e}\n")
        sh.last_status = 1
    return ok()


_SCRIPT_KEYWORDS_RX = re.compile(
    r"(?:^|[\s;&|])(?:if|for|while|case|function|until|select)\b"
    r"|^[A-Za-z_]\w*\s*\(\s*\)\s*\{"
)


def from_script_keywords(text):
    """Heuristic: does this input contain shell-script control structures?"""
    if "\n" in text:
        return True
    cleaned = re.sub(r"'[^']*'|\"[^\"]*\"", "", text)
    return bool(_SCRIPT_KEYWORDS_RX.search(cleaned))


# ---------------------------------------------------------------------------
# Parser & executor
# ---------------------------------------------------------------------------
def expand_vars(token, sh):
    def repl(m):
        name = m.group(1) or m.group(2)
        if name == "?":
            return str(sh.last_status)
        return sh.env.get(name, "")
    return re.sub(r"\$\{(\w+)\}|\$(\w+|\?)", repl, token)


def expand_glob(token, sh):
    if not any(c in token for c in "*?["):
        return [token]
    if "/" in token:
        d, pat = token.rsplit("/", 1)
        node, _ = sh.vfs.resolve(sh.cwd, d)
        prefix = d + "/"
    else:
        node, _ = sh.vfs.resolve(sh.cwd, ".")
        prefix = ""
    if node is None or node["type"] != "dir":
        return [token]
    matches = [prefix + n for n in sorted(node["children"]) if fnmatch.fnmatch(n, token.split("/")[-1])]
    return matches if matches else [token]


def tokenize(line, sh):
    """Quoting-aware tokenizer:
       - single quotes: literal, no expansion, no globbing
       - double quotes: variable expansion only, no globbing
       - unquoted: variable expansion + globbing
    """
    out = []
    i = 0
    n = len(line)
    while i < n:
        c = line[i]
        if c.isspace():
            i += 1
            continue
        token = ""
        was_quoted = False
        can_glob = True
        emitted = False
        while i < n and not line[i].isspace():
            c = line[i]
            if c == "'":
                j = line.find("'", i + 1)
                if j == -1:
                    return None, "unterminated single quote"
                token += line[i+1:j]
                i = j + 1
                was_quoted = True
                can_glob = False
                emitted = True
            elif c == '"':
                j = i + 1
                content = ""
                while j < n and line[j] != '"':
                    if line[j] == "\\" and j + 1 < n and line[j+1] in '"\\$`':
                        content += line[j+1]
                        j += 2
                    else:
                        content += line[j]
                        j += 1
                if j >= n:
                    return None, "unterminated double quote"
                content = expand_vars(content, sh)
                token += content
                i = j + 1
                was_quoted = True
                can_glob = False
                emitted = True
            elif c == "\\" and i + 1 < n:
                token += line[i+1]
                i += 2
                can_glob = False
            else:
                token += c
                i += 1
                emitted = True
        if not emitted and not was_quoted:
            continue
        if can_glob:
            token = expand_vars(token, sh)
            out.extend(expand_glob(token, sh))
        else:
            out.append(token)
    return out, None


def split_pipeline(tokens):
    """Split tokens around | into a list of [cmd_tokens]."""
    pipes = []
    current = []
    for t in tokens:
        if t == "|":
            pipes.append(current); current = []
        else:
            current.append(t)
    pipes.append(current)
    return pipes


def extract_redirects(tokens, sh):
    """Return (cleaned_tokens, stdin_text or None, stdout_target, append)."""
    cleaned = []
    stdin_text = None
    stdout_target = None
    append = False
    i = 0
    while i < len(tokens):
        t = tokens[i]
        if t == ">" and i + 1 < len(tokens):
            stdout_target = tokens[i+1]; append = False; i += 2; continue
        if t == ">>" and i + 1 < len(tokens):
            stdout_target = tokens[i+1]; append = True; i += 2; continue
        if t == "<" and i + 1 < len(tokens):
            node, _ = sh.vfs.resolve(sh.cwd, tokens[i+1])
            stdin_text = node_text(node) if node and node["type"] == "file" else ""
            i += 2; continue
        cleaned.append(t); i += 1
    return cleaned, stdin_text, stdout_target, append


def split_logical(line):
    """Split on ;, &&, || while respecting quotes. Returns list of (op, segment)."""
    segments = []
    current = ""
    i = 0
    in_q = None
    while i < len(line):
        c = line[i]
        if in_q:
            current += c
            if c == in_q:
                in_q = None
            i += 1; continue
        if c in ("'", '"'):
            in_q = c; current += c; i += 1; continue
        if line[i:i+2] == "&&":
            segments.append((None if not segments else segments[-1][0], current.strip()))
            segments.append(("&&", None))
            current = ""; i += 2; continue
        if line[i:i+2] == "||":
            segments.append((None if not segments else segments[-1][0], current.strip()))
            segments.append(("||", None))
            current = ""; i += 2; continue
        if c == ";":
            segments.append((None if not segments else segments[-1][0], current.strip()))
            segments.append((";", None))
            current = ""; i += 1; continue
        current += c; i += 1
    if current.strip():
        segments.append((None, current.strip()))
    # Convert to list of (op, cmd) where op governs whether cmd runs based on prev status
    result = []
    pending_op = None
    for op, seg in segments:
        if seg is None:
            pending_op = op
        else:
            result.append((pending_op, seg))
            pending_op = None
    return result


def execute_command(sh, tokens, stdin):
    """Execute a single command (no pipes/redirects). tokens = [cmd, args...]."""
    if not tokens:
        return ok()
    name = tokens[0]
    args = tokens[1:]
    if name in sh.aliases:
        alias_tokens, _ = tokenize(sh.aliases[name], sh)
        if alias_tokens:
            return execute_command(sh, alias_tokens + args, stdin)
    if name in sh.functions:
        # Set positional params
        saved = {f"_pos{i}": sh.env.get(f"_pos{i}") for i in range(10)}
        for i, a in enumerate(args, 1):
            sh.env[f"_pos{i}"] = a
        try:
            execute_statements(sh, sh.functions[name])
            return ("", "", sh.last_status)
        finally:
            for k, v in saved.items():
                if v is None:
                    sh.env.pop(k, None)
                else:
                    sh.env[k] = v
    fn = COMMANDS.get(name)
    if fn is None:
        return ("", f"{name}: command not found\n", 127)
    try:
        return fn(sh, args, stdin)
    except SystemExit:
        raise
    except Exception as e:
        return ("", f"{name}: error: {e}\n", 1)


def run_pipeline(sh, segment):
    tokens, terr = tokenize(segment, sh)
    if terr:
        return ("", f"shell: {terr}\n", 2)
    if not tokens:
        return ok()
    pipeline = split_pipeline(tokens)
    stdin = ""
    last_status = 0
    final_stdout = ""
    final_stderr = ""
    for i, cmd_tokens in enumerate(pipeline):
        cmd_tokens, redir_stdin, stdout_target, append = extract_redirects(cmd_tokens, sh)
        in_text = redir_stdin if redir_stdin is not None else stdin
        out, errout, status = execute_command(sh, cmd_tokens, in_text)
        last_status = status
        if stdout_target:
            if append:
                node, _ = sh.vfs.resolve(sh.cwd, stdout_target)
                existing = node_text(node) if node and node["type"] == "file" else ""
                sh.vfs.mkfile(sh.cwd, stdout_target, existing + out)
            else:
                sh.vfs.mkfile(sh.cwd, stdout_target, out)
            out = ""
        if i == len(pipeline) - 1:
            final_stdout = out
            final_stderr = errout
        else:
            stdin = out
            if errout:
                final_stderr += errout
    return (final_stdout, final_stderr, last_status)


def run_line(sh, line, from_script=False):
    line = line.strip()
    if not line or line.startswith("#"):
        return
    if not from_script:
        sh.history.append(line)
    # Bare variable assignment: VAR=value (no spaces around =)
    m = re.match(r"^([A-Za-z_]\w*)=(.*)$", line)
    if m and not line.startswith("export"):
        var, val = m.group(1), m.group(2)
        # Strip quotes
        if (val.startswith('"') and val.endswith('"')) or \
           (val.startswith("'") and val.endswith("'")):
            val = val[1:-1]
        val = expand_vars(val, sh)
        # Command substitution $(...)
        val = expand_cmdsub(sh, val)
        sh.env[var] = val
        sh.last_status = 0
        return
    parts = split_logical(line)
    last_status = sh.last_status
    for op, segment in parts:
        if op == "&&" and last_status != 0:
            continue
        if op == "||" and last_status == 0:
            continue
        # Command substitution in the segment
        segment = expand_cmdsub(sh, segment)
        out, errout, status = run_pipeline(sh, segment)
        if out:
            sys.stdout.write(out)
            if not out.endswith("\n"):
                sys.stdout.write("\n")
        if errout:
            sys.stderr.write(errout)
        sys.stdout.flush()
        last_status = status
        sh.last_status = status
        sh.env["?"] = str(status)


def expand_cmdsub(sh, text):
    """Expand $(...) by running the inner command and substituting its output."""
    def repl(m):
        inner = m.group(1)
        out, _, _ = run_pipeline(sh, inner)
        return out.rstrip("\n")
    # Non-greedy, doesn't handle nesting
    return re.sub(r"\$\(([^()]*)\)", repl, text)


# ---------------------------------------------------------------------------
# REPL
# ---------------------------------------------------------------------------
def setup_readline(sh):
    if not _HAS_READLINE or readline is None:
        return
    try:
        # Load saved history
        if HIST_FILE.exists():
            try:
                readline.read_history_file(str(HIST_FILE))
            except Exception:
                pass
        readline.set_history_length(1000)

        # Tab completer
        def completer(text, state):
            buf = readline.get_line_buffer()
            stripped = buf.lstrip()
            try:
                if " " not in stripped:
                    # Completing a command
                    options = [c for c in COMMANDS if c.startswith(text)]
                    options += [a for a in sh.aliases if a.startswith(text)]
                    options = sorted(set(options))
                else:
                    # Completing a path
                    if "/" in text:
                        d, prefix = text.rsplit("/", 1)
                        d = d or "/"
                    else:
                        d, prefix = ".", text
                    node, abs_p = sh.vfs.resolve(sh.cwd, d)
                    if node is None or node["type"] != "dir":
                        return None
                    kids = sh.vfs.list_children(abs_p)
                    options = []
                    for name, child in kids.items():
                        if name.startswith(prefix):
                            full = (d.rstrip("/") + "/" + name) if d not in (".", "") else name
                            if child and child["type"] == "dir":
                                full += "/"
                            options.append(full)
                    options.sort()
                return options[state] if state < len(options) else None
            except Exception:
                return None

        readline.set_completer(completer)
        readline.parse_and_bind("tab: complete")
        # Treat / as a word boundary so path completion behaves naturally
        try:
            readline.set_completer_delims(" \t\n;|&<>")
        except Exception:
            pass
    except Exception:
        pass


def main():
    # Enable ANSI + UTF-8 on Windows
    if os.name == "nt":
        try:
            import ctypes
            kernel32 = ctypes.windll.kernel32
            kernel32.SetConsoleMode(kernel32.GetStdHandle(-11), 7)
            kernel32.SetConsoleOutputCP(65001)
            kernel32.SetConsoleCP(65001)
        except Exception:
            pass
        try:
            sys.stdout.reconfigure(encoding="utf-8", errors="replace")
            sys.stderr.reconfigure(encoding="utf-8", errors="replace")
            sys.stdin.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass

    sh = Shell()
    setup_readline(sh)
    print("\033[1;36m" + r"""
   __    _                     ______             _
  / /   (_)___  __  ___  __   /_  __/__________ _(_)___  ___  _____
 / /   / / __ \/ / / / |/_/    / / / ___/ __ `/ / __ \/ _ \/ ___/
/ /___/ / / / / /_/ />  <     / / / /  / /_/ / / / / /  __/ /
\____/_/_/ /_/\__,_/_/|_|    /_/ /_/   \__,_/_/_/ /_/\___/_/
""" + "\033[0m")
    print(f"Linux Training Terminal (Ubuntu 22.04 emulation)")
    print(f"Type 'help' for the list of commands. Type 'exit' to quit.\n")

    try:
        while sh.running:
            buffer = ""
            depth = 0
            try:
                first = input(sh.prompt())
            except EOFError:
                print()
                break
            except KeyboardInterrupt:
                print("^C")
                continue
            buffer = first
            depth += script_open_close_delta(first)
            while depth > 0:
                try:
                    cont = input("> ")
                except EOFError:
                    break
                except KeyboardInterrupt:
                    print("^C")
                    buffer = ""
                    depth = 0
                    break
                buffer += "\n" + cont
                depth += script_open_close_delta(cont)
            if not buffer.strip():
                continue
            try:
                if not from_script_keywords(buffer):
                    run_line(sh, buffer)
                else:
                    run_script(sh, buffer)
            except SystemExit:
                break
            except Exception as e:
                sys.stderr.write(f"shell error: {e}\n")
            sh.save_state()
    finally:
        sh.save_state()
        if _HAS_READLINE and readline is not None:
            try:
                readline.write_history_file(str(HIST_FILE))
            except Exception:
                pass
        print("logout")


if __name__ == "__main__":
    main()
