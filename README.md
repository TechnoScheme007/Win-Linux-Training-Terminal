# Linux Training Terminal
<img width="1106" height="622" alt="Screenshot 2026-04-08 121512" src="https://github.com/user-attachments/assets/18220a64-bd0e-4302-b6b9-78c9005d1011" />

A self-contained Linux shell emulator for Windows. Around **125 commands**, real shell scripting, sandboxed Windows folder mounts, and a Kali-style security toolkit — all in **a single Python file** with no required dependencies.

Built for people who want to practice Linux command-line skills on Windows without spinning up WSL, a VM, or dual-booting Ubuntu.

---

## Why

Switching to Linux is intimidating if your fingers don't already know the commands. This terminal lets you build that muscle memory inside a safe sandbox on the Windows machine you already have.

- No installation, no dependencies, no admin rights required
- Persistent virtual filesystem — your work survives between sessions
- Real shell semantics: pipes, redirection, globbing, scripting
- Real network tools where it makes sense (DNS, HTTP, port scanning)
- A `reset-fs` command if you `rm -rf /` and want to start over

It is **not** a Linux emulator. It cannot run real ELF binaries, install packages, or boot a kernel. For that, use WSL2 or Ubuntu. This is a *trainer* — focused on the shell experience.

---

## Quick start

```bash
python linux_terminal.py
```

Or on Windows, just double-click **`run.bat`**.

Optional, for tab completion and arrow-key history on Windows:

```bash
pip install -r requirements.txt
```

Requires Python 3.8+. No other dependencies.

---

## Features

### Shell

- ~125 commands (see full list with `help` inside the terminal)
- Pipes (`|`), redirection (`>`, `>>`, `<`)
- Logical chains (`&&`, `||`, `;`)
- Environment variables (`$VAR`, `${VAR}`, `$?`)
- Globbing (`*`, `?`, `[abc]`)
- Single and double quoting with proper expansion rules
- Aliases (`alias ll='ls -la'`)
- Persistent history and state across sessions
- ANSI colors

### Scripting

Full multi-line scripting support:

```bash
for f in *.txt; do
    echo "Processing $f"
    wc -l "$f"
done

if [ -f welcome.txt ]; then
    echo "found"
else
    echo "missing"
fi

greet() { echo "hello $_pos1"; }
greet world
```

Run script files with `bash script.sh`, `sh script.sh`, or `source script.sh`.

### Filesystem

A persistent virtual filesystem rooted at `/` — `/home/user`, `/etc`, `/var`, `/tmp`, `/usr`, etc. Every file operation actually persists to disk in `vfs_state/filesystem.json`. Your changes survive between sessions. Use `reset-fs` to wipe.

Commands include: `ls`, `cd`, `pwd`, `mkdir`, `rmdir`, `rm`, `cp`, `mv`, `touch`, `cat`, `head`, `tail`, `find`, `tree`, `stat`, `file`, `du`, `df`, `chmod`, `chown`, `ln`, and more.

### Text processing

`grep`, `sed` (basic `s///`), `awk` (basic `{print}`), `sort`, `uniq`, `cut`, `tr`, `tee`, `wc`, `rev`, `nl`, `tac`, `diff`, `cat -n`, `nano`/`vim` (line-mode editor).

### Archives

Real `tar`, `gzip`, `gunzip`, `zip`, `unzip` operating on the virtual filesystem:

```bash
tar -czf backup.tar.gz Documents
tar -xzf backup.tar.gz
zip stuff.zip Documents
unzip -l stuff.zip
gzip notes.txt
```

### Sandboxed Windows mounts

Bridge real Windows folders into the virtual filesystem with strict safety rails:

```bash
mount C:\path\to\folder /mnt/win
mount -r C:\readonly\folder /mnt/ro
ls /mnt/win
echo "from terminal" > /mnt/win/notes.txt
mount       # list mounts
umount /mnt/win
```

Inside `/mnt/win`, every command (`ls`, `cat`, `cp`, `find`, `grep -r`, `tree`, `tar`, ...) operates on **real Windows files**.

**Safety rails enforced automatically:**

- **Path jail** — cannot escape the mount root via `..` or symlinks
- **Forbidden roots** — cannot mount drive roots, `C:\Windows`, `C:\Program Files (x86)`, `C:\ProgramData`, or the bare user profile
- **10 MB cap** on file writes through mounts
- **Extension blocklist** — `.exe .bat .cmd .com .dll .sys .msi .ps1 .vbs .scr .lnk` cannot be created/overwritten via mounts
- **Read-only mounts** with `-r`
- **Mount points cannot be `rm`'d** — must `umount`

### Real network

Outbound network commands that actually work, with sane caps:

- **`curl`** / **`wget`** — real HTTP(S) GETs (10 MB response cap, 15s timeout, supports `-o`, `-O`, `-X`, `-H`, `-I`, `-s`)
- **`dig`** / **`nslookup`** / **`host`** — real DNS lookups (A, AAAA, PTR)
- **`whois`** — real WHOIS protocol queries (follows IANA referrals)
- **`nmap`** — real TCP-connect port scanning, **capped at 200 ports**, single host only, no CIDR ranges, no SYN scan
- **`nc`** / **`netcat`** — real TCP **client** (`-z` port check or send-stdin mode). **Listen mode is disabled.**
- **`dirb`** / **`gobuster`** — real HTTP directory brute force from a wordlist, capped at 500 requests with 50ms inter-request sleep
- **`cewl`** — real URL-to-wordlist extraction

### Security training toolkit

Pure-Python implementations of common Kali tools, useful for CTF practice:

- **`crunch`** — wordlist generator with patterns (`@,%^`), output cap 100k entries
- **`hashid`** — identify hash types by length and format (MD5, SHA family, bcrypt, SHA crypt, Argon2, base64-encoded variants)
- **`john`** / **`hashcat`** — wordlist attack against MD5/SHA1/SHA224/SHA256/SHA384/SHA512/NTLM hashes (auto-detects format by length, supports `-m` mode codes)
- **`xxd`** / **`hexdump`** — hex dump with `-r` reverse
- **`strings`** — extract printable strings from any file
- **`binwalk`** — file signature scanner (PNG, JPEG, ZIP, ELF, PDF, RAR, 7z, gzip, ...)
- **`base32`** / **`base64`** — encode and decode
- **`rot13`** / **`caesar`** — classical ciphers
- **`md5sum`** / **`sha1sum`** / **`sha256sum`** — checksums
- **`cowsay`** / **`figlet`** — because every Linux trainer needs them

### Safety: KALI_OFFLINE mode

Set `export KALI_OFFLINE=1` to disable **all** real-network commands instantly. Use this for offline CTF practice or in environments where outbound traffic isn't allowed. Everything else still works.

The first time a real-network command runs in a session, it prints:

```
[real network] outbound traffic is enabled. Set KALI_OFFLINE=1 to disable.
```

---

## Authorized use only

The network and security tools in this trainer are intended for:

- **Authorized penetration testing** with documented permission
- **CTF competitions** and security training labs
- **Defensive research** on systems you own
- **Learning** how these tools work in a controlled sandbox

Do not use them against systems or networks you do not own or have explicit permission to test. The author accepts no responsibility for misuse.

---

## Limitations

This is a shell trainer, not a Linux kernel. It cannot:

- Run real ELF binaries or install packages (no `apt`, no `pip` for the trainer's commands)
- Run TUI editors (`vim` and `nano` are line-mode here)
- Manage real processes (`ps`, `top`, `kill` are stubs)
- Mount real disk partitions or use raw sockets
- Open listening sockets (no `nc -l`, no inbound services)
- Touch the real Windows filesystem outside of explicitly mounted folders

For anything requiring real Linux internals, install **WSL2** or **Ubuntu**. This trainer is the bridge that gets your hands ready for that switch.

---

## Architecture

Single-file Python (`linux_terminal.py`, ~3000 lines, no required dependencies):

- **Virtual filesystem** persisted to JSON, with binary file support via base64
- **Mount-aware path resolution** that transparently routes operations to real disk inside mount points
- **Quoting-aware tokenizer** with proper single/double-quote semantics
- **Recursive-descent script parser** for `if`/`for`/`while`/functions
- **Pipeline executor** with redirection extraction
- **Command registry** via decorator (`@cmd("name", "alias")`)

State lives in `vfs_state/` next to the script:

```
vfs_state/
├── filesystem.json   # the virtual filesystem (your files)
├── mounts.json       # configured Windows mounts
├── env.json          # exported environment variables
└── history.txt       # shell history
```

Wipe `vfs_state/` to factory-reset, or run `reset-fs` from inside the terminal.

---

## Contributing

Pull requests welcome. The command registry makes adding new commands easy — define a function decorated with `@cmd("name")` that takes `(shell, args, stdin)` and returns `(stdout, stderr, status)`. Look at any existing command for an example.

---

## License

MIT — see [LICENSE](LICENSE).
