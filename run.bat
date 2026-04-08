@echo off
REM Launcher for the Linux Training Terminal
title Linux Training Terminal
chcp 65001 >nul
set PYTHONIOENCODING=utf-8
cd /d "%~dp0"
python -X utf8 linux_terminal.py
pause
