@echo off
setlocal
cd /d "%~dp0"
set PYTHONDONTWRITEBYTECODE=1

echo ============================================================
echo   HYPERION Portable Static Analysis ^& Mutation Studio
echo   Location: %~dp0
echo ============================================================

where python >nul 2>&1
if errorlevel 1 (
    echo [ERROR] Python 3.10+ not found in PATH on this machine.
    pause
    exit /b 1
)

python main.py %*
endlocal
