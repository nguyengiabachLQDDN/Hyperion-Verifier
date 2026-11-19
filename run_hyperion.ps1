# HYPERION Portable PowerShell Launcher
param(
    [switch]$BenchmarkCli,
    [switch]$StressCli,
    [int]$Scale = 4,
    [int]$Port = 8765,
    [switch]$NoBrowser
)

$ErrorActionPreference = "Stop"
Set-Location -Path $PSScriptRoot
$env:PYTHONDONTWRITEBYTECODE = "1"

$pyArgs = @("main.py", "--port", $Port)
if ($NoBrowser) { $pyArgs += "--no-browser" }
if ($BenchmarkCli) { $pyArgs += @("--benchmark-cli", "--scale", $Scale) }
elseif ($StressCli) { $pyArgs += @("--stress-cli", "--scale", $Scale) }

& python @pyArgs
