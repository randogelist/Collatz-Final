@echo off
setlocal EnableExtensions DisableDelayedExpansion
cd /d "%~dp0"
set "VERSION=v0_1_0_construction"
set "PREFIX=GOODWORKFLOWFRONTIER::%VERSION%::"
set "LEAN_EXE=%COLLATZ_LEAN_EXE%"
if not defined LEAN_EXE set "LEAN_EXE=%USERPROFILE%\.elan\toolchains\leanprover--lean4---v4.33.0\bin\lean.exe"
if not exist "%LEAN_EXE%" (
  echo %PREFIX%ERROR=LEAN_433_NOT_FOUND_SET_COLLATZ_LEAN_EXE
  goto :fail
)
if not exist ".build" mkdir ".build"
if errorlevel 1 goto :fail
:unique_output
set "OUT=%CD%\.build\windows_%RANDOM%_%RANDOM%"
if exist "%OUT%" goto :unique_output
mkdir "%OUT%"
if errorlevel 1 goto :fail
set "LEAN_PATH=%OUT%"
set "LEAN_SRC_PATH="
set "FINDSTR=%SystemRoot%\System32\findstr.exe"
"%LEAN_EXE%" --version > "%OUT%\lean-version.log" 2>&1
if errorlevel 1 goto :fail
"%FINDSTR%" /L /C:"version 4.33.0," "%OUT%\lean-version.log" >nul
if errorlevel 1 goto :fail
"%FINDSTR%" /L /C:"d8b18978322de05a8f3dba51ef03cf5461676c17" "%OUT%\lean-version.log" >nul
if errorlevel 1 goto :fail
echo %PREFIX%TOOLCHAIN=PASS
echo %PREFIX%REUSE=DISABLED_FRESH_OUTPUT_ALL_MODULES_REBUILT
echo %PREFIX%MATHLIB=NOT_REQUIRED
if not exist "scripts\modules.txt" goto :fail
if not exist "scripts\audit_endpoints.txt" goto :fail
if not exist "scripts\axiom_guard.lean" goto :fail
set "COMPILED=0"
for /f "usebackq eol=# delims=" %%M in ("scripts\modules.txt") do (
  call :compile %%M
  if errorlevel 1 goto :fail
)
> "%OUT%\AxiomAudit.lean" echo import Lean
for /f "usebackq eol=# delims=" %%M in ("scripts\modules.txt") do >> "%OUT%\AxiomAudit.lean" echo import %%M
for /f "usebackq eol=# delims=" %%E in ("scripts\audit_endpoints.txt") do >> "%OUT%\AxiomAudit.lean" echo #print axioms %%E
type "scripts\axiom_guard.lean" >> "%OUT%\AxiomAudit.lean"
"%LEAN_EXE%" "%OUT%\AxiomAudit.lean" > "%OUT%\axiom-audit.log" 2>&1
if errorlevel 1 (
  type "%OUT%\axiom-audit.log"
  goto :fail
)
"%FINDSTR%" /L /C:"AXIOM_WHITELIST_PASS:" "%OUT%\axiom-audit.log" >nul
if errorlevel 1 goto :fail
type "%OUT%\axiom-audit.log"
> "%OUT%\receipt.txt" echo WORKFLOW=YOU_ARE_GOODWORKFLOWFRONTIER
>> "%OUT%\receipt.txt" echo VERSION=%VERSION%
>> "%OUT%\receipt.txt" echo BUILD=PASS
>> "%OUT%\receipt.txt" echo AXIOM_AUDIT=PASS
>> "%OUT%\receipt.txt" echo ALLOWED_AXIOMS=propext Classical.choice Quot.sound
>> "%OUT%\receipt.txt" echo REUSED=0
>> "%OUT%\receipt.txt" echo COMPILED=%COMPILED%
>> "%OUT%\receipt.txt" echo ACCEPTED_WITNESS=NOT_SUPPLIED
>> "%OUT%\receipt.txt" echo COLLATZ_PROVED=NO
>> "%OUT%\receipt.txt" echo SEARCH_EXECUTED=NO
echo %PREFIX%SUMMARY=BUILD=PASS;AXIOM_AUDIT=PASS;NEW=%COMPILED%;REUSED=0;ACCEPTED_WITNESS=NOT_SUPPLIED;COLLATZ_PROVED=NO
exit /b 0

:compile
set "MODULE=%~1"
if not exist "%MODULE%.lean" exit /b 1
"%LEAN_EXE%" -o "%OUT%\%MODULE%.olean" "%MODULE%.lean" > "%OUT%\%MODULE%.log" 2>&1
if errorlevel 1 (
  type "%OUT%\%MODULE%.log"
  exit /b 1
)
if not exist "%OUT%\%MODULE%.olean" exit /b 1
set /a COMPILED+=1 >nul
echo %PREFIX%MODULE_%MODULE%=COMPILED_PASS
exit /b 0

:fail
echo %PREFIX%SUMMARY=BUILD=FAIL;COLLATZ_PROVED=NO
exit /b 1
