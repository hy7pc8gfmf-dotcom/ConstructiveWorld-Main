@echo off
"C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe" -Q . "" -Q "..\001" "" %1
exit /b %errorlevel%
