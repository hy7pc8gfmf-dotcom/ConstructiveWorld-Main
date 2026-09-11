@echo off
"C:\Rocq-Platform~9.0~2025.08\bin\coqc.exe" -Q . "" -Q "..\001" "" %1
exit /b %errorlevel%
