@echo off
cd /d D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo
"C:/Rocq-Platform~9.1~2026.01/bin/coqc.exe" -q -Q . "" UpReqMinPKLChain.v
exit /b %ERRORLEVEL%
