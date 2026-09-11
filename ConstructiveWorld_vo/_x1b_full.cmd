@echo off
cd /d D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo
"C:/Rocq-Platform~9.0~2025.08/bin/coqc.exe" -q -Q . "" UpReqMinPKLChain.v
exit /b %ERRORLEVEL%
