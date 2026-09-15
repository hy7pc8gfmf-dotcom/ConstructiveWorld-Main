@echo off
rem TempInterp regression seat round2: G1 trial compile of fixed repo UpReqTempInterp.v
cd /d "D:\ComplexAnalysis\ConstructiveWorld-Main"
del /q "_tint2_g1.log" "_tint2_g1.err" "_tint2_g1.exit" 2>NUL
"C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe" -Q ConstructiveWorld_vo "" ConstructiveWorld_vo\UpReqTempInterp.v < NUL > "_tint2_g1.log" 2> "_tint2_g1.err"
echo EXITCODE=%ERRORLEVEL% > "_tint2_g1.exit"
