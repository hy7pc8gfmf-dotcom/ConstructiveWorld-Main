@echo off
rem TempInterp regression seat round2: G4 coqchk full-path 9.0
cd /d "D:\ComplexAnalysis\ConstructiveWorld-Main"
del /q "_tint2_g4.log" "_tint2_g4.err" "_tint2_g4.exit" 2>NUL
"C:\Rocq-Platform~9.0~2025.08\bin\coqchk.exe" -Q ConstructiveWorld_vo "" UpReqTempInterp < NUL > "_tint2_g4.log" 2> "_tint2_g4.err"
echo EXITCODE=%ERRORLEVEL% > "_tint2_g4.exit"
