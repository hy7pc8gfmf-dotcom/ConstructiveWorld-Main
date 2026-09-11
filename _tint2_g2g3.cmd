@echo off
rem TempInterp regression seat round2: G2 (assumptions probe) + G3 (extraction probe)
cd /d "D:\ComplexAnalysis\ConstructiveWorld-Main"
del /q "_tint2_g2.log" "_tint2_g2.err" "_tint2_g2.exit" "_tint2_g3.log" "_tint2_g3.err" "_tint2_g3.exit" "_tint2_g3_extract.ml" "_tint2_g3_extract.mli" 2>NUL
"C:\Rocq-Platform~9.0~2025.08\bin\coqc.exe" -Q ConstructiveWorld_vo "" _tint2_g2_probe.v < NUL > "_tint2_g2.log" 2> "_tint2_g2.err"
echo EXITCODE=%ERRORLEVEL% > "_tint2_g2.exit"
"C:\Rocq-Platform~9.0~2025.08\bin\coqc.exe" -Q ConstructiveWorld_vo "" _tint2_g3_probe.v < NUL > "_tint2_g3.log" 2> "_tint2_g3.err"
echo EXITCODE=%ERRORLEVEL% > "_tint2_g3.exit"
