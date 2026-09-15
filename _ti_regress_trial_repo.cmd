@echo off
rem TempInterp regression seat: trial compile of repo-side UpReqTempInterp.v (repro)
cd /d "D:\ComplexAnalysis\ConstructiveWorld-Main"
del /q "_ti_regress_trial_repo.log" "_ti_regress_trial_repo.err" "_ti_regress_trial_repo.exit" 2>NUL
"C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe" -Q ConstructiveWorld_vo "" ConstructiveWorld_vo\UpReqTempInterp.v < NUL > "_ti_regress_trial_repo.log" 2> "_ti_regress_trial_repo.err"
echo EXITCODE=%ERRORLEVEL% > "_ti_regress_trial_repo.exit"
