@echo off
rem _mc2 probe: merged-file base region truncated at hang-stmt+200 (L103046, ends at Qed)
rem 等价编译条件 = 91c 全量编译轨（ROCQPATH + -q, 9.1），仅换为沙箱单文件
cd /d "D:\ComplexAnalysis\ConstructiveWorld-Main\releases\_mc2_probe"
powershell -NoProfile -ExecutionPolicy Bypass -File "D:\ComplexAnalysis\新算法实践\live\cpu_guard.ps1" -LoadLimit 60 -CoolSec 5 -MaxWaitSec 600 -CoreN 0 -Command "$env:ROCQPATH='D:\ComplexAnalysis\ConstructiveWorld-Main\releases\_mc2_probe'; & 'C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe' -q base91_probe.v"
echo EXIT=%ERRORLEVEL%> _probe91_exit.txt
