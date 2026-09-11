# _merge220_compile.ps1 — 合并轨编译（cpu_guard -Command 调用；内嵌引号收拢在本文件）
Set-Location "D:\ComplexAnalysis\ConstructiveWorld-Main\releases"
$coqc = "C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
& $coqc -Q . "" "CW_ConstructiveWorld_220.v" > "_merge220_compile.log" 2>&1
exit $LASTEXITCODE
