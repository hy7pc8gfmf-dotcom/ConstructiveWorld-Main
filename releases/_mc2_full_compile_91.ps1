# _mc2_full_compile_90.ps1 — 合并轨全量编译（收口席续；9.0 与 coqchk 同版本；ROCQPATH 供 loadpath）
Set-Location "D:\ComplexAnalysis\ConstructiveWorld-Main\releases"
$env:ROCQPATH = "D:\ComplexAnalysis\ConstructiveWorld-Main\releases"
$coqc = "C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
& $coqc -q "CW_ConstructiveWorld_220.v" > "_mc2_full_compile.log" 2>&1
"EXIT=$LASTEXITCODE" | Out-File -Append "_mc2_full_compile.log" -Encoding utf8
exit $LASTEXITCODE
