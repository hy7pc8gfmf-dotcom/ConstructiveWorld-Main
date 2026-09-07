#!/bin/bash
cd "$(dirname "$0")"
K="C:\Rocq-Platform~9.0~2025.08\bin\coqchk.exe"
pass=0; failn=0
for f in *.vo; do
  m="${f%.vo}"
  "$K" -Q . "" "$m" > "_chk_$m.log" 2>&1
  e=$?
  if [ $e -eq 0 ] && grep -q "Modules were successfully checked" "_chk_$m.log"; then
    pass=$((pass+1)); echo "$m PASS"
  else
    failn=$((failn+1)); echo "$m FAIL(exit=$e)"
  fi
done
echo "===coqchk 认证：$pass 过 / $failn 败==="
