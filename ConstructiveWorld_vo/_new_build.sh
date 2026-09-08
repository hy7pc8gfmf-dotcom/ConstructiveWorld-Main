#!/bin/bash
cd "$(dirname "$0")"
C="C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
for m in UpKVDrift UpLoeb UpLoebD2 UpQKBound UpRefuted; do
  "$C" -Q . "" "$m.v" > "_$m.build.log" 2>&1
  echo "$m EXIT=$?"
done
