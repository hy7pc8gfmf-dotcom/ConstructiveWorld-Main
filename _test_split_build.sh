#!/bin/bash
cd "$(dirname "$0")"
C="C:\Rocq-Platform~9.1~2026.01\bin\coqc.exe"
fail=0; pass=0
while IFS= read -r f; do
  f="${f#ConstructiveWorld_vo/}"; f="${f#ConstructiveWorld_Live/}"
  [ -f "ConstructiveWorld_Live/$f" ] || continue
  v="${f%.v}.vo"
  if [ -f "ConstructiveWorld_Live/$v" ] && [ "ConstructiveWorld_Live/$v" -nt "ConstructiveWorld_Live/$f" ]; then
    echo "$f SKIP"; continue
  fi
  "$C" -async-proofs off -Q CW219_split "" -Q ConstructiveWorld_Live "" -Q ../001 "" "ConstructiveWorld_Live/$f" > "_test_${f%.v}.log" 2>&1
  e=$?
  if [ $e -eq 0 ]; then pass=$((pass+1)); echo "$f OK"; else fail=$((fail+1)); echo "$f FAIL($e)"; tail -4 "_test_${f%.v}.log"; fi
done < <(grep '\.v$' ConstructiveWorld_Live/_CoqProject | grep -v CW_ConstructiveWorld_219)
echo "===结果: $pass 绿 / $fail 败==="
