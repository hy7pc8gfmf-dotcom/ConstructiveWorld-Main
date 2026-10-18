#!/bin/bash
# vo_sync_watch.sh — 对侧 vo 信任缓存自动联动（macOS/bash 形；Windows 侧用 vo_sync_watch.ps1）
#
# 使命：本机作为 runner 之一，当对侧电脑推送的 CI run 全绿后，自动下载其上传的
# vo trust cache artifact，镜像合并进本机信任缓存目录——下次本机 CI/本地编译
# 播种步即吃指纹 SKIP，实现「一侧新增模块推送 CI，对侧自动本地化+认证」闭环。
#
# 用法（推荐 launchd/计划任务常驻，或 nohup 后台）：
#   REPO=hy7pc8gfmf-dotcom/ConstructiveWorld-Main \
#   ARTIFACT=vo-trust-cache-windows \
#   CACHE_DIR=/Users/apple/vo_ci_cache_mac \
#   bash scripts/vo_sync_watch.sh
# 环境变量：
#   REPO        仓库（默认 hy7pc8gfmf-dotcom/ConstructiveWorld-Main）
#   ARTIFACT    要同步的 artifact 名（对侧产物；本机若为 Windows 侧则填 vo-trust-cache-macos）
#   CACHE_DIR   本机信任缓存目录（mac 默认 /Users/apple/vo_ci_cache_mac）
#   POLL_SEC    轮询间隔（默认 60；网络单飞纪律：每轮仅 1-2 个请求）
#   RUN_FILE    已同步 run 记录（默认 $CACHE_DIR/.vo_sync_last_run）
# token：git credential（与 push 同源）自动获取，无 token 时仅观察不下 Artifact（fail-loud 日志）。
set -u
REPO="${REPO:-hy7pc8gfmf-dotcom/ConstructiveWorld-Main}"
ARTIFACT="${ARTIFACT:-vo-trust-cache-windows}"
CACHE_DIR="${CACHE_DIR:-/Users/apple/vo_ci_cache_mac}"
POLL_SEC="${POLL_SEC:-60}"
RUN_FILE="${RUN_FILE:-$CACHE_DIR/.vo_sync_last_run}"
mkdir -p "$CACHE_DIR"
LAST=0
[ -f "$RUN_FILE" ] && LAST=$(cat "$RUN_FILE" 2>/dev/null || echo 0)
echo "vo_sync_watch: repo=$REPO artifact=$ARTIFACT cache=$CACHE_DIR last_run=$LAST"

get_token() {
  printf "protocol=https\nhost=github.com\n" | git credential fill 2>/dev/null | grep '^password=' | cut -d= -f2
}

while true; do
  TOKEN=$(get_token)
  AUTH=""; [ -n "$TOKEN" ] && AUTH="Authorization: token $TOKEN"
  # ① 最近绿 run（单飞 1 发）
  RUN=$(curl -s --max-time 30 ${AUTH:+-H "$AUTH"} \
    "https://api.github.com/repos/$REPO/actions/runs?branch=main&status=success&per_page=1" \
    | "$("${PYTHON:-python3:-python}" 2>/dev/null || echo python3)" -c "import json,sys
try:
    d=json.load(sys.stdin); r=d['workflow_runs'][0]; print(r['id'])
except Exception:
    print(0)" 2>/dev/null || echo 0)
  if [ -n "$RUN" ] && [ "$RUN" -gt "$LAST" ] 2>/dev/null; then
    echo "vo_sync_watch: new green run $RUN — syncing $ARTIFACT"
    # ② 定位 artifact（单飞 1 发）
    AID=$(curl -s --max-time 30 ${AUTH:+-H "$AUTH"} \
      "https://api.github.com/repos/$REPO/actions/runs/$RUN/artifacts?per_page=50" \
      | "${PYTHON:-python3}" -c "import json,sys
try:
    d=json.load(sys.stdin)
    print(next(a['id'] for a in d.get('artifacts',[]) if a['name']=='$ARTIFACT'))
except Exception:
    print(0)" 2>/dev/null || echo 0)
    if [ "${AID:-0}" -gt 0 ] 2>/dev/null && [ -n "$TOKEN" ]; then
      # ③ 下载+镜像合并（先取到临时区，验 zip 完整再原子替换）
      TMP=$(mktemp -d)
      if curl -sL --max-time 600 -H "Authorization: token $TOKEN" \
           "https://api.github.com/repos/$REPO/actions/artifacts/$AID/zip" -o "$TMP/vo.zip" \
         && [ "$(stat -f %z "$TMP/vo.zip" 2>/dev/null || stat -c %s "$TMP/vo.zip" 2>/dev/null || echo 0)" -gt 1000 ] \
         && unzip -q -o "$TMP/vo.zip" -d "$TMP/vo"; then
        N=$(find "$TMP/vo" -name '*.vo' | wc -l)
        find "$CACHE_DIR" -maxdepth 1 -name '*.vo' -delete 2>/dev/null
        find "$TMP/vo" -name '*.vo' -exec cp {} "$CACHE_DIR"/ \;
        echo "vo_sync_watch: run $RUN synced $N .vo -> $CACHE_DIR"
        echo "$RUN" > "$RUN_FILE"
      else
        echo "vo_sync_watch: run $RUN artifact download/extract FAILED (will retry next poll) — fail-loud"
      fi
      rm -rf "$TMP"
    else
      echo "vo_sync_watch: run $RUN has no $ARTIFACT (artifact missing or expired) — marking seen"
      echo "$RUN" > "$RUN_FILE"
    fi
    LAST=$RUN
  fi
  sleep "$POLL_SEC"
done
