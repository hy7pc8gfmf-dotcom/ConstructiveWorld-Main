# vo_sync_watch.ps1 — 对侧 vo 信任缓存自动联动（Windows/PowerShell 形；mac 侧用 vo_sync_watch.sh）
#
# 使命：Windows runner 侧常驻计划任务——对侧（mac）推送的 CI run 全绿后，自动下载
# vo-trust-cache-macos artifact，镜像合并进 Windows 本地信任缓存树
# （D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo）——下次 CI
# Seed trust cache 步播种即吃指纹 SKIP，实现双机自动联动认证。
#
# 一次性安装（管理员或用户级计划任务，每 2 分钟轮询）：
#   schtasks /Create /TN "vo_sync_watch" /SC MINUTE /MO 2 /TR ^
#     "pwsh -File D:\actions-runner\scripts\vo_sync_watch.ps1" /F
# 参数（脚本头部默认值可改）：
#   $Repo / $Artifact / $CacheDir / $StateFile
# token：git credential（与 push 同源）自动获取。

$Repo      = "hy7pc8gfmf-dotcom/ConstructiveWorld-Main"
$Artifact  = "vo-trust-cache-macos"
$CacheDir  = "D:\ComplexAnalysis\ConstructiveWorld-Main\ConstructiveWorld_vo"
$StateFile = "D:\actions-runner\.vo_sync_last_run"

function Get-Token {
  $out = "protocol=https`nhost=github.com`n" | git credential fill 2>$null
  ($out | Select-String '^password=' ) -replace '^password=', ''
}

$Last = 0
if (Test-Path $StateFile) { $Last = [long](Get-Content $StateFile -ErrorAction SilentlyContinue) }
Write-Output "vo_sync_watch: repo=$Repo artifact=$Artifact cache=$CacheDir last_run=$Last"

while ($true) {
  try {
    $Token = Get-Token
    $H = @{ }
    if ($Token) { $H["Authorization"] = "token $Token" }
    # ① 最近绿 run
    $runs = Invoke-RestMethod -Headers $H -TimeoutSec 30 `
      "https://api.github.com/repos/$Repo/actions/runs?branch=main&status=success&per_page=1"
    $RunId = 0
    if ($runs.workflow_runs.Count -gt 0) { $RunId = [long]$runs.workflow_runs[0].id }
    if ($RunId -gt $Last) {
      Write-Output "vo_sync_watch: new green run $RunId — syncing $Artifact"
      # ② 定位 artifact
      $arts = Invoke-RestMethod -Headers $H -TimeoutSec 30 `
        "https://api.github.com/repos/$Repo/actions/runs/$RunId/artifacts?per_page=50"
      $aid = ($arts.artifacts | Where-Object { $_.name -eq $Artifact } | Select-Object -First 1).id
      if ($aid -and $Token) {
        # ③ 下载+镜像合并
        $tmp = Join-Path $env:TEMP ("vo_sync_" + [guid]::NewGuid().ToString("N"))
        New-Item -ItemType Directory -Path $tmp -Force | Out-Null
        $zip = Join-Path $tmp "vo.zip"
        Invoke-WebRequest -Headers @{ Authorization = "token $Token" } -TimeoutSec 600 `
          -Uri "https://api.github.com/repos/$Repo/actions/artifacts/$aid/zip" -OutFile $zip
        Expand-Archive -Path $zip -DestinationPath (Join-Path $tmp "vo") -Force
        $vos = Get-ChildItem -Path (Join-Path $tmp "vo") -Filter *.vo -Recurse
        Get-ChildItem -Path $CacheDir -Filter *.vo -File -ErrorAction SilentlyContinue | Remove-Item -Force
        $vos | ForEach-Object { Copy-Item $_.FullName $CacheDir -Force }
        Write-Output "vo_sync_watch: run $RunId synced $($vos.Count) .vo -> $CacheDir"
        Set-Content -Path $StateFile -Value $RunId
        Remove-Item -Recurse -Force $tmp
      }
      else {
        Write-Output "vo_sync_watch: run $RunId has no $Artifact — marking seen"
        Set-Content -Path $StateFile -Value $RunId
      }
      $Last = $RunId
    }
  }
  catch {
    Write-Output "vo_sync_watch: poll error: $($_.Exception.Message) — retry next cycle"
  }
  Start-Sleep -Seconds 60
}
