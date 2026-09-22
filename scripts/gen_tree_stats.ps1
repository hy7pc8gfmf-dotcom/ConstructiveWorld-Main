<#
=====================================================================
 gen_tree_stats.ps1 — S7/PA4+PB6 全树模块计数 tree-stats.json 生成器
 (ConstructiveWorld 补强战役 SLICE-S7 工具件 · 工具族 · 零编译零网络零 git 写)
---------------------------------------------------------------------
 六维计数:
   1 全树 .v      = 侧树 Live_X 递归 *.v(全量)
   2 Live_X 顶层  = 侧树 Live_X 深度0 *.v(沙箱系子目录天然排除)
   3 UpAbl 顶层   = Live_X 深度0 名前缀 UpAbl*.v
   4 attn 沙箱    = Live_X\attn 递归 *.v
   5 order 行数   = order.txt 物理行数(在册三方: 主库Live/侧树Live/vo树, 另探 scripts)
   6 提交面数     = 主库 git 提交面: ConstructiveWorld_Live/*.v(仓面 *.v 另附)
 三口径分列 (PB6: 注册面/侧树顶层/沙箱):
   A 注册面   = 维度5+6 (git 提交面 + order 行数)
   B 侧树顶层 = 维度2+3 —— ★论文引用口径固定=侧树顶层(维度2), 防锈声明随 JSON 落盘★
   C 沙箱     = 维度4
 对账 (fail-loud): 内嵌 09-22 双席手测真值——
   PR-B: Live_X顶层 841 / 全量 1402 / attn沙箱 363 / UpAbl顶层 226 / order 572 / 提交面 609
   PR-C: Live_X顶层 839 / UpAbl顶层 226 / order 572 / 提交面 609
   任一 |实测-手测|/手测 > 5% → 退出码 2, 判「并列存证·禁硬判」(PRWO 施工单红线)。
 用法:
   pwsh -File gen_tree_stats.ps1 -SelfTest          # 现树跑一轮+对账表(验收模式)
   pwsh -File gen_tree_stats.ps1 -TamperTest        # 负向自测: 假真值注入须触发退出码2
   pwsh -File gen_tree_stats.ps1 [-OutFile x.json] [-CI]   # 常规产出; -CI=runner 韧性
 领地: 只读统计(库树/git 只读), 唯一写面 = -OutFile(默认本工具旁 tree-stats.json)。
 coq.yml 正本零触碰(CI #107 rerun 在飞面); 本件随 R11x 注册波入库 scripts/ 后 CI 消费。
=====================================================================
#>
[CmdletBinding()]
param(
  [string]$SideTree = 'D:\ComplexAnalysis\新算法实践\Live_X',
  [string]$MainRepo = 'D:\ComplexAnalysis\ConstructiveWorld-Main',
  [string]$SideLive = 'D:\ComplexAnalysis\ConstructiveWorld_Live',
  [string]$VoTree   = 'D:\ComplexAnalysis\ConstructiveWorld_vo',
  [string]$OutFile  = '',
  [switch]$SelfTest,
  [switch]$TamperTest,
  [switch]$CI
)
$ErrorActionPreference = 'Stop'
$script:FailLoud = $false

# --- 计数原语: 按 Name 后过滤 '*.v'(免 -Filter 8.3 短名伪匹配), 只读 -----------------
function Count-V {
  param([string]$Dir, [switch]$Recurse)
  if ([string]::IsNullOrWhiteSpace($Dir) -or -not (Test-Path -LiteralPath $Dir)) { return $null }
  $gci = @{ LiteralPath = $Dir; File = $true; Force = $false }
  if ($Recurse) { $gci.Recurse = $true }
  @(Get-ChildItem @gci | Where-Object { $_.Name -like '*.v' }).Count
}
function Get-OrderLines {
  param([string[]]$Paths)
  $out = [ordered]@{}
  foreach ($p in $Paths) {
    if (Test-Path -LiteralPath $p) {
      $n = 0
      foreach ($l in [System.IO.File]::ReadLines($p)) { $n++ }
      $out[$p] = $n
    } else { $out[$p] = $null }
  }
  $out
}
function Get-GitFace {
  param([string]$Repo, [string]$Pathspec)
  try {
    $lines = @(& git -C $Repo ls-files -- $Pathspec 2>$null)
    if ($LASTEXITCODE -ne 0) { return $null }
    @($lines | Where-Object { $_ -match '\.v$' }).Count
  } catch { return $null }
}

# --- 六维计数 -------------------------------------------------------------------
$topFiles      = $null
$liveTop       = $null
if (Test-Path -LiteralPath $SideTree) {
  $topFiles = @(Get-ChildItem -LiteralPath $SideTree -File | Where-Object { $_.Name -like '*.v' })
  $liveTop  = $topFiles.Count
}
$fullTree      = Count-V $SideTree -Recurse
$attnSandbox   = Count-V (Join-Path $SideTree 'attn') -Recurse
$upablTop      = if ($null -ne $topFiles) { @($topFiles | Where-Object { $_.Name -like 'UpAbl*.v' }).Count } else { $null }
$upablRec      = $null
if (Test-Path -LiteralPath $SideTree) {
  $upablRec = @(Get-ChildItem -LiteralPath $SideTree -Recurse -File | Where-Object { $_.Name -like 'UpAbl*.v' }).Count
}
$orderLines    = Get-OrderLines @(
  (Join-Path $MainRepo 'ConstructiveWorld_Live\order.txt'),
  (Join-Path $SideLive 'order.txt'),
  (Join-Path $VoTree 'order.txt'),
  (Join-Path $MainRepo 'scripts\order.txt')
)
$orderVals     = @($orderLines.Values | Where-Object { $null -ne $_ })
$orderMax      = if ($orderVals.Count) { [int]($orderVals | Measure-Object -Maximum).Maximum } else { $null }
$orderMin      = if ($orderVals.Count) { [int]($orderVals | Measure-Object -Minimum).Minimum } else { $null }
$orderConsist  = if ($orderVals.Count -ge 2) { if ($orderMax -eq $orderMin) { 'three-way-consistent' } else { 'DIVERGED' } } else { 'insufficient-copies' }

$faceLiveDir   = Get-GitFace $MainRepo 'ConstructiveWorld_Live/*.v'
$faceRepoAll   = Get-GitFace $MainRepo '*.v'
$headNote      = $null
try {
  $h = & git -C $MainRepo log -1 --format='%h|%ad' --date=iso 2>$null
  if ($LASTEXITCODE -eq 0 -and $h) { $headNote = ($h -join '') }
} catch { $headNote = $null }

# --- 对账真值(09-22 PR-B/PR-C 手测) 与 fail-loud 判定 ----------------------------
$manual = [ordered]@{
  live_x_top    = @{ PRB = 841;  PRC = 839 }
  full_tree_v   = @{ PRB = 1402; PRC = $null }
  attn_sandbox  = @{ PRB = 363;  PRC = $null }
  upabl_top     = @{ PRB = 226;  PRC = 226 }
  order_lines   = @{ PRB = 572;  PRC = 572 }
  commit_face   = @{ PRB = 609;  PRC = 609 }
}
if ($TamperTest) { $manual.live_x_top.PRB = 500 }   # 负向注入: 340/841=40%>>5% 须触发退出码2

function Test-Recon {
  param([string]$Key, [int]$Actual)
  $prb = $manual[$Key].PRB; $prc = $manual[$Key].PRC
  $row = [ordered]@{ actual = $Actual }
  foreach ($seat in @('PRB','PRC')) {
    $m = $manual[$Key].$seat
    if ($null -eq $m) { $row[$seat] = $null; continue }
    $d = [math]::Round((($Actual - $m) / $m) * 100, 2)
    $row[$seat] = @{ manual = $m; delta_pct = $d; verdict = $(if ([math]::Abs($d) -gt 5) { 'FAIL(>5%)' } else { 'PASS' }) }
    if ([math]::Abs($d) -gt 5) { $script:FailLoud = $true }
  }
  $row
}

$recon = [ordered]@{}
if ($null -ne $liveTop)      { $recon['live_x_top']    = Test-Recon 'live_x_top'    $liveTop }
if ($null -ne $fullTree)     { $recon['full_tree_v']   = Test-Recon 'full_tree_v'   $fullTree }
if ($null -ne $attnSandbox)  { $recon['attn_sandbox']  = Test-Recon 'attn_sandbox'  $attnSandbox }
if ($null -ne $upablTop)     { $recon['upabl_top']     = Test-Recon 'upabl_top'     $upablTop }
if ($null -ne $orderMax)     { $recon['order_lines']   = Test-Recon 'order_lines'   $orderMax }
if ($null -ne $faceLiveDir)  { $recon['commit_face']   = Test-Recon 'commit_face'   $faceLiveDir }

# --- JSON 组装 -------------------------------------------------------------------
$stats = [ordered]@{
  schema       = 'cw.tree-stats/v1 (S7/PA4+PB6)'
  generated_at = (Get-Date -Format 'yyyy-MM-dd HH:mm:ss zzz')
  head_note    = $headNote
  paper_citation_caliber = @{
    fixed    = 'side_tree_top_level'
    statement= '论文引用口径固定=侧树顶层(Live_X 深度0 *.v, 沙箱系子目录天然排除); 本期实测=' + $liveTop + '; 口径定义防锈, 数值随树面时点漂移属正常(PB6)'
  }
  calibers     = [ordered]@{
    A_registration = [ordered]@{ order_lines = $orderLines; order_lines_max = $orderMax; order_consistency = $orderConsist; commit_face_live_dir = $faceLiveDir; commit_face_repo_all_v = $faceRepoAll }
    B_side_tree_top= [ordered]@{ live_x_top = $liveTop; upabl_top = $upablTop }
    C_sandbox      = [ordered]@{ attn_sandbox = $attnSandbox }
  }
  dimensions   = [ordered]@{
    full_tree_v   = $fullTree
    live_x_top    = $liveTop
    upabl_top     = $upablTop
    upabl_recursive = $upablRec
    attn_sandbox  = $attnSandbox
    order_lines   = $orderMax
    commit_face   = $faceLiveDir
  }
  decomposition_sanity = [ordered]@{
    formula = 'full_tree_v = live_x_top + subdir_v; subdir_v = attn_sandbox + expired_archive + experiment_dirs + ...'
    note    = '沙箱 363 为 09-22 双席手测同值锚——口径定义经锚定复核'
  }
  reconciliation = $recon
  fail_loud    = [ordered]@{
    rule = '|actual-manual|/manual > 5% => exit 2, 并列存证禁硬判'
    triggered = $script:FailLoud
  }
}
$json = $stats | ConvertTo-Json -Depth 8

if (-not $SelfTest) {
  if ([string]::IsNullOrEmpty($OutFile)) { $OutFile = Join-Path $PSScriptRoot 'tree-stats.json' }
  [System.IO.File]::WriteAllText($OutFile, $json, (New-Object System.Text.UTF8Encoding($false)))
  Write-Host "tree-stats.json => $OutFile"
} else {
  # 自测模式: 对账表打屏, JSON 落盘同常规(供报告贴存)
  if ([string]::IsNullOrEmpty($OutFile)) { $OutFile = Join-Path $PSScriptRoot 'tree-stats.json' }
  [System.IO.File]::WriteAllText($OutFile, $json, (New-Object System.Text.UTF8Encoding($false)))
  Write-Host '=== S7 六维×三口径 自测对账表 (实测 vs PR-B/PR-C 09-22 手测) ==='
  Write-Host ('{0,-14}{1,8} | {2:>6}/{3,-10} | {4:>6}/{5,-10} | {6}' -f 'dimension','actual','PRB','d%','PRC','d%','verdict')
  foreach ($k in $recon.Keys) {
    $r = $recon[$k]; $b = $r['PRB']; $c = $r['PRC']
    $bs = if ($b) { '{0} {1,6}%' -f $b.manual, $b.delta_pct } else { '  --' }
    $cs = if ($c) { '{0} {1,6}%' -f $c.manual, $c.delta_pct } else { '  --' }
    $allv = @(); if ($b) { $allv += $b.verdict }; if ($c) { $allv += $c.verdict }
    $v = if ($allv -contains 'FAIL(>5%)') { 'FAIL>5% 并列存证·禁硬判' } else { 'PASS(<5%)' }
    Write-Host ('{0,-14}{1,8} | {2,-16} | {3,-16} | {4}' -f $k, $r.actual, $bs, $cs, $v)
  }
  Write-Host ('order 三方一致性: {0}  |  HEAD: {1}' -f $orderConsist, $headNote)
}

if ($TamperTest) {
  if ($script:FailLoud) { Write-Host 'TamperTest: fail-loud 正确触发(退出码2预期)'; exit 2 }
  else { Write-Host 'TamperTest: 负向注入未被捕获 = 工具失效!'; exit 3 }
}
# fail-loud 门: 本地默认退出码 2(并列存证禁硬判); -CI 面(record-only)不红屏, 判定随 JSON 落盘供审计。
if ($script:FailLoud -and -not $CI) { exit 2 }
exit 0
