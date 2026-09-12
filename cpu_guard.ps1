# cpu_guard.ps1 — CPU 负载调控执行包装（替代温度方式，更可行）
# 用法: pwsh -File cpu_guard.ps1 -Command "<命令>" [-LoadLimit 85] [-CoolSec 5] [-MaxWaitSec 600] [-CoreN <0..15>]
# 规则：
#   1. 每 0.5s 探测 CPU 总负载（Win32_Processor LoadPercentage，稳定可读）
#   2. 总负载 > LoadLimit(默认 85%) → 冷却 CoolSec(5s)，冷却中持续探测，≤ 阈值恢复执行
#   3. 核心分散：-CoreN 绑核（不同子代理/脚本不同核，避免热集中；子进程继承亲和性）
#   4. 超 MaxWaitSec 仍忙 → ABORT（系统持续高负载，不叠加任务）
# 注：温度传感器（ACPI）在本机不可信（恒定 97°C 不随负载变化）——改用 CPU 负载调控。
param(
  [Parameter(Mandatory=$true)][string]$Command,
  [double]$LoadLimit = 99.0,
  [int]$CoolSec = 5,
  [int]$MaxWaitSec = 600,
  [int]$CoreN = -1
)
# 核心分散：绑定指定逻辑核
if ($CoreN -ge 0) {
  $nproc = [Environment]::ProcessorCount
  if ($CoreN -lt $nproc) {
    try {
      $proc = [System.Diagnostics.Process]::GetCurrentProcess()
      $proc.ProcessorAffinity = [IntPtr](([int64]1) -shl $CoreN)
      Write-Host "[cpu_guard] pinned to core $CoreN"
    } catch { Write-Host "[cpu_guard] affinity failed: $($_.Exception.Message)" }
  }
}
function Get-Load { [math]::Round(((Get-CimInstance Win32_Processor | Measure-Object -Property LoadPercentage -Average).Average), 1) }
$elapsed = 0; $cooled = 0
while ($elapsed -lt $MaxWaitSec) {
  $l = Get-Load
  if ($l -le $LoadLimit) {
    if ($cooled -gt 0) { Write-Host "[cpu_guard] cooled ${cooled}s; load=${l}% -> executing" }
    else { Write-Host "[cpu_guard] OK load=${l}% -> executing" }
    Invoke-Expression $Command
    exit $LASTEXITCODE
  }
  Start-Sleep -Milliseconds 500
  $elapsed += 0.5; $cooled += 0.5
  if ([math]::Floor($cooled) % $CoolSec -eq 0 -and $cooled -gt 0) { Write-Host "[cpu_guard] cooling ${cooled}s: load=${l}% > ${LoadLimit}%" }
}
Write-Host "[cpu_guard] ABORT: load > ${LoadLimit}% after ${MaxWaitSec}s"
exit 2




