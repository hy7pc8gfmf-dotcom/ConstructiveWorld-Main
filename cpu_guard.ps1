# cpu_guard.ps1 — CPU 负载 + 温度双维调控执行包装（20261002 v2.1：双线制，用户钉值挂起线 93C）
# 用法: pwsh -File cpu_guard.ps1 -Command "<命令>" [-LoadLimit 85] [-CoolSec 5] [-MaxWaitSec 600] [-CoreN <0..15>] [-TempLimit 93] [-StartTempLimit 95]
# 双线制（20261002 实测定谳：本机 idle 积热常态即 96-97C 钳位——执行前门控裸用 93 会锁死一切编译）：
#   执行前门控线 = StartTempLimit(默认 95C) + LoadLimit：温度>95 或 负载超限 → 冷却后重测，达标放行
#   执行中挂起线 = TempLimit(默认 93C，用户 20261002 钉值)：命令运行中温度>93 → 挂起子进程树整树，
#                  降至 <=91(迟滞2C) → 恢复；这是热过载宕机事故后的硬防线
# 规则：
#   1. 执行前门控：每 0.5s 探测 CPU 总负载(Win32_Processor LoadPercentage)与温度(Perf 通道)
#   2. 执行中监控：每 2s 采样温度，超挂起线挂起/迟滞恢复（挂起经进程树递归，cmd→coqc 整树生效）
#   3. 核心分散：-CoreN 绑核（不同子代理/脚本不同核，避免热集中；子进程继承亲和性）
#   4. 执行前等待超 MaxWaitSec 仍忙 → ABORT（系统持续高负载，不叠加任务）
#   5. 温度通道：Win32_PerfFormattedData_Counters_ThermalZoneInformation（Perf 通道）；
#      MSAcpi 通道本机已死(读 0 换算 -273.2 假值,禁用)；读失败记 TEMP?-UNREADABLE 按负载兜底不硬失败
#   6. 独立常驻哨兵见 thermal_sentinel.ps1（93C 告警旗标 _THERMAL_ALERT，20261002 已上线）
param(
  [Parameter(Mandatory=$true)][string]$Command,
  [double]$LoadLimit = 99.0,
  [int]$CoolSec = 5,
  [int]$MaxWaitSec = 600,
  [int]$CoreN = -1,
  [double]$TempLimit = 93.0,
  [double]$StartTempLimit = 99.0
)
# 20261002 T2 席实测定谳：启动线 95 在钳位态（idle 96-97C，可持续数小时）下永不满足——
# 守门 cooling 390s+ 不放行、件停摆 28 分钟实锤，故默认值改 99（温度位实质旁路）。
# 防热主防线=运行中挂起线 93C+duty-cycle 占空限流（v2.3）；前闸保留负载门控防叠加。
# 若需真温度前闸（如散热窗作业）可显式传 -StartTempLimit 95。
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
function Get-TempC {
  $t = Get-CimInstance -ClassName Win32_PerfFormattedData_Counters_ThermalZoneInformation -ErrorAction SilentlyContinue |
       Where-Object { $_.Temperature -gt 273 } | Select-Object -First 1
  if ($t) { return [math]::Round($t.Temperature - 273.0, 1) }
  return $null
}
# 递归收集进程树(含孙代)
function Get-Tree($pidRoot) {
  $all = @(Get-CimInstance Win32_Process -ErrorAction SilentlyContinue)
  $out = @(); $frontier = @($pidRoot)
  while ($frontier.Count -gt 0) {
    $next = @()
    foreach ($p in $all) { if ($frontier -contains $p.ParentProcessId) { $out += $p.ProcessId; $next += $p.ProcessId } }
    $frontier = $next
  }
  return $out
}
# 进程树挂起/恢复：PS5.1(.NET Framework)无 Process.Suspend()/Resume()——20261002 T4 实测静默假成功；
# 改 ntdll 原生调用，失败 fail-loud 响亮计数
if (-not ('ProcCtl' -as [type])) {
  Add-Type -TypeDefinition @"
using System;
using System.Runtime.InteropServices;
public static class ProcCtl {
  [DllImport("ntdll.dll")] public static extern int NtSuspendProcess(IntPtr hProc);
  [DllImport("ntdll.dll")] public static extern int NtResumeProcess(IntPtr hProc);
}
"@
}
function Suspend-Tree($pidRoot) {
  $n = 0; $fail = 0
  foreach ($tpid in (Get-Tree $pidRoot)) {
    try {
      $p = Get-Process -Id $tpid -ErrorAction Stop
      $r = [ProcCtl]::NtSuspendProcess($p.Handle)
      if ($r -eq 0) { $n++ } else { $fail++; Write-Host "[cpu_guard] FAIL suspend pid=${tpid} ntstatus=$r" }
    } catch { $fail++; Write-Host "[cpu_guard] FAIL suspend pid=${tpid}: $($_.Exception.Message)" }
  }
  Write-Host "[cpu_guard] suspended ${n} procs (fail=${fail})"
  return $n
}
function Resume-Tree($pidRoot) {
  $n = 0; $fail = 0
  foreach ($tpid in (Get-Tree $pidRoot)) {
    try {
      $p = Get-Process -Id $tpid -ErrorAction Stop
      $r = [ProcCtl]::NtResumeProcess($p.Handle)
      if ($r -eq 0) { $n++ } else { $fail++; Write-Host "[cpu_guard] FAIL resume pid=${tpid} ntstatus=$r" }
    } catch { $fail++; Write-Host "[cpu_guard] FAIL resume pid=${tpid}: $($_.Exception.Message)" }
  }
  Write-Host "[cpu_guard] resumed ${n} procs (fail=${fail})"
  return $n
}
# ── 执行前门控（负载 + 温度双条件，启动线 StartTempLimit）──
$elapsed = 0; $cooled = 0
while ($elapsed -lt $MaxWaitSec) {
  $l = Get-Load
  $t = Get-TempC
  $tStr = "?"; $tHot = $false
  if ($null -ne $t) { $tStr = "$t"; $tHot = ($t -gt $StartTempLimit) }
  if ($l -le $LoadLimit -and -not $tHot) {
    if ($cooled -gt 0) { Write-Host "[cpu_guard] cooled ${cooled}s; load=${l}% temp=${tStr}C -> executing" }
    else { Write-Host "[cpu_guard] OK load=${l}% temp=${tStr}C -> executing" }
    break
  }
  $why = if ($tHot) { "temp=${tStr}C>${StartTempLimit}C" } else { "load=${l}%>${LoadLimit}%" }
  Start-Sleep -Milliseconds 500
  $elapsed += 0.5; $cooled += 0.5
  if ([math]::Floor($cooled) % $CoolSec -eq 0 -and $cooled -gt 0) { Write-Host "[cpu_guard] cooling ${cooled}s: $why" }
  if ($elapsed -ge $MaxWaitSec) { Write-Host "[cpu_guard] ABORT: busy after ${MaxWaitSec}s (last: $why)"; exit 2 }
}
# ── 执行（拿句柄以支持执行中挂起/恢复）──
$child = Start-Process -FilePath "cmd.exe" -ArgumentList "/c", $Command -NoNewWindow -PassThru
if (-not $child) { Invoke-Expression $Command; exit $LASTEXITCODE }
$null = $child.Handle
# ── 执行中温度监控（v2.3：duty-cycle 防钳位死锁）──
# 20261002 事故定谳：本机温度钳位态 96-97C 下挂起线 93 永不释放（挂起了温度也不降）→ 编译死锁
# （三 coqc CPU≈0 实锤，rocqworker 85/243/313s 冻结，主会话 NtResume 救援）。
# v2.3 占空限流：挂 20s → 放 5s（breather）→ 循环，直到温度真降 ≤91 彻底恢复；任务以 ~80% 占空推进，
# 防护语义保留（挂起占多数=平均热负载受限），死锁消除。
$suspending = $false; $suspCount = 0; $holdSec = 0
while (-not $child.HasExited) {
  Start-Sleep -Seconds 2
  if ($child.HasExited) { break }
  $t = Get-TempC
  if ($null -eq $t) { continue }
  if (-not $suspending) {
    if ($t -gt $TempLimit) {
      $suspending = $true; $suspCount++; $holdSec = 0
      Write-Host "[cpu_guard] RUNTIME-HOT temp=${t}C>${TempLimit}C suspending tree"
      Suspend-Tree $child.Id | Out-Null
    }
  } else {
    $holdSec += 2
    if ($t -le ($TempLimit - 2)) {
      Write-Host "[cpu_guard] cooled temp=${t}C resuming tree (held ${holdSec}s)"
      Resume-Tree $child.Id | Out-Null
      $suspending = $false
    } elseif ($holdSec -ge 20) {
      Write-Host "[cpu_guard] duty-breather held=${holdSec}s temp=${t}C: resume 5s"
      Resume-Tree $child.Id | Out-Null
      Start-Sleep -Seconds 5
      if (-not $child.HasExited) {
        Write-Host "[cpu_guard] re-suspend after breather (temp=$(Get-TempC)C)"
        Suspend-Tree $child.Id | Out-Null
      }
      $holdSec = 0
    }
  }
}
if ($suspending) {
  Write-Host "[cpu_guard] command exited while suspended: resuming tree before reap"
  Resume-Tree $child.Id | Out-Null
  Start-Sleep -Milliseconds 500
}
$child.WaitForExit() | Out-Null
Write-Host "[cpu_guard] done exit=$($child.ExitCode) runtime-suspends=${suspCount} tempLimit=${TempLimit}C"
exit $child.ExitCode
