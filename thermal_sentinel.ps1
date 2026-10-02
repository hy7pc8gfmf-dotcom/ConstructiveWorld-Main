# thermal_sentinel.ps1 — 温度监控哨兵（20261001 重建，用户钉值上限 93C）
# 用法: powershell -File thermal_sentinel.ps1 [-TempLimit 93] [-IntervalSec 10] [-LogFile <csv>]
# 行为:
#   1. 每 IntervalSec 读 Perf 通道温度(Win32_PerfFormattedData_Counters_ThermalZoneInformation)
#      —— MSAcpi 通道本机已死(读 0 换算出 -273.2 假值,禁用)
#   2. 追加 _THERMAL_log.csv (时间,温度C[,ALERT])
#   3. 温度 > TempLimit → 写 _THERMAL_ALERT 旗标(时间+Top3 负载进程),回落 <=TempLimit-2 自动清除
#   4. 读失败连续计数,失败行记 ERR 不刷假值;存 _THERMAL_SENTINEL_STOP 旗标即退出
param(
  [double]$TempLimit = 93.0,
  [int]$IntervalSec = 10,
  [string]$LogFile = "D:\ComplexAnalysis\新算法实践\attn\_THERMAL_log.csv",
  [string]$AlertFlag = "D:\ComplexAnalysis\新算法实践\attn\_THERMAL_ALERT",
  [string]$StopFlag = "D:\ComplexAnalysis\新算法实践\attn\_THERMAL_SENTINEL_STOP"
)
function Get-TempC {
  $t = Get-CimInstance -ClassName Win32_PerfFormattedData_Counters_ThermalZoneInformation -ErrorAction SilentlyContinue |
       Where-Object { $_.Temperature -gt 273 } | Select-Object -First 1
  if ($t) { return [math]::Round($t.Temperature - 273.0, 1) }
  return $null
}
$failStreak = 0
$alerting = $false
Write-Host "[thermal_sentinel] started limit=${TempLimit}C interval=${IntervalSec}s log=$LogFile"
while ($true) {
  if (Test-Path $StopFlag) { Write-Host "[thermal_sentinel] stop flag seen, exiting"; exit 0 }
  $ts = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
  $c = Get-TempC
  if ($null -eq $c) {
    $failStreak++
    if ($failStreak -ge 3) { Add-Content -Path $LogFile -Value "$ts,ERR" }
  } else {
    $failStreak = 0
    if ($c -gt $TempLimit) {
      Add-Content -Path $LogFile -Value "$ts,$c,ALERT"
      if (-not $alerting) {
        $alerting = $true
        $top = Get-Process | Sort-Object CPU -Descending | Select-Object -First 3 |
               ForEach-Object { "$($_.Id):$($_.ProcessName)" }
        Set-Content -Path $AlertFlag -Value "$ts TEMP=$c LIMIT=$TempLimit top=$($top -join ' ')"
        Write-Host "[thermal_sentinel] ALERT ${c}C > ${TempLimit}C flag written"
      }
    } else {
      Add-Content -Path $LogFile -Value "$ts,$c"
      if ($alerting -and $c -le ($TempLimit - 2)) {
        $alerting = $false
        Remove-Item $AlertFlag -ErrorAction SilentlyContinue
        Write-Host "[thermal_sentinel] recovered ${c}C, alert cleared"
      }
    }
  }
  Start-Sleep -Seconds $IntervalSec
}
