# _z2_run.ps1 - 席Z2 内层 runner（单一入口；数组参数零引号嵌套，X2 卡先例）
# 用法: pwsh -File _z2_run.ps1 -Target <file.v> [-Full] [-Chk <file.vo>]
param(
  [Parameter(Mandatory=$true)][string]$Target,
  [switch]$Full,
  [string]$Chk = ""
)
$bin = "C:/Rocq-Platform~9.1~2026.01/bin"
Set-Location "D:/ComplexAnalysis/ConstructiveWorld_vo"
if ($Chk -ne "") {
  $a = @("-Q", ".", "", $Chk)
  & "$bin/coqchk.exe" @a
  exit $LASTEXITCODE
}
if ($Full) {
  $a = @("-Q", ".", "", $Target)
} else {
  $a = @("-vos", "-Q", ".", "", $Target)
}
& "$bin/coqc.exe" @a
exit $LASTEXITCODE
