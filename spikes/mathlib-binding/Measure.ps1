$ErrorActionPreference = 'Stop'
$bindingRoot = 'spikes/mathlib-binding'
Set-Location -LiteralPath $bindingRoot
. './environment.ps1'
$lakeExe = '$ELAN_HOME/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe'
$bindingBuild = [IO.Path]::GetFullPath("$bindingRoot/.lake/build")
$expectedBuild = 'spikes/mathlib-binding/.lake/build'
if ($bindingBuild -ne $expectedBuild) { throw 'Unexpected build directory' }
if (Test-Path -LiteralPath $bindingBuild) {
  if ((Get-Item -LiteralPath $bindingBuild).Attributes -band [IO.FileAttributes]::ReparsePoint) { throw 'Refuse reparse-point build cleanup' }
  Remove-Item -LiteralPath $bindingBuild -Recurse -Force
}
$bindingTimings = @()
function Invoke-BindingMeasurement([string]$label, [string[]]$lakeArgs) {
  $started = [DateTime]::UtcNow.ToString('o')
  $watch = [Diagnostics.Stopwatch]::StartNew()
  & $lakeExe @lakeArgs 2>&1 | Tee-Object -FilePath "./logs/$label.log"
  $resultCode = $LASTEXITCODE
  $watch.Stop()
  $row = [pscustomobject]@{label=$label;command=('lake '+($lakeArgs -join ' '));started_utc=$started;ended_utc=[DateTime]::UtcNow.ToString('o');elapsed_seconds=$watch.Elapsed.TotalSeconds;exit_code=$resultCode}
  $script:bindingTimings += $row
  ConvertTo-Json -InputObject @($script:bindingTimings) -Depth 5 | Set-Content -LiteralPath './logs/measurements.json' -Encoding utf8
  if ($resultCode -ne 0) { throw "Failed $label" }
}
Invoke-BindingMeasurement 'clean-package-build' @('build','Binding')
Invoke-BindingMeasurement 'warm-noop-build' @('build','Binding')
foreach ($i in 1..3) { Invoke-BindingMeasurement "warm-elaboration-$i" @('env','lean','Binding.lean') }
