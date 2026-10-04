$ErrorActionPreference = 'Stop'
Set-Location -LiteralPath 'spikes/mathlib-binding'
. './environment.ps1'
$timingRows=@()
foreach($caseName in @('A08','A05')){
  $watch=[Diagnostics.Stopwatch]::StartNew()
  $started=[DateTime]::UtcNow.ToString('o')
  & '$ELAN_HOME/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env lean "${caseName}Timing.lean" -o ".lake/build/lib/lean/${caseName}Timing.olean" 2>&1|Tee-Object -FilePath "./logs/case-$caseName-elaboration.log"
  $code=$LASTEXITCODE
  $watch.Stop()
  $timingRows+=[pscustomobject]@{label="case-$caseName-elaboration";command="lake env lean ${caseName}Timing.lean -o .lake/build/lib/lean/${caseName}Timing.olean";started_utc=$started;elapsed_seconds=$watch.Elapsed.TotalSeconds;exit_code=$code}
  if($code -ne 0){throw "Case $caseName failed"}
  $watch.Restart()
  $started=[DateTime]::UtcNow.ToString('o')
  & '$ELAN_HOME/toolchains/leanprover--lean4---v4.32.1/bin/lake.exe' env leanchecker -v "${caseName}Timing" 2>&1|Tee-Object -FilePath "./logs/case-$caseName-kernel.log"
  $code=$LASTEXITCODE
  $watch.Stop()
  $timingRows+=[pscustomobject]@{label="case-$caseName-kernel-replay";command="lake env leanchecker -v ${caseName}Timing";started_utc=$started;elapsed_seconds=$watch.Elapsed.TotalSeconds;exit_code=$code}
  ConvertTo-Json -InputObject @($timingRows) -Depth 5|Set-Content -LiteralPath './logs/case-measurements.json' -Encoding utf8
  if($code -ne 0){throw "Case $caseName replay failed"}
}
