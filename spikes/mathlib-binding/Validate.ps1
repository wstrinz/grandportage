$ErrorActionPreference='Stop'
Set-Location -LiteralPath 'spikes/mathlib-binding'
$expectedHashes=@{'GP-A08b'='6a390a0fbd25371e8aca0cf64fb69d892c694cb0a142a21787d4c179abf745bd';'GP-A05'='469b5e4060a64295eaaa170e8957d282404d6fc68445408e9255a430fa6170a4'}
foreach($id in $expectedHashes.Keys){if((Get-FileHash -LiteralPath "../../corpus/must/$id.json" -Algorithm SHA256).Hash.ToLower() -ne $expectedHashes[$id]){throw "Case bytes changed: $id"}}
$fragmentBinding=Get-Content -LiteralPath 'Binding.lean' -Raw
$fragmentStart=$fragmentBinding.IndexOf('/-- The exact GP-A08b')
$fragmentA05Start=$fragmentBinding.IndexOf('/-- In characteristic 2')
$fragmentEnd=$fragmentBinding.IndexOf('/-- Shows why')
if(-not (Get-Content -LiteralPath 'A08Timing.lean' -Raw).Contains($fragmentBinding.Substring($fragmentStart,$fragmentA05Start-$fragmentStart))){throw 'A08 timed proof differs'}
if(-not (Get-Content -LiteralPath 'A05Timing.lean' -Raw).Contains($fragmentBinding.Substring($fragmentA05Start,$fragmentEnd-$fragmentA05Start))){throw 'A05 timed proof differs'}
$measurements=Get-Content -LiteralPath './logs/measurements.json' -Raw|ConvertFrom-Json
$caseMeasurements=Get-Content -LiteralPath './logs/case-measurements.json' -Raw|ConvertFrom-Json
$kernel=Get-Content -LiteralPath './logs/kernel-replay-timing.json' -Raw|ConvertFrom-Json
if($measurements.Count -ne 5 -or $caseMeasurements.Count -ne 4 -or @($measurements+$caseMeasurements|Where-Object exit_code -NE 0).Count -gt 0 -or $kernel.exit_code -ne 0){throw 'Incomplete or failed final measurement'}
$audit=Get-Content -LiteralPath './logs/warm-elaboration-3.log' -Raw
$lines=@($audit -split '\r?\n'|Where-Object {$_ -match "^'Binding\..*depends on axioms:"})
if($lines.Count -ne 11 -or $audit -match 'sorryAx|_native'){throw 'Invalid final axiom audit'}
$source=Get-Content -LiteralPath 'Binding.lean' -Raw
if($source -match '\bsorry\b|\badmit\b|native_decide|\baxiom\s' -or $source -match '\[CommRing R\]'){throw 'Unexpected proof hole/native route/narrow ring assumption'}
$provenance=Get-Content -LiteralPath './logs/provenance.json' -Raw|ConvertFrom-Json
if(@($provenance.dependencies|Where-Object matches -EQ $false).Count -gt 0){throw 'Dependency pin mismatch'}
[pscustomobject]@{status='passed';corpus_hashes_unchanged=$true;dependency_heads_match=$true;final_axiom_reports=11;sorry_or_native_axiom=$false;final_measurement_exit_codes='all zero';shared_corpus_git_diff=@($provenance.corpus_git_diff)}|ConvertTo-Json -Depth 5|Set-Content -LiteralPath './logs/validation.json' -Encoding utf8
