param(
    [string]$SourceRepo = '$DEV/grand-portage',
    [string]$Commit = 'ac4155787207e2847d248cffed7be871d5dcd577'
)
$ErrorActionPreference = 'Stop'
$gpWorkspace = Split-Path -Parent $PSScriptRoot
$gpRows = @(git -C $SourceRepo ls-tree -r $Commit)
if ($LASTEXITCODE -ne 0) { throw 'Could not enumerate pinned oracle tree.' }
$gpInventory = @(
    foreach ($gpRow in $gpRows) {
        if ($gpRow -notmatch '^(\d+) (\S+) ([0-9a-f]+)\t(.+)$') { throw "Unexpected git tree row: $gpRow" }
        $gpObjectId = $Matches[3]
        $gpPath = $Matches[4]
        $gpCategory = switch -Regex ($gpPath) {
            '^tests/' { 'tests'; break }
            '(^|/)(fixtures|examples)/' { 'fixtures_examples'; break }
            '^review/' { 'release_review'; break }
            '^HISTORY/' { 'history_documents'; break }
            '^lean/' { 'lean_theory'; break }
            '(^|/)[^/]+\.md$' { 'documentation'; break }
            '^grandportage/' { 'implementation'; break }
            default { 'other' }
        }
        [pscustomobject][ordered]@{path=$gpPath; git_object=$gpObjectId; category=$gpCategory; review_status='unreviewed'}
    }
)
$gpResult = [ordered]@{
    schema_version=1
    purpose='Phase 0a source coverage inventory, not extracted cases or oracle verdicts'
    source_repo=$SourceRepo
    commit=$Commit
    generated_at_utc=[DateTime]::UtcNow.ToString('o')
    coverage_note='Pinned tree only. Historical deleted paths and prior revisions require a separate history pass.'
    sources=$gpInventory
}
$gpResult | ConvertTo-Json -Depth 6 | Set-Content -LiteralPath (Join-Path $gpWorkspace 'corpus\SOURCE-INVENTORY.json') -Encoding utf8
$gpInventory | Group-Object category | Sort-Object Name | Select-Object Name,Count
"Total tracked paths: $($gpInventory.Count)"
