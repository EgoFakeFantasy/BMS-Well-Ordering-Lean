# 核对原证明资源的内容快照；只读，不恢复或覆盖文件。
$ErrorActionPreference = 'Stop'
$bmsRoot = [IO.Path]::GetFullPath((Join-Path $PSScriptRoot '..'))
$bmsManifest = Get-Content -Raw -LiteralPath (Join-Path $bmsRoot 'docs/legacy-resource-baseline.json') | ConvertFrom-Json
$bmsChanged = @(foreach ($bmsEntry in $bmsManifest.files) {
    $bmsPath = Join-Path $bmsRoot $bmsEntry.path
    if (-not (Test-Path -LiteralPath $bmsPath -PathType Leaf)) {
        "$($bmsEntry.path): missing"
    } elseif ((Get-FileHash -LiteralPath $bmsPath -Algorithm SHA256).Hash.ToLowerInvariant() -ne $bmsEntry.sha256) {
        "$($bmsEntry.path): changed"
    }
})
if ($bmsChanged.Count -ne 0) {
    $bmsChanged | Write-Output
    throw 'Legacy resource contents differ from the preserved local baseline; review before publication.'
}
Write-Output "Legacy resources unchanged: $($bmsManifest.files.Count) Lean files."
