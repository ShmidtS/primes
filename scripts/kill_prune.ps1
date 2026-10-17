$ErrorActionPreference = 'SilentlyContinue'
Get-CimInstance Win32_Process | Where-Object { $_.CommandLine -match 'prune_mathlib_v3' } | ForEach-Object {
  Write-Output ("KILL bash " + $_.ProcessId)
  Stop-Process -Id $_.ProcessId -Force
}
Get-Process lake, lean -ErrorAction SilentlyContinue | ForEach-Object {
  Write-Output ("KILL " + $_.ProcessName + " " + $_.Id)
  Stop-Process -Id $_.Id -Force
}
Write-Output DONE
