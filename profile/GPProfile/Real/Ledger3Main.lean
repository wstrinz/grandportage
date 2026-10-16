import GPProfile.Real.Ledger3

/-!
The `gp_ledger3` executable: `GPProfile.Real.LedgerRun3` on stdin (`--guard`: the merge guard). The runner's
definitions stay in `GPProfile.Real.Ledger3`, so the Lane P runner can import them (GP 0.52 P2).
-/

open GPProfile.Real in
def main (args : List String) : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut text := ""
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    text := text ++ line
  match Lean.Json.parse text with
  | .error e => IO.eprintln s!"gp_ledger3: input is not JSON: {e}"; return 2
  | .ok plan =>
    let run := if args.contains "--guard" then LedgerRun3.guardLedger3 else LedgerRun3.runLedger3
    IO.println (run plan).compress; return 0
