import Spike.Poly
import Spike.Lrat
open Lean
def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  match args with
  | ["poly", path] =>
    let input ← IO.FS.readFile path
    match Json.parse input >>= Spike.Poly.candidate with
    | .error e => out.putStrLn (Json.mkObj [("status",toJson "REFUSE"),("error",toJson e)]).compress; return 2
    | .ok b => out.putStrLn (Json.mkObj [("valid",toJson b)]).compress; return if b then 0 else 1
  | ["external", python, script, path] =>
    let input ← IO.FS.readFile path
    let result ← IO.Process.output {cmd := python, args := #[script]} (some input)
    match Json.parse result.stdout with
    | .error _ => out.putStrLn "{\"valid\":false,\"error\":\"invalid child JSON\"}"; return 2
    | .ok j =>
      let binding := (j.getObjVal? "request" >>= Json.getStr?).toOption == some input
      let version := (j.getObjVal? "checker" >>= Json.getStr?).toOption == some "fraction-cofactor-v1"
      let valid := (j.getObjVal? "valid" >>= Json.getBool?).toOption == some true
      let ok := result.exitCode == 0 && binding && version && valid
      out.putStrLn (Json.mkObj [("valid",toJson ok),("binding",toJson binding),("version",toJson version),("exit_code",toJson result.exitCode.toNat)]).compress
      return if ok then 0 else 1
  | ["lrat", path, kind] =>
    let proof ← IO.FS.readFile path
    let f := if kind == "unsat" then Spike.Lrat.cnf else Spike.Lrat.satCnf
    match Spike.Lrat.parseAndCheck proof f with
    | .error e => out.putStrLn (Json.mkObj [("status",toJson "REFUSE"),("error",toJson e)]).compress; return 2
    | .ok b => out.putStrLn (Json.mkObj [("valid",toJson b)]).compress; return if b then 0 else 1
  | _ => out.putStrLn "usage: poly PATH | external PYTHON SCRIPT PATH | lrat PATH unsat/sat"; return 2
