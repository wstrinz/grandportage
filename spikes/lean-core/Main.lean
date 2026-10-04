import Spike
open Lean Spike
def main (args : List String) : IO UInt32 := do
  let input ← match args with
    | [path] => IO.FS.readFile path
    | _ => (← IO.getStdin).readToEnd
  let lines := (input.splitOn "\n").filter (fun l => !l.trimAscii.toString.isEmpty)
  let out ← IO.getStdout
  match foldLines lines.toArray with
  | .error e => out.putStrLn (Json.mkObj [("status", toJson "REFUSE"),("error",toJson e)]).compress
                return 2
  | .ok s => out.putStrLn (Json.mkObj [("status",toJson "OK"),("claims",summary s)]).compress
             return 0
