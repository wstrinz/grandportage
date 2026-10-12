import Lean.Data.Json

/-!
Pinned fixtures for the 3b corpus (C5). A case names a fixture by the SHA-256 of its bytes; the
runner finds the file through `oracle/history/PIN.json`, recomputes the digest and attaches the
parsed fixture to the case only when the bytes match the pin. Mutation cases describe one edit of
the fixture (`set` a value at a path, `reverse` an array), which `applyMutation` performs.

This is custody, not mathematics: nothing here is trusted for a verdict. A held claim's meaning
comes from the checker replaying the statement built from the attached fixture; the digest only
decides which bytes that statement is built from and which receipt it may bind.
-/

namespace GPProfile.Real
open Lean

/-! ## SHA-256 (FIPS 180-4) -/

namespace Sha256

def k : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def h0 : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- The message, padded to a multiple of 64 bytes with its bit length. -/
def pad (msg : ByteArray) : ByteArray := Id.run do
  let len := msg.size
  let mut out := msg.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  let bits := len * 8
  for i in [0:8] do
    out := out.push ((bits >>> (8 * (7 - i))) % 256).toUInt8
  out

/-- One 64-byte block at `off`. -/
def compress (h : Array UInt32) (b : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let byte (j : Nat) : UInt32 := (b.get! (off + 4 * i + j)).toUInt32
    w := w.push ((byte 0 <<< 24) ||| (byte 1 <<< 16) ||| (byte 2 <<< 8) ||| byte 3)
  for i in [16:64] do
    let x := w[i - 15]!
    let y := w[i - 2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i - 16]! + s0 + w[i - 7]! + s1)
  let mut a := h[0]!
  let mut bb := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + s1 + ch + k[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& bb) ^^^ (a &&& c) ^^^ (bb &&& c)
    let t2 := s0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := bb
    bb := a
    a := t1 + t2
  #[h[0]! + a, h[1]! + bb, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

def hexWord (x : UInt32) : String :=
  let s := String.ofList (Nat.toDigits 16 x.toNat)
  "".pushn '0' (8 - s.length) ++ s

/-- The lowercase hexadecimal SHA-256 digest of `msg`. -/
def hex (msg : ByteArray) : String := Id.run do
  let b := pad msg
  let mut h := h0
  for i in [0:b.size / 64] do
    h := compress h b (64 * i)
  String.join (h.toList.map hexWord)

end Sha256

/-! ## Mutations -/

/-- Apply `f` at `path` (object keys and array indices) inside `j`. -/
def jsonAt (f : Json → Except String Json) : List Json → Json → Except String Json
  | [], j => f j
  | step :: rest, j =>
    match step, j with
    | .str key, .obj _ => do
      let v ← match j.getObjVal? key with
        | .ok v => pure v
        | .error _ => throw s!"mutation path: no key '{key}'"
      pure (j.setObjVal! key (← jsonAt f rest v))
    | idx, .arr a => do
      let i ← match idx.getNat? with
        | .ok i => pure i
        | .error _ => throw "mutation path: expected an array index"
      unless i < a.size do throw "mutation path: index out of range"
      pure (.arr (a.set! i (← jsonAt f rest a[i]!)))
    | _, _ => throw "mutation path does not fit the fixture"

/-- `{op: "set", path, value}` or `{op: "reverse", path}`. -/
def applyMutation (fixture mutation : Json) : Except String Json := do
  let path ← (← mutation.getObjVal? "path").getArr?
  match (mutation.getObjVal? "op").toOption.bind (·.getStr?.toOption) with
  | some "set" => jsonAt (fun _ => mutation.getObjVal? "value") path.toList fixture
  | some "reverse" =>
    jsonAt (fun j => match j with | .arr a => pure (.arr a.reverse) | _ => throw "reverse needs an array")
      path.toList fixture
  | _ => throw "unknown mutation op"

/-! ## Attaching a pinned fixture (runner, IO) -/

/-- Attach the fixture a case pins by `inputs.fixture_sha256` as the case's `fixture` field, when
`oracle/history/PIN.json` lists a file with that digest and its bytes hash to it. Otherwise the case
is returned unchanged (and its C5 route stays pending). -/
def attachFixture (root : System.FilePath) (case : Json) : IO Json := do
  let some sha := (do (← (← case.getObjVal? "inputs").getObjVal? "fixture_sha256").getStr?).toOption
    | return case
  let pin ← IO.ofExcept (Json.parse (← IO.FS.readFile (root / "oracle" / "history" / "PIN.json")))
  let files := ((pin.getObjVal? "files") >>= Json.getArr?).toOption.getD #[]
  let some entry := files.find? fun f => (f.getObjValAs? String "sha256").toOption == some sha | return case
  let some path := (entry.getObjValAs? String "path").toOption | return case
  let bytes ← IO.FS.readBinFile (root / "oracle" / "history" / "checkout" / path)
  unless Sha256.hex bytes == sha do return case
  let some text := String.fromUTF8? bytes | return case
  let some fixture := (Json.parse text).toOption | return case
  return case.setObjVal! "fixture" fixture

end GPProfile.Real
