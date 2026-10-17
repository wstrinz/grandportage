import Lean

/-!
The Lane P binder (`gp_bindp`; design §1, §3). Lean core only. `gp bind` runs it inside a campaign
package with `lake env`, after `lake build`. It imports the package's modules and **elaborates
nothing**: no user text is parsed, no tactic runs and no initializer executes.

For each registered code it reports whether the declaration exists and is a `Prop`, and a canonical
serialization of every campaign-local constant in its closure (types and definition bodies; theorem
types only). `gp` hashes each with SHA-256 into the code's closure hash; pinned dependencies are
covered by the environment stamp (toolchain and manifest revisions).

For each `lean_theorem` warrant it builds `thmDecl (type := P₁ → … → Pₙ → S, value := const T)` from the
registered codes and asks the Lean kernel to add it. The kernel's definitional check unfolds the
registered statements, so a statement mismatch fails in the kernel. It also collects `T`'s axioms by
walking the constants themselves; anything beyond `propext`, `Quot.sound` and `Classical.choice`
(`sorryAx`, `Lean.ofReduceBool`, a custom axiom) refuses the warrant.

P2 (GP 0.52):
- For each Comparator challenge it finds the challenge theorem in its emitted module and checks that its type is
  exactly the claim's `P₁ → … → Pₙ → S` built from the registered codes (`Expr` equality up to binder names), so the
  emitter is not trusted. The receipt's other checks (pins, log, challenge SHA-256) are gp's.
- For each bridge code it asks the kernel to add `X ↔ GPBinding.LaneP.meaning3 "<literal>" := Iff.refl X`: the code's
  definition is the literal 3a/3b meaning (`BridgeSound`), checked without elaborating anything.

usage: gp_bindp <input.json>   (prints the report as JSON)
-/

namespace GPProfile.LaneP.Binder
open Lean

def standardAxioms : List Name := [``propext, ``Quot.sound, ``Classical.choice]

structure Ser where
  ids : Std.HashMap Expr Nat := {}
  lines : Array String := #[]

partial def level : Level → String
  | .zero => "0"
  | .succ l => s!"(s {level l})"
  | .max a b => s!"(max {level a} {level b})"
  | .imax a b => s!"(imax {level a} {level b})"
  | .param n => s!"(p {n})"
  | .mvar _ => "(?)"

/-- A shared-subterm (DAG) serialization: each distinct subterm is one line, numbered in DFS order.
Binder names, binder info and metadata are not semantic and are left out. -/
partial def expr (e : Expr) : StateM Ser Nat := do
  if let .mdata _ x := e then return ← expr x
  if let some i := (← get).ids.get? e then return i
  let body ← match e with
    | .bvar i => pure s!"b {i}"
    | .fvar _ => pure "fvar"
    | .mvar _ => pure "mvar"
    | .sort l => pure s!"S {level l}"
    | .const n ls => pure s!"C {n} {ls.map level}"
    | .app f a => do pure s!"A {← expr f} {← expr a}"
    | .lam _ t b _ => do pure s!"L {← expr t} {← expr b}"
    | .forallE _ t b _ => do pure s!"P {← expr t} {← expr b}"
    | .letE _ t v b _ => do pure s!"D {← expr t} {← expr v} {← expr b}"
    | .lit (.natVal n) => pure s!"N {n}"
    | .lit (.strVal s) => pure s!"T {s.quote}"
    | .mdata _ x => do pure s!"M {← expr x}"
    | .proj s i x => do pure s!"J {s} {i} {← expr x}"
  let st ← get
  set { st with ids := st.ids.insert e st.lines.size, lines := st.lines.push body }
  return st.lines.size

/-- A constant's canonical text and the constants it uses (theorems: the type only). -/
def constant (info : ConstantInfo) : String × Array Name :=
  let serial (kind : String) (es : List Expr) (extra : String) : String :=
    let (roots, st) := (es.mapM expr).run {}
    s!"{kind} {info.levelParams}{extra} roots {roots}\n" ++ "\n".intercalate st.lines.toList
  let used (es : List Expr) : Array Name := es.foldl (fun acc e => acc ++ e.getUsedConstants) #[]
  match info with
  | .defnInfo v => (serial "def" [v.type, v.value] "", used [v.type, v.value])
  | .opaqueInfo v => (serial "opaque" [v.type, v.value] "", used [v.type, v.value])
  | .thmInfo v => (serial "theorem" [v.type] "", used [v.type])
  | .axiomInfo v => (serial "axiom" [v.type] "", used [v.type])
  | .quotInfo v => (serial "quot" [v.type] "", used [v.type])
  | .inductInfo v =>
    (serial "inductive" [v.type] s!" params {v.numParams} indices {v.numIndices} ctors {v.ctors}",
      used [v.type] ++ v.ctors.toArray)
  | .ctorInfo v => (serial "ctor" [v.type] s!" of {v.induct} idx {v.cidx}", used [v.type])
  | .recInfo v => (serial "rec" [v.type] "", used [v.type])

def isLocal (env : Environment) (roots : List Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => match env.header.moduleNames[idx.toNat]? with
    | some m => roots.contains m.getRoot
    | none => false
  | none => false

/-- The campaign-local closure of `start`, as (name, canonical text), in BFS order. -/
def closure (env : Environment) (roots : List Name) (start : Name) : Array (Name × String) := Id.run do
  let mut seen : NameSet := NameSet.empty.insert start
  let mut queue : Array Name := #[start]
  let mut out : Array (Name × String) := #[]
  let mut i := 0
  while h : i < queue.size do
    let n := queue[i]
    i := i + 1
    let some info := env.find? n | continue
    let (text, used) := constant info
    out := out.push (n, text)
    for m in used do
      if !seen.contains m && isLocal env roots m then
        seen := seen.insert m
        queue := queue.push m
  return out

/-- Every axiom `start` depends on, by walking the constants themselves (no precomputed tables). -/
def axiomsOf (env : Environment) (start : Name) : Array Name := Id.run do
  let mut seen : NameSet := NameSet.empty.insert start
  let mut stack : Array Name := #[start]
  let mut axs : Array Name := #[]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    let some info := env.find? n | continue
    if info matches .axiomInfo _ then axs := axs.push n
    let es : List Expr := info.type :: (info.value? (allowOpaque := true)).toList
    let more : Array Name := match info with
      | .inductInfo v => v.ctors.toArray
      | _ => #[]
    for m in es.foldl (fun acc e => acc ++ e.getUsedConstants) more do
      if !seen.contains m then
        seen := seen.insert m
        stack := stack.push m
  return axs.qsort Name.lt

structure Code where
  code : Nat
  kind : String
  decl : Name
  of : Nat

def codeExpr (codes : List Code) : Nat → Nat → Except String Expr
  | 0, _ => throw "negation nesting too deep"
  | fuel + 1, c => do
    let some k := codes.find? (·.code == c) | throw s!"unregistered code {c}"
    match k.kind with
    | "lean" => pure (.const k.decl [])
    | "not" => pure (mkApp (.const ``Not []) (← codeExpr codes fuel k.of))
    | other => throw s!"code {c} is {other}, not a Lean statement"

def theoremType (codes : List Code) (stmt : Nat) (premises : List Nat) : Except String Expr := do
  let s ← codeExpr codes 8 stmt
  premises.foldrM (fun p acc => do pure (.forallE `h (← codeExpr codes 8 p) acc .default)) s

def moduleOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some idx => (env.header.moduleNames[idx.toNat]?.map (·.toString)).getD ""
  | none => ""

/-- Ask the kernel to add `name : type := value`; "ok" or its message. -/
def kernelAdd (env : Environment) (name : Name) (lps : List Name) (type value : Expr) : IO String :=
  match Environment.addDeclCore env 200000000 512 (.thmDecl (mkTheoremValEx name lps type value [name])) none with
  | .ok _ => pure "ok"
  | .error e => (e.toMessageData {}).toString

def run (input : Json) : IO Json := do
  let get {α} [FromJson α] (j : Json) (k : String) : IO α := IO.ofExcept (j.getObjValAs? α k)
  let roots : List Name := (← get (α := List String) input "roots").map String.toName
  let imports : Array Import := ((← get (α := List String) input "imports").map fun m =>
    ({ module := m.toName } : Import)).toArray
  let codes ← (← get (α := List Json) input "codes").mapM fun j => do
    pure ({ code := ← get j "code", kind := ← get j "kind",
            decl := ((j.getObjValAs? String "decl").toOption.getD "").toName,
            of := (j.getObjValAs? Nat "of").toOption.getD 0 } : Code)
  initSearchPath (← findSysroot)
  let env ← importModules imports {} (trustLevel := 0)
  let codeRows ← codes.mapM fun c => do
    if c.kind != "lean" then
      return Json.mkObj [("code", toJson c.code), ("kind", toJson c.kind)]
    match env.find? c.decl with
    | none => return Json.mkObj [("code", toJson c.code), ("found", toJson false)]
    | some info =>
      let isProp := info.type == .sort .zero && info.levelParams.isEmpty && isLocal env roots c.decl
      let cl := closure env roots c.decl
      return Json.mkObj [("code", toJson c.code), ("found", toJson true), ("prop", toJson isProp),
        ("module", toJson (moduleOf env c.decl)),
        ("closure", Json.arr (cl.map fun (n, t) => Json.arr #[toJson n.toString, toJson t]))]
  let mut thmRows : Array Json := #[]
  let mut i := 0
  for t in ← get (α := List Json) input "theorems" do
    i := i + 1
    let id : String ← get t "id"
    let decl : Name := (← get (α := String) t "decl").toName
    let stmt : Nat ← get t "stmt"
    let premises : List Nat ← get t "premises"
    let some info := env.find? decl
      | thmRows := thmRows.push (Json.mkObj [("id", toJson id), ("found", toJson false)]); continue
    let axs := axiomsOf env decl
    let axiomsOk := axs.all standardAxioms.contains
    let kernel ← match theoremType codes stmt premises with
      | .error e => pure s!"type: {e}"
      | .ok ty =>
        let lps := info.levelParams
        kernelAdd env (Name.mkSimple s!"_gp_lanep_check_{i}") lps ty (.const decl (lps.map Level.param))
    thmRows := thmRows.push (Json.mkObj [("id", toJson id), ("found", toJson true),
      ("axioms", toJson (axs.map (·.toString))), ("axiomsOk", toJson axiomsOk), ("kernel", toJson kernel),
      ("module", toJson (moduleOf env decl))])
  -- Comparator challenges: the emitted theorem's type is exactly the claim's (P2).
  let mut chalRows : Array Json := #[]
  for c in (input.getObjValAs? (List Json) "challenges").toOption.getD [] do
    let id : String ← get c "id"
    let decl : Name := (← get (α := String) c "decl").toName
    let module : String ← get c "module"
    let typeOk ← match env.find? decl, theoremType codes (← get c "stmt") (← get c "premises") with
      | some info, .ok ty => pure (info.levelParams.isEmpty && info.type == ty)
      | _, _ => pure false
    chalRows := chalRows.push (Json.mkObj [("id", toJson id), ("found", toJson (env.contains decl)),
      ("module", toJson (moduleOf env decl == module)), ("typeOk", toJson typeOk)])
  -- Bridge codes: the definition is the literal 3a/3b meaning, `X ↔ meaning3 lit` by `Iff.refl` (P2).
  let mut bridgeRows : Array Json := #[]
  for b in (input.getObjValAs? (List Json) "bridges").toOption.getD [] do
    let code : Nat ← get b "code"
    let decl : Name := (← get (α := String) b "decl").toName
    let lit : String ← get b "lit"
    let meaning := mkApp (.const `GPBinding.LaneP.meaning3 []) (mkStrLit lit)
    -- Syntactic first, so the kernel never has to evaluate `meaning3` on two different literals.
    let kernel ← match env.find? `GPBinding.LaneP.meaning3, env.find? decl with
      | none, _ => pure "GPBinding.LaneP.meaning3 is not imported"
      | _, none => pure s!"{decl} is missing"
      | some _, some info =>
        if info.value?.map (· == meaning) != some true then
          pure s!"{decl} is not `meaning3` of this literal"
        else
          let ty := mkApp2 (.const ``Iff []) (.const decl []) meaning
          kernelAdd env (Name.mkSimple s!"_gp_lanep_bridge_{code}") [] ty (mkApp (.const ``Iff.refl []) (.const decl []))
    bridgeRows := bridgeRows.push (Json.mkObj [("code", toJson code), ("kernel", toJson kernel)])
  return Json.mkObj [("schema", "gp-bindp/v1"), ("lean", toJson Lean.versionString),
    ("githash", toJson Lean.githash), ("codes", Json.arr codeRows.toArray), ("theorems", Json.arr thmRows),
    ("challenges", Json.arr chalRows), ("bridges", Json.arr bridgeRows)]

end GPProfile.LaneP.Binder

def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let input ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
    IO.println (← GPProfile.LaneP.Binder.run input).compress
    return 0
  | _ => IO.eprintln "usage: gp_bindp <input.json>"; return 2
