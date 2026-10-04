import GP50.Entry
import GP50.Presentation
namespace LifecycleConcerns
open GP50 Lean

-- One lifecycle-scenario/v1 object, with its literal properties retained.
structure Obj where
  key : String
  id : Nat
  category : String
  name : String
  props : List (String × Json)
def Obj.prop (o : Obj) (k : String) : Option Json := (o.props.find? (·.1 == k)).map (·.2)
def Obj.propStr (o : Obj) (k : String) : String := match o.prop k with | some (.str s) => s | _ => ""
def tombstone (o : Obj) : Bool := (o.category == "relation" || o.category == "argument") && o.props.map (·.1) == ["justification"]

-- Vocabulary-to-v0.37 field names (tools/lifecycle_inputs.py) and the pinned claim field split.
def fieldName : String → String
  | "context" => "model" | "statement_class" => "kind" | "identity_basis" => "identity_origin"
  | "coefficients_from_base" => "coefficients_in_base" | "citation" => "cite" | "statement" => "statement"
  | k => s!"unmapped:{k}"
def identifying : List String := ["kind","model","statement"]
def licensing : List String :=
  ["certificate","scope","identity_origin","lhs","rhs","ring_vars","coefficients_in_base","witness_kind","condition"]
-- Field values compare by canonical compressed JSON.
def field (o : Obj) (f : String) : Option String := (o.props.find? (fun p => fieldName p.1 == f)).map (·.2.compress)
inductive Kind where | amend | relicense | restate deriving DecidableEq, BEq, Repr
def kindName : Kind → String | .amend => "AMEND" | .relicense => "RELICENSE" | .restate => "RESTATE"
def moved (old new : Obj) (fs : List String) : List String := fs.filter fun f => field old f != field new f
-- AMEND is computed from the two records, never taken from the declaration.
def classify (old new : Obj) : Kind :=
  if !(moved old new identifying).isEmpty then .restate
  else if !(moved old new licensing).isEmpty then .relicense else .amend

theorem unmoved (old new : Obj) (fs : List String) (e : (moved old new fs).isEmpty = true) :
    ∀ f ∈ fs, field old f = field new f := by
  intro f m
  simp only [moved,List.isEmpty_iff,List.filter_eq_nil_iff] at e
  have h := e f m
  simpa using h
theorem amend_sound (old new : Obj) (h : classify old new = .amend) :
    ∀ f ∈ identifying ++ licensing, field old f = field new f := by
  unfold classify at h
  by_cases hi : (moved old new identifying).isEmpty = true
  · by_cases hl : (moved old new licensing).isEmpty = true
    · intro f member
      rcases List.mem_append.mp member with m | m
      · exact unmoved old new _ hi f m
      · exact unmoved old new _ hl f m
    · simp [hi,hl] at h
  · simp [hi] at h

-- Concern evaluators over production custody liveness.
def idOf (objs : List Obj) (name : String) : Nat := ((objs.find? (·.name == name)).map (·.id)).getD 0
def isLive (snapshot : Snapshot) (objs : List Obj) (name : String) : Bool := (eligibleIds snapshot).contains (idOf objs name)
def routeOf (o : Obj) : List String := match o.prop "transport_route" with
  | some (.arr steps) => steps.toList.filterMap fun s => match s.getObjVal? "relation" with | .ok (.str r) => some r | _ => none
  | _ => []
def liveRelation (snapshot : Snapshot) (objs : List Obj) (name : String) : Bool :=
  objs.any fun o => o.name == name && o.category == "relation" && !tombstone o && isLive snapshot objs name
def routeCleared (snapshot : Snapshot) (objs : List Obj) : Bool :=
  objs.all fun o => o.category != "argument" || tombstone o || !isLive snapshot objs o.name ||
    (routeOf o).all fun r => !snapshot.retracted.contains (idOf objs r)
def untypedCleared (snapshot : Snapshot) (objs : List Obj) : Bool :=
  objs.all fun o => o.category != "relation" || tombstone o || !isLive snapshot objs o.name ||
    o.propStr "relation_class" != "unspecified"
def contextCleared (snapshot : Snapshot) (objs : List Obj) : Bool :=
  objs.all fun o => o.category != "assertion" || !isLive snapshot objs o.name || isLive snapshot objs (o.propStr "context")

theorem routeCleared_sound (snapshot : Snapshot) (objs : List Obj) (ok : routeCleared snapshot objs = true) :
    ∀ o ∈ objs, o.category = "argument" → tombstone o = false → isLive snapshot objs o.name = true →
      ∀ r ∈ routeOf o, snapshot.retracted.contains (idOf objs r) = false := by
  intro o member cat notTomb live r route
  have each := List.all_eq_true.mp ok o member
  simp only [Bool.or_eq_true,bne_iff_ne,ne_eq,Bool.not_eq_true',cat,notTomb,live,not_true_eq_false,
    false_or,Bool.false_eq_true] at each
  rcases each with impossible | all
  · cases impossible
  · have h := List.all_eq_true.mp all r route
    simpa using h
theorem untypedCleared_sound (snapshot : Snapshot) (objs : List Obj) (ok : untypedCleared snapshot objs = true) :
    ∀ o ∈ objs, o.category = "relation" → tombstone o = false → isLive snapshot objs o.name = true →
      o.propStr "relation_class" ≠ "unspecified" := by
  intro o member cat notTomb live
  have each := List.all_eq_true.mp ok o member
  simp only [Bool.or_eq_true,bne_iff_ne,ne_eq,Bool.not_eq_true',cat,notTomb,live,not_true_eq_false,
    false_or,Bool.false_eq_true] at each
  rcases each with impossible | ok
  · cases impossible
  · exact ok
theorem contextCleared_sound (snapshot : Snapshot) (objs : List Obj) (ok : contextCleared snapshot objs = true) :
    ∀ o ∈ objs, o.category = "assertion" → isLive snapshot objs o.name = true →
      isLive snapshot objs (o.propStr "context") = true := by
  intro o member cat live
  have each := List.all_eq_true.mp ok o member
  simp only [Bool.or_eq_true,bne_iff_ne,ne_eq,Bool.not_eq_true',cat,live,not_true_eq_false,
    false_or,Bool.false_eq_true] at each
  rcases each with impossible | ok
  · cases impossible
  · exact ok
theorem liveRelation_sound (snapshot : Snapshot) (objs : List Obj) (name : String)
    (ok : liveRelation snapshot objs name = true) :
    ∃ o ∈ objs, o.name = name ∧ o.category = "relation" ∧ tombstone o = false ∧ isLive snapshot objs name = true := by
  rcases List.any_eq_true.mp ok with ⟨o,member,h⟩
  simp only [Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at h
  exact ⟨o,member,h.1.1.1,h.1.1.2,h.1.2,h.2⟩

def str (j : Json) (k : String) : Except String String := do (← j.getObjVal? k).getStr?
def decodeObjects (objects : Json) : Except String (List Obj) := do
  let entries ← match objects with | .obj kvs => pure kvs.toList | _ => throw "objects"
  entries.mapM fun (key,o) => do
    Decoder.exactFields o ["category","name","properties"]
    let id ← match (key.drop 7).toNat?, key.startsWith "object-" with
      | some n, true => pure n | _, _ => throw "unsupported object key"
    let props ← match ← o.getObjVal? "properties" with
      | .obj kvs => pure kvs.toList | _ => throw "properties"
    let category ← str o "category"
    if !(["context","relation","assertion","argument"].contains category) then throw "unsupported category"
    return ⟨key,id,category,← str o "name",props⟩

def binding (o : Obj) (source literal : String) : Binding :=
  ⟨s!"{o.category}:{o.name}","lifecycle-custody",(Json.mkObj (o.props.map fun (k,v) => (k,v))).compress,
    [source,literal],"gp50-inert-lifecycle-custody",1,1⟩
def custody (o : Obj) (source literal : String) : Warrant := ⟨o.id,o.id,1,binding o source literal,.citation o.key⟩

def buildEvents (objs : List Obj) (history : List Json) (source literal : String) : Except String (List Event) := do
  let mut out : List Event := []
  for step in history do
    let key ← str step "object"
    let some o := objs.find? (·.key == key) | throw "history object absent"
    out := out ++ [.declareClaim o.id] ++ (if tombstone o then [] else [.current ⟨o.id,1,binding o source literal⟩]) ++
      [.warrant (custody o source literal)]
    match (step.getObjVal? "replacement").toOption with
    | none => pure ()
    | some r =>
      Decoder.exactFields r ["prior","change"]
      let prior ← str r "prior"
      let some p := objs.find? (·.name == prior) | throw s!"missing replacement prior: {prior}"
      match ← str r "change" with
      | "relation_withdrawal" | "argument_retraction" =>
        if !tombstone o || o.category != p.category then throw "withdrawal must be a same-category tombstone"
        out := out ++ [.retract p.id]
      | "relation_reclassification" | "restatement" =>
        if o.category != p.category then throw "replacement changes category"
        out := out ++ [.supersede p.id o.id]
      | "annotation_only" =>
        if o.category != "assertion" || p.category != "assertion" then throw "annotation_only needs assertions"
        match classify p o with
        | .amend => out := out ++ [.supersede p.id o.id]
        | k => throw s!"annotation_only hides {kindName k}: {moved p o (identifying ++ licensing)}"
      | _ => throw "unknown replacement change"
  return out

def run (text source mode : String) : Except String Json := do
  let literal ← Decoder.parseUnique text
  Decoder.exactFields literal ["schema_version","id","seed","title","situation","inputs",
    "attempted_conclusion","expected","scope_or_region","sources"]
  if (← (← literal.getObjVal? "schema_version").getNat?) != 1 then throw "unsupported fixture schema"
  let caseId ← (← literal.getObjVal? "id").getStr?
  let inputs ← literal.getObjVal? "inputs"
  Decoder.exactFields inputs ["vocabulary","objects","history","question"]
  if (← str inputs "vocabulary") != "lifecycle-scenario/v1" then throw "unsupported vocabulary"
  if !(["normal","reverse","duplicates","reverse_duplicates"].contains mode) then throw "unknown control mode"
  let objs ← decodeObjects (← inputs.getObjVal? "objects")
  let history := (← (← inputs.getObjVal? "history").getArr?).toList
  let bound := literal.compress
  let forward ← buildEvents objs history source bound
  let mut events := forward
  if mode == "reverse" || mode == "reverse_duplicates" then events := events.reverse
  if mode == "duplicates" || mode == "reverse_duplicates" then events := events ++ events
  let state ← fold Admission.refuseAll events
  let snap := state.snapshot
  let question ← inputs.getObjVal? "question"
  let (concern,cleared) ← match (question.getObjVal? "object").toOption, (question.getObjVal? "concerns").toOption with
    | some (.str o), none => do
      if (← str question "collection") != "relations" then throw "unsupported collection"
      pure ("live_relation_query",liveRelation snap objs o)
    | none, some (.arr #[.str c]) => match c with
      | "retired_route_dependency" => pure (c,routeCleared snap objs)
      | "unresolved_relation" => pure (c,untypedCleared snap objs)
      | "retired_context_dependency" => pure (c,contextCleared snap objs)
      | _ => throw "unsupported concern"
    | none, none => do
      if question != Json.mkObj [] then throw "unsupported question"
      pure ("computed_amendment",true)
    | _, _ => throw "unsupported question"
  return Json.mkObj [("case",toJson caseId),("source_digest",toJson source),("mode",toJson mode),
    ("literal_fixture",literal),("bound_literal",toJson bound),("concern",toJson concern),
    ("cleared",toJson cleared),("identifying_fields",toJson identifying),("licensing_fields",toJson licensing),
    ("field_map",Json.mkObj ((objs.flatMap (·.props.map (·.1))).eraseDups.map fun k => (k,toJson (fieldName k)))),("live_names",toJson ((objs.filter (fun o => isLive snap objs o.name)).map (·.name))),
    ("state",stateJson state)]

#print axioms unmoved
#print axioms amend_sound
#print axioms routeCleared_sound
#print axioms untypedCleared_sound
#print axioms contextCleared_sound
#print axioms liveRelation_sound
end LifecycleConcerns

def main (args : List String) : IO UInt32 := do
  match args with
  | [path,digest,mode] =>
    let result := LifecycleConcerns.run (← IO.FS.readFile path) digest mode
    IO.println (match result with
      | .ok output => output.compress
      | .error e => (Lean.Json.mkObj [("status",Lean.toJson "MALFORMED"),("error",Lean.toJson e)]).compress)
    return 0
  | _ => return 2
