import GP50.Entry
open GP50
private def binding (input : String := "v1") : Binding :=
  ⟨"statement", "scope", "model", [input], "test-seam", 1, 1⟩
private def current (claim : Nat) (version : Nat := 1) (b : Binding := binding) : Event :=
  .current ⟨claim, version, b⟩
private def warrant (id claim : Nat) (evidence : Evidence)
    (version : Nat := 1) (b : Binding := binding) : Event :=
  .warrant ⟨id, claim, version, b, evidence⟩
-- Explicit component test seams, not sound admitted mathematics or corpus passes.
private def fixtureAdmission : Admission := {
  receipt := fun w data => w.binding.authority == "test-seam" && data == "checked"
  proof := fun _ _ => false
  rule := fun _ premises side => !premises.isEmpty && side == "registered"
  narrow := fun w premise => w.binding.statementHash == premise.binding.statementHash &&
    w.binding.modelHash == premise.binding.modelHash && w.binding.scopeHash == "narrow" &&
    premise.binding.scopeHash == "scope" }
private def heldClaims (events : List Event) (a : Admission := fixtureAdmission) :
    Except String (List Nat) := do
  return (← fold a events).claims
private def equals (value : Except String (List Nat)) (expected : List Nat) : Bool :=
  match value with | .ok got => got == expected | .error _ => false
private def ensure (name : String) (condition : Bool) : IO Unit := do
  if !condition then throw (IO.userError s!"FAILED: {name}")
  IO.println s!"PASS: {name}"
def main : IO Unit := do
  let root := [current 1, warrant 10 1 (.receipt "checked")]
  ensure "default admission is fail closed" (equals (heldClaims root .refuseAll) [])
  ensure "validated component receipt reaches its claim" (equals (heldClaims root) [1])
  ensure "unvalidated receipt is blocked"
    (equals (heldClaims [current 1, warrant 10 1 (.receipt "claimed-success")]) [])
  ensure "proof declaration pointer alone is blocked"
    (equals (heldClaims [current 1, warrant 10 1 (.theoremWarrant "True.intro")]) [])
  ensure "assertion citation and every absent attempt stay inert"
    (([Evidence.assertion, .citation "source", .attempt .absent,
      .attempt .failed, .attempt .timeout]).all fun e =>
        equals (heldClaims [current 1, warrant 10 1 e]) [])
  ensure "missing current binding blocks even checked data"
    (equals (heldClaims [warrant 10 1 (.receipt "checked")]) [])
  ensure "new explicit input version stales old receipt"
    (equals (heldClaims (root ++ [current 1 2 (binding "v2")])) [])
  let independent := root ++ [warrant 11 1 (.receipt "checked")]
  ensure "targeted retraction preserves independent support"
    (equals (heldClaims (independent ++ [.retract 10])) [1])
  ensure "all supports retracted removes claim"
    (equals (heldClaims (independent ++ [.retract 10, .retract 11])) [])
  ensure "failed retry leaves earlier current success"
    (equals (heldClaims (root ++ [warrant 11 1 (.attempt .failed)])) [1])
  let derived := root ++ [current 2, warrant 20 2 (.derived [10] "registered")]
  ensure "registered derived support reaches unasserted conclusion"
    (equals (heldClaims derived) [1,2])
  ensure "retracting a particular premise blocks its dependent"
    (equals (heldClaims (derived ++ [warrant 11 1 (.receipt "checked"), .retract 10])) [1])
  ensure "missing premise cannot be replaced by a claim-level neighbor"
    (equals (heldClaims (root ++ [current 2, warrant 20 2 (.derived [99] "registered")])) [1])
  ensure "unregistered rule is blocked"
    (equals (heldClaims (root ++ [current 2, warrant 20 2 (.derived [10] "prose")])) [1])
  ensure "conjunctive rule needs every reached premise"
    (equals (heldClaims (root ++ [current 3, warrant 30 3 (.assertion),
      current 2, warrant 20 2 (.derived [10,30] "registered")])) [1])
  let cycle := [current 1, current 2, warrant 10 1 (.derived [20] "registered"),
    warrant 20 2 (.derived [10] "registered")]
  ensure "registered circular rules cannot bootstrap authority" (equals (heldClaims cycle) [])
  let narrowBinding := {binding with scopeHash := "narrow"}
  let narrowed := root ++ [current 2 1 narrowBinding,
    warrant 20 2 (.narrow 10) 1 narrowBinding]
  ensure "validated narrowing depends on actual source support"
    (equals (heldClaims narrowed) [1,2] && equals (heldClaims (narrowed ++ [.retract 10])) [])
  let wrongObject := {narrowBinding with statementHash := "different-object"}
  ensure "narrowing cannot change statement objects"
    (equals (heldClaims (root ++ [current 2 1 wrongObject,
      warrant 20 2 (.narrow 10) 1 wrongObject])) [1])
  ensure "full event reversal preserves held membership"
    (equals (heldClaims derived.reverse) [1,2])
  ensure "duplicate events are idempotent"
    (equals (heldClaims (derived ++ derived)) [1,2])
  ensure "superseding with an absent attempt does not inherit authority"
    (equals (heldClaims (root ++ [warrant 11 1 (.attempt .timeout), .supersede 10 11])) [])
  let wire := "{\"schema_version\":1,\"events\":[{\"kind\":\"current\",\"value\":{\"claim\":1,\"version\":1,\"binding\":{\"statementHash\":\"statement\",\"scopeHash\":\"scope\",\"modelHash\":\"model\",\"inputHashes\":[\"v1\"],\"authority\":\"test-seam\",\"authorityVersion\":1,\"kernelVersion\":1}}},{\"kind\":\"warrant\",\"value\":{\"id\":10,\"claim\":1,\"version\":1,\"binding\":{\"statementHash\":\"statement\",\"scopeHash\":\"scope\",\"modelHash\":\"model\",\"inputHashes\":[\"v1\"],\"authority\":\"test-seam\",\"authorityVersion\":1,\"kernelVersion\":1},\"evidence\":{\"kind\":\"receipt\",\"data\":\"checked\"}}}]}"
  ensure "raw JSON decoder to fold to held succeeds through test validator"
    (match decodeFold fixtureAdmission wire with
      | .ok state => held state 1 && !held state 2
      | .error _ => false)
  ensure "duplicate discriminant cannot enter held pipeline"
    (match decodeFold fixtureAdmission "{\"schema_version\":1,\"events\":[{\"kind\":\"unknown\",\"kind\":\"declare_claim\",\"claim\":1}]}" with
      | .error _ => true | .ok _ => false)
  IO.println "Runtime: 23 component controls passed; no corpus or checker admission claim."

