import GP50.Runtime
namespace GP50.Queries

inductive Reason where
  | inactiveCustody | refusedOrUnregisteredEvidence
  | missingPremiseRecord (id : Nat) | unsupportedPremise (id : Nat)
  deriving Repr, BEq, DecidableEq

structure WarrantDiagnostic where
  id : Nat
  supported : Bool
  reasons : List Reason
  deriving Repr, BEq, DecidableEq

structure WhyNot where
  claim : Nat
  held : Bool
  warrants : List WarrantDiagnostic
  deriving Repr, BEq, DecidableEq

structure Earned where
  claim : Nat
  openObligations : List Nat
  deriving Repr, BEq, DecidableEq

def declaredPremises (w : Warrant) : List Nat :=
  match w.evidence with
  | .derived deps _ => deps | .narrow dep => [dep] | _ => []

-- requirements supplies opaque admission status; physical absence is separate.
def diagnose (admission : Admission) (state : RuntimeState) (w : Warrant) : WarrantDiagnostic :=
  let deps := canonicalIds (declaredPremises w)
  let missing := deps.filter fun id => (lookupWarrant state.snapshot id).isNone
  let unsupported := deps.filter fun id =>
    (lookupWarrant state.snapshot id).isSome && !state.supports.contains id
  let inactive := !live state.snapshot w
  let refused := !inactive && missing.isEmpty && (requirements admission state.snapshot w).isNone
  ⟨w.id, state.supports.contains w.id,
    (if inactive then [.inactiveCustody] else []) ++
    (if refused then [.refusedOrUnregisteredEvidence] else []) ++
    missing.map Reason.missingPremiseRecord ++ unsupported.map Reason.unsupportedPremise⟩

-- Use the same admission as evaluate/fold; domain registration does not mean claimed.
def whyNot (admission : Admission) (state : RuntimeState) (claim : Nat) : WhyNot :=
  ⟨claim, GP50.held state claim,
    ((state.snapshot.warrants.filter fun w => w.claim == claim).map
      (diagnose admission state)).eraseDups.mergeSort (fun a b => a.id ≤ b.id)⟩

-- Caller links/open IDs rank diagnostics only; they never alter runtime authority.
def earned (state : RuntimeState) (claimed : List Nat)
    (links : List (Nat × List Nat)) (openIds : List Nat) : List Earned :=
  ((canonicalIds state.claims).filter fun claim => !claimed.contains claim).map (fun claim =>
    ⟨claim, canonicalIds (((links.filter fun link => link.1 == claim).flatMap (·.2)).filter
      fun id => openIds.contains id)⟩) |>.mergeSort fun a b =>
        a.openObligations.length > b.openObligations.length ||
        (a.openObligations.length == b.openObligations.length && a.claim ≤ b.claim)

end GP50.Queries
