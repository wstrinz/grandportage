/-
# The backend is evidence, not authority

M2 introduces a semantic backend seam. This file states the trust boundary
without mentioning Singular: raw process success, parsing, certificate
production, decision-procedure checking, verifier-native structural checking,
independent certificate checking, and verdict freshness are different facts.

Python has three honest authority paths. Certificate-bearing answers are checked
by replayable arithmetic independent of the search that found them. Direct
normal-form decisions are inside the backend/verifier trusted computing base.
Some structural decisions are verifier-native and spawn no backend execution.
All three modes must be explicit and current; process success or parsing alone
is neither.
-/

namespace GrandPortage

universe u v w

/-- What one backend invocation retained. `claimedSuccess` is deliberately only
    data supplied by the execution layer; it proves no mathematics. -/
structure BackendArtifact (Raw : Type u) (Parsed : Type v)
    (Certificate : Type w) where
  claimedSuccess : Bool
  raw : Raw
  parsed : Option Parsed
  certificate : Option Certificate

/-- A certificate is checked against the parsed semantic answer. This is the
    replayable arithmetic side of the boundary, not the search that found the
    answer. -/
def IndependentlyChecked
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (artifact : BackendArtifact Raw Parsed Certificate)
    (checker : Parsed -> Certificate -> Prop) : Prop :=
  Exists fun parsed => Exists fun certificate =>
    artifact.parsed = some parsed /\
    artifact.certificate = some certificate /\
    checker parsed certificate

/-- Some semantic answers are direct decisions (for example a normal-form
    reduction), not certificate searches. Their checker is part of the named,
    versioned backend/verifier TCB and must accept the parsed answer explicitly. -/
def DecisionChecked
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (artifact : BackendArtifact Raw Parsed Certificate)
    (checker : Parsed -> Prop) : Prop :=
  Exists fun parsed => artifact.parsed = some parsed /\ checker parsed

/-- A verifier-native structural decision has no backend parse to retain. The
    proposition must still be established by the named, versioned verifier. -/
def StructurallyChecked (checker : Prop) : Prop := checker

/-- The three evidence modes Python actually implements. Keeping the disjunction
    visible prevents a trusted decision procedure or a structural fact from
    being misdescribed as independent certificate checking. -/
def Validated
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (artifact : BackendArtifact Raw Parsed Certificate)
    (certificateChecker : Parsed -> Certificate -> Prop)
    (decisionChecker : Parsed -> Prop)
    (structuralChecker : Prop) : Prop :=
  IndependentlyChecked artifact certificateChecker \/
  DecisionChecked artifact decisionChecker \/
  StructurallyChecked structuralChecker

/-- Executable authority requires validation plus freshness for the
    verifier/kernel/backend/input provenance. -/
def Licenses
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (current : Prop)
    (artifact : BackendArtifact Raw Parsed Certificate)
    (certificateChecker : Parsed -> Certificate -> Prop)
    (decisionChecker : Parsed -> Prop)
    (structuralChecker : Prop) : Prop :=
  current /\ Validated artifact certificateChecker decisionChecker
    structuralChecker

/-- A process may say success while producing no parseable semantic answer.
    That fact alone cannot license either backend evidence mode, and supplies
    no structural verification. -/
theorem backend_success_without_parse_does_not_license
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (raw : Raw) (certificateChecker : Parsed -> Certificate -> Prop)
    (decisionChecker : Parsed -> Prop) :
    Not (Licenses True
      { claimedSuccess := true, raw := raw, parsed := none,
        certificate := none }
      certificateChecker decisionChecker False) := by
  intro h
  rcases h.2 with hcert | hrest
  · rcases hcert with ⟨parsed, certificate, hparsed, _⟩
    cases hparsed
  · rcases hrest with hdecision | hstructural
    · rcases hdecision with ⟨parsed, hparsed, _⟩
      cases hparsed
    · exact hstructural

/-- Parsing is not validation. With no certificate, with the direct checker
    refusing, and with no structural proof, a parsed assertion is not authority. -/
theorem parsed_answer_without_validation_does_not_license
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (raw : Raw) (parsed : Parsed)
    (certificateChecker : Parsed -> Certificate -> Prop) :
    Not (Licenses True
      { claimedSuccess := true, raw := raw, parsed := some parsed,
        certificate := none }
      certificateChecker (fun _ => False) False) := by
  intro h
  rcases h.2 with hcert | hrest
  · rcases hcert with ⟨_, certificate, _, hcertificate, _⟩
    cases hcertificate
  · rcases hrest with hdecision | hstructural
    · rcases hdecision with ⟨_, _, impossible⟩
      exact impossible
    · exact hstructural

/-- Even valid old evidence is non-authoritative once its provenance is stale.
    It remains useful history; it simply cannot license transport. -/
theorem stale_validated_artifact_does_not_license
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (artifact : BackendArtifact Raw Parsed Certificate)
    (certificateChecker : Parsed -> Certificate -> Prop)
    (decisionChecker : Parsed -> Prop) (structuralChecker : Prop) :
    Not (Licenses False artifact certificateChecker decisionChecker
      structuralChecker) := by
  intro h
  exact h.1

/-- Fresh independently checked certificate evidence licenses its scoped use. -/
theorem independently_checked_current_artifact_licenses
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (artifact : BackendArtifact Raw Parsed Certificate)
    (certificateChecker : Parsed -> Certificate -> Prop)
    (decisionChecker : Parsed -> Prop) (structuralChecker : Prop)
    (current : Prop) (hcurrent : current)
    (hchecked : IndependentlyChecked artifact certificateChecker) :
    Licenses current artifact certificateChecker decisionChecker
      structuralChecker :=
  ⟨hcurrent, Or.inl hchecked⟩

/-- A fresh answer accepted by the named direct decision procedure also
    licenses its scoped use, while making that TCB assumption explicit. -/
theorem decision_checked_current_artifact_licenses
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (artifact : BackendArtifact Raw Parsed Certificate)
    (certificateChecker : Parsed -> Certificate -> Prop)
    (decisionChecker : Parsed -> Prop) (structuralChecker : Prop)
    (current : Prop) (hcurrent : current)
    (hchecked : DecisionChecked artifact decisionChecker) :
    Licenses current artifact certificateChecker decisionChecker
      structuralChecker :=
  ⟨hcurrent, Or.inr (Or.inl hchecked)⟩

/-- A fresh verifier-native structural proof licenses without pretending that a
    backend process ran. -/
theorem structurally_checked_current_decision_licenses
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (artifact : BackendArtifact Raw Parsed Certificate)
    (certificateChecker : Parsed -> Certificate -> Prop)
    (decisionChecker : Parsed -> Prop) (structuralChecker : Prop)
    (current : Prop) (hcurrent : current)
    (hchecked : StructurallyChecked structuralChecker) :
    Licenses current artifact certificateChecker decisionChecker
      structuralChecker :=
  ⟨hcurrent, Or.inr (Or.inr hchecked)⟩

/-- Changing the process success label cannot create any validation mode. -/
theorem success_label_irrelevant_to_validation
    {Raw : Type u} {Parsed : Type v} {Certificate : Type w}
    (artifact : BackendArtifact Raw Parsed Certificate)
    (certificateChecker : Parsed -> Certificate -> Prop)
    (decisionChecker : Parsed -> Prop) (structuralChecker : Prop)
    (label : Bool) :
    Validated { artifact with claimedSuccess := label }
        certificateChecker decisionChecker structuralChecker <->
    Validated artifact certificateChecker decisionChecker structuralChecker := by
  rfl

end GrandPortage