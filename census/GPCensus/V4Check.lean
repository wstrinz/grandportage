import GPCensus.V4
import LRATCatcher.Reflect

/-!
The DK V4 checks (`docs/DK-V4-DESIGN.md`), over decoded objects; `GPCensus.Profile` decodes and
delegates.

- `V4Count`: exactly `m` isomorphism classes among the members of `InS pts a0 φ`.
- `v4ListedOk` holds it outright: representatives that are members with their actions and have
  pairwise-distinct canonical forms, centralising relabellings, every model of the listing CNF
  matched to a representative's canonical form, and an LRAT refutation of the CNF with all models
  blocked.
- `v4CatalogOk` holds it given a complete catalog: the catalog's members, with their actions,
  pairwise distinct. Completeness stays a visible premise of the statement (CELL-COMPLETE for the
  n = 23 cells).
-/

namespace GPCensus
open Hex Hex.GraphIso

variable {n k : Nat}

/-- Exactly `m` isomorphism classes meet the members. -/
def V4Count (n k pts : Nat) (a0 : List (List Nat)) (φ : Formula) (m : Nat) : Prop :=
  ∃ Hs : List (Colored n k), Hs.length = m ∧ (∀ H ∈ Hs, InS pts a0 φ H) ∧
    Hs.Pairwise (fun a b => ¬ Isomorphic a b) ∧
    ∀ G : Colored n k, InS pts a0 φ G → ∃ H ∈ Hs, Isomorphic G H

/-- Representatives: members by their actions, pairwise-distinct canonical forms, `m` of them. -/
def repsOk (pts : Nat) (a0 : List (List Nat)) (φ : Formula) (m : Nat)
    (reps : List (Colored n k × List (List Nat))) : Bool :=
  reps.all (fun r => memberB pts a0 φ r.1 r.2) && reps.length == m &&
    decide ((reps.map fun r => canon r.1).Nodup)

def v4ListedOk (pts : Nat) (a0 : List (List Nat)) (φ : Formula) (m : Nat) (Bs : List (Colored n k))
    (reps : List (Colored n k × List (List Nat))) (ls : List (Label n)) (proof : String) : Bool :=
  decide (2 ≤ k) && repsOk pts a0 φ m reps &&
    Bs.all (fun B => (reps.map fun r => canon r.1).contains (canon B)) &&
    ls.all (centB pts a0) && LRATCatcher.checkLratCnf (v4ListCnf n k pts a0 φ ls Bs) proof

theorem repsOk_facts {pts : Nat} {a0 : List (List Nat)} {φ : Formula} {m : Nat}
    {reps : List (Colored n k × List (List Nat))} (h : repsOk pts a0 φ m reps = true) :
    (reps.map (·.1)).length = m ∧ (∀ H ∈ reps.map (·.1), InS pts a0 φ H) ∧
      (reps.map (·.1)).Pairwise (fun a b => ¬ Isomorphic a b) := by
  simp only [repsOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨hmem, hlen⟩, hnd⟩ := h
  have hnd' : ((reps.map (·.1)).map canon).Nodup := by
    rw [List.map_map]; exact hnd
  refine ⟨by simpa using hlen, fun H hH => ?_, pairwise_noniso_of_canon hnd'⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hH
  exact memberB_sound (hmem r hr)

theorem v4ListedOk_sound {pts : Nat} {a0 : List (List Nat)} {φ : Formula} {m : Nat}
    {Bs : List (Colored n k)} {reps : List (Colored n k × List (List Nat))} {ls : List (Label n)}
    {proof : String} (h : v4ListedOk pts a0 φ m Bs reps ls proof = true) : V4Count n k pts a0 φ m := by
  simp only [v4ListedOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨hk, hreps⟩, hcover⟩, hls⟩, hlrat⟩ := h
  obtain ⟨hlen, hmem, hpw⟩ := repsOk_facts hreps
  refine ⟨reps.map (·.1), hlen, hmem, hpw, fun G hG => ?_⟩
  have complete := v4_listed_of_unsat hk (fun l hl => centB_sound (hls l hl))
    (LRATCatcher.checkLratCnf_sound _ _ hlrat)
  obtain ⟨B, hB, hGB⟩ := complete G hG
  have hc := hcover B hB
  simp only [List.contains_iff_mem, List.mem_map] at hc
  obtain ⟨r, hr, hcr⟩ := hc
  refine ⟨r.1, List.mem_map_of_mem hr, hGB.trans ?_⟩
  exact (iso_iff_canon_eq _ _).mpr hcr.symm

theorem v4CatalogOk_sound {pts : Nat} {a0 : List (List Nat)} {φ : Formula} {m : Nat}
    {reps : List (Colored n k × List (List Nat))} (h : repsOk pts a0 φ m reps = true)
    (hcomplete : ∀ G : Colored n k, InS pts a0 φ G → ∃ H ∈ reps.map (·.1), Isomorphic G H) :
    V4Count n k pts a0 φ m := by
  obtain ⟨hlen, hmem, hpw⟩ := repsOk_facts h
  exact ⟨reps.map (·.1), hlen, hmem, hpw, hcomplete⟩

end GPCensus
