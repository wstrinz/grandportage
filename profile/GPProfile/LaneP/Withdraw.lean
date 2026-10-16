import GPProfile.Withdraw

/-!
Withdrawal for Lane P (design §6, W3P). A P claim `k` files its warrants at ids
`pWarrantId k slot = 2^61 + 16·k + slot` with `slot < 16`: theorem 0, discharge 1, weakening 2,
recorded-only citations 3. Withdrawing `k` retracts all sixteen slots. Claim keys stay below 2^53, so
these ids never meet the 3a/3b ranges (`k` and `2^60 + k`).

W1 and W2 are generic in the admission (`GPProfile.Withdraw.resolve_retracts`,
`reachable_of_retracting`); W3P is `withdraw_unholdsP`. Mathlib-free.
-/

namespace GPProfile.LaneP
open GP50 GPProfile.Withdraw

def pBase : Nat := 2 ^ 61

def pWarrantId (key slot : Nat) : Nat := pBase + 16 * key + slot

def withdrawTargetsP (ks : List Nat) : List Nat :=
  ks.flatMap fun k => (List.range 16).map (pWarrantId k)

def withdrawEventsP (ks : List Nat) : List Event := (withdrawTargetsP ks).map Event.retract

/-- Every warrant of the log sits in one of its claim's sixteen P slots. -/
def ProfileIdsP (l : List Event) : Prop :=
  ∀ w, Event.warrant w ∈ l → ∃ s, s < 16 ∧ w.id = pWarrantId w.claim s

/-- W1P: a P withdrawal only un-holds. -/
theorem withdraw_antitoneP (a : Admission) (l : List Event) (ks : List Nat) (hl : NoSupersede l)
    (s' : RuntimeState) (h : fold a (l ++ withdrawEventsP ks) = .ok s') :
    ∃ s, fold a l = .ok s ∧ ∀ k, held s' k = true → held s k = true := by
  unfold withdrawEventsP fold at h
  unfold fold
  rw [resolve_retracts l _ hl] at h
  cases hr : resolve l with
  | error e => simp [hr, Except.map] at h
  | ok snap =>
    simp only [hr, Except.map, except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    refine ⟨_, rfl, fun k hk => ?_⟩
    subst h
    obtain ⟨w, hw, hc, hreach⟩ := (held_evaluate_iff a _ k).mp hk
    exact (held_evaluate_iff a snap k).mpr ⟨w, hw, hc,
      reachable_of_retracting ⟨rfl, fun x hx => by simp [mem_canonicalIds, hx]⟩ a hreach⟩

/-- W2P: a log without supersessions that resolves still resolves with P withdrawals added. -/
theorem withdraw_resolvesP (l : List Event) (ks : List Nat) (hl : NoSupersede l)
    (h : ∃ s, resolve l = .ok s) : ∃ s', resolve (l ++ withdrawEventsP ks) = .ok s' := by
  obtain ⟨s, hs⟩ := h
  unfold withdrawEventsP
  rw [resolve_retracts l _ hl, hs]
  exact ⟨_, rfl⟩

/-- W3P: a withdrawn P claim is not held. -/
theorem withdraw_unholdsP (a : Admission) (l : List Event) (ks : List Nat) (hl : NoSupersede l)
    (hids : ProfileIdsP l) {k : Nat} (hk : k ∈ ks) (s : RuntimeState)
    (h : fold a (l ++ withdrawEventsP ks) = .ok s) : held s k = false := by
  unfold withdrawEventsP fold at h
  rw [resolve_retracts l _ hl] at h
  cases hr : resolve l with
  | error e => simp [hr, Except.map] at h
  | ok snap =>
    simp only [hr, Except.map, except_bind_ok, pure, Except.pure, Except.ok.injEq] at h
    subst h
    cases hh : held (evaluate a _) k
    · rfl
    obtain ⟨w, hw, hc, hreach⟩ := (held_evaluate_iff a _ k).mp hh
    obtain ⟨w', _, hid, hlive⟩ := reachable_live hreach
    obtain ⟨sl, hsl, hwid⟩ := hids w (resolve_warrant_mem l snap hr w hw)
    have hin : w.id ∈ withdrawTargetsP ks :=
      List.mem_flatMap.mpr ⟨k, hk, List.mem_map.mpr ⟨sl, List.mem_range.mpr hsl, by rw [hwid, hc]⟩⟩
    simp [live, mem_canonicalIds, hid, hin] at hlive

end GPProfile.LaneP
