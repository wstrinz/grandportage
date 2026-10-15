import GP50.RuntimeProofs
import GPProfile.Real.Plan

/-!
Claim withdrawal (GP 0.51, docs/WITHDRAWAL-DESIGN.md §2–3). Withdrawing claim `k` appends
`withdrawEvents [k]`, the Kernel's `retract k` and `retract (theoremWarrantId k)`, to the log both folds
read (`Plan.runWith`, `Plan3.run`); `Ledger.events` itself stays `Guard.Simple`. The Kernel is unchanged.

Held claims keep their meaning after any withdrawal: `Semantic.fold_held_meaning`,
`GPBinding.Admission.fold_held_meaning` and `GPBinding.Real.fold_held_meaning3` quantify over every event
list. The obligations proved here are the design's three:
- W1 `withdraw_antitone`: anything held after the retracts are added was held before;
- W2 `withdraw_resolves`: a log with no supersede events that resolves still resolves with them, so a
  withdrawal never breaks a fold, a filing or a merge;
- W3 `withdraw_unholds`: a withdrawn key is not held, for every log with the profile's warrant ids
  (`ProfileIds`), and so for every 3a and 3b run (`runWith_withdrawn`, `run3_withdrawn`).

Mathlib-free; audited in CI by `tests/test_gp50_axiom_audit.py`.
-/

namespace GPProfile.Withdraw
open GP50 GPProfile GPProfile.Real

/-! ## Retracts appended to a log without supersessions -/

/-- A log with no supersede events: every log the profile files (`noSupersede_of_simple`). -/
def NoSupersede (l : List Event) : Prop := ∀ e ∈ l, ∀ a b, e ≠ .supersede a b

theorem noSupersede_of_simple {l : List Event} (h : Guard.Simple l) : NoSupersede l := by
  intro e he a b heq
  have := h e he
  subst heq
  simp [Guard.simple] at this

/-- The ids withdrawal retracts: each key and its theorem warrant id. -/
def withdrawTargets (ks : List Nat) : List Nat := ks.flatMap fun k => [k, theoremWarrantId k]

theorem withdrawEvents_eq (ks : List Nat) : withdrawEvents ks = (withdrawTargets ks).map Event.retract := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [withdrawEvents, withdrawTargets] at ih ⊢; exact ih

theorem filterMap_none {α β : Type} (xs : List α) : xs.filterMap (fun _ => (none : Option β)) = [] :=
  List.filterMap_eq_nil_iff.mpr fun _ _ => rfl

/-- Appending retracts to a log without supersessions changes only the retracted set. -/
theorem resolve_retracts (l : List Event) (ts : List Nat) (hl : NoSupersede l) :
    resolve (l ++ ts.map Event.retract) =
      (resolve l).map fun s => { s with retracted := canonicalIds (s.retracted ++ ts) } := by
  have hlinks : ∀ (f : Event → Option (Nat × Nat)), (∀ e, (∀ a b, e ≠ .supersede a b) → f e = none) →
      l.filterMap f = [] := fun f hf =>
    List.filterMap_eq_nil_iff.mpr fun e he => hf e (hl e he)
  unfold resolve
  simp only [currentsIn, warrantsIn, List.filterMap_append, List.filterMap_map, Function.comp_def]
  rw [hlinks _ (fun e he => by cases e <;> simp_all)]
  simp only [filterMap_none, List.filterMap_some, List.append_nil, List.eraseDups_nil, List.mergeSort_nil,
    List.forIn_nil, bind, Except.bind, pure, Except.pure, Except.map]
  split
  · rfl
  · split
    · rfl
    · simp only [Except.ok.injEq, Snapshot.mk.injEq, true_and, and_true]
      apply EventOrder.canonicalIds_eq_of_mem_iff
      intro x
      simp [mem_canonicalIds]

/-! ## Retracting more only removes support -/

/-- `s'` is `s` with a retracted set containing `s`'s. -/
def Retracting (s s' : Snapshot) : Prop :=
  s' = { s with retracted := s'.retracted } ∧ ∀ x ∈ s.retracted, x ∈ s'.retracted

theorem live_of_retracting {s s' : Snapshot} (h : Retracting s s') {w : Warrant} (hl : live s' w = true) :
    live s w = true := by
  obtain ⟨heq, hsub⟩ := h
  rw [heq] at hl
  simp only [live, Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hl ⊢
  refine ⟨⟨⟨hl.1.1.1, ?_⟩, hl.1.2⟩, hl.2⟩
  cases hc : s.retracted.contains w.id
  · rfl
  · exact absurd (hsub _ (List.contains_iff_mem.mp hc)) (by simpa using hl.1.1.2)

theorem requirements_of_retracting {s s' : Snapshot} (h : Retracting s s') (a : Admission) {w : Warrant}
    {deps : List Nat} (hr : requirements a s' w = some deps) : requirements a s w = some deps := by
  have hl : live s' w = true := by
    cases hw : live s' w
    · simp [requirements, hw] at hr
    · rfl
  have hlookup : lookupWarrant s' = lookupWarrant s := by rw [h.1]; rfl
  unfold requirements at hr ⊢
  rw [hlookup] at hr
  simpa [live_of_retracting h hl, hl] using hr

theorem reachable_of_retracting {s s' : Snapshot} (h : Retracting s s') (a : Admission) {id : Nat}
    (hr : Reachable (supportNodes a s') id) : Reachable (supportNodes a s) id := by
  induction hr with
  | @fire node deps member req _ ih =>
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp member
    have hw' : w ∈ s.warrants := by rw [h.1] at hw; exact hw
    exact Reachable.fire (node := ⟨w.id, requirements a s w⟩) (List.mem_map.mpr ⟨w, hw', rfl⟩)
      (requirements_of_retracting h a req) ih

/-! ## W1 and W2 -/

/-- W1: withdrawal only un-holds. Anything held after the retracts are added was held before. -/
theorem withdraw_antitone (a : Admission) (l : List Event) (ks : List Nat) (hl : NoSupersede l)
    (s' : RuntimeState) (h : fold a (l ++ withdrawEvents ks) = .ok s') :
    ∃ s, fold a l = .ok s ∧ ∀ k, held s' k = true → held s k = true := by
  rw [withdrawEvents_eq] at h
  unfold fold at h ⊢
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

/-- W2: a log with no supersede events that resolves still resolves with withdrawals added, so a withdrawal
never breaks a fold, a filing or a merge. -/
theorem withdraw_resolves (l : List Event) (ks : List Nat) (hl : NoSupersede l) (h : ∃ s, resolve l = .ok s) :
    ∃ s', resolve (l ++ withdrawEvents ks) = .ok s' := by
  obtain ⟨s, hs⟩ := h
  rw [withdrawEvents_eq, resolve_retracts l _ hl, hs]
  exact ⟨_, rfl⟩

/-! ## W3 -/

theorem warrantFor_mem {values : List Warrant} {id : Nat} {w : Warrant} (found : warrantFor values id = .ok w) :
    w ∈ values := by
  unfold warrantFor at found
  split at found <;> try contradiction
  rename_i value restEq
  have eqValue : value = w := Except.ok.inj found
  subst w
  have member : value ∈ (values.filter fun w => w.id == id).eraseDups := by rw [restEq]; simp
  exact (List.mem_filter.mp (eraseDups_mem_source _ _ member)).1

theorem mapM_mem {α β : Type} {f : α → Except String β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ xs, f x = .ok y
  | [], ys, h, y, hy => by
    change Except.ok [] = Except.ok ys at h; cases h; simp at hy
  | x :: xs, ys, h, y, hy => by
    cases hx : f x with
    | error e => simp [List.mapM_cons, hx] at h
    | ok z =>
      cases hxs : xs.mapM f with
      | error e => simp [List.mapM_cons, hx, hxs] at h
      | ok zs =>
        have hys : z :: zs = ys := by simpa [List.mapM_cons, hx, hxs] using h
        subst hys
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨x, List.mem_cons_self, hx⟩
        · obtain ⟨x', hx', hf⟩ := mapM_mem hxs y hy
          exact ⟨x', List.mem_cons_of_mem _ hx', hf⟩

/-- A resolved snapshot's warrants are warrants of the log. -/
theorem resolve_warrant_mem (events : List Event) (snapshot : Snapshot) (resolved : resolve events = .ok snapshot) :
    ∀ w ∈ snapshot.warrants, Event.warrant w ∈ events := by
  unfold resolve at resolved
  cases currentMap : (canonicalIds ((currentsIn events).map (·.claim))).mapM (currentFor (currentsIn events)) with
  | error message => simp only [currentMap, except_bind_error] at resolved; contradiction
  | ok currents =>
    simp only [currentMap, except_bind_ok] at resolved
    cases warrantMap : (canonicalIds ((warrantsIn events).map (·.id))).mapM (warrantFor (warrantsIn events)) with
    | error message => simp only [warrantMap, except_bind_error] at resolved; contradiction
    | ok warrants =>
      simp only [warrantMap, except_bind_ok] at resolved
      have snapshotEq := except_return_constant _ _ _ resolved
      rw [← congrArg Snapshot.warrants snapshotEq]
      intro w hw
      obtain ⟨_, _, hf⟩ := mapM_mem warrantMap w hw
      obtain ⟨e, he, hew⟩ := List.mem_filterMap.mp (warrantFor_mem hf)
      cases e <;> simp at hew
      subst hew
      exact he

theorem reachable_live {a : Admission} {snap : Snapshot} {id : Nat} (h : Reachable (supportNodes a snap) id) :
    ∃ w ∈ snap.warrants, w.id = id ∧ live snap w = true := by
  cases h with
  | fire member req _ =>
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp member
    refine ⟨w, hw, rfl, ?_⟩
    cases hl : live snap w
    · simp [requirements, hl] at req
    · rfl

/-- The warrant ids the profile files: a claim's support warrant has the claim's key as its id, its theorem
warrant `theoremWarrantId key` (`Ledger.fileRaw`, `Ledger.mintTheorem`, `Ledger3.fileRaw`). -/
def ProfileIds (l : List Event) : Prop :=
  ∀ w, Event.warrant w ∈ l → w.id = w.claim ∨ w.id = theoremWarrantId w.claim

/-- W3: a withdrawn key is not held. -/
theorem withdraw_unholds (a : Admission) (l : List Event) (ks : List Nat) (hl : NoSupersede l)
    (hids : ProfileIds l) {k : Nat} (hk : k ∈ ks) (s : RuntimeState) (h : fold a (l ++ withdrawEvents ks) = .ok s) :
    held s k = false := by
  rw [withdrawEvents_eq] at h
  unfold fold at h
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
    have hin : w.id ∈ withdrawTargets ks := by
      rcases hids w (resolve_warrant_mem l snap hr w hw) with e | e <;>
        exact List.mem_flatMap.mpr ⟨k, hk, by simp [e, hc]⟩
    simp [live, mem_canonicalIds, hid, hin] at hlive


/-! ## Every run: the profile files only `Simple` events with the profile's warrant ids -/

/-- The filing invariant: `Guard.Simple` events with the profile's warrant ids. -/
def Filed (l : List Event) : Prop := Guard.Simple l ∧ ProfileIds l

theorem filed_append {a b : List Event} : Filed (a ++ b) ↔ Filed a ∧ Filed b := by
  simp only [Filed, Guard.Simple, ProfileIds, List.mem_append, or_imp, forall_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, h2, h4⟩
  · rintro ⟨⟨h1, h3⟩, h2, h4⟩; exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem filed_nil : Filed [] := And.intro (fun _ h => nomatch h) (fun _ h => nomatch h)

theorem filed_of {t : List Event} (hs : ∀ e ∈ t, Guard.simple e = true) (hi : ∀ w, Event.warrant w ∈ t → w.id = w.claim) :
    Filed t := ⟨hs, fun w hw => .inl (hi w hw)⟩

theorem fileRaw_filed (l : Ledger) (i : Item) (h : Filed l.events) : Filed (l.fileRaw i).events := by
  unfold Ledger.fileRaw
  cases i.support <;> simp only [List.append_assoc] <;>
    exact filed_append.mpr ⟨h, filed_of (by simp [Guard.simple]) (by simp)⟩

theorem fileRaw3_filed (l : Ledger3) (i : Item3) (h : Filed l.events) : Filed (l.fileRaw i).events := by
  unfold Ledger3.fileRaw
  cases i.support <;> simp only [List.append_assoc] <;>
    exact filed_append.mpr ⟨h, filed_of (by simp [Guard.simple]) (by simp)⟩

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β} (h : x >>= f = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem foldlM_inv {σ α : Type} (P : σ → Prop) (step : σ → α → Except String σ)
    (hstep : ∀ s a s', P s → step s a = .ok s' → P s') :
    ∀ (xs : List α) (s s' : σ), P s → xs.foldlM step s = .ok s' → P s'
  | [], s, s', hs, h => by cases h; exact hs
  | x :: xs, s, s', hs, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨t, ht, h⟩ := bind_ok h
    exact foldlM_inv P step hstep xs t s' (hstep s x t hs ht) h

theorem file_filed {l l' : Ledger} {i : Item} (h : Filed l.events) (hf : l.file i = .ok l') : Filed l'.events := by
  unfold Ledger.file at hf
  split at hf
  · cases hf; exact fileRaw_filed l i h
  · cases hf

theorem fileAll_filed {items : List Item} {l l' : Ledger} (h : Filed l.events) (hf : fileAll items l = .ok l') :
    Filed l'.events :=
  foldlM_inv (fun l : Ledger => Filed l.events) _ (fun _ _ _ hs ht => file_filed hs ht) items l l' h hf

theorem foldl_fileRaw_filed : ∀ (items : List Item) (l : Ledger), Filed l.events →
    Filed (items.foldl (fun l i => l.fileRaw i) l).events
  | [], _, h => h
  | i :: is, l, h => foldl_fileRaw_filed is (l.fileRaw i) (fileRaw_filed l i h)

theorem fileAllFast_filed {items : List Item} {l l' : Ledger} (h : Filed l.events)
    (hf : fileAllFast items l = .ok l') : Filed l'.events := by
  unfold fileAllFast at hf
  dsimp only at hf
  split at hf
  · cases hf
    rw [fileRawAll_eq]
    exact foldl_fileRaw_filed items l h
  · exact fileAll_filed h hf

theorem mintTheorem_filed {l l' : Ledger} {i : Item} {d : Option String} (h : Filed l.events)
    (hm : l.mintTheorem i = .ok (l', d)) : Filed l'.events := by
  unfold Ledger.mintTheorem at hm
  dsimp only at hm
  split at hm
  · cases hm; exact h
  · split at hm
    · cases hm
      exact filed_append.mpr ⟨h, ⟨by simp [Guard.Simple, Guard.simple], by simp [ProfileIds]⟩⟩
    · cases hm

theorem fileAll3_filed {items : List Item3} {l l' : Ledger3} (h : Filed l.events) (hf : fileAll3 items l = .ok l') :
    Filed l'.events :=
  foldlM_inv (fun l : Ledger3 => Filed l.events) _ (fun l i l' hs ht => by
    unfold Ledger3.file at ht
    split at ht
    · cases ht; exact fileRaw3_filed l i hs
    · cases ht) items l l' h hf

/-- W3 for every 3a run (`gp_ledger`): a withdrawn key is not held in the final fold. -/
theorem runWith_withdrawn (p : Plan) (m : CheckMemo) (records : List BinderRecord) (o : Outcome)
    (h : p.runWith m records = .ok o) {k : Nat} (hk : k ∈ p.withdrawn) : held o.state k = false := by
  unfold Plan.runWith at h
  obtain ⟨l1, h1, h⟩ := bind_ok h
  have f1 := fileAllFast_filed filed_nil h1
  obtain ⟨⟨l2, t2⟩, h2, h⟩ := bind_ok h
  have f2 : Filed l2.events := foldlM_inv (fun acc : Ledger × List (Nat × String) => Filed acc.1.events) _
    (fun acc i acc' hs ht => by
      split at ht
      · obtain ⟨⟨l, d⟩, hm, ht⟩ := bind_ok ht
        cases ht
        exact mintTheorem_filed hs hm
      · cases ht; exact hs) _ _ _ f1 h2
  obtain ⟨st, h3, h⟩ := bind_ok h
  obtain ⟨l5, h5, h⟩ := bind_ok h
  have f5 := fileAllFast_filed f2 h5
  obtain ⟨⟨l6, t6⟩, h6, h⟩ := bind_ok h
  have f6 : Filed l6.events := foldlM_inv (fun acc : Ledger × List (Nat × String) => Filed acc.1.events) _
    (fun acc i acc' hs ht => by
      obtain ⟨⟨l, d⟩, hm, ht⟩ := bind_ok ht
      cases ht
      exact mintTheorem_filed hs hm) _ _ _ f5 h6
  obtain ⟨fin, h7, h⟩ := bind_ok h
  cases h
  exact withdraw_unholds _ _ _ (noSupersede_of_simple f6.1) f6.2 hk fin h7

/-- W3 for every 3b run (`gp_ledger3`; `Plan3.runWith_eq`): a withdrawn key is not held. -/
theorem run3_withdrawn (p : Plan3) (o : Outcome3) (h : p.run = .ok o) {k : Nat} (hk : k ∈ p.withdrawn) :
    held o.state k = false := by
  unfold Plan3.run at h
  obtain ⟨l1, h1, h⟩ := bind_ok h
  have f1 := fileAll3_filed filed_nil h1
  obtain ⟨st, h2, h⟩ := bind_ok h
  cases h
  exact withdraw_unholds _ _ _ (noSupersede_of_simple f1.1) f1.2 hk st h2

end GPProfile.Withdraw
