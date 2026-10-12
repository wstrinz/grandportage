import GP50.EventOrderProofs

/-!
The commit guard on profile logs (post-G4 handoff, Track K).

The profile files claims as declarations, version-1 currents and warrants, and never retracts or
supersedes (`Simple`). On such logs `resolve` fails exactly when two currents for one claim, or two
warrants with one id, differ (`resolve_isOk_iff`). Conflicts only accumulate, so a log resolves
exactly when every prefix does (`resolve_prefix`). That licenses resolving once after filing
everything instead of after every append.
-/

namespace GPProfile.Guard
open GP50

/-! ## Lawful equality for the event types (the Kernel's own instances are private) -/

theorem binding_beq (a b : Binding) : instBEqBinding.beq a b = true ↔ a = b := by
  cases a; cases b
  simp [instBEqBinding.beq, Bool.and_eq_true, beq_iff_eq]

instance lawfulBinding : LawfulBEq Binding where
  rfl := binding_beq _ _ |>.mpr rfl
  eq_of_beq := binding_beq _ _ |>.mp

theorem status_beq (a b : AttemptStatus) : instBEqAttemptStatus.beq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [instBEqAttemptStatus.beq, AttemptStatus.ctorIdx]

instance lawfulAttemptStatus : LawfulBEq AttemptStatus where
  rfl := status_beq _ _ |>.mpr rfl
  eq_of_beq := status_beq _ _ |>.mp

theorem evidence_beq (a b : Evidence) : instBEqEvidence.beq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [instBEqEvidence.beq, beq_iff_eq]

instance lawfulEvidence : LawfulBEq Evidence where
  rfl := evidence_beq _ _ |>.mpr rfl
  eq_of_beq := evidence_beq _ _ |>.mp

theorem warrant_beq (a b : Warrant) : instBEqWarrant.beq a b = true ↔ a = b := by
  cases a; cases b
  simp [instBEqWarrant.beq, Bool.and_eq_true, beq_iff_eq]

instance lawfulWarrant : LawfulBEq Warrant where
  rfl := warrant_beq _ _ |>.mpr rfl
  eq_of_beq := warrant_beq _ _ |>.mp

theorem current_beq (a b : Current) : instBEqCurrent.beq a b = true ↔ a = b := by
  cases a; cases b
  simp [instBEqCurrent.beq, Bool.and_eq_true, beq_iff_eq]

instance lawfulCurrent : LawfulBEq Current where
  rfl := current_beq _ _ |>.mpr rfl
  eq_of_beq := current_beq _ _ |>.mp

/-! ## Profile logs -/

/-- An event the profile files: a declaration, a version-1 current, or a warrant. -/
def simple : Event → Bool
  | .declareClaim _ => true
  | .current c => c.version == 1
  | .warrant _ => true
  | _ => false

def Simple (l : List Event) : Prop := ∀ e ∈ l, simple e = true

/-- No two currents for one claim differ, and no two warrants with one id differ. -/
def NoConflict (l : List Event) : Prop :=
  (∀ x ∈ currentsIn l, ∀ y ∈ currentsIn l, x.claim = y.claim → x = y) ∧
  (∀ x ∈ warrantsIn l, ∀ y ∈ warrantsIn l, x.id = y.id → x = y)

theorem currentsIn_append (a b : List Event) : currentsIn (a ++ b) = currentsIn a ++ currentsIn b := by
  simp [currentsIn, List.filterMap_append]

theorem warrantsIn_append (a b : List Event) : warrantsIn (a ++ b) = warrantsIn a ++ warrantsIn b := by
  simp [warrantsIn, List.filterMap_append]

theorem noConflict_prefix {a b : List Event} (h : NoConflict (a ++ b)) : NoConflict a := by
  refine ⟨fun x hx y hy => h.1 x ?_ y ?_, fun x hx y hy => h.2 x ?_ y ?_⟩ <;>
    simp_all [currentsIn_append, warrantsIn_append]

theorem version_of_simple {l : List Event} (hs : Simple l) {c : Current} (hc : c ∈ currentsIn l) :
    c.version = 1 := by
  simp only [currentsIn, List.mem_filterMap] at hc
  obtain ⟨e, he, hce⟩ := hc
  cases e with
  | current c' =>
    simp only [Option.some.injEq] at hce
    subst hce
    have := hs _ he
    simpa [simple] using this
  | _ => simp at hce

/-! ## Selecting a single binding -/

theorem singleton_iff {α : Type} [BEq α] [LawfulBEq α] (xs : List α) (a : α) :
    xs.eraseDups = [a] ↔ ∀ x, x ∈ xs ↔ x = a := by
  constructor
  · intro h x
    rw [← List.mem_eraseDups, h]
    simp
  · intro h
    have hnd := GP50.eraseDups_nodup xs
    have hmem : ∀ x, x ∈ xs.eraseDups ↔ x = a := fun x => by rw [List.mem_eraseDups]; exact h x
    match hxs : xs.eraseDups with
    | [] => exact absurd ((hmem a).mpr rfl) (by simp [hxs])
    | [b] =>
      have := (hmem b).mp (by simp [hxs])
      simp [this]
    | b :: c :: rest =>
      have hb := (hmem b).mp (by simp [hxs])
      have hc := (hmem c).mp (by simp [hxs])
      rw [hxs] at hnd
      simp [hb, hc] at hnd

theorem foldl_max_aux : ∀ (l : List Current) (m : Nat), m ≤ 1 → (∀ x ∈ l, x.version = 1) →
    l.foldl (fun n v => max n v.version) m = if l = [] then m else 1
  | [], m, _, _ => by simp
  | x :: xs, m, hm, hl => by
    simp only [List.foldl_cons, reduceCtorEq, if_false]
    rw [hl x List.mem_cons_self, show max m 1 = 1 by omega,
      foldl_max_aux xs 1 (Nat.le_refl 1) fun y hy => hl y (List.mem_cons_of_mem _ hy)]
    split <;> rfl

theorem foldl_max_one (l : List Current) (h : ∀ x ∈ l, x.version = 1) (hne : l ≠ []) :
    l.foldl (fun n v => max n v.version) 0 = 1 := by
  rw [foldl_max_aux l 0 (Nat.zero_le _) h]
  simp [hne]

theorem currentFor_ok {cs : List Current} {c : Nat} (hv : ∀ x ∈ cs, x.version = 1)
    {v : Current} (hv0 : v ∈ cs) (hc : v.claim = c)
    (huniq : ∀ x ∈ cs, ∀ y ∈ cs, x.claim = y.claim → x = y) : currentFor cs c = .ok v := by
  unfold currentFor
  have hm : cs.filter (fun x => x.claim == c) ≠ [] := by
    intro h
    have : v ∈ cs.filter (fun x => x.claim == c) := List.mem_filter.mpr ⟨hv0, by simp [hc]⟩
    rw [h] at this
    simp at this
  have hn := foldl_max_one _ (fun x hx => hv x (List.mem_filter.mp hx).1) hm
  have hsel : ((cs.filter (fun x => x.claim == c)).filter fun x => x.version == 1).eraseDups = [v] := by
    rw [singleton_iff]
    intro x
    simp only [List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨⟨hx, hxc⟩, -⟩
      exact huniq x hx v hv0 (hxc.trans hc.symm)
    · rintro rfl
      exact ⟨⟨hv0, hc⟩, hv _ hv0⟩
  simp only [hn, hsel]
  rfl

theorem warrantFor_ok {ws : List Warrant} {w : Warrant} (hw : w ∈ ws)
    (huniq : ∀ x ∈ ws, ∀ y ∈ ws, x.id = y.id → x = y) : warrantFor ws w.id = .ok w := by
  unfold warrantFor
  have hsel : (ws.filter fun x => x.id == w.id).eraseDups = [w] := by
    rw [singleton_iff]
    intro x
    simp only [List.mem_filter, beq_iff_eq]
    constructor
    · rintro ⟨hx, hxi⟩
      exact huniq x hx w hw hxi
    · rintro rfl
      exact ⟨hw, rfl⟩
  simp only [hsel]

theorem mapM_ok_iff {α β ε : Type} (f : α → Except ε β) :
    ∀ xs : List α, (∃ ys, xs.mapM f = .ok ys) ↔ ∀ x ∈ xs, ∃ y, f x = .ok y
  | [] => by simp [List.mapM_nil, pure, Except.pure]
  | x :: xs => by
    rw [List.mapM_cons]
    cases hx : f x with
    | error e =>
      simp only [bind, Except.bind]
      constructor
      · rintro ⟨_, h⟩; cases h
      · intro h; obtain ⟨y, hy⟩ := h x List.mem_cons_self; rw [hx] at hy; cases hy
    | ok y =>
      have ih := mapM_ok_iff f xs
      cases hxs : xs.mapM f with
      | error e =>
        simp only [bind, Except.bind, hxs]
        constructor
        · rintro ⟨_, h⟩; cases h
        · intro h
          obtain ⟨_, hys⟩ := ih.mpr fun z hz => h z (List.mem_cons_of_mem _ hz)
          rw [hxs] at hys; cases hys
      | ok ys =>
        simp only [bind, Except.bind, hxs, pure, Except.pure]
        refine ⟨fun _ z hz => ?_, fun _ => ⟨_, rfl⟩⟩
        rcases List.mem_cons.mp hz with rfl | hz
        · exact ⟨y, hx⟩
        · exact (ih.mp ⟨ys, hxs⟩) z hz

theorem no_links {l : List Event} (hs : Simple l) :
    (l.filterMap fun e => match e with | .supersede a b => some (a, b) | _ => none) = [] := by
  rw [List.filterMap_eq_nil_iff]
  intro e he
  have := hs e he
  cases e <;> simp_all [simple]

theorem mem_canonicalIds {xs : List Nat} {a : Nat} : a ∈ canonicalIds xs ↔ a ∈ xs := by
  simp [canonicalIds, List.mem_mergeSort]

theorem resolve_ok_of_lookups (l : List Event) (hs : Simple l) (cur : List Current) (war : List Warrant)
    (hcur : (canonicalIds ((currentsIn l).map (·.claim))).mapM (currentFor (currentsIn l)) = .ok cur)
    (hwar : (canonicalIds ((warrantsIn l).map (·.id))).mapM (warrantFor (warrantsIn l)) = .ok war) :
    ∃ s, resolve l = .ok s := by
  unfold resolve
  simp only [hcur, hwar]
  rw [List.filterMap_eq_nil_iff.mpr (fun e he => by have := hs e he; cases e <;> simp_all [simple])]
  simp only [List.eraseDups_nil, List.mergeSort_nil, List.forIn_nil]
  exact ⟨_, rfl⟩

theorem currentFor_inv {cs : List Current} {c : Nat} {v : Current} (hv : ∀ x ∈ cs, x.version = 1)
    (h : currentFor cs c = .ok v) : ∀ x ∈ cs, x.claim = c → x = v := by
  intro x hx hxc
  unfold currentFor at h
  have hm : cs.filter (fun x => x.claim == c) ≠ [] := by
    intro he
    have : x ∈ cs.filter (fun x => x.claim == c) := List.mem_filter.mpr ⟨hx, by simp [hxc]⟩
    rw [he] at this; simp at this
  dsimp only at h
  rw [foldl_max_one _ (fun y hy => hv y (List.mem_filter.mp hy).1) hm] at h
  generalize hsel : ((cs.filter fun x => x.claim == c).filter fun x => x.version == 1).eraseDups = sel at h
  match sel, hsel, h with
  | [w], hsel, h =>
    have hw : w = v := by cases h; rfl
    subst hw
    have := (singleton_iff _ w).mp hsel x
    exact this.mp (by simp [List.mem_filter, hx, hxc, hv x hx])

theorem warrantFor_inv {ws : List Warrant} {i : Nat} {w : Warrant} (h : warrantFor ws i = .ok w) :
    ∀ x ∈ ws, x.id = i → x = w := by
  intro x hx hxi
  unfold warrantFor at h
  generalize hsel : (ws.filter fun x => x.id == i).eraseDups = sel at h
  match sel, hsel, h with
  | [y], hsel, h =>
    have hy : y = w := by cases h; rfl
    subst hy
    exact ((singleton_iff _ y).mp hsel x).mp (by simp [List.mem_filter, hx, hxi])

/-- On profile logs, `resolve` succeeds exactly when there is no conflict. -/
theorem resolve_ok_iff {l : List Event} (hs : Simple l) : (∃ s, resolve l = .ok s) ↔ NoConflict l := by
  have hv : ∀ x ∈ currentsIn l, x.version = 1 := fun x hx => version_of_simple hs hx
  constructor
  · rintro ⟨st, h⟩
    unfold resolve at h
    cases hmc : (canonicalIds ((currentsIn l).map (·.claim))).mapM (currentFor (currentsIn l)) with
    | error e => simp [hmc, bind, Except.bind] at h
    | ok cur =>
      cases hmw : (canonicalIds ((warrantsIn l).map (·.id))).mapM (warrantFor (warrantsIn l)) with
      | error e => simp [hmc, hmw, bind, Except.bind] at h
      | ok war =>
        have hc := (mapM_ok_iff _ _).mp ⟨cur, hmc⟩
        have hw := (mapM_ok_iff _ _).mp ⟨war, hmw⟩
        refine ⟨fun x hx y hy hxy => ?_, fun x hx y hy hxy => ?_⟩
        · obtain ⟨v, hfv⟩ := hc x.claim (mem_canonicalIds.mpr (List.mem_map_of_mem hx))
          exact (currentFor_inv hv hfv x hx rfl).trans (currentFor_inv hv hfv y hy hxy.symm).symm
        · obtain ⟨v, hfv⟩ := hw x.id (mem_canonicalIds.mpr (List.mem_map_of_mem hx))
          exact (warrantFor_inv hfv x hx rfl).trans (warrantFor_inv hfv y hy hxy.symm).symm
  · intro hn
    obtain ⟨cur, hcur⟩ := (mapM_ok_iff (currentFor (currentsIn l)) _).mpr fun c hc => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_canonicalIds.mp hc)
      exact ⟨x, currentFor_ok hv hx rfl hn.1⟩
    obtain ⟨war, hwar⟩ := (mapM_ok_iff (warrantFor (warrantsIn l)) _).mpr fun i hi => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (mem_canonicalIds.mp hi)
      exact ⟨x, warrantFor_ok hx hn.2⟩
    exact resolve_ok_of_lookups l hs cur war hcur hwar

/-- A profile log resolves only if every prefix resolves. -/
theorem resolve_prefix {a b : List Event} (hs : Simple (a ++ b)) (h : ∃ s, resolve (a ++ b) = .ok s) :
    ∃ s, resolve a = .ok s :=
  (resolve_ok_iff fun e he => hs e (List.mem_append_left _ he)).mpr
    (noConflict_prefix ((resolve_ok_iff hs).mp h))

end GPProfile.Guard
