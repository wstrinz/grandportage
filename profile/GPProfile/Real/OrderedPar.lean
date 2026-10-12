import GPProfile.Real.Ordered
import GPProfile.Real.IdealZero

/-!
An ordered leaf replayed faster (ud22 performance, DECISIONS 2026-10-10). `orderedCheckFast` is
`orderedCheck` with two changes, and is proved equal to it (`orderedCheckFast_eq`); it replaces
`orderedCheck` in compiled code (`@[csimp]`), as `orderedExplainFast` replaces `orderedExplain`.
`GPBinding.Real.OrderedSound` applies unchanged. The changes:

- each cofactor is converted once, in its own task, for both its canonical-form check and the
  identity (`oCanonicalWith_eq`, `parEach_eq`);
- the final identity is decided by `idealZero` (`idealZero_eq`): the monoid and cone terms are built in
  Hex as before, and the ideal term `Σ cᵢ·eᵢ` is added into them term by term, without building the
  products as polynomials.
-/

namespace GPProfile.Real
open GPProfile Hex

/-- `xs.map f`, one task per element: for a few expensive elements, where `parMap`'s chunks of
neighbours would serialise them. -/
def parEach {α β : Type} (f : α → β) (xs : List α) : List β :=
  (xs.map fun x => Task.spawn fun _ => f x).map Task.get

theorem parEach_eq {α β : Type} (f : α → β) (xs : List α) : parEach f xs = xs.map f := by
  simp only [parEach, List.map_map]
  rfl

/-- `parEach`, each task spawned at the priority `prio` gives its element (a scheduling hint only). -/
def parEachPrio {α β : Type} (prio : α → Task.Priority) (f : α → β) (xs : List α) : List β :=
  (xs.map fun x => Task.spawn (fun _ => f x) (prio x)).map Task.get

theorem parEachPrio_eq {α β : Type} (prio : α → Task.Priority) (f : α → β) (xs : List α) :
    parEachPrio prio f xs = xs.map f := by
  simp only [parEachPrio, List.map_map]
  rfl

/-- `oCanonical`, each cofactor checked against its conversion in `Cs` (`canonical` is the conversion
read back), so a cofactor is converted once for both the check and the identity. -/
def oCanonicalWith (r : RealSys) (c : OCert) (Cs : List (Option (P r.vars.length Rat))) : Bool :=
  let n := r.vars.length
  let ok := fun (q : Sparse) => canonical n q == some q
  r.eqs.all ok && r.guards.all ok && r.signs.all (ok ·.1) &&
    (c.cofactors.zip Cs).all fun t => t.2.map ofHex == some t.1

theorem all_zip_map {α β : Type} (l : List α) (f : α → β) (g : α × β → Bool) :
    (l.zip (l.map f)).all g = l.all fun x => g (x, f x) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.zip_cons_cons, List.all_cons, ih]

theorem oCanonicalWith_eq (r : RealSys) (c : OCert) :
    oCanonicalWith r c (parEach (toHexQ r.vars.length) c.cofactors) = oCanonical r c := by
  simp only [oCanonicalWith, oCanonical, parEach_eq, all_zip_map]
  rfl

theorem mapM_parEach {α β : Type} (f : α → Option β) (l : List α) : (parEach f l).mapM id = l.mapM f := by
  simp only [parEach_eq, List.mapM_map]
  rfl

/-- The monoid and cone terms of `oAssemble`: everything but the ideal term. -/
def oHead {n : Nat} (G Q : List (P n Rat)) (pows : List Nat) (k : Nat)
    (T : List (List (Rat × P n Rat) × List Nat)) : P n Rat :=
  ((Q.zip pows).map fun t => t.1 ^ t.2).prod * guardTerm G k + (T.map (coneHex Q)).sum

theorem oAssemble_head {n : Nat} (E G Q C : List (P n Rat)) (pows : List Nat) (k : Nat)
    (T : List (List (Rat × P n Rat) × List Nat)) :
    oAssemble E G Q C pows k T = oHead G Q pows k T + (List.zipWith (· * ·) C E).sum := rfl

/-- `orderedCheck`, deciding the identity by `idealZero` (`orderedCheckFast_eq`). -/
def orderedCheckFast (r : RealSys) (c : OCert) : Bool :=
  let n := r.vars.length
  let m := (strictAtoms r).length
  let Cs := parEach (toHexQ n) c.cofactors
  if !oCanonicalWith r c Cs then false
  else if !r.signs.all (fun a => a.2 == -1 || a.2 == 0 || a.2 == 1) then false
  else if c.cofactors.length != r.eqs.length + (zeroAtoms r).length then false
  else if c.posPow.length != m then false
  else if !c.cone.all (·.posIdx.all (· < m)) then false
  else match selectGuards r.guards c.guardSel with
  | none => false
  | some sg =>
  if c.guardPow > maxExponent || c.posPow.any (· > maxExponent) ||
      c.cone.any (·.posIdx.length > maxExponent) || monoidDegree r c sg > maxRhsDegree then false
  else match c.cone.mapM (ConeTerm.expand n) with
    | .error _ => false
    | .ok T =>
      if !T.all (fun t => t.1.all fun u => decide (0 ≤ u.1)) then false
      else match (r.eqs ++ zeroAtoms r).mapM (toHexQ n), sg.mapM (toHexQ n),
          (strictAtoms r).mapM (posHex n), Cs.mapM id with
        | some E, some G, some Q, some C => idealZero (oHead G Q c.posPow c.guardPow T) C E
        | _, _, _, _ => false

theorem orderedCheckFast_eq (r : RealSys) (c : OCert) : orderedCheckFast r c = orderedCheck r c := by
  unfold orderedCheckFast orderedCheck orderedResidual
  simp only [oCanonicalWith_eq, mapM_parEach]
  split
  · simp_all
  split
  · simp_all
  split
  · simp_all
  split
  · simp_all
  split
  · simp_all
  split
  · simp_all
  rename_i sg hsg
  simp only [hsg]
  split
  · simp_all
  split
  · simp_all
  rename_i T hT
  simp only [hT]
  split
  · simp_all
  split
  · rename_i E G Q C hE hG hQ hC
    simp only [hE, hG, hQ, hC, idealZero_eq, oAssemble_head]
  · rename_i hne
    cases hE : (r.eqs ++ zeroAtoms r).mapM (toHexQ r.vars.length) <;>
      cases hG : sg.mapM (toHexQ r.vars.length) <;>
      cases hQ : (strictAtoms r).mapM (posHex r.vars.length) <;>
      cases hC : c.cofactors.mapM (toHexQ r.vars.length) <;>
      first | exact (hne _ _ _ _ hE hG hQ hC).elim | simp_all

@[csimp] theorem orderedCheck_eq_fast : @orderedCheck = @orderedCheckFast := by
  funext r c
  exact (orderedCheckFast_eq r c).symm

theorem orderedExplain_ok {r : RealSys} {c : OCert} (h : orderedCheck r c = true) : orderedExplain r c = .ok () := by
  unfold orderedCheck at h
  unfold orderedExplain
  split at h <;> simp_all

/-- `orderedExplain`: an accepted certificate is known by `orderedCheckFast`, without the residual. -/
def orderedExplainFast (r : RealSys) (c : OCert) : Except OrdFail Unit :=
  if orderedCheckFast r c then .ok () else orderedExplain r c

@[csimp] theorem orderedExplain_eq_fast : @orderedExplain = @orderedExplainFast := by
  funext r c
  unfold orderedExplainFast
  split
  · rename_i h
    rw [orderedCheckFast_eq] at h
    exact orderedExplain_ok h
  · rfl

end GPProfile.Real
