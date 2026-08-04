/-
# IMAGE_CLOSURE/ALONG/IDENTITY does not rest on density

The kernel licenses the cell like this:

  "the image is DENSE in its closure, so the pullback O(closure) -> O(image) is
   INJECTIVE and a relation vanishing on the image vanishes on the closure.
   ... the direction follows from A PROPERTY OF THE MAP, not from the name of
   the edge type."

and gates it on `_MAP_POLYNOMIAL`.

Three things are wrong with that, and the cell is still SOUND -- for a reason
that makes a different gate necessary.

  1. DENSITY IS NOT A PROPERTY OF THE MAP.  A set is dense in its own closure
     by the definition of closure.  Citing it as though the map earned it makes
     a tautology look like a hypothesis, which is how the project's other free
     gate (`zariski_dense`) survived as long as it did.

  2. THE ARGUMENT IS ABOUT POINTS AND THE CLAIM IS ABOUT AN IDEAL.  "Vanishes
     on the closure" and "lies in the ideal of the closure" agree only when
     that ideal is radical, and an elimination ideal need not be.  `radMem_mem`
     below is the gap.

  3. THE CONDITION IT ACTUALLY NEEDS IS NOT CHECKED.  The honest argument is
     the elimination theorem at the level of ideals, and what it requires is
     that the rewriting BE A SENTENCE IN THE TARGET RING.  Nothing tests that.
-/

import GrandPortage.Localization

namespace GrandPortage

universe u

/-- The elimination ideal: what survives in the subring `B`.

    `B` stands for the polynomials expressible after the projection -- those
    mentioning none of the eliminated variables.  Modelling it as a bare
    predicate is enough here, because every statement below is about MEMBERSHIP
    and none of them needs `B` to be closed under anything. -/
def ElimIdeal {R : Type u} (I : Ideal R) (B : R → Prop) : Ideal R :=
  fun g => I g ∧ B g

/-- ALONG, and it is unconditional GIVEN EXPRESSIBILITY.  No density, no
    reducedness, no property of the map: `g` is in the source ideal and is a
    sentence in the target ring, therefore it is in the elimination ideal. -/
theorem elim_along {R : Type u} {I : Ideal R} {B : R → Prop} {g : R}
    (h : I g) (hb : B g) : ElimIdeal I B g := ⟨h, hb⟩

/-- AGAINST, also unconditional and needing nothing at all.  So the cell is
    EXACT in both directions, and the asymmetry the kernel comment worries
    about is not here. -/
theorem elim_against {R : Type u} {I : Ideal R} {B : R → Prop} {g : R}
    (h : ElimIdeal I B g) : I g := h.1

/-- THE GATE THE CELL ACTUALLY NEEDS, and the one nothing checks.

    Drop expressibility and the transport fails immediately -- not subtly, and
    not only for exotic ideals.  `x*y = 1` is true on the hyperbola and is not
    a sentence in `k[x]`. -/
theorem elim_needs_expressibility {R : Type u} [Inhabited R] :
    ¬ (∀ (I : Ideal R) (B : R → Prop) (g : R), I g → ElimIdeal I B g) := by
  intro h
  exact (h (fun _ => True) (fun _ => False) default trivial).2

/-! ## The points/ideal gap

`RadMem I g` -- some power of `g` lies in `I` -- is the algebraic content of
"`g` vanishes wherever `I` does".  It reuses `PowerOf` from `Localization.lean`
rather than introducing a second notion of power. -/

def RadMem {R : Type u} [Mul R] [OfNat R 1] (I : Ideal R) (g : R) : Prop :=
  ∃ m, PowerOf g m ∧ I m

def fours : Ideal Int := fun n => ∃ k, n = 4 * k

theorem two_radMem_fours : RadMem fours 2 :=
  ⟨2 * (2 * 1), PowerOf.step (PowerOf.step PowerOf.one), ⟨1, by decide⟩⟩

theorem two_not_mem_fours : ¬ fours 2 := by
  intro h; obtain ⟨k, hk⟩ := h; omega

/-- VANISHING IS NOT MEMBERSHIP.  The density argument concludes that a
    relation vanishes on the closure; `verify.identity` decides membership in
    the closure's ideal by reduction modulo a Groebner basis.  Those agree only
    when the ideal is radical, and an elimination ideal need not be.

    So the stated justification does not reach the thing being justified -- the
    cell is sound, and not for the reason written next to it. -/
theorem radMem_mem :
    ¬ (∀ (I : Ideal Int) (g : Int), RadMem I g → I g) :=
  fun h => two_not_mem_fours (h fours 2 two_radMem_fours)

/-! ## What this settles

The cell STAYS `True` in both directions.  What changes is the argument and,
because the argument changes, the gate.

  * `_MAP_POLYNOMIAL` is not the condition.  `operations.eliminate` mints these
    edges from a PROJECTION, whose map is polynomial always -- so on the one
    path that constructs an IMAGE_CLOSURE the gate cannot fail.  A gate that
    cannot fail is the `zariski_dense` shape a second time: it makes a reader
    stop without making the tool check anything.

  * EXPRESSIBILITY is the condition, and it is checkable -- `lhs` and `rhs`
    must mention no eliminated variable.  The machinery already exists:
    `cas.foreign_symbols` is exactly this test, pointed at coefficients instead
    of ring variables.

  * Which puts this condition in the SAME CLASS as `coefficients_in_base`, the
    one the formalization could not see because a typed statement carries no
    symbols.  Both exist only because a claim here is a STRING.

    NOT A FIFTH KERNEL GATE, and the count of gate shapes is unchanged.
    `_MAP_POLYNOMIAL` remains the kernel's gate on this cell; expressibility is
    enforced in `check` as INEXPRESSIBLE-CONCLUSION, for the same reason
    `coefficients_in_base` is checked rather than gated -- it is decidable by
    looking at the strings, and the kernel does not read models.  What is new
    is that the CLASS now has two members, which is evidence for the claim that
    the class exists at all. -/

end GrandPortage
