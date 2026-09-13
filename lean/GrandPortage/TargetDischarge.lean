import GrandPortage.CancellationInterpreter
namespace GrandPortage.CertificateInterpreter
/-- Interface for a field target. Canonical Q/R/C adapters are not assumed built. -/
structure FieldTarget {A : Type} (o : Operations A) : Prop where
  laws : Laws o
  nontrivial : o.one ≠ o.zero
  mul_assoc : ∀ a b c, o.mul (o.mul a b) c = o.mul a (o.mul b c)
  left_inverse : ∀ a, a ≠ o.zero → ∃ b, o.mul b a = o.one

theorem field_target_U {A : Type} {o : Operations A} (t : FieldTarget o) :
    o.one ≠ o.zero := t.nontrivial

theorem field_target_Z {A : Type} {o : Operations A} (t : FieldTarget o) :
    NoZeroDivisors o := by
  intro a b h
  by_cases ha : a = o.zero
  · exact Or.inl ha
  · obtain ⟨inverse, hi⟩ := t.left_inverse a ha
    right
    calc
      b = o.mul o.one b := (t.laws.one_mul b).symm
      _ = o.mul (o.mul inverse a) b := by rw [hi]
      _ = o.mul inverse (o.mul a b) := t.mul_assoc _ _ _
      _ = o.zero := by rw [h, t.laws.mul_zero]

theorem ordered_target_O {A : Type} {o : Operations A} (order : Ordering o) :
    Nonempty (Ordering o) := ⟨order⟩

def modTwo_field_target : FieldTarget modTwo where
  laws := modTwo_laws
  nontrivial := by decide
  mul_assoc := by decide
  left_inverse := by decide
end GrandPortage.CertificateInterpreter
