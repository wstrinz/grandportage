import GP50.Narrowing
namespace GP50.Semantic
theorem checked_narrow_sound (p : Profile) (dest source : Clause p)
    (accepted : checkNarrow p dest source = true)
    (sourceTrue : Means p source.stmt source.scope) :
    Means p dest.stmt dest.scope := by
  simp only [checkNarrow, Bool.and_eq_true] at accepted
  have same := p.same_sound dest.stmt source.stmt accepted.1
  have smaller := accepted.2.1
  intro ctx present
  rw [same]
  exact sourceTrue ctx (p.le_sound dest.scope source.scope ctx smaller present)

#print axioms checked_narrow_sound
end GP50.Semantic
