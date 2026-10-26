import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.coordinate_gauge

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations

/-- Agreement of an actual absorbing-point operator with an ambient map on
the set where that operator is used. The convex comparison set `Q` need not
be contained in `A` or in the operator domain; only the actual inputs do. -/
def ModelRealizationOn {E : Type} {A : Set E} (φ : Operator (Option A) none)
    (F : E → E) (Q : Set E) (S : Set (Option A)) : Prop :=
  ∀ x ∈ S, ∃ a b : A,
    x = some a ∧ a.val ∈ Q ∧ φ.func (some a) = some b ∧ b.val = F a.val

theorem ModelRealizationOn.subset_dom {E : Type} {A : Set E}
    {φ : Operator (Option A) none} {F : E → E} {Q : Set E} {S : Set (Option A)}
    (h : ModelRealizationOn φ F Q S) : S ⊆ dom φ := by
  intro x hx
  rcases h x hx with ⟨a, b, rfl, _, hab, _⟩
  simp [dom, hab]

end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
