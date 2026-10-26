import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Real.Basic

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open Module
noncomputable section
variable {A E F : Type} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [AddCommGroup F] [Module ℝ F] [FiniteDimensional ℝ F]

/-- If a projection already sees all available rank, it is injective on the
actual derivative range. This is the linear step needed in the constant-rank
argument; no equality of nonlinear fibers is assumed. -/
theorem zero_of_projected_zero_of_rank_bound (D : A →ₗ[ℝ] E) (P : E →ₗ[ℝ] F)
    (hdim : finrank ℝ D.range ≤ finrank ℝ F) (hsurj : Function.Surjective (P.comp D))
    (v : A) (hv : P (D v) = 0) : D v = 0 := by
  let P' : D.range →ₗ[ℝ] F := P.comp D.range.subtype
  have hs : Function.Surjective P' := by
    intro y
    obtain ⟨a, ha⟩ := hsurj y
    exact ⟨⟨D a, ⟨a, rfl⟩⟩, ha⟩
  have hdim' : finrank ℝ F ≤ finrank ℝ D.range := by
    have h := P'.finrank_range_le
    rw [LinearMap.range_eq_top.mpr hs, finrank_top] at h
    exact h
  have hinj : Function.Injective P' :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hdim hdim')).mpr hs
  have hzero : (⟨D v, ⟨v, rfl⟩⟩ : D.range) = 0 := hinj (by simpa [P'] using hv)
  exact congrArg Subtype.val hzero

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
