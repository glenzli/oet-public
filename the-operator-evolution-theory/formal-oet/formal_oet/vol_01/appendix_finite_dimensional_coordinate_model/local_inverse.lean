import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.coordinate_gauge
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/--
Library background result for local fiber geometry.
Inverse-function branch only: the actual derivative determinant gives a
genuine open neighborhood and the actual singleton level fiber.
-/
theorem actual_nonsingular_local_fiber (F : E → E) (Q : Set E) (hQ : IsOpen Q)
    (hF : ContDiffOn ℝ 1 F Q) (x : E) (hx : x ∈ Q)
    (hdet : (fderiv ℝ F x).toLinearMap.det ≠ 0) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ Q ∧ Set.InjOn F W ∧
      {z | z ∈ W ∧ F z = F x} = {x} := by
  have hc : ContDiffAt ℝ 1 F x := (hF x hx).contDiffAt (hQ.mem_nhds hx)
  let T := fderiv ℝ F x
  have hker : T.toLinearMap.ker = ⊥ := by
    by_contra h
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr h)
  have hbij : Function.Bijective T.toLinearMap :=
    ⟨LinearMap.ker_eq_bot.mp hker,
      LinearMap.surjective_of_injective (LinearMap.ker_eq_bot.mp hker)⟩
  let e : E ≃L[ℝ] E := (LinearEquiv.ofBijective T.toLinearMap hbij).toContinuousLinearEquiv
  have he : (e : E →L[ℝ] E) = T := by ext v; rfl
  have hd : HasFDerivAt F (e : E →L[ℝ] E) x := by
    rw [he]
    exact hc.differentiableAt_one.hasFDerivAt
  let H := hc.toOpenPartialHomeomorph F hd one_ne_zero
  have hxH : x ∈ H.source := hc.mem_toOpenPartialHomeomorph_source hd one_ne_zero
  have hinj : Set.InjOn F (H.source ∩ Q) := H.injOn.mono Set.inter_subset_left
  refine ⟨H.source ∩ Q, H.open_source.inter hQ, ⟨hxH, hx⟩, Set.inter_subset_right, hinj, ?_⟩
  ext z
  constructor
  · intro hz
    exact hinj hz.1 ⟨hxH, hx⟩ hz.2
  · rintro rfl
    exact ⟨⟨hxH, hx⟩, rfl⟩

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
