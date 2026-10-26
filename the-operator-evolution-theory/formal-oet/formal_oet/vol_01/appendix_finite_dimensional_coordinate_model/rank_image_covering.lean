import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.volumetric_covering
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.internal_cover_transport
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/--
OET anchor: h-a57e9e873735ed63
**命题（欧氏覆盖数的维数估计）- 仿射子空间中的内部覆盖**
The core bound applies to any finite-dimensional normed ambient space. The
Euclidean model is instantiated in `actual_euclidean_affine_subspace_cover`.
The set need not be closed; its own points are the centers of the open-ball cover.
-/
theorem internal_affine_subspace_cover
    (center : E) (W : Submodule ℝ E) (S : Set E) (radius epsilon : ℝ)
    (hr : 0 ≤ radius) (he : 0 < epsilon)
    (hS : ∀ y ∈ S, y - center ∈ W ∧ ‖y - center‖ ≤ radius) :
    covering_number edist (ENNReal.ofReal epsilon) S ≤
      ENNReal.ofReal ((1 + 2 * radius / epsilon) ^ Module.finrank ℝ W) := by
  let Q : Set W := {v | v.val + center ∈ S}
  let f : W → E := fun v => v.val + center
  have hQ : ∀ v ∈ Q, ‖v‖ ≤ radius := by
    intro v hv
    have h := (hS (v.val + center) hv).2
    simpa using h
  have himage : f '' Q = S := by
    ext y
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hy
      refine ⟨⟨y - center,(hS y hy).1⟩,?_,?_⟩
      · simpa [Q] using hy
      · simp [f]
  have hd : ∀ x ∈ Q, ∀ y ∈ Q, edist (f x) (f y) = edist x y := by
    intro x _ y _
    exact edist_add_right x.val y.val center
  rw [← himage, internal_cover_image_eq edist edist f Q _ hd]
  exact internal_cover_volume_upper radius epsilon hr he Q hQ

/-- Rank-dimensional packing takes place in the actual affine range of T.
The general subspace bound retains centers in the actual image of S. -/
theorem internal_affine_image_rank_bound (T : E →L[ℝ] E) (b x₀ : E)
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) (S : Set E)
    (hS : ∀ x ∈ S, ‖x - x₀‖ ≤ R) :
    covering_number edist (ENNReal.ofReal ε) ((fun x => T x + b) '' S) ≤
      ENNReal.ofReal ((1 + 2 * ‖T‖ * R / ε) ^ Module.finrank ℝ T.toLinearMap.range) := by
  have hbound : ∀ y ∈ (fun x => T x + b) '' S,
      y - (T x₀ + b) ∈ T.toLinearMap.range ∧ ‖y - (T x₀ + b)‖ ≤ ‖T‖ * R := by
    rintro y ⟨x, hx, rfl⟩
    have hdiff : T x + b - (T x₀ + b) = T (x - x₀) := by
      rw [map_sub]
      abel
    rw [hdiff]
    exact ⟨⟨x - x₀, rfl⟩,
      (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hS x hx) (norm_nonneg _))⟩
  simpa [mul_assoc] using internal_affine_subspace_cover (T x₀ + b) T.toLinearMap.range
    ((fun x => T x + b) '' S) (‖T‖ * R) ε (mul_nonneg (norm_nonneg _) hR) hε hbound

theorem rank_zero_affine_image (T : E →L[ℝ] E) (b : E)
    (hT : Module.finrank ℝ T.toLinearMap.range = 0) (S : Set E) (hS : S.Nonempty) :
    (fun x => T x + b) '' S = {b} := by
  haveI : Subsingleton T.toLinearMap.range :=
    (Module.finrank_eq_zero_iff_of_free ℝ T.toLinearMap.range).mp hT
  have hz (x : E) : T x = 0 :=
    congrArg Subtype.val (Subsingleton.elim (⟨T x, ⟨x, rfl⟩⟩ : T.toLinearMap.range) 0)
  simp only [hz, zero_add]
  ext y
  simp only [Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨x, _, rfl⟩; rfl
  · rintro rfl; exact ⟨hS.choose, hS.choose_spec, rfl⟩

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
