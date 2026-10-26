import Mathlib.Analysis.InnerProductSpace.SingularValues

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open scoped BigOperators
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} (T : E →ₗ[ℝ] E) (hn : Module.finrank ℝ E = n)

def singular_basis : OrthonormalBasis (Fin n) ℝ E :=
  T.isSymmetric_adjoint_comp_self.eigenvectorBasis hn

theorem norm_singular_basis (i : Fin n) : ‖T (singular_basis T hn i)‖ = T.singularValues i := by
  apply (sq_eq_sq₀ (norm_nonneg _) (T.singularValues_nonneg _)).mp
  have h := T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis hn i
  have hi := congrArg (fun w => inner ℝ (singular_basis T hn i) w) h
  simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
    inner_smul_right, singular_basis, OrthonormalBasis.norm_eq_one, one_pow, mul_one] at hi
  exact hi.trans (T.sq_singularValues_fin hn i).symm

theorem norm_sq_singular_coordinates (v : E) :
    ‖T v‖ ^ 2 = ∑ i : Fin n, T.singularValues i ^ 2 * ((singular_basis T hn).repr v i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← LinearMap.adjoint_inner_right]
  change inner ℝ v ((T.adjoint ∘ₗ T) v) = _
  rw [← (singular_basis T hn).repr.inner_map_map]
  change (∑ i : Fin n, (singular_basis T hn).repr ((T.adjoint ∘ₗ T) v) i *
    (singular_basis T hn).repr v i) = _
  apply Finset.sum_congr rfl
  intro i _
  have h := T.isSymmetric_adjoint_comp_self.eigenvectorBasis_apply_self_apply hn v i
  change (singular_basis T hn).repr ((T.adjoint ∘ₗ T) v) i = _ at h
  rw [h, ← T.sq_singularValues_fin hn i]
  simp only [singular_basis, RCLike.ofReal_real_eq_id, id_eq]
  ring

theorem singular_coordinate_square_sum (v : E) :
    (∑ i : Fin n, ((singular_basis T hn).repr v i) ^ 2) = ‖v‖ ^ 2 := by
  rw [← EuclideanSpace.real_norm_sq_eq, (singular_basis T hn).repr.norm_map]

include hn in
theorem singular_value_norm_bounds [NeZero n] (v : E) :
    T.singularValues (n - 1) * ‖v‖ ≤ ‖T v‖ ∧
      ‖T v‖ ≤ T.singularValues 0 * ‖v‖ := by
  have hlo : (T.singularValues (n - 1) * ‖v‖) ^ 2 ≤ ‖T v‖ ^ 2 := by
    rw [mul_pow, ← singular_coordinate_square_sum T hn v, norm_sq_singular_coordinates T hn v,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    apply pow_le_pow_left₀ (T.singularValues_nonneg _)
    exact T.singularValues_antitone (by omega)
  have hhi : ‖T v‖ ^ 2 ≤ (T.singularValues 0 * ‖v‖) ^ 2 := by
    rw [mul_pow, ← singular_coordinate_square_sum T hn v, norm_sq_singular_coordinates T hn v,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact pow_le_pow_left₀ (T.singularValues_nonneg _) (T.singularValues_antitone (Nat.zero_le _)) 2
  constructor
  · nlinarith [norm_nonneg (T v), mul_nonneg (T.singularValues_nonneg (n - 1)) (norm_nonneg v)]
  · nlinarith [norm_nonneg (T v), mul_nonneg (T.singularValues_nonneg 0) (norm_nonneg v)]

include hn in
theorem singular_values_of_norm_scaling (c : ℝ)
    (hc : ∀ v, ‖T v‖ = c * ‖v‖) (i : Fin n) : T.singularValues i = c := by
  rw [← norm_singular_basis T hn i, hc, (singular_basis T hn).norm_eq_one, mul_one]

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
