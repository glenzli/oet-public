import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.nonlinear_colip
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.singular_geometry
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
noncomputable section

def plane_coordinate (i : Fin 2) : EuclideanPlane →L[ℝ] ℝ := EuclideanSpace.proj i

theorem periodic_polar_as_sum : periodic_polar = fun z =>
    (Real.exp (z 0) * Real.cos (z 1)) • EuclideanSpace.single 0 1 +
      (Real.exp (z 0) * Real.sin (z 1)) • EuclideanSpace.single 1 1 := by
  funext z
  ext i
  fin_cases i <;> simp [periodic_polar]

def periodic_polar_differential (z : EuclideanPlane) : EuclideanPlane →L[ℝ] EuclideanPlane :=
  (Real.exp (z 0) • (-Real.sin (z 1) • plane_coordinate 1) +
    Real.cos (z 1) • (Real.exp (z 0) • plane_coordinate 0)).smulRight
      (EuclideanSpace.single 0 1) +
  (Real.exp (z 0) • (Real.cos (z 1) • plane_coordinate 1) +
    Real.sin (z 1) • (Real.exp (z 0) • plane_coordinate 0)).smulRight
      (EuclideanSpace.single 1 1)

theorem periodic_polar_cont_diff : ContDiff ℝ 1 periodic_polar := by
  rw [periodic_polar_as_sum]
  exact (((plane_coordinate 0).contDiff.exp.mul
    (plane_coordinate 1).contDiff.cos).smul_const _).add
      (((plane_coordinate 0).contDiff.exp.mul
        (plane_coordinate 1).contDiff.sin).smul_const _)

theorem periodic_polar_has_fderiv (z : EuclideanPlane) :
    HasFDerivAt periodic_polar (periodic_polar_differential z) z := by
  rw [periodic_polar_as_sum]
  exact ((((plane_coordinate 0).hasFDerivAt.exp.mul
    (plane_coordinate 1).hasFDerivAt.cos).smul_const _).add
      (((plane_coordinate 0).hasFDerivAt.exp.mul
        (plane_coordinate 1).hasFDerivAt.sin).smul_const _))

theorem periodic_polar_differential_apply (z v : EuclideanPlane) :
    periodic_polar_differential z v =
      !₂[Real.exp (z 0) * (Real.cos (z 1) * v 0 - Real.sin (z 1) * v 1),
        Real.exp (z 0) * (Real.sin (z 1) * v 0 + Real.cos (z 1) * v 1)] := by
  ext i
  fin_cases i <;> simp [periodic_polar_differential, plane_coordinate] <;> ring

theorem periodic_polar_differential_norm (z v : EuclideanPlane) :
    ‖periodic_polar_differential z v‖ = Real.exp (z 0) * ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).mp
  rw [periodic_polar_differential_apply, EuclideanSpace.real_norm_sq_eq,
    mul_pow, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  calc
    _ = Real.exp (z 0) ^ 2 *
        ((Real.sin (z 1) ^ 2 + Real.cos (z 1) ^ 2) * (v 0 ^ 2 + v 1 ^ 2)) := by ring
    _ = _ := by rw [Real.sin_sq_add_cos_sq]; ring

/--
OET anchor: h-3e4095f278f5ea6b
导数下界与全局 co-Lip (ii)：仅有导数长度下界仍然不足。
Both canonical singular values of the actual derivative equal exp(s).
-/
theorem periodic_polar_singular_values (z : EuclideanPlane) (i : Fin 2) :
    (periodic_polar_differential z).toLinearMap.singularValues i = Real.exp (z 0) := by
  exact singular_values_of_norm_scaling (periodic_polar_differential z).toLinearMap
    (finrank_euclideanSpace_fin (𝕜 := ℝ)) (Real.exp (z 0))
    (periodic_polar_differential_norm z) i

/-- All fields of the earlier calculus interface are now derived from the
displayed map; none are assumptions supplied by its caller. -/
def periodic_polar_differential_facts : PeriodicPolarDifferentialCertificate where
  differential := periodic_polar_differential
  continuously_differentiable := periodic_polar_cont_diff
  has_derivative := periodic_polar_has_fderiv
  norm_action := periodic_polar_differential_norm

/--
OET anchor: h-3e4095f278f5ea6b
导数下界与全局 co-Lip (ii)：仅有导数长度下界仍然不足。
The actual derivative is an exp(s)-scaled Euclidean isometry, while the actual
periodic map fails every positive global co-Lip bound on the stated rectangle.
-/
theorem periodic_polar_counterexample :
    ContDiff ℝ 1 periodic_polar ∧
    (∀ z ∈ periodic_polar_domain, ∀ v,
      ‖periodic_polar_differential z v‖ = Real.exp (z 0) * ‖v‖ ∧
      ‖v‖ ≤ ‖periodic_polar_differential z v‖) ∧
    ¬ ∃ κ : ℝ, 0 < κ ∧ EuclideanCoLipOn periodic_polar periodic_polar_domain κ :=
  uniform_derivative_nondegeneracy_does_not_imply_global_colip periodic_polar_differential_facts

theorem periodic_polar_domain_nonempty : periodic_polar_domain.Nonempty :=
  ⟨periodic_polar_first, periodic_polar_first_mem_domain⟩

theorem periodic_polar_domain_is_open : IsOpen periodic_polar_domain := by
  have h₀ : Continuous (fun z : EuclideanPlane => z 0) := (plane_coordinate 0).continuous
  have h₁ : Continuous (fun z : EuclideanPlane => z 1) := (plane_coordinate 1).continuous
  exact (isOpen_lt continuous_const h₀).inter
    ((isOpen_lt h₀ continuous_const).inter
      ((isOpen_lt continuous_const h₁).inter (isOpen_lt h₁ continuous_const)))

theorem periodic_polar_domain_convex : Convex ℝ periodic_polar_domain := by
  have h₀ := (convex_Ioo (0 : ℝ) 1).linear_preimage (plane_coordinate 0).toLinearMap
  have h₁ := (convex_Ioo (0 : ℝ) (4 * Real.pi)).linear_preimage
    (plane_coordinate 1).toLinearMap
  convert h₀.inter h₁ using 1
  ext z
  change (0 < z 0 ∧ z 0 < 1 ∧ 0 < z 1 ∧ z 1 < 4 * Real.pi) ↔
    ((0 < z 0 ∧ z 0 < 1) ∧ (0 < z 1 ∧ z 1 < 4 * Real.pi))
  tauto

/--
OET anchor: h-3e4095f278f5ea6b
导数下界与全局 co-Lip (ii)：全方向长度下界不足的二维凸开域反例。
The globally C¹ map supplies a C¹ extension of its restriction to the open
rectangle. Both derivative bounds refer to its actual Fréchet derivative.
-/
theorem exists_uniform_derivative_lower_without_global_colip :
    ∃ (Q : Set EuclideanPlane) (F : EuclideanPlane → EuclideanPlane),
      Q.Nonempty ∧ IsOpen Q ∧ Convex ℝ Q ∧ ContDiff ℝ 1 F ∧
      (∀ z ∈ Q, ∀ v, ‖v‖ ≤ ‖fderiv ℝ F z v‖) ∧
      (∀ z ∈ Q, (1 : ℝ) ≤ (fderiv ℝ F z).toLinearMap.singularValues 1) ∧
      ¬ Set.InjOn F Q ∧
      ¬ ∃ κ : ℝ, 0 < κ ∧ EuclideanCoLipOn F Q κ := by
  refine ⟨periodic_polar_domain, periodic_polar,
    periodic_polar_domain_nonempty, periodic_polar_domain_is_open,
    periodic_polar_domain_convex, periodic_polar_cont_diff, ?_, ?_, ?_,
    periodic_polar_counterexample.2.2⟩
  · intro z hz v
    rw [(periodic_polar_has_fderiv z).fderiv]
    exact (periodic_polar_counterexample.2.1 z hz v).2
  · intro z hz
    have hsv : (periodic_polar_differential z).toLinearMap.singularValues 1 =
        Real.exp (z 0) := by
      simpa using periodic_polar_singular_values z (1 : Fin 2)
    rw [(periodic_polar_has_fderiv z).fderiv, hsv]
    exact Real.one_le_exp (le_of_lt hz.1)
  · intro hinj
    exact periodic_polar_pair_ne (hinj periodic_polar_first_mem_domain
      periodic_polar_second_mem_domain periodic_polar_pair_has_equal_output)

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
