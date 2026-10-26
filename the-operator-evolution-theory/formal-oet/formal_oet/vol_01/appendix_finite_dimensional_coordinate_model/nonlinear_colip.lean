import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_and_calculus
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model

noncomputable section

open scoped InnerProduct InnerProductSpace RealInnerProductSpace

/-- A global scalar co-Lip lower bound on a subset of a normed space. -/
def EuclideanCoLipOn {E : Type} [NormedAddCommGroup E]
    (F : E → E) (Q : Set E) (κ : ℝ) : Prop :=
  ∀ x ∈ Q, ∀ y ∈ Q, κ * ‖x - y‖ ≤ ‖F x - F y‖

/-- The Euclidean plane used by the periodic polar counterexample. -/
abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

/-- The convex open rectangle in the periodic polar counterexample. -/
def periodic_polar_domain : Set EuclideanPlane :=
  {z | 0 < z 0 ∧ z 0 < 1 ∧ 0 < z 1 ∧ z 1 < 4 * Real.pi}

/-- The periodic polar map `(s,t) ↦ exp(s) (cos t, sin t)`. -/
def periodic_polar (z : EuclideanPlane) : EuclideanPlane :=
  !₂[Real.exp (z 0) * Real.cos (z 1),
      Real.exp (z 0) * Real.sin (z 1)]

/-- The first point in the explicit noninjective pair. -/
def periodic_polar_first : EuclideanPlane :=
  !₂[(1 : ℝ) / 2, Real.pi]

/-- The second point, one full angular period after `periodic_polar_first`. -/
def periodic_polar_second : EuclideanPlane :=
  !₂[(1 : ℝ) / 2, Real.pi + 2 * Real.pi]

/--
A standard-calculus certificate for the periodic polar map. The certificate
contains only the derivative identification and the elementary fact that its
Jacobi map is `exp(s)` times an orthogonal rotation.
-/
structure PeriodicPolarDifferentialCertificate where
  differential : EuclideanPlane → EuclideanPlane →L[ℝ] EuclideanPlane
  continuously_differentiable : ContDiff ℝ 1 periodic_polar
  has_derivative : ∀ z, HasFDerivAt periodic_polar (differential z) z
  norm_action : ∀ z v, ‖differential z v‖ = Real.exp (z 0) * ‖v‖

theorem periodic_polar_first_mem_domain :
    periodic_polar_first ∈ periodic_polar_domain := by
  simp only [periodic_polar_first, periodic_polar_domain, Set.mem_setOf_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · exact Real.pi_pos
  · linarith [Real.pi_pos]

theorem periodic_polar_second_mem_domain :
    periodic_polar_second ∈ periodic_polar_domain := by
  simp only [periodic_polar_second, periodic_polar_domain, Set.mem_setOf_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

theorem periodic_polar_pair_has_equal_output :
    periodic_polar periodic_polar_first = periodic_polar periodic_polar_second := by
  ext i
  fin_cases i <;>
    simp [periodic_polar, periodic_polar_first, periodic_polar_second,
      Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem periodic_polar_pair_ne :
    periodic_polar_first ≠ periodic_polar_second := by
  intro h
  have hcoord := congrArg (fun z : EuclideanPlane => z 1) h
  simp [periodic_polar_first, periodic_polar_second] at hcoord

/--
Auxiliary conditional calculation. The actual differential, norm action, and canonical
singular values are constructed in `periodic_polar_derivative.lean`.
**命题（一致导数非退化不蕴含全局 co-Lip）**
周期极坐标映射的导数在每点都是至少单位尺度的正交缩放，
但映射仍因角变量的周期性而不满足任何正的全局 co-Lip 下界。
The standard derivative calculation is the external premise; domain
membership, the periodic collision, and failure of every positive co-Lip
constant are proved here.
-/
theorem uniform_derivative_nondegeneracy_does_not_imply_global_colip
    (hD : PeriodicPolarDifferentialCertificate) :
    ContDiff ℝ 1 periodic_polar ∧
    (∀ z ∈ periodic_polar_domain, ∀ v,
      ‖hD.differential z v‖ = Real.exp (z 0) * ‖v‖ ∧
      ‖v‖ ≤ ‖hD.differential z v‖) ∧
    ¬ ∃ κ : ℝ, 0 < κ ∧ EuclideanCoLipOn periodic_polar periodic_polar_domain κ := by
  refine ⟨hD.continuously_differentiable, ?_, ?_⟩
  · intro z hz v
    refine ⟨hD.norm_action z v, ?_⟩
    rw [hD.norm_action]
    have hexp : 1 ≤ Real.exp (z 0) := Real.one_le_exp (le_of_lt hz.1)
    calc
      ‖v‖ = 1 * ‖v‖ := by ring
      _ ≤ Real.exp (z 0) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hexp (norm_nonneg v)
  · rintro ⟨κ, hκ, hcolip⟩
    have hbound := hcolip periodic_polar_first periodic_polar_first_mem_domain
      periodic_polar_second periodic_polar_second_mem_domain
    have hnorm : 0 < ‖periodic_polar_first - periodic_polar_second‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr periodic_polar_pair_ne)
    have hpositive : 0 < κ * ‖periodic_polar_first - periodic_polar_second‖ :=
      mul_pos hκ hnorm
    rw [periodic_polar_pair_has_equal_output, sub_self, norm_zero] at hbound
    exact (not_lt_of_ge hbound) hpositive

/-- A `C¹` realization of `D` as the derivative on an open neighborhood of `Q`. -/
def C1DerivativeOnOpenNeighborhood
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → E) (D : E → E →L[ℝ] E) (Q : Set E) : Prop :=
  ∃ O : Set E,
    IsOpen O ∧ Q ⊆ O ∧ ContDiffOn ℝ 1 F O ∧
      ∀ z ∈ Q, HasFDerivAt F (D z) z

/-- A pointwise Jacobi quadratic lower bound gives the two-point inequality
by applying the real mean value theorem along the actual line segment. -/
theorem integrated_quadratic_lower
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → E) (D : E → E →L[ℝ] E) (Q : Set E) (μ : ℝ)
    (hC1 : C1DerivativeOnOpenNeighborhood F D Q) (hQ : Convex ℝ Q)
    (hD : ∀ z ∈ Q, ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪D z v, v⟫_ℝ)
    (x : E) (hx : x ∈ Q) (y : E) (hy : y ∈ Q) :
    μ * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫_ℝ := by
  rcases hC1 with ⟨O, hO, hQO, hcont, hderiv⟩
  let g : ℝ → ℝ := fun t => ⟪F (AffineMap.lineMap y x t), x - y⟫_ℝ
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt g ⟪D (AffineMap.lineMap y x t) (x - y), x - y⟫_ℝ t := by
    have hf := (hderiv _ (hQ.lineMap_mem hy hx ht)).comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := y) (b := x))
    simpa [g] using HasDerivAt.inner ℝ hf (hasDerivAt_const t (x - y))
  have hb := (convex_Icc (0 : ℝ) 1).mul_sub_le_image_sub_of_le_deriv
    (fun t ht => (hg t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    (fun t ht => by
      rw [(hg t (interior_subset ht)).deriv]
      exact hD _ (hQ.lineMap_mem hy hx (interior_subset ht)) (x - y))
    0 (by simp) 1 (by simp) (by norm_num)
  simpa [g, inner_sub_left] using hb

/--
OET anchor: h-3e4095f278f5ea6b
**命题（导数下界与全局 co-Lip，(i)）**
导数沿输入方向的正向分量下界经线段积分给出强单调性，再与 Cauchy-Schwarz 不等式共同推出
全局欧氏 co-Lip 下界和受限单射性。
The two-point quadratic inequality is derived above from the real mean value
theorem on the line segment; no integration certificate is required.
-/
theorem jacobi_quadratic_lower_gives_global_colip
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : E → E) (D : E → E →L[ℝ] E) (Q : Set E)
    (μ : ℝ) (hμ : 0 < μ)
    (hQ_nonempty : Q.Nonempty) (hQ_convex : Convex ℝ Q)
    (hC1 : C1DerivativeOnOpenNeighborhood F D Q)
    (hD : ∀ z ∈ Q, ∀ v, μ * ‖v‖ ^ 2 ≤ ⟪D z v, v⟫_ℝ) :
    EuclideanCoLipOn F Q μ ∧ Set.InjOn F Q := by
  have _ := hQ_nonempty
  have hcolip : EuclideanCoLipOn F Q μ := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst y
      simp
    · have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      have hlower := integrated_quadratic_lower F D Q μ hC1 hQ_convex hD x hx y hy
      have hupper := real_inner_le_norm (F x - F y) (x - y)
      have hproduct :
          μ * ‖x - y‖ ^ 2 ≤ ‖F x - F y‖ * ‖x - y‖ :=
        hlower.trans hupper
      nlinarith
  refine ⟨hcolip, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have hnorm : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hbound := hcolip x hx y hy
  rw [hxy, sub_self, norm_zero] at hbound
  have hpositive : 0 < μ * ‖x - y‖ := mul_pos hμ hnorm
  exact (not_lt_of_ge hbound) hpositive

/--
OET anchor: h-3e4095f278f5ea6b
**命题（导数下界与全局 co-Lip，(i) 的对称部表达）**
-/
theorem jacobi_quadratic_form_eq_symmetric_part
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) (v : E) :
    ⟪((2 : ℝ)⁻¹ • (A + A†)) v, v⟫_ℝ = ⟪A v, v⟫_ℝ := by
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    real_inner_smul_left, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  ring

end

end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
