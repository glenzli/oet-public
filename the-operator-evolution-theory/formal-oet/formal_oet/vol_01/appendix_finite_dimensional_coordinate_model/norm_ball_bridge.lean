import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.finite_dimensional_geometry
import Mathlib.Analysis.Seminorm

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.appendix_separating_gauge_specialization
noncomputable section

/-- The original full coordinate distance is the ordinary supremum norm distance. -/
theorem coordinate_full_dist_eq_sup_norm {n : ℕ} [NeZero n]
    {A : Set (CoordinateVector n)} (x y : A) :
    coordinate_full_dist (some x) (some y) = ENNReal.ofReal ‖x.val - y.val‖ := by
  simp only [coordinate_full_dist, full_gauge_dist, comp_pseudo_metric,
    full_nonempty_finset, coordinate_dist]
  rw [Pi.norm_def, ENNReal.ofReal_coe_nnreal, ENNReal.coe_finset_sup]
  congr 1
  funext i
  simp [ENNReal.coe_nnreal_eq, Real.norm_eq_abs]

/-- A genuine seminorm extended by the same absorbing-point convention.
A positive lower norm-equivalence bound below guarantees separation on `A`. -/
def coordinate_norm_distance {n : ℕ} {A : Set (CoordinateVector n)}
    (p : Seminorm ℝ (CoordinateVector n)) : CoordinatePoint n A → CoordinatePoint n A → ENNReal
  | some x, some y => ENNReal.ofReal (p (x.val - y.val))
  | none, none => 0
  | _, _ => ⊤

/-- Build the ball comparison from the stated real norm-equivalence constants;
neither ball inclusion is an input. -/
def norm_ball_comparison_of_norm_bounds {n : ℕ} [NeZero n]
    {A : Set (CoordinateVector n)} (p : Seminorm ℝ (CoordinateVector n))
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (hlower : ∀ v, a * ‖v‖ ≤ p v) (hupper : ∀ v, p v ≤ b * ‖v‖) :
    NormBallComparisonCertificate (CoordinatePoint n A)
      coordinate_full_dist (coordinate_norm_distance p)
      (ENNReal.ofReal (ε / b)) (ENNReal.ofReal ε) (ENNReal.ofReal (ε / a)) := by
  have hsmall : 0 < ENNReal.ofReal (ε / b) := ENNReal.ofReal_pos.mpr (div_pos hε hb)
  have hlarge : 0 < ENNReal.ofReal (ε / a) := ENNReal.ofReal_pos.mpr (div_pos hε ha)
  constructor
  · intro x y hxy
    cases x with
    | none =>
      cases y <;> simp_all [coordinate_full_dist, full_gauge_dist, comp_pseudo_metric,
        full_nonempty_finset, coordinate_dist, coordinate_norm_distance]
    | some x =>
      cases y with
      | none =>
        simp [coordinate_full_dist, full_gauge_dist, comp_pseudo_metric,
          full_nonempty_finset, coordinate_dist] at hxy
        have ht := lt_of_le_of_lt (Finset.le_sup (f := fun _ : Fin n => (⊤ : ENNReal))
          (Finset.mem_univ (0 : Fin n))) hxy
        exact (not_lt_of_ge le_top ht).elim
      | some y =>
        rw [coordinate_full_dist_eq_sup_norm,
          ENNReal.ofReal_lt_ofReal_iff (div_pos hε hb)] at hxy
        change ENNReal.ofReal (p (x.val - y.val)) < ENNReal.ofReal ε
        apply (ENNReal.ofReal_lt_ofReal_iff hε).mpr
        exact (hupper _).trans_lt (by nlinarith [(lt_div_iff₀ hb).mp hxy])
  · intro x y hxy
    cases x with
    | none =>
      cases y <;> simp_all [coordinate_full_dist, full_gauge_dist, comp_pseudo_metric,
        full_nonempty_finset, coordinate_dist, coordinate_norm_distance]
    | some x =>
      cases y with
      | none => simp [coordinate_norm_distance] at hxy
      | some y =>
        change ENNReal.ofReal (p (x.val - y.val)) < ENNReal.ofReal ε at hxy
        have hp := (ENNReal.ofReal_lt_ofReal_iff hε).mp hxy
        rw [coordinate_full_dist_eq_sup_norm,
          ENNReal.ofReal_lt_ofReal_iff (div_pos hε ha)]
        apply (lt_div_iff₀ ha).mpr
        nlinarith [hlower (x.val - y.val)]

/--
OET anchor: h-5cd365cd756cb93e
**命题（范数比较、拓扑与覆盖）**
实际坐标全族距离与范数距离在具体半径 ε/b、ε、ε/a 下的球包含及内覆盖数比较。
-/
theorem coordinate_norm_ball_and_covering_number_comparison {n : ℕ} [NeZero n]
    {A : Set (CoordinateVector n)} (p : Seminorm ℝ (CoordinateVector n))
    (a b ε : ℝ) (ha : 0 < a) (hb : 0 < b) (hε : 0 < ε)
    (hlower : ∀ v, a * ‖v‖ ≤ p v) (hupper : ∀ v, p v ≤ b * ‖v‖)
    (S : Set (CoordinatePoint n A)) :
    (∀ x : CoordinatePoint n A, ball coordinate_full_dist x (ENNReal.ofReal (ε / b)) ⊆
      ball (coordinate_norm_distance p) x (ENNReal.ofReal ε)) ∧
    (∀ x : CoordinatePoint n A, ball (coordinate_norm_distance p) x (ENNReal.ofReal ε) ⊆
      ball coordinate_full_dist x (ENNReal.ofReal (ε / a))) ∧
    covering_number coordinate_full_dist (ENNReal.ofReal (ε / a)) S ≤
      covering_number (coordinate_norm_distance p) (ENNReal.ofReal ε) S ∧
    covering_number (coordinate_norm_distance p) (ENNReal.ofReal ε) S ≤
      covering_number coordinate_full_dist (ENNReal.ofReal (ε / b)) S :=
  norm_ball_and_covering_number_comparison _ _ _ _ _ S
    (norm_ball_comparison_of_norm_bounds p a b ε ha hb hε hlower hupper)

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
