import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_geometry
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.norm_ball_bridge

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators
noncomputable section
variable {n : ℕ}

/-- The standard Euclidean norm on the original coordinate-vector model. -/
def euclidean_seminorm : Seminorm ℝ (CoordinateVector n) :=
  (normSeminorm ℝ (EuclideanSpace ℝ (Fin n))).comp euclidean_coordinates.toLinearEquiv.toLinearMap

def euclidean_distance {A : Set (CoordinateVector n)} :
    CoordinatePoint n A → CoordinatePoint n A → ENNReal :=
  coordinate_norm_distance euclidean_seminorm

@[simp] theorem euclidean_distance_some {A : Set (CoordinateVector n)} (x y : A) :
    euclidean_distance (some x) (some y) = ENNReal.ofReal ‖euclidean_coordinates (x.val - y.val)‖ :=
  rfl

def coordinate_support (v : CoordinateVector n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i ≠ 0)

theorem euclidean_norm_sq_support (v : CoordinateVector n) :
    ‖euclidean_coordinates v‖ ^ 2 = ∑ i ∈ coordinate_support v, |v i| ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [euclidean_coordinates, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.toLp_apply, Real.norm_eq_abs]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro i hi hnot
  have hz : v i = 0 := by simpa [coordinate_support, hi] using hnot
  simp [hz]

theorem euclidean_norm_le_support_mul_sup (v : CoordinateVector n) :
    ‖euclidean_coordinates v‖ ≤ Real.sqrt (coordinate_support v).card * ‖v‖ := by
  have hs : ‖euclidean_coordinates v‖ ^ 2 ≤ (coordinate_support v).card * ‖v‖ ^ 2 := by
    rw [euclidean_norm_sq_support]
    calc
      (∑ i ∈ coordinate_support v, |v i| ^ 2) ≤
          ∑ _i ∈ coordinate_support v, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (abs_nonneg _)
          (by simpa [Real.norm_eq_abs] using norm_le_pi_norm v i) 2
      _ = _ := by simp
  have hsqrt : (Real.sqrt (coordinate_support v).card * ‖v‖) ^ 2 =
      (coordinate_support v).card * ‖v‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hnon : 0 ≤ Real.sqrt (coordinate_support v).card * ‖v‖ := by positivity
  nlinarith [norm_nonneg (euclidean_coordinates v)]

/--
OET anchor: h-1873ded007b293ec
**习题（正交坐标支撑的欧氏界）**
The actual coordinate support gives the squared-distance identity and its
Euclidean bound by the original full coordinate distance.
-/
theorem orthogonal_coordinate_support_bound [NeZero n]
    {A : Set (CoordinateVector n)} (x y : A) :
    euclidean_distance (some x) (some y) ^ 2 =
        ∑ i ∈ coordinate_support (x.val - y.val), (coordinate_dist i (some x) (some y)) ^ 2 ∧
      euclidean_distance (some x) (some y) ≤
        ENNReal.ofReal (Real.sqrt (coordinate_support (x.val - y.val)).card) *
          coordinate_full_dist (some x) (some y) := by
  constructor
  · rw [euclidean_distance_some, ← ENNReal.ofReal_pow (norm_nonneg _), euclidean_norm_sq_support,
      ENNReal.ofReal_sum_of_nonneg (by intro i _; positivity)]
    apply Finset.sum_congr rfl
    intro i _
    exact ENNReal.ofReal_pow (abs_nonneg _) 2
  · rw [euclidean_distance_some, coordinate_full_dist_eq_sup_norm,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (euclidean_norm_le_support_mul_sup _)

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
