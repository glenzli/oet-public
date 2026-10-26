import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.actual_sparse_norms

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open WithLp
open scoped BigOperators
noncomputable section
variable {n : ℕ} [NeZero n]
local instance : DecidableEq (Fin n) := Classical.decEq _

/-- The first input coordinate is copied to every output coordinate. -/
def single_input_broadcast_matrix (n : ℕ) [NeZero n] : RealCertificate (Fin n) :=
  fun i _ => if i = 0 then 1 else 0

theorem single_input_broadcast_nonnegative (i j : Fin n) :
    0 ≤ single_input_broadcast_matrix n i j := by
  unfold single_input_broadcast_matrix
  split_ifs <;> norm_num

theorem single_input_broadcast_support_count :
    certificate_support_size (single_input_broadcast_matrix n) = n := by
  have he : (Finset.univ.filter (fun ij : Fin n × Fin n =>
      0 < single_input_broadcast_matrix n ij.1 ij.2)) =
      ({0} : Finset (Fin n)) ×ˢ Finset.univ := by
    ext ⟨i, j⟩
    by_cases hi : i = 0 <;> simp [single_input_broadcast_matrix, hi, eq_comm]
  rw [certificate_support_size, he]
  simp

theorem single_input_broadcast_nonzero_proportion :
    (certificate_support_size (single_input_broadcast_matrix n) : ℝ) / (n : ℝ) ^ 2 =
      1 / (n : ℝ) := by
  rw [single_input_broadcast_support_count]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

theorem single_input_broadcast_sup_norm :
    ‖sup_certificate_operator (single_input_broadcast_matrix n)‖ = 1 := by
  rw [sup_operator_norm_eq_row_sum _ single_input_broadcast_nonnegative]
  simp [matrix_infinity_bound, output_row_sum, single_input_broadcast_matrix]

theorem single_input_broadcast_euclidean_apply (u : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    euclidean_certificate_operator (single_input_broadcast_matrix n) u j = u 0 := by
  change (∑ i, (if i = 0 then (1 : ℝ) else 0) * u i) = _
  simp

theorem single_input_broadcast_frobenius_norm :
    certificate_frobenius_norm (single_input_broadcast_matrix n) = Real.sqrt n := by
  unfold certificate_frobenius_norm
  rw [Fintype.sum_prod_type]
  simp [single_input_broadcast_matrix]

theorem single_input_broadcast_euclidean_norm :
    ‖euclidean_certificate_operator (single_input_broadcast_matrix n)‖ = Real.sqrt n := by
  apply le_antisymm
  · exact (euclidean_operator_le_frobenius _).trans_eq single_input_broadcast_frobenius_norm
  · let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single 0 1
    have he : ‖e‖ = 1 := by simp [e]
    have hout : ‖euclidean_certificate_operator (single_input_broadcast_matrix n) e‖ =
        Real.sqrt n := by
      rw [EuclideanSpace.norm_eq]
      simp [single_input_broadcast_euclidean_apply, e]
    calc
      Real.sqrt n = ‖euclidean_certificate_operator (single_input_broadcast_matrix n) e‖ :=
        hout.symm
      _ ≤ ‖euclidean_certificate_operator (single_input_broadcast_matrix n)‖ * ‖e‖ :=
        (euclidean_certificate_operator (single_input_broadcast_matrix n)).le_opNorm e
      _ = ‖euclidean_certificate_operator (single_input_broadcast_matrix n)‖ := by rw [he, mul_one]

/--
OET anchor: h-661612e2b84e7cff
**习题（低非零比例与欧氏放大）**
The same concrete matrix has n nonzero entries, proportion 1/n, infinity
operator norm 1, and Euclidean operator norm sqrt(n). All norms are actual
continuous-linear-map norms; the lower Euclidean bound is witnessed by e_1.
-/
theorem single_input_broadcast_counts_and_norms (n : ℕ) [NeZero n] :
    certificate_support_size (single_input_broadcast_matrix n) = n ∧
    (certificate_support_size (single_input_broadcast_matrix n) : ℝ) / (n : ℝ) ^ 2 =
      1 / (n : ℝ) ∧
    ‖sup_certificate_operator (single_input_broadcast_matrix n)‖ = 1 ∧
    ‖euclidean_certificate_operator (single_input_broadcast_matrix n)‖ = Real.sqrt n :=
  ⟨single_input_broadcast_support_count, single_input_broadcast_nonzero_proportion,
    single_input_broadcast_sup_norm, single_input_broadcast_euclidean_norm⟩

/--
OET anchor: h-661612e2b84e7cff
The nonzero proportion tends to zero along positive dimensions n + 1.
-/
theorem single_input_broadcast_proportion_tendsto_zero :
    Filter.Tendsto (fun k : ℕ =>
      (certificate_support_size (single_input_broadcast_matrix (k + 1)) : ℝ) /
        ((k + 1 : ℕ) : ℝ) ^ 2) Filter.atTop (nhds 0) := by
  simp_rw [single_input_broadcast_nonzero_proportion, one_div]
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))

/--
OET anchor: h-661612e2b84e7cff
The actual Euclidean operator norms are unbounded and tend to infinity.
-/
theorem single_input_broadcast_euclidean_norm_tendsto_atTop :
    Filter.Tendsto (fun k : ℕ =>
      ‖euclidean_certificate_operator (single_input_broadcast_matrix (k + 1))‖)
      Filter.atTop Filter.atTop := by
  simp_rw [single_input_broadcast_euclidean_norm]
  exact Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop.comp (Filter.tendsto_add_atTop_nat 1))

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
