import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.sparse_matrix_norms
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.chain_propagation

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open scoped BigOperators
noncomputable section
variable {n : ℕ} [NeZero n]
local instance : DecidableEq (Fin n) := Classical.decEq _

theorem matrix_vector_mul_add (M : RealCertificate (Fin n)) (u v : CoordinateVector n) :
    real_matrix_vector_mul M (u + v) = real_matrix_vector_mul M u + real_matrix_vector_mul M v := by
  ext j
  simp [real_matrix_vector_mul, mul_add, Finset.sum_add_distrib]

theorem matrix_vector_mul_sum {ι : Type} (s : Finset ι)
    (M : RealCertificate (Fin n)) (v : ι → CoordinateVector n) :
    real_matrix_vector_mul M (∑ t ∈ s, v t) = ∑ t ∈ s, real_matrix_vector_mul M (v t) := by
  ext j
  simp only [real_matrix_vector_mul, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem matrix_vector_mul_comp (M N : RealCertificate (Fin n)) (v : CoordinateVector n) :
    real_matrix_vector_mul (real_certificate_mul M N) v =
      real_matrix_vector_mul M (real_matrix_vector_mul N v) := by
  ext j
  simp only [real_matrix_vector_mul, real_certificate_mul, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm

theorem matrix_vector_mul_empty (v : CoordinateVector n) :
    real_matrix_vector_mul (real_certificate_list_mul []) v = v := by
  ext j
  simp [real_matrix_vector_mul, real_certificate_list_mul]

/-- The displayed sum of the propagated residuals. The list is outermost first,
so `take t` is exactly the downstream product after the residual at position t. -/
def matrix_residual_sum (steps : List (RealCertificate (Fin n) × CoordinateVector n)) :
    CoordinateVector n :=
  ∑ t : Fin steps.length,
    real_matrix_vector_mul (real_certificate_list_mul ((steps.take t.val).map Prod.fst)) steps[t].2

theorem matrix_residual_sum_cons (M : RealCertificate (Fin n)) (r : CoordinateVector n)
    (steps : List (RealCertificate (Fin n) × CoordinateVector n)) :
    matrix_residual_sum ((M, r) :: steps) = r + real_matrix_vector_mul M (matrix_residual_sum steps) := by
  unfold matrix_residual_sum
  simp only [List.length_cons]
  erw [Fin.sum_univ_succ]
  simp only [Fin.getElem_fin, Fin.val_zero, List.take_zero, List.map_nil, List.getElem_cons_zero,
    Fin.val_succ, List.take_succ_cons, List.map_cons, List.getElem_cons_succ]
  rw [matrix_vector_mul_empty]
  simp only [real_certificate_list_mul, matrix_vector_mul_comp]
  rw [matrix_vector_mul_sum]

/-- Explicit variation-of-constants identity, including the empty product. -/
theorem affine_vector_envelope_closed_form
    (steps : List (RealCertificate (Fin n) × CoordinateVector n)) (initial : CoordinateVector n) :
    affine_vector_envelope steps initial =
      real_matrix_vector_mul (real_certificate_list_mul (steps.map Prod.fst)) initial +
        matrix_residual_sum steps := by
  induction steps with
  | nil => simp [affine_vector_envelope, matrix_residual_sum, matrix_vector_mul_empty]
  | cons step steps ih =>
    rcases step with ⟨M, r⟩
    rw [affine_vector_envelope, ih, matrix_vector_mul_add, matrix_residual_sum_cons]
    simp only [List.map_cons, real_certificate_list_mul, matrix_vector_mul_comp]
    abel

theorem matrix_infinity_bound_nonneg (M : RealCertificate (Fin n)) (hM : ∀ i j, 0 ≤ M i j) :
    0 ≤ matrix_infinity_bound M :=
  (Finset.sum_nonneg (fun i _ => hM i 0)).trans
    (Finset.le_sup' (output_row_sum M) (Finset.mem_univ 0))

theorem matrix_vector_mul_norm_le (M : RealCertificate (Fin n))
    (hM : ∀ i j, 0 ≤ M i j) (v : CoordinateVector n) :
    ‖real_matrix_vector_mul M v‖ ≤ matrix_infinity_bound M * ‖v‖ := by
  rw [← vector_sup_abs_eq_norm]
  apply Finset.sup'_le
  intro j _
  calc
    |∑ i, M i j * v i| ≤ ∑ i, |M i j * v i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, M i j * |v i| := by simp_rw [abs_mul, abs_of_nonneg (hM _ _)]
    _ ≤ ∑ i, M i j * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v i) (hM i j)
    _ = output_row_sum M j * ‖v‖ := by rw [output_row_sum, Finset.sum_mul]
    _ ≤ matrix_infinity_bound M * ‖v‖ :=
      mul_le_mul_of_nonneg_right (Finset.le_sup' (output_row_sum M) (Finset.mem_univ j)) (norm_nonneg _)

/-- The exact scalar product and downstream residual sum printed in the text. -/
def scalar_perturbation_sum
    (a : RealCertificate (Fin n) → ℝ)
    (steps : List (RealCertificate (Fin n) × CoordinateVector n)) (initial : ℝ) : ℝ :=
  (steps.map (fun step => a step.1)).prod * initial +
    ∑ t : Fin steps.length, ((steps.take t.val).map (fun step => a step.1)).prod * ‖steps[t].2‖

theorem scalar_perturbation_sum_cons
    (a : RealCertificate (Fin n) → ℝ) (M : RealCertificate (Fin n)) (r : CoordinateVector n)
    (steps : List (RealCertificate (Fin n) × CoordinateVector n)) (initial : ℝ) :
    scalar_perturbation_sum a ((M, r) :: steps) initial =
      a M * scalar_perturbation_sum a steps initial + ‖r‖ := by
  unfold scalar_perturbation_sum
  simp only [List.length_cons]
  erw [Fin.sum_univ_succ]
  simp only [Fin.getElem_fin, List.map_cons, List.prod_cons, Fin.val_zero, List.take_zero, List.map_nil,
    List.prod_nil, one_mul, List.getElem_cons_zero, Fin.val_succ, List.take_succ_cons,
    List.getElem_cons_succ]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  ring

theorem envelope_norm_le_scalar_perturbation_sum
    (a : RealCertificate (Fin n) → ℝ)
    (steps : List (RealCertificate (Fin n) × CoordinateVector n)) (initial : CoordinateVector n)
    (hM : ∀ step ∈ steps, ∀ i j, 0 ≤ step.1 i j)
    (ha : ∀ step ∈ steps, matrix_infinity_bound step.1 ≤ a step.1) :
    ‖affine_vector_envelope steps initial‖ ≤ scalar_perturbation_sum a steps ‖initial‖ := by
  induction steps with
  | nil => simp [affine_vector_envelope, scalar_perturbation_sum]
  | cons step steps ih =>
    rcases step with ⟨M, r⟩
    have hMn := hM (M, r) (by simp)
    have han := (matrix_infinity_bound_nonneg M hMn).trans (ha (M, r) (by simp))
    have hi := ih (fun step hs => hM step (by simp [hs])) (fun step hs => ha step (by simp [hs]))
    have hm := matrix_vector_mul_norm_le (n := n) M hMn (affine_vector_envelope steps initial)
    rw [affine_vector_envelope, scalar_perturbation_sum_cons]
    calc
      _ ≤ ‖real_matrix_vector_mul M (affine_vector_envelope steps initial)‖ + ‖r‖ := norm_add_le _ _
      _ ≤ matrix_infinity_bound M * ‖affine_vector_envelope steps initial‖ + ‖r‖ :=
        add_le_add hm le_rfl
      _ ≤ a M * ‖affine_vector_envelope steps initial‖ + ‖r‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (ha (M, r) (by simp)) (norm_nonneg _)) le_rfl
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hi han) le_rfl

/--
OET anchor: h-ef39fb9c4b025f07
**习题（逐步扰动与稀疏传播）**
The assumed component recurrence is exactly a hypothesis of the exercise.
The initial perturbation need not vanish. The vector bound retains its full
matrix product and the downstream residual sum; both the matrix-norm scalar
bound and the support-count scalar bound are proved, not supplied as input.
-/
theorem finite_nonnegative_perturbation_bounds
    (steps : List (RealCertificate (Fin n) × CoordinateVector n))
    (initial final : CoordinateVector n)
    (hM : ∀ step ∈ steps, ∀ i j, 0 ≤ step.1 i j)
    (hfinal : ∀ j, 0 ≤ final j) (hchain : AffineVectorChain steps initial final) :
    (∀ j, final j ≤
      (real_matrix_vector_mul (real_certificate_list_mul (steps.map Prod.fst)) initial +
        matrix_residual_sum steps) j) ∧
    ‖final‖ ≤ scalar_perturbation_sum matrix_infinity_bound steps ‖initial‖ ∧
    ‖final‖ ≤ scalar_perturbation_sum
      (fun M => row_support_size M * certificate_entry_max M) steps ‖initial‖ := by
  have hv := affine_vector_chain_unrolled_bound steps initial final hM hchain
  have hn : ‖final‖ ≤ ‖affine_vector_envelope steps initial‖ := by
    rw [← vector_sup_abs_eq_norm]
    apply Finset.sup'_le
    intro j _
    calc
      |final j| = final j := abs_of_nonneg (hfinal j)
      _ ≤ affine_vector_envelope steps initial j := hv j
      _ ≤ |affine_vector_envelope steps initial j| := le_abs_self _
      _ ≤ ‖affine_vector_envelope steps initial‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm (affine_vector_envelope steps initial) j
  refine ⟨?_, hn.trans (envelope_norm_le_scalar_perturbation_sum _ _ _ hM (fun _ _ => le_rfl)),
    hn.trans (envelope_norm_le_scalar_perturbation_sum _ _ _ hM ?_)⟩
  · simpa only [affine_vector_envelope_closed_form] using hv
  · intro step hs
    exact (sparse_actual_matrix_norm_bounds step.1 (hM step hs)).1

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
