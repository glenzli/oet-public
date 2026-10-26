import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.perturbation_bounds
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open scoped BigOperators
noncomputable section
variable {n : ℕ} [NeZero n]
local instance : DecidableEq (Fin n) := Classical.decEq _

def sup_certificate_operator (L : RealCertificate (Fin n)) :
    CoordinateVector n →L[ℝ] CoordinateVector n :=
  (Matrix.toLin' (fun j i => L i j)).toContinuousLinearMap

def one_certificate_operator (L : RealCertificate (Fin n)) :
    PiLp 1 (fun _ : Fin n => ℝ) →L[ℝ] PiLp 1 (fun _ : Fin n => ℝ) :=
  (PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin n => ℝ)).symm.toContinuousLinearMap.comp
    ((sup_certificate_operator L).comp
      (PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin n => ℝ)).toContinuousLinearMap)

theorem sup_operator_norm_le_row_sum (L : RealCertificate (Fin n)) (hL : ∀ i j, 0 ≤ L i j) :
    ‖sup_certificate_operator L‖ ≤ matrix_infinity_bound L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (matrix_infinity_bound_nonneg L hL)
  intro v
  exact matrix_vector_mul_norm_le L hL v

/-- For a nonnegative matrix, the all-ones vector attains its maximum row sum. -/
theorem sup_operator_norm_eq_row_sum (L : RealCertificate (Fin n))
    (hL : ∀ i j, 0 ≤ L i j) :
    ‖sup_certificate_operator L‖ = matrix_infinity_bound L := by
  apply le_antisymm (sup_operator_norm_le_row_sum L hL)
  unfold matrix_infinity_bound
  apply Finset.sup'_le
  intro j _
  have hrow : (sup_certificate_operator L) (fun _ : Fin n => (1 : ℝ)) j =
      output_row_sum L j := by
    change (∑ i, L i j * 1) = _
    simp [output_row_sum]
  calc
    output_row_sum L j ≤ |output_row_sum L j| := le_abs_self _
    _ = ‖((sup_certificate_operator L) (fun _ : Fin n => (1 : ℝ))) j‖ := by
      rw [hrow, Real.norm_eq_abs]
    _ ≤ ‖(sup_certificate_operator L) (fun _ : Fin n => (1 : ℝ))‖ :=
      norm_le_pi_norm _ j
    _ ≤ ‖sup_certificate_operator L‖ * ‖(fun _ : Fin n => (1 : ℝ))‖ :=
      (sup_certificate_operator L).le_opNorm _
    _ = ‖sup_certificate_operator L‖ := by simp

/-- The row-sum envelope is exactly the scalar envelope formed from actual
infinity operator norms, on every nonnegative step matrix. -/
theorem actual_norm_scalar_perturbation_sum_eq
    (steps : List (RealCertificate (Fin n) × CoordinateVector n)) (initial : ℝ)
    (hM : ∀ step ∈ steps, ∀ i j, 0 ≤ step.1 i j) :
    scalar_perturbation_sum (fun M => ‖sup_certificate_operator M‖) steps initial =
      scalar_perturbation_sum matrix_infinity_bound steps initial := by
  induction steps with
  | nil => rfl
  | cons step steps ih =>
    rw [scalar_perturbation_sum_cons, scalar_perturbation_sum_cons,
      sup_operator_norm_eq_row_sum step.1 (hM step (by simp)),
      ih (fun next hn => hM next (by simp [hn]))]

/--
OET anchor: h-ef39fb9c4b025f07
**习题（逐步扰动与稀疏传播）**
The scalar factors are the norms of the actual matrix operators on the sup-norm
space. The vector bound and sparse product bound retain the arbitrary initial
perturbation and every downstream residual, including empty products.
-/
theorem finite_nonnegative_actual_norm_perturbation_bounds
    (steps : List (RealCertificate (Fin n) × CoordinateVector n))
    (initial final : CoordinateVector n)
    (hM : ∀ step ∈ steps, ∀ i j, 0 ≤ step.1 i j)
    (hfinal : ∀ j, 0 ≤ final j) (hchain : AffineVectorChain steps initial final) :
    (∀ j, final j ≤
      (real_matrix_vector_mul (real_certificate_list_mul (steps.map Prod.fst)) initial +
        matrix_residual_sum steps) j) ∧
    ‖final‖ ≤ scalar_perturbation_sum (fun M => ‖sup_certificate_operator M‖)
      steps ‖initial‖ ∧
    ‖final‖ ≤ scalar_perturbation_sum
      (fun M => row_support_size M * certificate_entry_max M) steps ‖initial‖ := by
  have h := finite_nonnegative_perturbation_bounds steps initial final hM hfinal hchain
  refine ⟨h.1, ?_, h.2.2⟩
  rw [actual_norm_scalar_perturbation_sum_eq steps ‖initial‖ hM]
  exact h.2.1

theorem one_operator_norm_le_column_sum (L : RealCertificate (Fin n)) (hL : ∀ i j, 0 ≤ L i j) :
    ‖one_certificate_operator L‖ ≤ matrix_one_bound L := by
  have hnon : 0 ≤ matrix_one_bound L :=
    (Finset.sum_nonneg (fun j _ => hL 0 j)).trans
      (Finset.le_sup' (fun i : Fin n => ∑ j, L i j) (Finset.mem_univ 0))
  apply ContinuousLinearMap.opNorm_le_bound _ hnon
  intro v
  rw [PiLp.norm_eq_of_L1, PiLp.norm_eq_of_L1]
  change (∑ j, ‖∑ i, L i j * v i‖) ≤ matrix_one_bound L * ∑ i, ‖v i‖
  simp only [Real.norm_eq_abs]
  calc
    (∑ j, |∑ i, L i j * v i|) ≤ ∑ j, ∑ i, L i j * |v i| := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [abs_mul, abs_of_nonneg (hL _ _)] using
        Finset.abs_sum_le_sum_abs (fun i => L i j * v i) Finset.univ
    _ = ∑ i, (∑ j, L i j) * |v i| := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ i, matrix_one_bound L * |v i| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right
        (Finset.le_sup' (fun i : Fin n => ∑ j, L i j) (Finset.mem_univ i)) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/--
All three left sides below are the norms of actual continuous linear maps in
the specified normed spaces, not names for row/column-sum formulas.
-/
theorem all_actual_sparse_operator_norms (L : RealCertificate (Fin n))
    (hL : ∀ i j, 0 ≤ L i j) :
    ‖sup_certificate_operator L‖ ≤ row_support_size L * certificate_entry_max L ∧
    ‖one_certificate_operator L‖ ≤ column_support_size L * certificate_entry_max L ∧
    ‖euclidean_certificate_operator L‖ ≤
      Real.sqrt (certificate_support_size L) * certificate_entry_max L :=
  ⟨(sup_operator_norm_le_row_sum L hL).trans (matrix_infinity_le_sparse_row_bound L hL),
    (one_operator_norm_le_column_sum L hL).trans (matrix_one_le_sparse_column_bound L hL),
    (euclidean_operator_le_frobenius L).trans (frobenius_le_sparse_bound L hL)⟩


/--
OET anchor: h-36ae8406e21d3213
**推论（行支撑控制的距离上界）**
This is a matrix statement for every finite nonnegative real realization,
independent of whether the matrix is used as an operator's Lip certificate.
-/
theorem actual_row_count_operator_norm (L : RealCertificate (Fin n))
    (hL : ∀ i j, 0 ≤ L i j) :
    ‖sup_certificate_operator L‖ ≤ row_support_size L * certificate_entry_max L :=
  (all_actual_sparse_operator_norms L hL).1

/-- An external row-count bound and entry bound give the advertised s * lambda
coefficient. Nonnegativity of s follows from its row-count lower bound. -/
theorem row_count_coefficient_le_envelope (L : RealCertificate (Fin n))
    (hL : ∀ i j, 0 ≤ L i j) (s lambda : ℝ)
    (hs : (row_support_size L : ℝ) ≤ s) (hlambda : certificate_entry_max L ≤ lambda) :
    row_support_size L * certificate_entry_max L ≤ s * lambda :=
  mul_le_mul hs hlambda (certificate_entry_max_nonneg L hL) ((Nat.cast_nonneg _).trans hs)

/--
OET anchor: h-36ae8406e21d3213
Replacing the actual maximum row count and maximum entry by upper bounds
preserves the same actual infinity operator-norm estimate.
-/
theorem actual_row_count_operator_norm_envelope (L : RealCertificate (Fin n))
    (hL : ∀ i j, 0 ≤ L i j) (s lambda : ℝ)
    (hs : (row_support_size L : ℝ) ≤ s) (hlambda : certificate_entry_max L ≤ lambda) :
    ‖sup_certificate_operator L‖ ≤ s * lambda :=
  (actual_row_count_operator_norm L hL).trans
    (row_count_coefficient_le_envelope L hL s lambda hs hlambda)

/--
OET anchor: h-36ae8406e21d3213
The same external coefficient bounds the actual full-coordinate distance on Q.
-/
theorem actual_row_count_lip_distance_envelope {A : Set (CoordinateVector n)}
    (φ : Operator (CoordinatePoint n A) none)
    (Q : Set (CoordinatePoint n A)) (L : Fin n → Fin n → ENNReal)
    (hf : ∀ i j, L i j ≠ ⊤)
    (hL : IsLipMatrix coordinate_dist φ Q L)
    (s lambda : ℝ) (hs : (row_support_size (real_realization L) : ℝ) ≤ s)
    (hlambda : certificate_entry_max (real_realization L) ≤ lambda)
    (x y : CoordinatePoint n A) (hx : x ∈ Q) (hy : y ∈ Q) :
    coordinate_full_dist (φ.func x) (φ.func y) ≤
      ENNReal.ofReal (s * lambda) * coordinate_full_dist x y := by
  apply (actual_row_count_lip_distance φ Q L hf hL x y hx hy).trans
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal
    (row_count_coefficient_le_envelope (real_realization L)
      (fun _ _ => ENNReal.toReal_nonneg) s lambda hs hlambda)) _

/--
OET anchor: h-f09514ceb9b32a5a
**习题（非零计数与其他范数）**
The column-count and total-count bounds concern the norms of actual operators
on l1 and Euclidean space, respectively.
-/
theorem actual_column_and_total_count_norm_bounds (L : RealCertificate (Fin n))
    (hL : ∀ i j, 0 ≤ L i j) :
    ‖one_certificate_operator L‖ ≤ column_support_size L * certificate_entry_max L ∧
    ‖euclidean_certificate_operator L‖ ≤
      Real.sqrt (certificate_support_size L) * certificate_entry_max L :=
  (all_actual_sparse_operator_norms L hL).2

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
