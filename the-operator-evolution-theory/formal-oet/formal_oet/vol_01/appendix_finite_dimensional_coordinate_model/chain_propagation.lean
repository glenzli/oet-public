import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.fibers_and_derivatives
import Mathlib.Tactic

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model

noncomputable section

open scoped BigOperators

variable {I : Type} [Fintype I]

/-- Real matrix multiplication in OET input-to-output index order. -/
def real_certificate_mul (A₂ A₁ : RealCertificate I) : RealCertificate I :=
  fun i j => ∑ k : I, A₂ k j * A₁ i k

/-- Pointwise absolute value of a signed real matrix. -/
def certificate_abs (A : RealCertificate I) : RealCertificate I :=
  fun i j => |A i j|

theorem abs_real_certificate_mul_le
    (A₂ A₁ : RealCertificate I) (i j : I) :
    |real_certificate_mul A₂ A₁ i j| ≤
      real_certificate_mul (certificate_abs A₂) (certificate_abs A₁) i j := by
  unfold real_certificate_mul certificate_abs
  calc
    |∑ k : I, A₂ k j * A₁ i k| ≤ ∑ k : I, |A₂ k j * A₁ i k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : I, |A₂ k j| * |A₁ i k| := by
      apply Finset.sum_congr rfl
      intro k _
      rw [abs_mul]

/-- The two signed matrices used for the cancellation counterexample. -/
def cancellation_first : RealCertificate (Fin 2) :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1 else
    if i = 1 ∧ j = 1 then 1 else
    if i = 0 ∧ j = 1 then -1 else 0

def cancellation_second : RealCertificate (Fin 2) :=
  fun i j =>
    if i = 0 ∧ j = 0 then 1 else
    if i = 1 ∧ j = 0 then 1 else
    if i = 1 ∧ j = 1 then 1 else 0

theorem cancellation_channel_values :
    real_certificate_mul cancellation_second cancellation_first 0 0 = 0 ∧
    real_certificate_mul (certificate_abs cancellation_second)
      (certificate_abs cancellation_first) 0 0 = 2 := by
  norm_num [real_certificate_mul, cancellation_first, cancellation_second,
    certificate_abs, Fin.sum_univ_two]

/-- Ordered product of a list of real certificates. -/
def real_certificate_list_mul [DecidableEq I] :
    List (RealCertificate I) → RealCertificate I
  | [] => fun i j => if i = j then 1 else 0
  | A :: As => real_certificate_mul A (real_certificate_list_mul As)

/-- The recursively nested sum over all coordinate-channel sequences. -/
def coordinate_channel_sum [DecidableEq I] :
    List (RealCertificate I) → I → I → ℝ
  | [], i, j => if i = j then 1 else 0
  | A :: As, i, j => ∑ k : I, A k j * coordinate_channel_sum As i k

/-- Auxiliary real-matrix channel expansion, also used for signed derivatives.
有序矩阵乘积条目等于对全部中间坐标的递归嵌套求和。
正文的非负证书展开沿用 CH2 的有限矩阵乘积结论，不另设形式对象。
-/
theorem certificate_product_coordinate_channel_expansion [DecidableEq I]
    (As : List (RealCertificate I)) (i j : I) :
    real_certificate_list_mul As i j = coordinate_channel_sum As i j := by
  induction As generalizing j with
  | nil => rfl
  | cons A As ih =>
      unfold real_certificate_list_mul coordinate_channel_sum real_certificate_mul
      apply Finset.sum_congr rfl
      intro k _
      rw [ih]

/-- Scalar upper envelope for successive nonnegative one-step factors. -/
def scalar_prefix_bound : List ℝ → ℝ → ℝ
  | [], initial => initial
  | a :: as, initial => a * scalar_prefix_bound as initial

/-- A chain of scalar one-step bounds, listed from the final step backwards. -/
inductive ScalarChainBound : List ℝ → ℝ → ℝ → Prop
  | nil (initial final : ℝ) (h : final ≤ initial) :
      ScalarChainBound [] initial final
  | cons (a : ℝ) (as : List ℝ) (initial middle final : ℝ)
      (h_tail : ScalarChainBound as initial middle)
      (h_step : final ≤ a * middle) :
      ScalarChainBound (a :: as) initial final

theorem scalar_chain_bound
    (a : List ℝ) (initial final : ℝ)
    (ha : ∀ t ∈ a, 0 ≤ t)
    (hchain : ScalarChainBound a initial final) :
    final ≤ scalar_prefix_bound a initial := by
  induction hchain with
  | nil initial final h => simpa [scalar_prefix_bound] using h
  | cons a as initial middle final htail hstep ih =>
      have ih' := ih (fun t ht => ha t (by simp [ht]))
      exact hstep.trans (mul_le_mul_of_nonneg_left ih' (ha a (by simp)))

/--
Auxiliary scalar recurrence. The source-faithful actual operator chain is proved
in `sparse_matrix_norms.actual_sparse_chain_bound`.
**推论（逐步稀疏证书的复合上界）**
把每步的行支撑界与最大条目之积作为单步非负标量上界，递推得到乘积界。
-/
theorem sparse_step_certificate_composition_bound
    (step_bounds : List ℝ) (initial final : ℝ)
    (h_nonneg : ∀ t ∈ step_bounds, 0 ≤ t)
    (h_chain : ScalarChainBound step_bounds initial final) :
    final ≤ scalar_prefix_bound step_bounds initial :=
  scalar_chain_bound step_bounds initial final h_nonneg h_chain

/-- A real matrix acting on a coordinate vector in OET index order. -/
def real_matrix_vector_mul (M : RealCertificate I) (v : I → ℝ) : I → ℝ :=
  fun j => ∑ i : I, M i j * v i

/-- The affine envelope obtained by unrolling a finite list of matrix steps. -/
def affine_vector_envelope :
    List (RealCertificate I × (I → ℝ)) → (I → ℝ) → I → ℝ
  | [], initial => initial
  | (M, residual) :: steps, initial =>
      real_matrix_vector_mul M (affine_vector_envelope steps initial) + residual

/-- A finite pointwise recurrence, listed from the final step backwards. -/
inductive AffineVectorChain :
    List (RealCertificate I × (I → ℝ)) → (I → ℝ) → (I → ℝ) → Prop
  | nil (initial final : I → ℝ)
      (h : ∀ j, final j ≤ initial j) :
      AffineVectorChain [] initial final
  | cons (M : RealCertificate I) (residual : I → ℝ)
      (steps : List (RealCertificate I × (I → ℝ)))
      (initial middle final : I → ℝ)
      (h_tail : AffineVectorChain steps initial middle)
      (h_step : ∀ j,
        final j ≤ real_matrix_vector_mul M middle j + residual j) :
      AffineVectorChain ((M, residual) :: steps) initial final

theorem affine_vector_chain_unrolled_bound
    (steps : List (RealCertificate I × (I → ℝ)))
    (initial final : I → ℝ)
    (h_nonneg : ∀ step ∈ steps, ∀ i j, 0 ≤ step.1 i j)
    (h_chain : AffineVectorChain steps initial final) :
    ∀ j, final j ≤ affine_vector_envelope steps initial j := by
  induction h_chain with
  | nil initial final h => simpa [affine_vector_envelope] using h
  | cons M residual steps initial middle final h_tail h_step ih =>
      intro j
      have h_tail_nonneg : ∀ step ∈ steps, ∀ i j, 0 ≤ step.1 i j := by
        intro step hstep
        exact h_nonneg step (by simp [hstep])
      have h_middle := ih h_tail_nonneg
      calc
        final j ≤ real_matrix_vector_mul M middle j + residual j := h_step j
        _ ≤ real_matrix_vector_mul M (affine_vector_envelope steps initial) j +
            residual j := by
          have hmul : real_matrix_vector_mul M middle j ≤
              real_matrix_vector_mul M (affine_vector_envelope steps initial) j := by
            unfold real_matrix_vector_mul
            apply Finset.sum_le_sum
            intro i _
            exact mul_le_mul_of_nonneg_left (h_middle i)
              (h_nonneg (M, residual) (by simp) i j)
          linarith
        _ = affine_vector_envelope ((M, residual) :: steps) initial j := rfl


end

end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
