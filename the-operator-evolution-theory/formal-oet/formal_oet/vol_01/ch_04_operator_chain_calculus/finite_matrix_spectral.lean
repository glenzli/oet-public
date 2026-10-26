import formal_oet.vol_01.ch_04_operator_chain_calculus.prefix_products
import formal_oet.vol_01.ch_02_operator_bounds.matrix_composition
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Matrix.Normed

namespace formal_oet.vol_01.ch_04_operator_chain_calculus

noncomputable section

open formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators Matrix.Norms.Operator

variable {I : Type}
local instance instDecidableEqIFiniteMatrixSpectral : DecidableEq I := Classical.decEq I

/-- `ENNReal` 序列趋于零的尾部量词形式。 -/
def TendsToZeroENNReal (a : ℕ → ENNReal) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ∃ N : ℕ, ∀ k ≥ N, a k < ε

/-- `ENNReal` 序列沿任意尾部超过任意有限阈值。 -/
def UnboundedAlongTails (a : ℕ → ENNReal) : Prop :=
  ∀ B : ENNReal, B < ⊤ → ∀ N : ℕ, ∃ k ≥ N, B < a k

/-- 尾部无界序列乘以正的 `ENNReal` 常数后仍尾部无界。 -/
theorem unbounded_mul_const_of_pos
    (a : ℕ → ENNReal) (c : ENNReal)
    (ha : UnboundedAlongTails a) (hc : 0 < c) :
    UnboundedAlongTails (fun n => a n * c) := by
  intro B hB N
  have hB_ne_top : B ≠ ⊤ := ne_of_lt hB
  have hc_ne_zero : c ≠ 0 := ne_of_gt hc
  have hdiv_top : B / c < ⊤ := ENNReal.div_lt_top hB_ne_top hc_ne_zero
  rcases ha (B / c) hdiv_top N with ⟨n, hnN, hn⟩
  refine ⟨n, hnN, ?_⟩
  exact (ENNReal.div_lt_iff (Or.inl hc_ne_zero) (Or.inr hB_ne_top)).mp hn

/-- `ENNReal` 矩阵的有限值条件，对应正文中的 `[0,+∞)^{|I|×|I|}`。 -/
def FiniteValuedMatrix (M : I → I → ENNReal) : Prop :=
  ∀ i j : I, M i j < ⊤

/-- 有限值矩阵的乘积仍为有限值矩阵。 -/
theorem finite_valued_matrix_mul [Fintype I]
    (L₂ L₁ : I → I → ENNReal)
    (h₂ : FiniteValuedMatrix L₂) (h₁ : FiniteValuedMatrix L₁) :
    FiniteValuedMatrix (matrix_mul L₂ L₁) := by
  intro i j
  dsimp [FiniteValuedMatrix, matrix_mul] at h₂ h₁ ⊢
  rw [ENNReal.sum_lt_top]
  intro k _hk
  exact ENNReal.mul_lt_top (h₂ k j) (h₁ i k)

/-- 恒等矩阵是有限值矩阵。 -/
theorem finite_valued_matrix_id :
    FiniteValuedMatrix (matrix_id : I → I → ENNReal) := by
  intro i j
  by_cases hij : i = j <;> simp [matrix_id, hij]

/-- 常矩阵的每个有限前缀乘积仍为有限值矩阵。 -/
theorem finite_valued_matrix_prefix_product [Fintype I]
    (M : I → I → ENNReal) (hM : FiniteValuedMatrix M) :
    ∀ n : ℕ, FiniteValuedMatrix (matrix_prefix_product (fun _ : ℕ => M) n) := by
  intro n
  induction n with
  | zero => exact finite_valued_matrix_id
  | succ n ih =>
      simpa [matrix_prefix_product] using finite_valued_matrix_mul M _ hM ih

/-- The complex matrix obtained from a finite-valued `ENNReal` matrix. -/
noncomputable def complex_matrix_of_ennreal
    (M : I → I → ENNReal) : Matrix I I ℂ :=
  fun i j => (M i j).toReal

/-- The spectral radius of the associated finite complex matrix. -/
noncomputable def ennreal_matrix_spectral_radius
    [Fintype I] (M : I → I → ENNReal) : ENNReal :=
  spectralRadius ℂ (complex_matrix_of_ennreal M)

/--
For finite-valued matrices, the `ENNReal` multiplication convention is carried
to ordinary complex matrix multiplication, with the OET index orientation
reversing the two displayed factors.
-/
theorem complex_matrix_of_ennreal_matrix_mul [Fintype I]
    (L₂ L₁ : I → I → ENNReal)
    (h₂ : FiniteValuedMatrix L₂) (h₁ : FiniteValuedMatrix L₁) :
    complex_matrix_of_ennreal (matrix_mul L₂ L₁) =
      complex_matrix_of_ennreal L₁ * complex_matrix_of_ennreal L₂ := by
  ext i j
  simp only [complex_matrix_of_ennreal, matrix_mul, Matrix.mul_apply]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, Complex.ofReal_mul, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k _hk
    ring
  · intro k _hk
    exact ENNReal.mul_ne_top (ne_of_lt (h₂ k j)) (ne_of_lt (h₁ i k))

/-- A constant OET prefix product is the corresponding complex matrix power. -/
theorem complex_matrix_of_ennreal_prefix_product [Fintype I]
    (M : I → I → ENNReal) (hM : FiniteValuedMatrix M) :
    ∀ n : ℕ,
      complex_matrix_of_ennreal (matrix_prefix_product (fun _ : ℕ => M) n) =
        (complex_matrix_of_ennreal M) ^ n := by
  intro n
  induction n with
  | zero =>
      ext i j
      by_cases hij : i = j <;>
        simp [matrix_prefix_product, matrix_id, complex_matrix_of_ennreal, hij]
  | succ n ih =>
      rw [matrix_prefix_product,
        complex_matrix_of_ennreal_matrix_mul M _ hM
          (finite_valued_matrix_prefix_product M hM n), ih, pow_succ]

/-- Each finite `ENNReal` prefix-product entry is the norm of its complex image. -/
theorem prefix_product_entry_eq_complex_nnnorm [Fintype I]
    (M : I → I → ENNReal) (hM : FiniteValuedMatrix M)
    (n : ℕ) (i j : I) :
    matrix_prefix_product (fun _ : ℕ => M) n i j =
      (↑‖((complex_matrix_of_ennreal M) ^ n) i j‖₊ : ENNReal) := by
  rw [← congrFun (congrFun (complex_matrix_of_ennreal_prefix_product M hM n) i) j]
  change matrix_prefix_product (fun _ : ℕ => M) n i j =
    (↑‖((matrix_prefix_product (fun _ : ℕ => M) n i j).toReal : ℂ)‖₊ : ENNReal)
  rw [Complex.nnnorm_real, Real.nnnorm_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.coe_toNNReal
    (ne_of_lt (finite_valued_matrix_prefix_product M hM n i j))).symm

/-- Gelfand's formula turns spectral radius below one into norm decay. -/
theorem complex_matrix_powers_nnnorm_tendsto_zero_of_spectral_radius_lt_one
    [Fintype I]
    (A : Matrix I I ℂ) (hrho : spectralRadius ℂ A < 1) :
    Filter.Tendsto (fun n : ℕ => (↑‖A ^ n‖₊ : ENNReal))
      Filter.atTop (nhds 0) := by
  obtain ⟨q, hrho_q, hq_one⟩ := exists_between hrho
  have hroot : ∀ᶠ n : ℕ in Filter.atTop,
      (↑‖A ^ n‖₊ : ENNReal) ^ (1 / (n : ℝ)) < q :=
    ((tendsto_order.1 (spectrum.gelfand_formula A)).2 q hrho_q)
  have hpositive : ∀ᶠ n : ℕ in Filter.atTop, 0 < n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => lt_of_lt_of_le Nat.zero_lt_one hn⟩
  have hnorm : ∀ᶠ n : ℕ in Filter.atTop,
      (↑‖A ^ n‖₊ : ENNReal) ≤ q ^ n :=
    (hroot.and hpositive).mono fun n hn => by
      have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn.2
      have hrpow := ENNReal.rpow_lt_rpow hn.1 hnreal
      have hcancel : (1 / (n : ℝ)) * (n : ℝ) = 1 := by
        field_simp
      exact (show (↑‖A ^ n‖₊ : ENNReal) < q ^ n by
        calc
          (↑‖A ^ n‖₊ : ENNReal) =
              (↑‖A ^ n‖₊ : ENNReal) ^ ((1 / (n : ℝ)) * (n : ℝ)) := by
                rw [hcancel, ENNReal.rpow_one]
          _ = ((↑‖A ^ n‖₊ : ENNReal) ^ (1 / (n : ℝ))) ^ (n : ℝ) :=
            ENNReal.rpow_mul _ _ _
          _ < q ^ (n : ℝ) := hrpow
          _ = q ^ n := ENNReal.rpow_natCast q n).le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq_one)
    (Filter.Eventually.of_forall fun _ => zero_le _)
    hnorm

/-- Every entry is bounded by the matrix `L∞` operator norm. -/
theorem complex_entry_nnnorm_le_linfty_op_nnnorm [Fintype I]
    (A : Matrix I I ℂ) (i j : I) : ‖A i j‖₊ ≤ ‖A‖₊ := by
  rw [Matrix.linfty_opNNNorm_def]
  exact le_trans
    (Finset.single_le_sum (fun k _ => zero_le ‖A i k‖₊) (Finset.mem_univ j))
    (Finset.le_sup (f := fun i : I => ∑ j : I, ‖A i j‖₊)
      (Finset.mem_univ i))

/-- Spectral radius below one makes every constant prefix-product entry tend to zero. -/
theorem prefix_product_entries_tendsto_zero_of_spectral_radius_lt_one
    [Fintype I]
    (M : I → I → ENNReal) (hM : FiniteValuedMatrix M)
    (hrho : ennreal_matrix_spectral_radius M < 1) :
    ∀ i j : I, Filter.Tendsto
      (fun n => matrix_prefix_product (fun _ : ℕ => M) n i j)
      Filter.atTop (nhds 0) := by
  intro i j
  have hnorm :=
    complex_matrix_powers_nnnorm_tendsto_zero_of_spectral_radius_lt_one
      (complex_matrix_of_ennreal M) hrho
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hnorm
  · exact Filter.Eventually.of_forall fun _ => zero_le _
  · exact Filter.Eventually.of_forall fun n => by
      rw [prefix_product_entry_eq_complex_nnnorm M hM n i j]
      exact_mod_cast complex_entry_nnnorm_le_linfty_op_nnnorm
        ((complex_matrix_of_ennreal M) ^ n) i j

/-- Spectral radius above one makes the norms of the matrix powers tail-unbounded. -/
theorem complex_matrix_powers_nnnorm_unbounded_of_one_lt_spectral_radius
    [Fintype I] [Nonempty I]
    (A : Matrix I I ℂ) (hrho : 1 < spectralRadius ℂ A) :
    UnboundedAlongTails (fun n : ℕ => (↑‖A ^ n‖₊ : ENNReal)) := by
  have hpow : Filter.Tendsto (fun n : ℕ => (spectralRadius ℂ A) ^ n)
      Filter.atTop (nhds ⊤) :=
    ENNReal.tendsto_pow_atTop_nhds_top_iff.2 hrho
  intro B hB N
  have hB_eventually : ∀ᶠ n : ℕ in Filter.atTop,
      B < (spectralRadius ℂ A) ^ n :=
    hpow.eventually (Ioi_mem_nhds hB)
  have hN_eventually : ∀ᶠ n : ℕ in Filter.atTop, N ≤ n :=
    Filter.eventually_ge_atTop N
  rcases (hB_eventually.and hN_eventually).exists with ⟨n, hBn, hNn⟩
  refine ⟨n, hNn, hBn.trans_le ?_⟩
  exact (spectrum.spectralRadius_pow_le' A n).trans
    (spectrum.spectralRadius_le_nnnorm (𝕜 := ℂ) (A ^ n))

/-- A tail-unbounded finite sum has a fixed tail-unbounded summand. -/
theorem exists_unbounded_coordinate_of_sum_unbounded
    {α : Type} [Fintype α] (a : α → ℕ → ENNReal)
    (hsum : UnboundedAlongTails (fun n => ∑ i : α, a i n)) :
    ∃ i : α, UnboundedAlongTails (a i) := by
  classical
  by_contra h
  push Not at h
  have hbounded : ∀ i : α, ∃ B : ENNReal, B < ⊤ ∧
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → a i k ≤ B := by
    intro i
    have hi := h i
    simp only [UnboundedAlongTails] at hi
    push Not at hi
    exact hi
  choose B hB N hN using hbounded
  let totalB : ENNReal := ∑ i : α, B i
  let maxN : ℕ := Finset.univ.sup N
  have htotalB : totalB < ⊤ := by
    dsimp [totalB]
    rw [ENNReal.sum_lt_top]
    intro i _hi
    exact hB i
  rcases hsum totalB htotalB maxN with ⟨k, hkN, hkB⟩
  have hcoord : ∀ i : α, a i k ≤ B i := by
    intro i
    apply hN i k
    exact (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hkN
  exact (not_lt_of_ge (Finset.sum_le_sum fun i _hi => hcoord i)) hkB

/-- The operator norm is bounded by the sum of all nonnegative prefix-product entries. -/
theorem complex_power_nnnorm_le_total_prefix_mass [Fintype I]
    (M : I → I → ENNReal) (hM : FiniteValuedMatrix M) (n : ℕ) :
    (↑‖(complex_matrix_of_ennreal M) ^ n‖₊ : ENNReal) ≤
      ∑ i : I, ∑ j : I,
        matrix_prefix_product (fun _ : ℕ => M) n i j := by
  have hnnreal : ‖(complex_matrix_of_ennreal M) ^ n‖₊ ≤
      ∑ i : I, ∑ j : I,
        ‖((complex_matrix_of_ennreal M) ^ n) i j‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    apply Finset.sup_le
    intro i _hi
    exact Finset.single_le_sum
      (fun k _ => zero_le (∑ j : I, ‖((complex_matrix_of_ennreal M) ^ n) k j‖₊))
      (Finset.mem_univ i)
  calc
    (↑‖(complex_matrix_of_ennreal M) ^ n‖₊ : ENNReal) ≤
        ↑(∑ i : I, ∑ j : I,
          ‖((complex_matrix_of_ennreal M) ^ n) i j‖₊ : NNReal) := by
      exact_mod_cast hnnreal
    _ = ∑ i : I, ∑ j : I,
        (↑‖((complex_matrix_of_ennreal M) ^ n) i j‖₊ : ENNReal) := by
      simp
    _ = ∑ i : I, ∑ j : I,
        matrix_prefix_product (fun _ : ℕ => M) n i j := by
      apply Finset.sum_congr rfl
      intro i _hi
      apply Finset.sum_congr rfl
      intro j _hj
      exact (prefix_product_entry_eq_complex_nnnorm M hM n i j).symm

/-- Spectral radius above one makes the total prefix-product mass tail-unbounded. -/
theorem total_prefix_mass_unbounded_of_one_lt_spectral_radius
    [Fintype I] [Nonempty I]
    (M : I → I → ENNReal) (hM : FiniteValuedMatrix M)
    (hrho : 1 < ennreal_matrix_spectral_radius M) :
    UnboundedAlongTails (fun n => ∑ i : I, ∑ j : I,
      matrix_prefix_product (fun _ : ℕ => M) n i j) := by
  have hnorm :=
    complex_matrix_powers_nnnorm_unbounded_of_one_lt_spectral_radius
      (complex_matrix_of_ennreal M) hrho
  intro B hB N
  rcases hnorm B hB N with ⟨n, hnN, hBn⟩
  exact ⟨n, hnN,
    hBn.trans_le (complex_power_nnnorm_le_total_prefix_mass M hM n)⟩

/-- Spectral radius above one gives a fixed tail-unbounded matrix entry. -/
theorem prefix_product_has_unbounded_entry_of_one_lt_spectral_radius
    [Fintype I]
    (M : I → I → ENNReal) (hM : FiniteValuedMatrix M)
    (hrho : 1 < ennreal_matrix_spectral_radius M) :
    ∃ i j : I, UnboundedAlongTails
      (fun n => matrix_prefix_product (fun _ : ℕ => M) n i j) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI := hI
      have hrho_zero : ennreal_matrix_spectral_radius M = 0 := by
        unfold ennreal_matrix_spectral_radius
        exact spectrum.SpectralRadius.of_subsingleton _
      rw [hrho_zero] at hrho
      exact False.elim (not_lt_of_ge (zero_le (1 : ENNReal)) hrho)
  | inr hI =>
      letI := hI
      have htotal := total_prefix_mass_unbounded_of_one_lt_spectral_radius M hM hrho
      obtain ⟨i, hi⟩ := exists_unbounded_coordinate_of_sum_unbounded
        (fun i n => ∑ j : I,
          matrix_prefix_product (fun _ : ℕ => M) n i j) htotal
      obtain ⟨j, hj⟩ := exists_unbounded_coordinate_of_sum_unbounded
        (fun j n => matrix_prefix_product (fun _ : ℕ => M) n i j) hi
      exact ⟨i, j, hj⟩

/--
The standard finite-matrix spectral facts used by the constant-certificate
criterion, now constructed from Mathlib rather than assumed by callers.
-/
structure FiniteMatrixSpectralCertificate (I : Type) [Fintype I] where
  subunit_power_decay : ∀ (M : I → I → ENNReal),
    FiniteValuedMatrix M → ennreal_matrix_spectral_radius M < 1 →
      ∀ i j : I, Filter.Tendsto
        (fun k => matrix_prefix_product (fun _ : ℕ => M) k i j)
        Filter.atTop (nhds 0)
  superunit_power_unbounded : ∀ (M : I → I → ENNReal),
    FiniteValuedMatrix M → 1 < ennreal_matrix_spectral_radius M →
      ∃ i j : I, UnboundedAlongTails
        (fun k => matrix_prefix_product (fun _ : ℕ => M) k i j)

/-- The canonical finite-matrix spectral certificate proved above. -/
noncomputable def finite_matrix_spectral_certificate
    (I : Type) [Fintype I] : FiniteMatrixSpectralCertificate I where
  subunit_power_decay := fun M hM hrho =>
    prefix_product_entries_tendsto_zero_of_spectral_radius_lt_one M hM hrho
  superunit_power_unbounded := fun M hM hrho =>
    prefix_product_has_unbounded_entry_of_one_lt_spectral_radius M hM hrho

end


end formal_oet.vol_01.ch_04_operator_chain_calculus
