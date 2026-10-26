import formal_oet.vol_01.ch_02_operator_bounds.gauge_choice
import formal_oet.vol_01.ch_04_operator_chain_calculus.finite_matrix_spectral
import formal_oet.vol_01.exercise_solutions.foundation_examples
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.Analysis.SpecificLimits.Basic

namespace formal_oet.vol_01.exercise_solutions.spectral_iteration

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_04_operator_chain_calculus
open gauge_choice (PlanePoint coordinate_dist read_coordinate finite_part)
open scoped BigOperators Matrix Matrix.Norms.Operator

noncomputable section

local instance inst_decidable_eq_fin_two : DecidableEq (Fin 2) := Classical.decEq _
local instance inst_decidable_eq_unit : DecidableEq Unit := Classical.decEq _

def cancellation (x : ℝ × ℝ) : ℝ × ℝ := (x.1 + x.2, -x.1 - x.2)
def cancellation_operator : Operator PlanePoint none := ⟨Option.map cancellation, rfl⟩
def least_lip : Matrix (Fin 2) (Fin 2) ENNReal := fun _ _ => 1

private theorem cancellation_bound (x y : ℝ × ℝ) :
    |(x.1 + x.2) - (y.1 + y.2)| ≤ |x.1 - y.1| + |x.2 - y.2| := by
  calc
    _ = |(x.1 - y.1) + (x.2 - y.2)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _

/-- OET anchor: h-51ab39dbe6ea409d
The all-ones matrix is a legal global Lip certificate for the absorbing extension. -/
theorem least_lip_valid :
    IsLipMatrix coordinate_dist cancellation_operator finite_part least_lip := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩; simp [dom, cancellation_operator]
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ j
    have hneg : (-x.1 - x.2) - (-y.1 - y.2) = -((x.1 + x.2) - (y.1 + y.2)) := by ring
    have hr := ENNReal.ofReal_le_ofReal (cancellation_bound x y)
    rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)] at hr
    fin_cases j <;>
      simpa [coordinate_dist, cancellation_operator, cancellation,
        read_coordinate, least_lip, Fin.sum_univ_two, hneg, abs_sub_comm] using hr

/-- OET anchor: h-51ab39dbe6ea409d
Every legal Lip matrix has all entries at least one, including extended-valued ones. -/
theorem least_lip_minimal (M : Fin 2 → Fin 2 → ENNReal)
    (hM : IsLipMatrix coordinate_dist cancellation_operator finite_part M) :
    ∀ i j, least_lip i j ≤ M i j := by
  intro i j
  have ha := hM.2 (some (1, 0)) ⟨(1, 0), rfl⟩ (some (0, 0)) ⟨(0, 0), rfl⟩ j
  have hb := hM.2 (some (0, 1)) ⟨(0, 1), rfl⟩ (some (0, 0)) ⟨(0, 0), rfl⟩ j
  fin_cases i <;> fin_cases j <;>
    norm_num [coordinate_dist, read_coordinate, cancellation_operator, cancellation,
      Fin.sum_univ_two, least_lip] at ha hb ⊢ <;> assumption

/-- OET anchor: h-51ab39dbe6ea409d
The powers of the least certificate are two to the previous power times that certificate. -/
theorem least_lip_pow (n : ℕ) : least_lip ^ (n + 1) = (2 : ENNReal) ^ n • least_lip := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    ext i j
    simp [Matrix.mul_apply, least_lip, pow_succ]
    ring

private theorem least_lip_spectrum :
    spectrum ℂ (complex_matrix_of_ennreal least_lip) = {0, 2} := by
  ext z
  simp only [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  have hd : inst_decidable_eq_fin_two = instDecidableEqFin 2 := Subsingleton.elim _ _
  rw [hd]
  simp only [Matrix.det_fin_two, Matrix.sub_apply, Matrix.algebraMap_eq_diagonal,
    Matrix.diagonal_apply, complex_matrix_of_ennreal, least_lip]
  norm_num
  have hf : (z - 1) * (z - 1) - 1 = z * (z - 2) := by ring
  rw [hf, mul_eq_zero]
  simp only [sub_eq_zero]

/-- OET anchor: h-51ab39dbe6ea409d
The book's actual spectral-radius definition applied to the least matrix equals two. -/
theorem least_lip_spectral_radius : ennreal_matrix_spectral_radius least_lip = 2 := by
  change spectralRadius ℂ (complex_matrix_of_ennreal least_lip) = 2
  unfold spectralRadius
  rw [least_lip_spectrum]
  simp [iSup_or, iSup_sup_eq]

/-- OET anchor: h-51ab39dbe6ea409d
Every real-plane input reaches the origin after two or more applications. -/
theorem cancellation_iterate (n : ℕ) (x : ℝ × ℝ) :
    (cancellation_operator.func^[n + 2]) (some x) = some (0, 0) := by
  induction n with
  | zero =>
    simp [Function.iterate_succ_apply', cancellation_operator, cancellation]
    ring
  | succ n ih =>
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, Function.iterate_succ_apply', ih]
    simp [cancellation_operator, cancellation]

/-- OET anchor: h-9bee8ae73f2048ff
The zero matrix is valid on the actual image after the first step. -/
theorem image_zero_lip :
    IsLipMatrix coordinate_dist cancellation_operator
      (cancellation_operator.func '' finite_part) (fun _ _ => 0) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩; simp [dom, cancellation_operator]
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩ _ ⟨_, ⟨y, rfl⟩, rfl⟩ j
    have hx := cancellation_iterate 0 x
    have hy := cancellation_iterate 0 y
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at hx hy
    rw [hx, hy]
    simp [coordinate_dist]

def cubic (x : ℝ) : ℝ := x + x ^ 3
def cubic_operator : Operator (Option ℝ) none := ⟨Option.map cubic, rfl⟩
def real_component (_ : Unit) := foundation_examples.extend_distance
  (fun x y : ℝ => ENNReal.ofReal |x - y|)
def real_domain : Set (Option ℝ) := Set.range some

private theorem cubic_distance (x y : ℝ) :
    |cubic x - cubic y| = |x - y| * (1 + x ^ 2 + x * y + y ^ 2) := by
  have hq : 0 ≤ 1 + x ^ 2 + x * y + y ^ 2 := by
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y)]
  rw [show cubic x - cubic y = (x - y) * (1 + x ^ 2 + x * y + y ^ 2) by
    unfold cubic; ring, abs_mul, abs_of_nonneg hq]

/-- OET anchor: h-51ab39dbe6ea409d
The scalar certificate one is valid on the entire nonabsorbing domain. -/
theorem unit_colip_valid :
    IsCoLipMatrix real_component cubic_operator real_domain (fun _ _ => 1) := by
  refine ⟨⟨some 0, ⟨0, rfl⟩⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩; simp [dom, cubic_operator]
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ j
    simp only [real_component, foundation_examples.extend_distance, cubic_operator,
      Option.map_some, Fintype.sum_unique, one_mul]
    apply ENNReal.ofReal_le_ofReal
    rw [cubic_distance]
    nlinarith [abs_nonneg (x-y), sq_nonneg (x+y), sq_nonneg (x-y)]

private theorem scalar_bound_le_one (k : ℝ)
    (h : ∀ x y : ℝ, k * |x-y| ≤ |cubic x-cubic y|) : k ≤ 1 := by
  by_contra hk
  have hk : 1 < k := lt_of_not_ge hk
  let t := Real.sqrt ((k-1)/2)
  have ht : 0 < t := Real.sqrt_pos.2 (by linarith)
  have ht2 : t^2 = (k-1)/2 := Real.sq_sqrt (by linarith)
  have hb := h t 0
  rw [cubic_distance] at hb
  simp only [sub_zero, abs_of_pos ht, zero_pow (by omega : 2 ≠ 0), mul_zero, add_zero] at hb
  have hsmall : 1+t^2 < k := by linarith
  nlinarith [mul_pos ht (sub_pos.2 hsmall)]

/-- OET anchor: h-51ab39dbe6ea409d
Every extended-valued scalar co-Lip certificate is bounded above by one. -/
theorem unit_colip_maximal (K : Unit → Unit → ENNReal)
    (hK : IsCoLipMatrix real_component cubic_operator real_domain K) : K () () ≤ 1 := by
  have htwo := hK.2.2 (some 1) ⟨1, rfl⟩ (some 0) ⟨0, rfl⟩ ()
  norm_num [real_component, foundation_examples.extend_distance, cubic_operator, cubic] at htwo
  have hfinite : K () () ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) htwo
  have hb : ∀ x y : ℝ, (K () ()).toReal * |x-y| ≤ |cubic x-cubic y| := by
    intro x y
    have hxy := hK.2.2 (some x) ⟨x, rfl⟩ (some y) ⟨y, rfl⟩ ()
    simp only [real_component, foundation_examples.extend_distance, cubic_operator,
      Option.map_some, Fintype.sum_unique] at hxy
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hxy
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _)] using hr
  have hreal := scalar_bound_le_one _ hb
  exact (ENNReal.toReal_le_toReal hfinite (by simp)).mp (by simpa using hreal)

/-- OET anchor: h-51ab39dbe6ea409d
The maximal one-channel certificate has spectral radius one. -/
theorem unit_colip_spectral_radius :
    ennreal_matrix_spectral_radius (fun _ _ : Unit => (1 : ENNReal)) = 1 := by
  have heq : complex_matrix_of_ennreal (fun _ _ : Unit => (1 : ENNReal)) =
      (1 : Matrix Unit Unit ℂ) := by ext i j; cases i; cases j; simp [complex_matrix_of_ennreal]
  rw [ennreal_matrix_spectral_radius, heq]
  exact spectrum.spectralRadius_one

def gap (x y : ℝ) (n : ℕ) : ℝ := |(cubic^[n]) x - (cubic^[n]) y|

private theorem gap_step (x y : ℝ) (n : ℕ) :
    gap x y n * (1 + (gap x y n)^2 / 4) ≤ gap x y (n+1) := by
  unfold gap
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply', cubic_distance]
  have hq :
      |(cubic^[n]) x-(cubic^[n]) y|^2 / 4 ≤
        ((cubic^[n]) x)^2 + (cubic^[n]) x * (cubic^[n]) y + ((cubic^[n]) y)^2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg ((cubic^[n]) x+(cubic^[n]) y)]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

private theorem gap_initial_le (x y : ℝ) (n : ℕ) : |x-y| ≤ gap x y n := by
  induction n with
  | zero => simp [gap]
  | succ n ih =>
    have hg : 0 ≤ gap x y n := abs_nonneg _
    have hs := gap_step x y n
    nlinarith [sq_nonneg (gap x y n)]

/-- OET anchor: h-9bee8ae73f2048ff
Each fixed pair has its own geometric lower bound, depending on the initial distance. -/
theorem gap_geometric_lower_bound (x y : ℝ) (n : ℕ) :
    |x-y| * (1+|x-y|^2/4)^n ≤ gap x y n := by
  induction n with
  | zero => simp [gap]
  | succ n ih =>
    have hg : 0 ≤ gap x y n := abs_nonneg _
    have hin := gap_initial_le x y n
    have hsq : |x-y|^2 ≤ (gap x y n)^2 := (sq_le_sq₀ (abs_nonneg _) hg).2 hin
    calc
      _ = (|x-y| * (1+|x-y|^2/4)^n) * (1+|x-y|^2/4) := by rw [pow_succ]; ring
      _ ≤ gap x y n * (1+|x-y|^2/4) :=
        mul_le_mul_of_nonneg_right ih (by positivity)
      _ ≤ gap x y n * (1+(gap x y n)^2/4) :=
        mul_le_mul_of_nonneg_left (by linarith) hg
      _ ≤ _ := gap_step x y n

/-- OET anchor: h-51ab39dbe6ea409d
All distinct real pairs diverge under self-composition despite maximal co-Lip radius one. -/
theorem cubic_iterate_distance_tendsto (x y : ℝ) (hxy : x ≠ y) :
    Filter.Tendsto (gap x y) Filter.atTop Filter.atTop := by
  have hd : 0 < |x-y| := abs_pos.2 (sub_ne_zero.2 hxy)
  have hr : 1 < 1+|x-y|^2/4 := by nlinarith [sq_pos_of_pos hd]
  have ht := Filter.Tendsto.const_mul_atTop hd (tendsto_pow_atTop_atTop_of_one_lt hr)
  exact Filter.tendsto_atTop_mono (gap_geometric_lower_bound x y) ht

/-- OET anchor: h-9bee8ae73f2048ff
Real iterates coincide with iterates of the absorbing extension. -/
theorem cubic_operator_iterate (n : ℕ) (x : ℝ) :
    (cubic_operator.func^[n]) (some x) = some ((cubic^[n]) x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rfl

/-- OET anchor: h-51ab39dbe6ea409d
The real distance satisfies the book's extended pseudometric axioms. -/
theorem scalar_gauge_valid :
    ExtendedPseudoMetric (Option ℝ) none (real_component ()) := by
  apply foundation_examples.extend_distance_is_extended
  · intro x; simp
  · intro x y; simp [abs_sub_comm]
  · intro x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le x y z)

end
end formal_oet.vol_01.exercise_solutions.spectral_iteration
