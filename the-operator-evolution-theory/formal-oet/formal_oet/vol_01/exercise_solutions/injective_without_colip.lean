import formal_oet.vol_01.exercise_solutions.foundation_examples
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Mathlib.Tactic

namespace formal_oet.vol_01.exercise_solutions.injective_without_colip

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

noncomputable section

/-- The usual real distance, with an isolated absorbing point. -/
def real_component (_ : Unit) : Option ℝ → Option ℝ → ENNReal :=
  foundation_examples.extend_distance (fun x y : ℝ => ENNReal.ofReal |x - y|)

/-- The square map on real inputs, extended by fixing the absorber. -/
def square_operator : Operator (Option ℝ) none :=
  ⟨Option.map (fun x : ℝ => x ^ 2), rfl⟩

/-- The actual nonabsorbing evaluation domain. -/
def unit_interval : Set (Option ℝ) := some '' Set.Icc (0 : ℝ) 1

private theorem real_component_is_extended (i : Unit) :
    ExtendedPseudoMetric (Option ℝ) none (real_component i) := by
  apply foundation_examples.extend_distance_is_extended
  · intro x
    simp
  · intro x y
    simp [abs_sub_comm]
  · intro x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le x y z)

private theorem real_component_separating : IsSeparating real_component := by
  intro x y hzero
  have h := hzero ()
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y => simp [real_component, foundation_examples.extend_distance] at h
  | some x =>
      cases y with
      | none => simp [real_component, foundation_examples.extend_distance] at h
      | some y =>
          have habs : |x - y| ≤ 0 := ENNReal.ofReal_eq_zero.mp h
          have hxy : x = y :=
            sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm habs (abs_nonneg _)))
          exact congrArg some hxy

private theorem zero_mem_unit_interval : some (0 : ℝ) ∈ unit_interval :=
  ⟨0, by norm_num, rfl⟩

private theorem one_mem_unit_interval : some (1 : ℝ) ∈ unit_interval :=
  ⟨1, by norm_num, rfl⟩

private theorem unit_interval_subset_dom : unit_interval ⊆ dom square_operator := by
  rintro _ ⟨x, _, rfl⟩
  simp [dom, square_operator]

/--
OET anchor: h-218697f5beb9e317
单射但无正 co-Lip 证书的平方映射例使用真实的分离扩展规范空间，
其非空受限域是实区间 `[0,1]` 在吸收元扩展中的像。
-/
theorem square_model_valid :
    (∀ i, ExtendedPseudoMetric (Option ℝ) none (real_component i)) ∧
    IsSeparating real_component ∧ unit_interval.Nonempty ∧
      unit_interval ⊆ dom square_operator :=
  ⟨real_component_is_extended, real_component_separating,
    ⟨some 0, zero_mem_unit_interval⟩, unit_interval_subset_dom⟩

/--
OET anchor: h-218697f5beb9e317
平方算子在实际受限域 `[0,1]` 上单射。
-/
theorem square_injective_on_unit_interval : Set.InjOn square_operator.func unit_interval := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
  have hsq : x ^ 2 = y ^ 2 := by
    simpa [square_operator] using hxy
  exact congrArg some ((sq_eq_sq₀ hx.1 hy.1).mp hsq)

private theorem square_zero_colip :
    IsCoLipMatrix real_component square_operator unit_interval (fun _ _ => 0) := by
  refine ⟨⟨some 0, zero_mem_unit_interval⟩, unit_interval_subset_dom, ?_⟩
  intro x hx y hy j
  simp

private theorem square_colip_entry_zero (K : Unit → Unit → ENNReal)
    (hK : IsCoLipMatrix real_component square_operator unit_interval K) :
    K () () = 0 := by
  have hK_one := hK.2.2 (some 1) one_mem_unit_interval
    (some 0) zero_mem_unit_interval ()
  norm_num [real_component, square_operator, foundation_examples.extend_distance] at hK_one
  have hK_finite : K () () ≠ ⊤ := ne_top_of_le_ne_top (by simp) hK_one
  by_contra hK_ne_zero
  have hk_pos : 0 < (K () ()).toReal := ENNReal.toReal_pos hK_ne_zero hK_finite
  have hk_le_one : (K () ()).toReal ≤ 1 := by
    simpa using ENNReal.toReal_mono (by simp : (1 : ENNReal) ≠ ⊤) hK_one
  let t : ℝ := (K () ()).toReal / 2
  have ht_pos : 0 < t := by dsimp [t]; linarith
  have ht_le_one : t ≤ 1 := by dsimp [t]; linarith
  have ht_mem : some t ∈ unit_interval :=
    ⟨t, ⟨le_of_lt ht_pos, ht_le_one⟩, rfl⟩
  have hbound := hK.2.2 (some t) ht_mem (some 0) zero_mem_unit_interval ()
  have hbound' : K () () * ENNReal.ofReal t ≤ ENNReal.ofReal (t ^ 2) := by
    simpa [real_component, square_operator, foundation_examples.extend_distance,
      abs_of_nonneg (le_of_lt ht_pos), abs_of_nonneg (sq_nonneg t)] using hbound
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound'
  have hreal' : (K () ()).toReal * t ≤ t ^ 2 := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (le_of_lt ht_pos),
      ENNReal.toReal_ofReal (sq_nonneg t)] using hreal
  dsimp [t] at hreal'
  nlinarith [sq_pos_of_pos hk_pos]

/--
OET anchor: h-218697f5beb9e317
平方算子在 `[0,1]` 上的合法单分量 co-Lip 矩阵族恰好只有零矩阵。
先用端点对排除无穷系数，再以 `t=K.toReal/2` 排除全部正系数；
反向验证零矩阵确实满足原始 `IsCoLipMatrix` 定义。
-/
theorem square_colip_iff_zero (K : Unit → Unit → ENNReal) :
    IsCoLipMatrix real_component square_operator unit_interval K ↔ K = fun _ _ => 0 := by
  constructor
  · intro hK
    funext i j
    cases i
    cases j
    exact square_colip_entry_zero K hK
  · rintro rfl
    exact square_zero_colip

end

end formal_oet.vol_01.exercise_solutions.injective_without_colip
