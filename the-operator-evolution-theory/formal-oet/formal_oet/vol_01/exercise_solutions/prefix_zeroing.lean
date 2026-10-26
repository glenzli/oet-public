import formal_oet.vol_01.ch_04_operator_chain_calculus.spectral_regimes

namespace formal_oet.vol_01.exercise_solutions.prefix_zeroing

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_04_operator_chain_calculus

open scoped BigOperators

variable {X I : Type} {bot : X}
local instance inst_decidable_eq : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-92845f1b79fdc073
若点对落入该中心点的零化半径以下，则下一步在目标分量精确零化。

这是一般链版本中使用的点态半径形式。
-/
theorem zeroing_step_of_annihilation_radius
    (ϕ : Operator X bot) (U : Set X) (i j : I) (ν : ENNReal)
    {x y : X}
    (hν_le : ν ≤ annihilation_radius d ϕ i (singleton_nonempty_finset j) U y)
    (hx : x ∈ U) (hxy : d i x y < ν) :
    d j (ϕ.func x) (ϕ.func y) = 0 := by
  have hxy_ann : d i x y <
      annihilation_radius d ϕ i (singleton_nonempty_finset j) U y :=
    lt_of_lt_of_le hxy hν_le
  rcases lt_iSup_iff.mp hxy_ann with ⟨r, hr⟩
  rcases lt_iSup_iff.mp hr with ⟨hr_fin_pos, hr'⟩
  rcases lt_iSup_iff.mp hr' with ⟨h_subset, hxy_r⟩
  have hx_ball : x ∈ OpenBall d i y r ∩ U := ⟨hxy_r, hx⟩
  exact distance_recurrence_zeroing_of_ball d ϕ U i j y x r hx_ball h_subset

/--
OET anchor: h-0ff7986894ec9221
**习题 #h-0ff7986894ec9221（长链中的有限步归零）**
前缀上界使迭代点对进入零化半径时，随后一步在目标分量精确归零。
-/
theorem self_iteration_eventual_zero_of_prefix_bound [Fintype I]
    (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ν : ENNReal) (Lpow : ℕ → I → I → ENNReal)
    (hν_le : ν ≤ min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U)
    (h_iter_mem :
      ∀ n : ℕ, ∀ z ∈ U, (OperatorChain (List.replicate n ϕ)).func z ∈ U)
    (h_iter_lip :
      ∀ n : ℕ, IsLipMatrix d (OperatorChain (List.replicate n ϕ)) U (Lpow n))
    (h_decay_to_radius :
      ∀ x ∈ U, ∀ y ∈ U, (∀ l : I, d l x y ≠ ⊤) →
        ∃ N : ℕ, ∀ n ≥ N,
          matrix_vector_bound (Lpow n) (DistanceVector d x y) i < ν) :
    ∀ x ∈ U, ∀ y ∈ U, (∀ l : I, d l x y ≠ ⊤) →
      ∃ N : ℕ, ∀ n ≥ N,
        d j ((OperatorChain (List.replicate n ϕ)).func x)
          ((OperatorChain (List.replicate n ϕ)).func y) = 0 := by
  intro x hx y hy hfinite
  rcases h_decay_to_radius x hx y hy hfinite with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro k hk
  rcases Nat.exists_eq_add_of_le hk with ⟨m, rfl⟩
  let n := N + m
  have hnN : N ≤ n := Nat.le_add_right N m
  have hx_n : (OperatorChain (List.replicate n ϕ)).func x ∈ U := h_iter_mem n x hx
  have hy_n : (OperatorChain (List.replicate n ϕ)).func y ∈ U := h_iter_mem n y hy
  have h_lip :=
    (h_iter_lip n).2 x hx y hy i
  have hdist_lt :
      d i ((OperatorChain (List.replicate n ϕ)).func x)
        ((OperatorChain (List.replicate n ϕ)).func y) < ν :=
    lt_of_le_of_lt h_lip (hN n hnN)
  have hzero :=
    zeroing_step_of_min_annihilation_radius d ϕ U i j ν hν_le hx_n hy_n hdist_lt
  have hk_eq : N + 1 + m = n + 1 := by omega
  rw [hk_eq]
  simpa [n, OperatorChain] using hzero

/--
OET anchor: h-92845f1b79fdc073
**解答：长链中的有限步归零，一般链形式**
For a general operator chain, once the L-prefix upper bound for the current
input component lies below a uniform pointwise annihilation radius, the next
step is exactly zero in the target component.
-/
theorem chain_eventual_zero_of_prefix_bound
    [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (L : ℕ → I → I → ENNReal)
    (i j : I) (ν : ENNReal) (m₀ : ℕ)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hL : ∀ n : ℕ, IsLipMatrix d (ϕ n) (U n) (L n))
    (hν_le :
      ∀ m ≥ m₀, ∀ y ∈ U m,
        ν ≤ annihilation_radius d (ϕ m) i (singleton_nonempty_finset j) (U m) y)
    (x y : X) (hx : x ∈ U 0) (hy : y ∈ U 0)
    (h_decay :
      ∃ M : ℕ, ∀ m ≥ M,
        matrix_vector_bound (matrix_prefix_product L m) (DistanceVector d x y) i < ν) :
    ∃ M : ℕ, m₀ ≤ M ∧
      ∀ m ≥ M,
        d j ((chain_prefix_operator ϕ (m + 1)).func x)
          ((chain_prefix_operator ϕ (m + 1)).func y) = 0 := by
  rcases h_decay with ⟨M_decay, hM_decay⟩
  refine ⟨max m₀ M_decay, Nat.le_max_left _ _, ?_⟩
  intro m hm
  have hm₀ : m₀ ≤ m := le_trans (Nat.le_max_left m₀ M_decay) hm
  have hm_decay : M_decay ≤ m := le_trans (Nat.le_max_right m₀ M_decay) hm
  have hx_m : (chain_prefix_operator ϕ m).func x ∈ U m :=
    chain_prefix_maps_to_sequence ϕ U hU_step m hx
  have hy_m : (chain_prefix_operator ϕ m).func y ∈ U m :=
    chain_prefix_maps_to_sequence ϕ U hU_step m hy
  have h_lip :=
    chain_prefix_lip_distance_upper d ϕ U L hU_step hU_dom hL
      m x y hx hy i
  have hdist_lt :
      d i ((chain_prefix_operator ϕ m).func x)
        ((chain_prefix_operator ϕ m).func y) < ν :=
    lt_of_le_of_lt h_lip (hM_decay m hm_decay)
  have hzero :=
    zeroing_step_of_annihilation_radius d (ϕ m) (U m) i j ν
      (hν_le m hm₀ ((chain_prefix_operator ϕ m).func y) hy_m)
      hx_m hdist_lt
  simpa [chain_prefix_operator] using hzero

/--
OET anchor: h-0ff7986894ec9221
**习题 #h-0ff7986894ec9221（长链中的有限步归零）**

习题使用的极限形式：前缀上界趋零与严格正的统一零化半径共同推出尾部精确归零。
本定理保留题面的一基索引；证明中才把 `ϕ (n + 1)`、`U (n + 1)` 与
`L (n + 1)` 重编号为零基序列，以调用一般链辅助定理。
-/
theorem chain_prefix_annihilation_eventual_zero_textbook
    [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (L : ℕ → I → I → ENNReal)
    (i j : I) (ν : ENNReal) (m₀ : ℕ)
    (hν_pos : 0 < ν)
    (hm₀ : 1 ≤ m₀)
    (hU1_ne : (U 1).Nonempty)
    (hU_step : ∀ m ≥ 1, U (m + 1) = (ϕ m).func '' U m)
    (hU_dom : ∀ m ≥ 1, U m ⊆ dom (ϕ m))
    (hL : ∀ m ≥ 1, IsLipMatrix d (ϕ m) (U m) (L m))
    (hν_le : ∀ m ≥ m₀, ∀ y ∈ U m,
      ν ≤ annihilation_radius d (ϕ m) i
        (singleton_nonempty_finset j) (U m) y)
    (x y : X) (hx : x ∈ U 1) (hy : y ∈ U 1)
    (h_decay : TendsToZeroENNReal
      (fun r => matrix_vector_bound
        (matrix_prefix_product (fun n => L (n + 1)) r)
        (DistanceVector d x y) i)) :
    ∃ M : ℕ, m₀ ≤ M ∧ ∀ m ≥ M,
      d j ((chain_prefix_operator (fun n => ϕ (n + 1)) m).func x)
        ((chain_prefix_operator (fun n => ϕ (n + 1)) m).func y) = 0 := by
  have _ := hU1_ne
  let ϕ₀ : ℕ → Operator X bot := fun n => ϕ (n + 1)
  let U₀ : ℕ → Set X := fun n => U (n + 1)
  let L₀ : ℕ → I → I → ENNReal := fun n => L (n + 1)
  have hU_step₀ : ∀ n : ℕ, U₀ (n + 1) = (ϕ₀ n).func '' U₀ n := by
    intro n
    simpa [U₀, ϕ₀, Nat.add_assoc] using hU_step (n + 1) (by omega)
  have hU_dom₀ : ∀ n : ℕ, U₀ n ⊆ dom (ϕ₀ n) := by
    intro n
    exact hU_dom (n + 1) (by omega)
  have hL₀ : ∀ n : ℕ, IsLipMatrix d (ϕ₀ n) (U₀ n) (L₀ n) := by
    intro n
    exact hL (n + 1) (by omega)
  have hν_le₀ :
      ∀ r ≥ m₀ - 1, ∀ z ∈ U₀ r,
        ν ≤ annihilation_radius d (ϕ₀ r) i
          (singleton_nonempty_finset j) (U₀ r) z := by
    intro r hr z hz
    exact hν_le (r + 1) (by omega) z hz
  have h_decay₀ : TendsToZeroENNReal
      (fun r => matrix_vector_bound (matrix_prefix_product L₀ r)
        (DistanceVector d x y) i) := by
    simpa [L₀] using h_decay
  rcases h_decay₀ ν hν_pos with ⟨R_decay, hR_decay⟩
  rcases chain_eventual_zero_of_prefix_bound
      d ϕ₀ U₀ L₀ i j ν (m₀ - 1)
      hU_step₀ hU_dom₀ hL₀ hν_le₀ x y hx hy ⟨R_decay, hR_decay⟩ with
    ⟨R, hR₀, hR⟩
  refine ⟨R + 1, by omega, ?_⟩
  intro m hm
  have hR_pred : R ≤ m - 1 := by omega
  have hzero := hR (m - 1) hR_pred
  have hpred : m - 1 + 1 = m := by omega
  simpa [ϕ₀, hpred] using hzero

end

end formal_oet.vol_01.exercise_solutions.prefix_zeroing
