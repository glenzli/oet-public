import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix

namespace formal_oet.vol_01.ch_02_operator_bounds

noncomputable section

set_option linter.style.longLine false

open formal_oet.vol_01.ch_01_foundations
open Finset

variable {X I : Type} {bot : X} [Fintype I]
local instance instDecidableEqIMatrixComposition : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/-- 矩阵乘法 L2 * L1 -/
noncomputable def matrix_mul (L2 L1 : I → I → ENNReal) : I → I → ENNReal :=
  fun i j => ∑ k : I, L2 k j * L1 i k

/-- 恒等矩阵 -/
def matrix_id : I → I → ENNReal :=
  fun i j => if i = j then 1 else 0

/--
OET anchor: h-c80171fa685dc795
**推论 #h-c80171fa685dc795（有限复合的局部矩阵界）**
归纳定义的有限复合有界性：任意 n 步复合的局部矩阵界可以写成前向连乘形式。
-/
inductive RightChainLipBounded : List (Operator X bot) → Set X → (I → I → ENNReal) → Prop
  | nil (U : Set X) (hU : ∀ x ∈ U, x ≠ bot) : RightChainLipBounded [] U matrix_id
  | cons (ϕ : Operator X bot) (tail_ϕs : List (Operator X bot)) (U : Set X)
         (L_phi L_tail : I → I → ENNReal)
         (h_tail : RightChainLipBounded tail_ϕs U L_tail)
         (h_phi : IsLipMatrix d ϕ ((OperatorChain tail_ϕs).func '' U) L_phi) :
         RightChainLipBounded (ϕ :: tail_ϕs) U (matrix_mul L_phi L_tail)

/--
全复合 Lip 矩阵复合（任意 n 步）。
-/
theorem right_chain_lip_matrix (ϕs : List (Operator X bot)) (U : Set X) (L : I → I → ENNReal)
    (h_bound : RightChainLipBounded d ϕs U L) :
    IsLipMatrix d (OperatorChain ϕs) U L := by
  induction h_bound with
  | nil U hU =>
    dsimp [OperatorChain, IsLipMatrix]
    constructor
    · intro x hx
      dsimp [dom]
      exact hU x hx
    · intro x hx y hy j
      dsimp [matrix_id]
      have h_sum : (∑ i : I, (if i = j then (1 : ENNReal) else 0) * d i x y) = d j x y := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
        have h_zero : (∑ i ∈ Finset.erase Finset.univ j, (if i = j then (1 : ENNReal) else 0) * d i x y) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have h_ne : i ≠ j := Finset.ne_of_mem_erase hi
          rw [if_neg h_ne, zero_mul]
        rw [h_zero, add_zero, if_pos rfl, one_mul]
      rw [h_sum]
  | cons ϕ tail_ϕs U L_phi L_tail h_tail h_phi ih =>
    dsimp [OperatorChain]
    dsimp [IsLipMatrix] at h_phi ih ⊢
    rcases h_phi with ⟨h_phi_dom, h_phi_ineq⟩
    rcases ih with ⟨h_tail_dom, h_tail_ineq⟩
    constructor
    · intro x hx
      dsimp [dom]
      have h_tail_eval : (OperatorChain tail_ϕs).func x ∈ (OperatorChain tail_ϕs).func '' U := Set.mem_image_of_mem _ hx
      exact h_phi_dom h_tail_eval
    · intro x hx y hy j
      have h_tail_x : (OperatorChain tail_ϕs).func x ∈ (OperatorChain tail_ϕs).func '' U := Set.mem_image_of_mem _ hx
      have h_tail_y : (OperatorChain tail_ϕs).func y ∈ (OperatorChain tail_ϕs).func '' U := Set.mem_image_of_mem _ hy
      have step1 := h_phi_ineq ((OperatorChain tail_ϕs).func x) h_tail_x ((OperatorChain tail_ϕs).func y) h_tail_y j
      have step2 : ∑ k : I, L_phi k j * d k ((OperatorChain tail_ϕs).func x) ((OperatorChain tail_ϕs).func y) ≤ ∑ k : I, L_phi k j * (∑ i : I, L_tail i k * d i x y) := by
        apply Finset.sum_le_sum
        intro k _
        gcongr
        exact h_tail_ineq x hx y hy k
      have step3 : ∑ k : I, L_phi k j * (∑ i : I, L_tail i k * d i x y) = ∑ k : I, ∑ i : I, L_phi k j * (L_tail i k * d i x y) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
      have step4 : ∑ k : I, ∑ i : I, L_phi k j * (L_tail i k * d i x y) = ∑ i : I, ∑ k : I, (L_phi k j * L_tail i k) * d i x y := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro k _
        rw [mul_assoc]
      have step5 : ∑ i : I, ∑ k : I, (L_phi k j * L_tail i k) * d i x y = ∑ i : I, (∑ k : I, L_phi k j * L_tail i k) * d i x y := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
      calc
        d j (ϕ.func ((OperatorChain tail_ϕs).func x)) (ϕ.func ((OperatorChain tail_ϕs).func y)) ≤ ∑ k : I, L_phi k j * d k ((OperatorChain tail_ϕs).func x) ((OperatorChain tail_ϕs).func y) := step1
        _ ≤ ∑ k : I, L_phi k j * (∑ i : I, L_tail i k * d i x y) := step2
        _ = ∑ k : I, ∑ i : I, L_phi k j * (L_tail i k * d i x y) := step3
        _ = ∑ i : I, ∑ k : I, (L_phi k j * L_tail i k) * d i x y := step4
        _ = ∑ i : I, (∑ k : I, L_phi k j * L_tail i k) * d i x y := step5
        _ = ∑ i : I, matrix_mul L_phi L_tail i j * d i x y := rfl

/--
OET anchor: h-c80171fa685dc795
**推论 #h-c80171fa685dc795（有限复合的局部矩阵界, co-Lip 保距下限）**
-/
inductive RightChainCoLipBounded : List (Operator X bot) → Set X → (I → I → ENNReal) → Prop
  | nil (U : Set X) (hU : ∀ x ∈ U, x ≠ bot) (hU_ne : U.Nonempty) : RightChainCoLipBounded [] U matrix_id
  | cons (ϕ : Operator X bot) (tail_ϕs : List (Operator X bot)) (U : Set X)
         (K_phi K_tail : I → I → ENNReal)
         (h_tail : RightChainCoLipBounded tail_ϕs U K_tail)
         (h_phi : IsCoLipMatrix d ϕ ((OperatorChain tail_ϕs).func '' U) K_phi) :
         RightChainCoLipBounded (ϕ :: tail_ϕs) U (matrix_mul K_phi K_tail)

/--
全复合 co-Lip 矩阵复合（任意 n 步）。
-/
theorem right_chain_colip_matrix (ϕs : List (Operator X bot)) (U : Set X) (K : I → I → ENNReal)
    (h_bound : RightChainCoLipBounded d ϕs U K) :
    IsCoLipMatrix d (OperatorChain ϕs) U K := by
  induction h_bound with
  | nil U hU hU_ne =>
    dsimp [OperatorChain, IsCoLipMatrix]
    constructor
    · exact hU_ne
    · constructor
      · intro x hx
        dsimp [dom]
        exact hU x hx
      · intro x hx y hy j
        dsimp [matrix_id]
        have h_sum : (∑ i : I, (if i = j then (1 : ENNReal) else 0) * d i x y) = d j x y := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
          have h_zero : (∑ i ∈ Finset.erase Finset.univ j, (if i = j then (1 : ENNReal) else 0) * d i x y) = 0 := by
            apply Finset.sum_eq_zero
            intro i hi
            have h_ne : i ≠ j := Finset.ne_of_mem_erase hi
            rw [if_neg h_ne, zero_mul]
          rw [h_zero, add_zero, if_pos rfl, one_mul]
        rw [h_sum]
  | cons ϕ tail_ϕs U K_phi K_tail h_tail h_phi ih =>
    dsimp [OperatorChain]
    dsimp [IsCoLipMatrix] at h_phi ih ⊢
    rcases h_phi with ⟨h_phi_ne, h_phi_dom, h_phi_ineq⟩
    rcases ih with ⟨h_tail_ne, h_tail_dom, h_tail_ineq⟩
    constructor
    · exact h_tail_ne
    · constructor
      · intro x hx
        dsimp [dom]
        have h_tail_eval : (OperatorChain tail_ϕs).func x ∈ (OperatorChain tail_ϕs).func '' U := Set.mem_image_of_mem _ hx
        exact h_phi_dom h_tail_eval
      · intro x hx y hy j
        have h_tail_x : (OperatorChain tail_ϕs).func x ∈ (OperatorChain tail_ϕs).func '' U := Set.mem_image_of_mem _ hx
        have h_tail_y : (OperatorChain tail_ϕs).func y ∈ (OperatorChain tail_ϕs).func '' U := Set.mem_image_of_mem _ hy
        have step1 := h_phi_ineq ((OperatorChain tail_ϕs).func x) h_tail_x ((OperatorChain tail_ϕs).func y) h_tail_y j
        have step2 : ∑ k : I, K_phi k j * d k ((OperatorChain tail_ϕs).func x) ((OperatorChain tail_ϕs).func y) ≥ ∑ k : I, K_phi k j * (∑ i : I, K_tail i k * d i x y) := by
          apply Finset.sum_le_sum
          intro k _
          gcongr
          exact h_tail_ineq x hx y hy k
        have step3 : ∑ k : I, K_phi k j * (∑ i : I, K_tail i k * d i x y) = ∑ k : I, ∑ i : I, K_phi k j * (K_tail i k * d i x y) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
        have step4 : ∑ k : I, ∑ i : I, K_phi k j * (K_tail i k * d i x y) = ∑ i : I, ∑ k : I, (K_phi k j * K_tail i k) * d i x y := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          rw [mul_assoc]
        have step5 : ∑ i : I, ∑ k : I, (K_phi k j * K_tail i k) * d i x y = ∑ i : I, (∑ k : I, K_phi k j * K_tail i k) * d i x y := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
        calc
          d j (ϕ.func ((OperatorChain tail_ϕs).func x)) (ϕ.func ((OperatorChain tail_ϕs).func y)) ≥ ∑ k : I, K_phi k j * d k ((OperatorChain tail_ϕs).func x) ((OperatorChain tail_ϕs).func y) := step1
          _ ≥ ∑ k : I, K_phi k j * (∑ i : I, K_tail i k * d i x y) := step2
          _ = ∑ k : I, ∑ i : I, K_phi k j * (K_tail i k * d i x y) := step3
          _ = ∑ i : I, ∑ k : I, (K_phi k j * K_tail i k) * d i x y := step4
          _ = ∑ i : I, (∑ k : I, K_phi k j * K_tail i k) * d i x y := step5
          _ = ∑ i : I, matrix_mul K_phi K_tail i j * d i x y := rfl

/--
OET anchor: h-c80171fa685dc795
**推论 #h-c80171fa685dc795（有限复合的局部矩阵界）**

这是正文命题的最终包装。`RightChainLipBounded` 与
`RightChainCoLipBounded` 分别逐步记录每个算子在其实际输入像集上的证书；两个分支彼此独立，
并保留正文中的非空有限复合与起始定义域前提。
-/
theorem finite_composition_local_matrix_bounds_textbook
    (ϕs : List (Operator X bot)) (hϕs : ϕs ≠ []) (U : Set X)
    (hU : U ⊆ dom (OperatorChain ϕs)) (L K : I → I → ENNReal) :
    (RightChainLipBounded d ϕs U L →
      IsLipMatrix d (OperatorChain ϕs) U L) ∧
    (RightChainCoLipBounded d ϕs U K →
      IsCoLipMatrix d (OperatorChain ϕs) U K) := by
  have _ := hϕs
  have _ := hU
  exact ⟨right_chain_lip_matrix d ϕs U L,
    right_chain_colip_matrix d ϕs U K⟩

/--
OET anchor: h-193cebcc1a7f9259
**命题 #h-193cebcc1a7f9259（Lip 矩阵复合律）**
-/
theorem lip_matrix_comp (ϕ1 ϕ2 : Operator X bot) (U1 U2 : Set X)
    (L1 L2 : I → I → ENNReal)
    (h_im : ∀ x ∈ U1, ϕ1.func x ∈ U2)
    (hL1 : IsLipMatrix d ϕ1 U1 L1)
    (hL2 : IsLipMatrix d ϕ2 U2 L2) :
    IsLipMatrix d (OperatorChain [ϕ2, ϕ1]) U1 (matrix_mul L2 L1) := by
  dsimp [IsLipMatrix] at hL1 hL2 ⊢
  rcases hL1 with ⟨hU1_dom, hL1_ineq⟩
  rcases hL2 with ⟨hU2_dom, hL2_ineq⟩
  constructor
  · intro x hx
    dsimp [OperatorChain, dom]
    have h_phi1_x_in_U2 := h_im x hx
    exact hU2_dom h_phi1_x_in_U2
  · intro x hx y hy j
    have h_phi1_x_in_U2 := h_im x hx
    have h_phi1_y_in_U2 := h_im y hy
    dsimp [OperatorChain]
    have step1 := hL2_ineq (ϕ1.func x) h_phi1_x_in_U2 (ϕ1.func y) h_phi1_y_in_U2 j
    have step2 : ∑ k : I, L2 k j * d k (ϕ1.func x) (ϕ1.func y) ≤ ∑ k : I, L2 k j * (∑ i : I, L1 i k * d i x y) := by
      apply sum_le_sum
      intro k _
      gcongr
      exact hL1_ineq x hx y hy k
    have step3 : ∑ k : I, L2 k j * (∑ i : I, L1 i k * d i x y) = ∑ k : I, ∑ i : I, L2 k j * (L1 i k * d i x y) := by
      apply sum_congr rfl
      intro k _
      rw [Finset.mul_sum]
    have step4 : ∑ k : I, ∑ i : I, L2 k j * (L1 i k * d i x y) = ∑ i : I, ∑ k : I, (L2 k j * L1 i k) * d i x y := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro k _
      rw [mul_assoc]
    have step5 : ∑ i : I, ∑ k : I, (L2 k j * L1 i k) * d i x y = ∑ i : I, (∑ k : I, L2 k j * L1 i k) * d i x y := by
      apply sum_congr rfl
      intro i _
      rw [sum_mul]
    calc
      d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func y)) ≤ ∑ k : I, L2 k j * d k (ϕ1.func x) (ϕ1.func y) := step1
      _ ≤ ∑ k : I, L2 k j * (∑ i : I, L1 i k * d i x y) := step2
      _ = ∑ k : I, ∑ i : I, L2 k j * (L1 i k * d i x y) := step3
      _ = ∑ i : I, ∑ k : I, (L2 k j * L1 i k) * d i x y := step4
      _ = ∑ i : I, (∑ k : I, L2 k j * L1 i k) * d i x y := step5
      _ = ∑ i : I, matrix_mul L2 L1 i j * d i x y := rfl

/--
OET anchor: h-0f256e6f1d38a612
**命题 #h-0f256e6f1d38a612（co-Lip 矩阵复合律）**
-/
theorem colip_matrix_comp (ϕ1 ϕ2 : Operator X bot) (U1 U2 : Set X)
    (K1 K2 : I → I → ENNReal)
    (h_im : ∀ x ∈ U1, ϕ1.func x ∈ U2)
    (hK1 : IsCoLipMatrix d ϕ1 U1 K1)
    (hK2 : IsCoLipMatrix d ϕ2 U2 K2) :
    IsCoLipMatrix d (OperatorChain [ϕ2, ϕ1]) U1 (matrix_mul K2 K1) := by
  dsimp [IsCoLipMatrix] at hK1 hK2 ⊢
  rcases hK1 with ⟨hU1_ne, hU1_dom, hK1_ineq⟩
  rcases hK2 with ⟨hU2_ne, hU2_dom, hK2_ineq⟩
  constructor
  · exact hU1_ne
  · constructor
    · intro x hx
      dsimp [OperatorChain, dom]
      have h_phi1_x_in_U2 := h_im x hx
      exact hU2_dom h_phi1_x_in_U2
    · intro x hx y hy j
      have h_phi1_x_in_U2 := h_im x hx
      have h_phi1_y_in_U2 := h_im y hy
      dsimp [OperatorChain]
      have step1 := hK2_ineq (ϕ1.func x) h_phi1_x_in_U2 (ϕ1.func y) h_phi1_y_in_U2 j
      have step2 : ∑ k : I, K2 k j * d k (ϕ1.func x) (ϕ1.func y) ≥ ∑ k : I, K2 k j * (∑ i : I, K1 i k * d i x y) := by
        apply sum_le_sum
        intro k _
        gcongr
        exact hK1_ineq x hx y hy k
      have step3 : ∑ k : I, K2 k j * (∑ i : I, K1 i k * d i x y) = ∑ k : I, ∑ i : I, K2 k j * (K1 i k * d i x y) := by
        apply sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
      have step4 : ∑ k : I, ∑ i : I, K2 k j * (K1 i k * d i x y) = ∑ i : I, ∑ k : I, (K2 k j * K1 i k) * d i x y := by
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro k _
        rw [mul_assoc]
      have step5 : ∑ i : I, ∑ k : I, (K2 k j * K1 i k) * d i x y = ∑ i : I, (∑ k : I, K2 k j * K1 i k) * d i x y := by
        apply sum_congr rfl
        intro i _
        rw [sum_mul]
      calc
        d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func y)) ≥ ∑ k : I, K2 k j * d k (ϕ1.func x) (ϕ1.func y) := step1
        _ ≥ ∑ k : I, K2 k j * (∑ i : I, K1 i k * d i x y) := step2
        _ = ∑ k : I, ∑ i : I, K2 k j * (K1 i k * d i x y) := step3
        _ = ∑ i : I, ∑ k : I, (K2 k j * K1 i k) * d i x y := step4
        _ = ∑ i : I, (∑ k : I, K2 k j * K1 i k) * d i x y := step5
        _ = ∑ i : I, matrix_mul K2 K1 i j * d i x y := rfl




/--
OET anchor: h-193cebcc1a7f9259
**命题 #h-193cebcc1a7f9259（Lip 矩阵复合律）- 像集受限版本**
使用精确的上游像集作为下游定义域。
-/
theorem lip_matrix_comp_exact (ϕ1 ϕ2 : Operator X bot) (U1 : Set X)
    (L_phi1 L_phi2 : I → I → ENNReal)
    (hL1 : IsLipMatrix d ϕ1 U1 L_phi1)
    (hL2 : IsLipMatrix d ϕ2 (operator_image ϕ1 U1) L_phi2) :
    IsLipMatrix d (OperatorChain [ϕ2, ϕ1]) U1 (matrix_mul L_phi2 L_phi1) := by
  apply lip_matrix_comp d ϕ1 ϕ2 U1 (operator_image ϕ1 U1) L_phi1 L_phi2
  · intro x hx
    exact Set.mem_image_of_mem ϕ1.func hx
  · exact hL1
  · exact hL2

/--
OET anchor: h-0f256e6f1d38a612
**命题 #h-0f256e6f1d38a612（co-Lip 矩阵复合律）- 像集受限版本**
使用精确的上游像集作为下游定义域。
-/
theorem colip_matrix_comp_exact (ϕ1 ϕ2 : Operator X bot) (U1 : Set X)
    (K_phi1 K_phi2 : I → I → ENNReal)
    (hK1 : IsCoLipMatrix d ϕ1 U1 K_phi1)
    (hK2 : IsCoLipMatrix d ϕ2 (operator_image ϕ1 U1) K_phi2) :
    IsCoLipMatrix d (OperatorChain [ϕ2, ϕ1]) U1 (matrix_mul K_phi2 K_phi1) := by
  apply colip_matrix_comp d ϕ1 ϕ2 U1 (operator_image ϕ1 U1) K_phi1 K_phi2
  · intro x hx
    exact Set.mem_image_of_mem ϕ1.func hx
  · exact hK1
  · exact hK2

/--
OET anchor: h-11006ddd8c43bfec
**注（零步复合的单位矩阵证书）**
零步链的单位矩阵同时是恒等映射的 Lip 与 co-Lip 矩阵。
-/
theorem zero_step_identity_matrix_lip_colip (U : Set X)
    (hU : ∀ x ∈ U, x ≠ bot) (hU_ne : U.Nonempty) :
    IsLipMatrix d (OperatorChain ([] : List (Operator X bot))) U matrix_id ∧
      IsCoLipMatrix d (OperatorChain ([] : List (Operator X bot))) U matrix_id := by
  constructor
  · exact right_chain_lip_matrix d [] U matrix_id (RightChainLipBounded.nil U hU)
  · exact right_chain_colip_matrix d [] U matrix_id (RightChainCoLipBounded.nil U hU hU_ne)

end

end formal_oet.vol_01.ch_02_operator_bounds
