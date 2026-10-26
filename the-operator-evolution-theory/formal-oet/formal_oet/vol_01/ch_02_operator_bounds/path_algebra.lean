import formal_oet.vol_01.ch_02_operator_bounds.matrix_composition

namespace formal_oet.vol_01.ch_02_operator_bounds

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open Finset

variable {I : Type} [Fintype I]
local instance instDecidableEqIPathAlgebra : DecidableEq I := Classical.decEq I

/--
OET anchor: h-e4154c34e95d3c23
**命题 #h-e4154c34e95d3c23（有限矩阵乘积条目的零值与正值判据）- 代数基础**
判定单步矩阵连乘等于零等价于全连乘不存在正路径。
-/
theorem matrix_mul_eq_zero_iff (L1 L2 : I → I → ENNReal) (i j : I) :
    matrix_mul L2 L1 i j = 0 ↔ ∀ k : I, L2 k j = 0 ∨ L1 i k = 0 := by
  dsimp [matrix_mul]
  rw [sum_eq_zero_iff]
  apply forall_congr'
  intro k
  rw [mul_eq_zero]
  constructor
  · intro h
    exact h (mem_univ k)
  · intro h _
    exact h

/--
OET anchor: h-e4154c34e95d3c23
**命题 #h-e4154c34e95d3c23（有限矩阵乘积条目的零值与正值判据）- 代数基础**
判定单步矩阵连乘大于零等价于存在严格正路径。
-/
theorem matrix_mul_pos_iff (K1 K2 : I → I → ENNReal) (i j : I) :
    matrix_mul K2 K1 i j > 0 ↔ ∃ k : I, K2 k j > 0 ∧ K1 i k > 0 := by
  dsimp [matrix_mul]
  constructor
  · intro h
    by_contra h_not
    push Not at h_not
    have h_zero : ∑ k : I, K2 k j * K1 i k = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      have hk := h_not k
      by_cases h2 : K2 k j > 0
      · have h1 : K1 i k ≤ 0 := hk h2
        have hz1 : K1 i k = 0 := le_antisymm h1 (zero_le _)
        rw [hz1, mul_zero]
      · push Not at h2
        have hz2 : K2 k j = 0 := le_antisymm h2 (zero_le _)
        rw [hz2, zero_mul]
    rw [h_zero] at h
    exact lt_irrefl 0 h
  · intro h
    rcases h with ⟨k, hk1, hk2⟩
    have h_ne1 := pos_iff_ne_zero.mp hk1
    have h_ne2 := pos_iff_ne_zero.mp hk2
    have h_mul_ne := mul_ne_zero h_ne1 h_ne2
    have h_mul_pos := pos_iff_ne_zero.mpr h_mul_ne
    apply lt_of_lt_of_le h_mul_pos
    apply Finset.single_le_sum (f := fun k_1 => K2 k_1 j * K1 i k_1)
    · intro _ _
      exact zero_le _
    · exact Finset.mem_univ k

/--
OET anchor: h-e4154c34e95d3c23
**命题 #h-e4154c34e95d3c23（有限矩阵乘积条目的零值与正值判据）- 连乘定义**
-/
noncomputable def matrix_list_mul : List (I → I → ENNReal) → I → I → ENNReal
  | [] => matrix_id
  | K :: Ks => matrix_mul K (matrix_list_mul Ks)

/-- A list-valued encoding of the successive Lip certificates on the actual image domains. -/
inductive RightChainLipCertificateList {X : Type} {bot : X}
    (d : I → X → X → ENNReal) :
    List (Operator X bot) → Set X → List (I → I → ENNReal) → Prop
  | nil (U : Set X) (hU : ∀ x ∈ U, x ≠ bot) :
      RightChainLipCertificateList d [] U []
  | cons (ϕ : Operator X bot) (tail : List (Operator X bot)) (U : Set X)
      (Lϕ : I → I → ENNReal) (Ls : List (I → I → ENNReal))
      (h_tail : RightChainLipCertificateList d tail U Ls)
      (hϕ : IsLipMatrix d ϕ ((OperatorChain tail).func '' U) Lϕ) :
      RightChainLipCertificateList d (ϕ :: tail) U (Lϕ :: Ls)

/-- A list-valued encoding of the successive co-Lip certificates on the actual image domains. -/
inductive RightChainCoLipCertificateList {X : Type} {bot : X}
    (d : I → X → X → ENNReal) :
    List (Operator X bot) → Set X → List (I → I → ENNReal) → Prop
  | nil (U : Set X) (hU : ∀ x ∈ U, x ≠ bot) (hU_ne : U.Nonempty) :
      RightChainCoLipCertificateList d [] U []
  | cons (ϕ : Operator X bot) (tail : List (Operator X bot)) (U : Set X)
      (Kϕ : I → I → ENNReal) (Ks : List (I → I → ENNReal))
      (h_tail : RightChainCoLipCertificateList d tail U Ks)
      (hϕ : IsCoLipMatrix d ϕ ((OperatorChain tail).func '' U) Kϕ) :
      RightChainCoLipCertificateList d (ϕ :: tail) U (Kϕ :: Ks)

theorem RightChainLipCertificateList.length_eq {X : Type} {bot : X}
    {d : I → X → X → ENNReal} {ϕs : List (Operator X bot)} {U : Set X}
    {Ls : List (I → I → ENNReal)}
    (h : RightChainLipCertificateList d ϕs U Ls) : ϕs.length = Ls.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simp [ih]

theorem RightChainCoLipCertificateList.length_eq {X : Type} {bot : X}
    {d : I → X → X → ENNReal} {ϕs : List (Operator X bot)} {U : Set X}
    {Ks : List (I → I → ENNReal)}
    (h : RightChainCoLipCertificateList d ϕs U Ks) : ϕs.length = Ks.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ _ _ _ _ ih => simp [ih]

/--
OET anchor: h-e4154c34e95d3c23
**命题 #h-e4154c34e95d3c23（有限矩阵乘积条目的零值与正值判据）- 存在正路径定义**
-/
inductive ExistsPositivePath : List (I → I → ENNReal) → I → I → Prop
  | nil_path (i : I) : ExistsPositivePath [] i i
  | cons_path (K : I → I → ENNReal) (Ks : List (I → I → ENNReal)) (i k j : I)
      (h_head : K k j > 0)
      (h_tail : ExistsPositivePath Ks i k) : ExistsPositivePath (K :: Ks) i j

/--
OET anchor: h-e4154c34e95d3c23
**命题 #h-e4154c34e95d3c23（有限矩阵乘积条目的零值与正值判据）- co-Lip 乘积条目的正值判据**
对于矩阵链列乘法，某元素严格大于零当且仅当存在一条全正路径。
-/
theorem list_matrix_mul_pos_iff (Ks : List (I → I → ENNReal)) (i j : I) :
    matrix_list_mul Ks i j > 0 ↔ ExistsPositivePath Ks i j := by
  induction Ks generalizing j with
  | nil =>
    unfold matrix_list_mul
    unfold matrix_id
    constructor
    · intro h
      split_ifs at h with heq
      · rw [heq]
        exact ExistsPositivePath.nil_path j
      · exact False.elim (lt_irrefl 0 h)
    · intro h
      cases h
      split_ifs with heq
      · exact zero_lt_one
      · exact False.elim (heq rfl)
  | cons K Ks ih =>
    unfold matrix_list_mul
    constructor
    · intro h
      have h_mul := matrix_mul_pos_iff (matrix_list_mul Ks) K i j
      rw [h_mul] at h
      rcases h with ⟨k, hk1, hk2⟩
      have h_tail := (ih k).mp hk2
      exact ExistsPositivePath.cons_path K Ks i k j hk1 h_tail
    · intro h
      cases h with
      | cons_path _ _ _ k _ hk_head hk_tail =>
        rw [matrix_mul_pos_iff]
        use k
        constructor
        · exact hk_head
        · exact (ih k).mpr hk_tail

/--
OET anchor: h-e4154c34e95d3c23
**命题 #h-e4154c34e95d3c23（有限矩阵乘积条目的零值与正值判据）- Lip 乘积条目的零值判据**
对于矩阵链列乘法，某元素为零当且仅当不存在任何全正路径（完全隔离）。
-/
theorem list_matrix_mul_eq_zero_iff (Ks : List (I → I → ENNReal)) (i j : I) :
    matrix_list_mul Ks i j = 0 ↔ ¬ ExistsPositivePath Ks i j := by
  have h_pos := list_matrix_mul_pos_iff Ks i j
  constructor
  · intro h h_path
    have h_pos_val := h_pos.mpr h_path
    rw [h] at h_pos_val
    exact lt_irrefl 0 h_pos_val
  · intro h
    by_contra h_ne
    have h_pos_val : matrix_list_mul Ks i j > 0 := pos_iff_ne_zero.mpr h_ne
    have h_path := h_pos.mp h_pos_val
    exact h h_path

/--
OET anchor: h-e4154c34e95d3c23
**命题（有限矩阵乘积条目的零值与正值判据）**

任意扩展非负矩阵列表的零值和正值判据。正文取非空列表；这里也保留空乘积的
单位矩阵情形。算子及其证书只在应用时选取，不是矩阵代数结论的前提。
-/
theorem finite_matrix_product_entry_zero_positive_textbook
    (Ms : List (I → I → ENNReal)) (i j : I) :
    (matrix_list_mul Ms i j = 0 ↔ ¬ ExistsPositivePath Ms i j) ∧
      (matrix_list_mul Ms i j > 0 ↔ ExistsPositivePath Ms i j) := by
  exact ⟨list_matrix_mul_eq_zero_iff Ms i j,
    list_matrix_mul_pos_iff Ms i j⟩

end

end formal_oet.vol_01.ch_02_operator_bounds
