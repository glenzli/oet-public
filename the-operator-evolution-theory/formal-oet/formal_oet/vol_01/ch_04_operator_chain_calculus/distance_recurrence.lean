import formal_oet.vol_01.ch_02_operator_bounds.matrix_composition
import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix


namespace formal_oet.vol_01.ch_04_operator_chain_calculus

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy

open scoped BigOperators

variable {X I : Type} {bot : X}
local instance instDecidableEqIDistanceRecurrence : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-5a1b95150c3a4df2
**§ #h-5a1b95150c3a4df2（算子链）**
The chain data is a finite ordered list, and this helper computes its composite.
The internal list is stored in composition order: the tail acts first.
-/
abbrev operator_chain {X : Type} {bot : X} (ϕs : List (Operator X bot)) :
    Operator X bot :=
  formal_oet.vol_01.ch_01_foundations.OperatorChain ϕs

/--
OET anchor: h-5a1b95150c3a4df2
**定义（距离向量）**
对于两点 `x,y`，距离向量的第 `i` 个分量为 `d i x y`。
-/
def DistanceVector (x y : X) (i : I) : ENNReal := d i x y

/--
OET anchor: h-5a1b95150c3a4df2
**§ #h-5a1b95150c3a4df2（距离向量递推）**
单步递推数据：同一算子同时携带合法 L/K 矩阵。
-/
structure DistanceVectorRecurrenceStep [Fintype I]
    (ϕ : Operator X bot) (U : Set X) where
  L : I → I → ENNReal
  K : I → I → ENNReal
  lip : IsLipMatrix d ϕ U L
  colip : IsCoLipMatrix d ϕ U K

/--
矩阵作用在距离向量上的第 `j` 个分量：
`∑ i, M i j * v i`。
-/
noncomputable def matrix_vector_bound [Fintype I]
    (M : I → I → ENNReal) (v : I → ENNReal) (j : I) : ENNReal :=
  ∑ i : I, M i j * v i

/--
OET anchor: h-664ab4248e21a8a0
**命题 #h-664ab4248e21a8a0（零化矩阵的链级下界）**
For a nonempty chain domain and valid Lip matrices on every tail input domain,
the first factor's all-component annihilation radius is a lower bound for every
output component of the composite.
-/
theorem chain_annihilation_matrix_lower_bound [Fintype I]
    (ϕs : List (Operator X bot)) (U : Set X) (i j : I)
    (h_len : 2 ≤ ϕs.length)
    (h_dom : U ⊆ dom (OperatorChain ϕs))
    (h_U_nonempty : U.Nonempty)
    (h_lip : HasTailLipMatrices d U ϕs) :
    min_annihilation_radius d (OperatorChain ϕs) i
        (singleton_nonempty_finset j) U ≥
      ⨅ l : I, min_annihilation_radius d (first_operator ϕs) i
        (singleton_nonempty_finset l) U :=
  composite_zero_radius_bound_1_exact d ϕs U i j h_len h_dom h_U_nonempty h_lip

/--
OET anchor: h-5a1b95150c3a4df2
**§ #h-5a1b95150c3a4df2（距离向量递推，上界部分）**
合法 Lip 矩阵给出链前后距离向量的逐分量上界。
-/
theorem distance_recurrence_lip_upper [Fintype I]
    (ϕ : Operator X bot) (U : Set X) (L : I → I → ENNReal)
    (hL : IsLipMatrix d ϕ U L) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ.func x) (ϕ.func y) ≤
        matrix_vector_bound L (DistanceVector d x y) j := by
  intro x hx y hy j
  simpa [matrix_vector_bound, DistanceVector] using hL.2 x hx y hy j

/--
OET anchor: h-5a1b95150c3a4df2
**§ #h-5a1b95150c3a4df2（距离向量递推，下界部分）**
合法 co-Lip 矩阵给出链前后距离向量的逐分量下界。
-/
theorem distance_recurrence_colip_lower [Fintype I]
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕ U K) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      matrix_vector_bound K (DistanceVector d x y) j ≤
        d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy j
  simpa [matrix_vector_bound, DistanceVector] using hK.2.2 x hx y hy j

/--
OET anchor: h-5a1b95150c3a4df2
**§ #h-5a1b95150c3a4df2（距离向量递推）**
L/K 两侧界的合并形式。
-/
theorem distance_vector_recurrence_bounds [Fintype I]
    (ϕ : Operator X bot) (U : Set X)
    (step : DistanceVectorRecurrenceStep d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      matrix_vector_bound step.K (DistanceVector d x y) j ≤
        d j (ϕ.func x) (ϕ.func y) ∧
      d j (ϕ.func x) (ϕ.func y) ≤
        matrix_vector_bound step.L (DistanceVector d x y) j := by
  intro x hx y hy j
  exact ⟨
    distance_recurrence_colip_lower d ϕ U step.K step.colip x hx y hy j,
    distance_recurrence_lip_upper d ϕ U step.L step.lip x hx y hy j⟩

/--
局部零化球给出单通路输出零距离。

这是正文中零化半径条件的直接 Lean 形式：一旦点对落入某个已证明会进入计算纤维的
开球，目标输出分量必为零。
-/
theorem distance_recurrence_zeroing_of_ball
    (ϕ : Operator X bot) (U : Set X) (i j : I) (center x : X) (r : ENNReal)
    (hx_ball : x ∈ OpenBall d i center r ∩ U)
    (h_ball :
      OpenBall d i center r ∩ U ⊆
        ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func center)) :
    d j (ϕ.func x) (ϕ.func center) = 0 := by
  have hx_fiber := h_ball hx_ball
  have h_zero :=
    (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j) (ϕ.func x) (ϕ.func center)).mp
      hx_fiber.2
  exact h_zero j (Finset.mem_singleton.mpr rfl)

/-- Local core of the chain-level fiber truncation step. -/
theorem chain_fiber_truncation_zero_step_core
    (dist_comm : ∀ i x y, d i x y = d i y x)
    (ϕ : Operator X bot) (U : Set X) (j : I) (x y : X)
    (hy_fiber :
      y ∈ ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func x)) :
    d j (ϕ.func x) (ϕ.func y) = 0 := by
  have h_zero_rev :
      d j (ϕ.func y) (ϕ.func x) = 0 :=
    (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j)
      (ϕ.func y) (ϕ.func x)).mp hy_fiber.2 j
        (Finset.mem_singleton.mpr rfl)
  calc
    d j (ϕ.func x) (ϕ.func y)
        = d j (ϕ.func y) (ϕ.func x) := dist_comm j (ϕ.func x) (ϕ.func y)
    _ = 0 := h_zero_rev

/--
OET anchor: h-9a65248d646a2b6f
**命题 #h-9a65248d646a2b6f（链级纤维截断与零距传播，截断步）**
At an actual chain input domain, membership in the next operator's computational
fiber forces zero output distance in the selected component.
-/
theorem chain_fiber_truncation_zero_step
    (dist_comm : ∀ i x y, d i x y = d i y x)
    (ϕ : Operator X bot) (U : Set X) (j : I) (x y : X)
    (hU : U ⊆ dom ϕ) (hx : x ∈ U) (hy : y ∈ U)
    (hy_fiber :
      y ∈ ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func x)) :
    d j (ϕ.func x) (ϕ.func y) = 0 := by
  have _ := hU hx
  have _ := hU hy
  exact chain_fiber_truncation_zero_step_core d dist_comm ϕ U j x y hy_fiber

/--
OET anchor: h-9a65248d646a2b6f
**命题 #h-9a65248d646a2b6f（链级纤维截断与零距传播，Lip 零距传播）**
合法 Lip 矩阵把全分量零测距点对送到全分量零测距点对。
-/
theorem all_components_zero_propagates_lip [Fintype I]
    (ϕ : Operator X bot) (U : Set X) (L : I → I → ENNReal)
    (hL : IsLipMatrix d ϕ U L) (x y : X)
    (hx : x ∈ U) (hy : y ∈ U)
    (hzero : ∀ i : I, d i x y = 0) :
    ∀ j : I, d j (ϕ.func x) (ϕ.func y) = 0 := by
  intro j
  have hupper := distance_recurrence_lip_upper d ϕ U L hL x hx y hy j
  have hsum : matrix_vector_bound L (DistanceVector d x y) j = 0 := by
    simp [matrix_vector_bound, DistanceVector, hzero]
  exact le_antisymm (by simpa [hsum] using hupper) (zero_le _)

/--
OET anchor: h-9a65248d646a2b6f
**命题 #h-9a65248d646a2b6f（链级纤维截断与零距传播，复合链形式）**
若复合链已有合法 Lip 矩阵，则起点处全分量零测距传递到链输出端。
-/
theorem chain_zero_distance_propagation_of_lip_matrix [Fintype I]
    (ϕs : List (Operator X bot)) (U : Set X) (L : I → I → ENNReal)
    (hL : IsLipMatrix d (OperatorChain ϕs) U L) (x y : X)
    (hx : x ∈ U) (hy : y ∈ U)
    (hzero : ∀ i : I, d i x y = 0) :
    ∀ j : I,
      d j ((OperatorChain ϕs).func x) ((OperatorChain ϕs).func y) = 0 := by
  exact all_components_zero_propagates_lip d (OperatorChain ϕs) U L hL x y hx hy hzero

/--
OET anchor: h-9a65248d646a2b6f
**命题 #h-9a65248d646a2b6f（链级纤维截断与零距传播，逐步 Lip 形式）**
Zero distance in every component at level `s` propagates to level `q` when each
intermediate step has a valid Lip matrix on its actual input domain.
-/
theorem chain_zero_distance_propagation_along_lip_steps [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (x x' : ℕ → X) (s q : ℕ) (hsq : s ≤ q)
    (hmem : ∀ p, s ≤ p → p < q → x p ∈ U p ∧ x' p ∈ U p)
    (hnext : ∀ p, s ≤ p → p < q →
      x (p + 1) = (ϕ p).func (x p) ∧ x' (p + 1) = (ϕ p).func (x' p))
    (hL : ∀ p, s ≤ p → p < q →
      ∃ L : I → I → ENNReal, IsLipMatrix d (ϕ p) (U p) L)
    (hzero : ∀ l : I, d l (x s) (x' s) = 0) :
    ∀ l : I, d l (x q) (x' q) = 0 := by
  apply all_component_zero_preserved_along_lip_steps d x x' s q hsq
  · intro p hsp hpq
    rcases hmem p hsp hpq with ⟨hxp, hx'p⟩
    rcases hnext p hsp hpq with ⟨hxnext, hx'next⟩
    rcases hL p hsp hpq with ⟨L, hLp⟩
    exact ⟨ϕ p, U p, L, hLp, hxp, hx'p, hxnext, hx'next⟩
  · exact hzero

/--
OET anchor: h-5a1b95150c3a4df2
**§ #h-5a1b95150c3a4df2（距离向量递推，零化截断分支）**
零化截断分支的显式形式。
-/
theorem distance_vector_recurrence_zero_branch
    (ϕ : Operator X bot) (U : Set X) (i j : I) (center x : X) (r : ENNReal)
    (hx_ball : x ∈ OpenBall d i center r ∩ U)
    (h_ball :
      OpenBall d i center r ∩ U ⊆
        ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func center)) :
    d j (ϕ.func x) (ϕ.func center) = 0 := by
  exact distance_recurrence_zeroing_of_ball d ϕ U i j center x r hx_ball h_ball

/--
OET anchor: h-5a1b95150c3a4df2
**§ #h-5a1b95150c3a4df2（距离向量递推，极小零化半径分支）**
点对距离严格小于极小零化半径时，正文中的零化截断条件由半径定义直接推出。
-/
theorem distance_vector_recurrence_zero_branch_of_min_radius
    (ϕ : Operator X bot) (U : Set X) (i j : I) (x y : X)
    (hx : x ∈ U) (hy : y ∈ U)
    (hxy : d i x y <
      min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U) :
    d j (ϕ.func x) (ϕ.func y) = 0 := by
  have h_min_le_ann :
      min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U ≤
        annihilation_radius d ϕ i (singleton_nonempty_finset j) U y :=
    iInf₂_le y hy
  have hxy_ann :
      d i x y < annihilation_radius d ϕ i (singleton_nonempty_finset j) U y :=
    lt_of_lt_of_le hxy h_min_le_ann
  rcases lt_iSup_iff.mp hxy_ann with ⟨r, hr⟩
  rcases lt_iSup_iff.mp hr with ⟨_hr_fin_pos, hr'⟩
  rcases lt_iSup_iff.mp hr' with ⟨h_ball, hxy_r⟩
  have hx_ball : x ∈ OpenBall d i y r ∩ U := ⟨hxy_r, hx⟩
  exact distance_recurrence_zeroing_of_ball d ϕ U i j y x r hx_ball h_ball

/--
OET anchor: h-5a1b95150c3a4df2
**§ #h-5a1b95150c3a4df2（链级行为传递）**
若全链没有触发截断，《算子界》 的链式 L/K 乘积给出链级双侧界。
-/
theorem distance_vector_chain_bounds [Fintype I]
    (ϕs : List (Operator X bot)) (U : Set X)
    (L K : I → I → ENNReal)
    (hL : RightChainLipBounded d ϕs U L)
    (hK : RightChainCoLipBounded d ϕs U K) :
    IsLipMatrix d (OperatorChain ϕs) U L ∧
      IsCoLipMatrix d (OperatorChain ϕs) U K := by
  exact ⟨right_chain_lip_matrix d ϕs U L hL,
    right_chain_colip_matrix d ϕs U K hK⟩

end

end formal_oet.vol_01.ch_04_operator_chain_calculus
