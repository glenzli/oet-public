import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_03_operator_local_degeneracy.component_partition
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Finset.Basic

set_option linter.style.longLine false

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

open formal_oet.vol_01.ch_01_foundations

noncomputable section

variable {X I : Type} {bot : X}
local instance instDecidableEqIComputationalFiber : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/-- 非空有限子族 -/
abbrev NonemptyFinset (I : Type) := { J : Finset I // J.Nonempty }


/-- 单元素非空子族 -/
def singleton_nonempty_finset (j : I) : NonemptyFinset I := ⟨{j}, Finset.singleton_nonempty j⟩

/-- 全指标非空子族。 -/
def full_nonempty_finset [Fintype I] [Nonempty I] : NonemptyFinset I :=
  ⟨Finset.univ, Finset.univ_nonempty⟩

/--
OET anchor: h-77b9589cc080d4f0
**定义（子族复合伪度量）**
$d_J(x, y) := \max_{j \in J} d_j(x, y)$
-/
def comp_pseudo_metric (J : NonemptyFinset I) (x y : X) : ENNReal :=
  J.val.sup (fun j => d j x y)

/-- 有限子族上的最大复合伪度量等于基础章定义的子族复合伪度量。 -/
theorem comp_pseudo_metric_eq_subfamily (J : NonemptyFinset I) :
    comp_pseudo_metric d J =
      subfamily_pseudometric d (↑J.val : Set I) := by
  funext x y
  apply le_antisymm
  · dsimp [comp_pseudo_metric, subfamily_pseudometric]
    apply Finset.sup_le
    intro j hj
    exact le_iSup_of_le ⟨j, hj⟩ le_rfl
  · dsimp [comp_pseudo_metric, subfamily_pseudometric]
    apply iSup_le
    intro j
    exact Finset.le_sup (f := fun k => d k x y) j.2

/-- A singleton finite subfamily recovers the selected component. -/
@[simp]
theorem comp_pseudo_metric_singleton (i : I) :
    comp_pseudo_metric d (singleton_nonempty_finset i) = d i := by
  funext x y
  dsimp [comp_pseudo_metric, singleton_nonempty_finset]
  simp

/--
复合伪度量 $d_J$ 等于 0 当且仅当子族中的每个测度均为 0。
-/
theorem comp_pseudo_metric_eq_zero_iff (J : NonemptyFinset I) (x y : X) :
    comp_pseudo_metric d J x y = 0 ↔ ∀ j ∈ J.val, d j x y = 0 := by
  dsimp [comp_pseudo_metric]
  exact Finset.sup_eq_bot_iff (fun j => d j x y) J.val

/--
OET anchor: h-77b9589cc080d4f0
**定义（计算纤维）**
$\operatorname{Fib}_{\phi, J}(y \mid U) := \{x \in U \mid d_J(\phi(x), y) = 0\}$
-/
def ComputationalFiber (ϕ : Operator X bot) (J : NonemptyFinset I) (U : Set X) (y : X) : Set X :=
  { x ∈ U | comp_pseudo_metric d J (ϕ.func x) y = 0 }

/--
OET anchor: h-8d9c504286a147a3
**命题（计算纤维的基本性质，(v)）- 单分量纤维**
单元素子族上的计算纤维就是对应单分量零距截面。
-/
theorem singleton_computational_fiber_eq (ϕ : Operator X bot) (U : Set X) (i : I) (y : X) :
    ComputationalFiber d ϕ (singleton_nonempty_finset i) U y =
      { x | x ∈ U ∧ d i (ϕ.func x) y = 0 } := by
  ext x
  constructor
  · intro hx
    constructor
    · exact hx.1
    · have h_all :=
        (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset i)
          (ϕ.func x) y).mp hx.2
      exact h_all i (Finset.mem_singleton.mpr rfl)
  · rintro ⟨hxU, hzero⟩
    constructor
    · exact hxU
    · apply (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset i)
        (ϕ.func x) y).mpr
      intro k hk
      have hk_eq : k = i := Finset.mem_singleton.mp hk
      simpa [hk_eq] using hzero

/--
OET anchor: h-8d9c504286a147a3
**命题（计算纤维的基本性质，(v)）- 全纤维包含单分量纤维**
全指标纤维包含于任意单分量纤维。
-/
theorem full_fiber_subset_singleton_fiber [Fintype I] [Nonempty I]
    (ϕ : Operator X bot) (U : Set X) (i : I) (y : X) :
    ComputationalFiber d ϕ (full_nonempty_finset : NonemptyFinset I) U y ⊆
      ComputationalFiber d ϕ (singleton_nonempty_finset i) U y := by
  intro x hx
  constructor
  · exact hx.1
  · apply (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset i)
      (ϕ.func x) y).mpr
    intro k hk
    have hk_eq : k = i := Finset.mem_singleton.mp hk
    rw [hk_eq]
    have h_all :=
      (comp_pseudo_metric_eq_zero_iff d (full_nonempty_finset : NonemptyFinset I)
        (ϕ.func x) y).mp hx.2
    exact h_all i (Finset.mem_univ i)

/--
OET anchor: h-8d9c504286a147a3
**命题（计算纤维的基本性质）- 分量交集律**
交集律：$\operatorname{Fib}_{\phi, J}(y \mid U) = \bigcap_{j \in J} \operatorname{Fib}_{\phi, j}(y \mid U)$
-/
theorem fiber_inter_law (ϕ : Operator X bot) (J : NonemptyFinset I) (U : Set X) (y : X) :
    ComputationalFiber d ϕ J U y = ⋂ j ∈ J.val, ComputationalFiber d ϕ (singleton_nonempty_finset j) U y := by
  ext x
  simp only [ComputationalFiber, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · rintro ⟨hx_U, h_comp⟩
    intro j hj
    have h_zero : ∀ k ∈ J.val, d k (ϕ.func x) y = 0 := (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) y).mp h_comp
    constructor
    · exact hx_U
    · apply (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j) (ϕ.func x) y).mpr
      intro k hk
      have hk_eq : k = j := Finset.mem_singleton.mp hk
      rw [hk_eq]
      exact h_zero j hj
  · intro h
    rcases J.prop with ⟨j0, hj0⟩
    have h_j0 := h j0 hj0
    have hx_U := h_j0.1
    constructor
    · exact hx_U
    · apply (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) y).mpr
      intro k hk
      have hk_eval := h k hk
      have h_zero := (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset k) (ϕ.func x) y).mp hk_eval.2
      exact h_zero k (Finset.mem_singleton.mpr rfl)

/--
OET anchor: h-8d9c504286a147a3
**命题（计算纤维的基本性质）- 子族单调性**
若 `J ⊆ K`，则 `K`-纤维包含于 `J`-纤维。
-/
theorem fiber_subset_of_index_subset (ϕ : Operator X bot) (J K : NonemptyFinset I)
    (U : Set X) (y : X) (hsub : J.val ⊆ K.val) :
    ComputationalFiber d ϕ K U y ⊆ ComputationalFiber d ϕ J U y := by
  intro x hx
  constructor
  · exact hx.1
  · apply (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) y).mpr
    intro j hj
    have h_all :=
      (comp_pseudo_metric_eq_zero_iff d K (ϕ.func x) y).mp hx.2
    exact h_all j (hsub hj)

/--
OET anchor: h-70882b889ff4ec94
**命题 #h-70882b889ff4ec94（纤维截断的单步判据，纤维成员形式）**
若 $y'$ 落入 $\phi(y)$ 的单分量计算纤维，则对应输出测距为零。
-/
theorem fiber_truncates_distance_of_mem (ϕ : Operator X bot) (U : Set X) (j : I) (y y' : X)
    (symm : ∀ x y : X, d j x y = d j y x)
    (hy'_fiber : y' ∈ ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func y)) :
    d j (ϕ.func y) (ϕ.func y') = 0 := by
  have h_zero_rev :
      d j (ϕ.func y') (ϕ.func y) = 0 := by
    have h_all :=
      (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j)
        (ϕ.func y') (ϕ.func y)).mp hy'_fiber.2
    exact h_all j (Finset.mem_singleton.mpr rfl)
  rw [symm]
  exact h_zero_rev

/--
OET anchor: h-70882b889ff4ec94
**命题 #h-70882b889ff4ec94（纤维截断的单步判据，复合形式）**
若第一步像点落入第二步的计算纤维，则两步复合后的输出测距为零。
-/
theorem composed_fiber_truncates_distance (ϕ1 ϕ2 : Operator X bot) (U2 : Set X) (j : I) (x x' : X)
    (symm : ∀ a b : X, d j a b = d j b a)
    (hx_dom : x ∈ dom ϕ1)
    (hx'_dom : x' ∈ dom ϕ1)
    (hx_image : ϕ1.func x ∈ U2)
    (hx'_image : ϕ1.func x' ∈ U2)
    (h_fiber :
      ϕ1.func x' ∈
        ComputationalFiber d ϕ2 (singleton_nonempty_finset j) U2 (ϕ2.func (ϕ1.func x))) :
    d j (ϕ2.func (ϕ1.func x)) (ϕ2.func (ϕ1.func x')) = 0 := by
  have _ := hx_dom
  have _ := hx'_dom
  have _ := hx_image
  have _ := hx'_image
  exact fiber_truncates_distance_of_mem d ϕ2 U2 j (ϕ1.func x) (ϕ1.func x') symm h_fiber

/--
OET anchor: h-8d9c504286a147a3
**命题（计算纤维的基本性质）- 目标零距不变性**
等价纤维的不变性：若 $d_J(y, y') = 0$，则 $\operatorname{Fib}_{\phi, J}(y \mid U) = \operatorname{Fib}_{\phi, J}(y' \mid U)$
-/
theorem fiber_eq_of_comp_dist_zero (ϕ : Operator X bot) (J : NonemptyFinset I) (U : Set X) (y y' : X)
    (triangle : ∀ j x y z, d j x z ≤ d j x y + d j y z)
    (symm : ∀ j x y, d j x y = d j y x)
    (h_dist : comp_pseudo_metric d J y y' = 0) :
    ComputationalFiber d ϕ J U y = ComputationalFiber d ϕ J U y' := by
  ext x
  dsimp [ComputationalFiber]
  have h_zero : ∀ j ∈ J.val, d j y y' = 0 := (comp_pseudo_metric_eq_zero_iff d J y y').mp h_dist
  have h_y_y'_symm : ∀ j ∈ J.val, d j y' y = 0 := by
    intro j hj
    rw [symm]
    exact h_zero j hj
  constructor
  · rintro ⟨hx_U, h_comp⟩
    have h_x_y : ∀ j ∈ J.val, d j (ϕ.func x) y = 0 := (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) y).mp h_comp
    constructor
    · exact hx_U
    · apply (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) y').mpr
      intro j hj
      have h_le := triangle j (ϕ.func x) y y'
      rw [h_x_y j hj, h_zero j hj, add_zero] at h_le
      exact le_antisymm h_le (zero_le _)
  · rintro ⟨hx_U, h_comp⟩
    have h_x_y' : ∀ j ∈ J.val, d j (ϕ.func x) y' = 0 := (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) y').mp h_comp
    constructor
    · exact hx_U
    · apply (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) y).mpr
      intro j hj
      have h_le := triangle j (ϕ.func x) y' y
      rw [h_x_y' j hj, h_y_y'_symm j hj, add_zero] at h_le
      exact le_antisymm h_le (zero_le _)

/--
OET anchor: h-8d9c504286a147a3
**命题（计算纤维的基本性质）- 纤维覆盖**
计算纤维的分划属性：所有像点的纤维的并集覆盖整个区域 $U$。
-/
theorem fiber_partition (ϕ : Operator X bot) (J : NonemptyFinset I) (U : Set X)
    (self_dist_zero : ∀ j x, d j x x = 0) :
    ⋃ y ∈ ϕ.func '' U, ComputationalFiber d ϕ J U y = U := by
  ext x
  constructor
  · simp only [Set.mem_iUnion]
    rintro ⟨y, _, h_fib⟩
    exact h_fib.1
  · intro hx
    simp only [Set.mem_iUnion]
    use ϕ.func x
    use Set.mem_image_of_mem ϕ.func hx
    dsimp [ComputationalFiber]
    constructor
    · exact hx
    · apply (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) (ϕ.func x)).mpr
      intro j _
      exact self_dist_zero j (ϕ.func x)

/--
OET anchor: h-8d9c504286a147a3
**命题（计算纤维的基本性质）- 纤维互斥**
计算纤维的互斥属性：对于任意两个像点，其纤维要么相等，要么不交。
这保证了商空间的等价类互斥性。
-/
theorem fiber_disjoint (ϕ : Operator X bot) (J : NonemptyFinset I) (U : Set X)
    (triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z)
    (symm : ∀ i x y, d i x y = d i y x) :
    ∀ y1 ∈ ϕ.func '' U, ∀ y2 ∈ ϕ.func '' U,
    ComputationalFiber d ϕ J U y1 = ComputationalFiber d ϕ J U y2 ∨
    Disjoint (ComputationalFiber d ϕ J U y1) (ComputationalFiber d ϕ J U y2) := by
  intro y1 _ y2 _
  by_cases h_comp : comp_pseudo_metric d J y1 y2 = 0
  · left
    exact fiber_eq_of_comp_dist_zero d ϕ J U y1 y2 triangle symm h_comp
  · right
    rw [Set.disjoint_iff]
    intro x hx
    have h1 := hx.1.2
    have h2 := hx.2.2
    have h_x_y1 : ∀ j ∈ J.val, d j (ϕ.func x) y1 = 0 := (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) y1).mp h1
    have h_x_y2 : ∀ j ∈ J.val, d j (ϕ.func x) y2 = 0 := (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) y2).mp h2
    have h_y1_y2 : ∀ j ∈ J.val, d j y1 y2 = 0 := by
      intro j hj
      have h_le := triangle j y1 (ϕ.func x) y2
      rw [symm j y1 (ϕ.func x), h_x_y1 j hj, h_x_y2 j hj, zero_add] at h_le
      exact le_antisymm h_le (zero_le _)
    have h_comp_zero : comp_pseudo_metric d J y1 y2 = 0 := (comp_pseudo_metric_eq_zero_iff d J y1 y2).mpr h_y1_y2
    exact False.elim (h_comp h_comp_zero)

/--
OET anchor: h-8d9c504286a147a3
**命题 #h-8d9c504286a147a3（计算纤维的基本性质）**

正文四个分支的同形最终定理。`J`、`K` 由 `NonemptyFinset` 同时编码有限性与非空性。
-/
theorem computational_fiber_partition_subfamily_monotonicity_textbook
    (ϕ : Operator X bot) (U : Set X) (hU : U ⊆ dom ϕ)
    (J K : NonemptyFinset I)
    (hmetric : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    (∀ y y', comp_pseudo_metric d J y y' = 0 →
      ComputationalFiber d ϕ J U y = ComputationalFiber d ϕ J U y') ∧
    ((⋃ y ∈ ϕ.func '' U, ComputationalFiber d ϕ J U y) = U ∧
      ∀ y₁ ∈ ϕ.func '' U, ∀ y₂ ∈ ϕ.func '' U,
        ComputationalFiber d ϕ J U y₁ = ComputationalFiber d ϕ J U y₂ ∨
          Disjoint (ComputationalFiber d ϕ J U y₁)
            (ComputationalFiber d ϕ J U y₂)) ∧
    (∀ y, ComputationalFiber d ϕ J U y =
      ⋂ j ∈ J.val, ComputationalFiber d ϕ (singleton_nonempty_finset j) U y) ∧
    (J.val ⊆ K.val → ∀ y,
      ComputationalFiber d ϕ K U y ⊆ ComputationalFiber d ϕ J U y) := by
  have _ := hU
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y y' hyy'
    exact fiber_eq_of_comp_dist_zero d ϕ J U y y'
      (fun i => (hmetric i).triangle) (fun i => (hmetric i).symm) hyy'
  · constructor
    · exact fiber_partition d ϕ J U (fun i => (hmetric i).dist_self)
    · exact fiber_disjoint d ϕ J U
        (fun i => (hmetric i).triangle) (fun i => (hmetric i).symm)
  · intro y
    exact fiber_inter_law d ϕ J U y
  · intro hJK y
    exact fiber_subset_of_index_subset d ϕ J K U y hJK

/--
OET anchor: h-ff54b8d36fa86c90
OET anchor: h-8d9c504286a147a3
**命题（恒等分量的纤维与零化半径）(i)**
同时支撑计算纤维基本性质中的恒等分量情形。
若 `i` 是恒等分量，则以 `ϕ(y)` 为目标的单分量计算纤维正是 `y` 的 `d_i` 零类在 `U` 中的截断。
-/
theorem id_component_singleton_fiber_eq_zero_class (ϕ : Operator X bot) (U : Set X) (i : I) (y : X)
    (hy : y ∈ U)
    (h_id : i ∈ IdComponent d ϕ U)
    (symm : ∀ x y : X, d i x y = d i y x)
    (triangle : ∀ x y z : X, d i x z ≤ d i x y + d i y z) :
    ComputationalFiber d ϕ (singleton_nonempty_finset i) U (ϕ.func y) =
      { x | x ∈ U ∧ d i x y = 0 } := by
  ext x
  constructor
  · intro hx
    constructor
    · exact hx.1
    · have hφxφy :
          d i (ϕ.func x) (ϕ.func y) = 0 := by
        have h_all :=
          (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset i)
            (ϕ.func x) (ϕ.func y)).mp hx.2
        exact h_all i (Finset.mem_singleton.mpr rfl)
      have hxφx : d i x (ϕ.func x) = 0 := by
        rw [symm x (ϕ.func x)]
        exact h_id.2 x hx.1
      have hφy_y : d i (ϕ.func y) y = 0 := h_id.2 y hy
      have hφx_y : d i (ϕ.func x) y = 0 := by
        have h_le := triangle (ϕ.func x) (ϕ.func y) y
        rw [hφxφy, hφy_y, zero_add] at h_le
        exact le_antisymm h_le (zero_le _)
      have h_le := triangle x (ϕ.func x) y
      rw [hxφx, hφx_y, zero_add] at h_le
      exact le_antisymm h_le (zero_le _)
  · rintro ⟨hxU, hxy⟩
    constructor
    · exact hxU
    · apply (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset i)
        (ϕ.func x) (ϕ.func y)).mpr
      intro k hk
      have hk_eq : k = i := Finset.mem_singleton.mp hk
      rw [hk_eq]
      have hφx_x : d i (ϕ.func x) x = 0 := h_id.2 x hxU
      have hy_φy : d i y (ϕ.func y) = 0 := by
        rw [symm y (ϕ.func y)]
        exact h_id.2 y hy
      have hx_φy : d i x (ϕ.func y) = 0 := by
        have h_le := triangle x y (ϕ.func y)
        rw [hxy, hy_φy, zero_add] at h_le
        exact le_antisymm h_le (zero_le _)
      have h_le := triangle (ϕ.func x) x (ϕ.func y)
      rw [hφx_x, hx_φy, zero_add] at h_le
      exact le_antisymm h_le (zero_le _)

/--
OET anchor: h-8d9c504286a147a3
**命题（计算纤维的基本性质，(vi)）- 恒等分量的一般目标纤维**
若 `i` 是恒等分量，则以任意目标 `y` 为目标的单分量计算纤维
正是 `y` 的 `d_i` 零类在 `U` 中的截断。
-/
theorem id_component_singleton_fiber_eq_zero_class_target
    (ϕ : Operator X bot) (U : Set X) (i : I) (y : X)
    (h_id : i ∈ IdComponent d ϕ U)
    (symm : ∀ x y : X, d i x y = d i y x)
    (triangle : ∀ x y z : X, d i x z ≤ d i x y + d i y z) :
    ComputationalFiber d ϕ (singleton_nonempty_finset i) U y =
      { x | x ∈ U ∧ d i x y = 0 } := by
  ext x
  constructor
  · intro hx
    constructor
    · exact hx.1
    · have hφx_y : d i (ϕ.func x) y = 0 := by
        have h_all :=
          (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset i)
            (ϕ.func x) y).mp hx.2
        exact h_all i (Finset.mem_singleton.mpr rfl)
      have hx_φx : d i x (ϕ.func x) = 0 := by
        rw [symm x (ϕ.func x)]
        exact h_id.2 x hx.1
      have h_le := triangle x (ϕ.func x) y
      rw [hx_φx, hφx_y, zero_add] at h_le
      exact le_antisymm h_le (zero_le _)
  · rintro ⟨hxU, hxy⟩
    constructor
    · exact hxU
    · apply (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset i)
        (ϕ.func x) y).mpr
      intro k hk
      have hk_eq : k = i := Finset.mem_singleton.mp hk
      rw [hk_eq]
      have hφx_x : d i (ϕ.func x) x = 0 := h_id.2 x hxU
      have h_le := triangle (ϕ.func x) x y
      rw [hφx_x, hxy, zero_add] at h_le
      exact le_antisymm h_le (zero_le _)

/--
OET anchor: h-8d9c504286a147a3
**命题（计算纤维的基本性质，(vi)）- 常值分量的最大纤维**
常值分量在与常值像零距等价的目标上给出全集纤维。
-/
theorem const_component_singleton_fiber_eq_univ_for_equiv_target
    (ϕ : Operator X bot) (U : Set X) (i : I) (u0 y : X)
    (hu0 : u0 ∈ U)
    (h_const : i ∈ ConstComponent d ϕ U)
    (triangle : ∀ x y z : X, d i x z ≤ d i x y + d i y z)
    (hy_equiv : d i (ϕ.func u0) y = 0) :
    ComputationalFiber d ϕ (singleton_nonempty_finset i) U y = U := by
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxU
    constructor
    · exact hxU
    · apply (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset i)
        (ϕ.func x) y).mpr
      intro k hk
      have hk_eq : k = i := Finset.mem_singleton.mp hk
      rw [hk_eq]
      have h_const_zero : d i (ϕ.func x) (ϕ.func u0) = 0 :=
        h_const x hxU u0 hu0
      have h_le := triangle (ϕ.func x) (ϕ.func u0) y
      rw [h_const_zero, hy_equiv, zero_add] at h_le
      exact le_antisymm h_le (zero_le _)

/--
OET anchor: h-8d9c504286a147a3
**命题（计算纤维的基本性质，(vi)）- 常值分量的空纤维**
常值分量在与常值像正距分离的目标上给出空纤维。
-/
theorem const_component_singleton_fiber_eq_empty_for_separated_target
    (ϕ : Operator X bot) (U : Set X) (i : I) (u0 y : X)
    (hu0 : u0 ∈ U)
    (h_const : i ∈ ConstComponent d ϕ U)
    (symm : ∀ x y : X, d i x y = d i y x)
    (triangle : ∀ x y z : X, d i x z ≤ d i x y + d i y z)
    (hy_pos : 0 < d i y (ϕ.func u0)) :
    ComputationalFiber d ϕ (singleton_nonempty_finset i) U y = ∅ := by
  ext x
  constructor
  · intro hx
    have h_fib_zero : d i (ϕ.func x) y = 0 := by
      have h_all :=
        (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset i)
          (ϕ.func x) y).mp hx.2
      exact h_all i (Finset.mem_singleton.mpr rfl)
    have h_const_zero : d i (ϕ.func x) (ϕ.func u0) = 0 :=
      h_const x hx.1 u0 hu0
    have h_y_φx : d i y (ϕ.func x) = 0 := by
      rw [symm y (ϕ.func x), h_fib_zero]
    have h_le := triangle y (ϕ.func x) (ϕ.func u0)
    rw [h_y_φx, h_const_zero, zero_add] at h_le
    have h_zero : d i y (ϕ.func u0) = 0 := le_antisymm h_le (zero_le _)
    exact False.elim ((ne_of_gt hy_pos) h_zero)
  · intro hx
    exact False.elim hx

end

end formal_oet.vol_01.ch_03_operator_local_degeneracy
