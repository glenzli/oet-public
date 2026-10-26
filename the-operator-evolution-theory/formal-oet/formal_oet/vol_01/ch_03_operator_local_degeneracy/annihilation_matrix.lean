import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
import formal_oet.vol_01.ch_03_operator_local_degeneracy.computational_fiber
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Finset

variable {X I : Type} {bot : X} [Fintype I]
local instance instDecidableEqIAnnihilationMatrix : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/-- 度量开球 $B_i(y, r)$ -/
def OpenBall (i : I) (y : X) (r : ENNReal) : Set X :=
  { x | d i x y < r }

/--
OET anchor: h-bb1487a09d8bf151
**定义（非平凡有限半径）**
$r \in (0, +\infty)$
-/
def FinitePositiveRadius (r : ENNReal) : Prop := 0 < r ∧ r ≠ ⊤

/--
OET anchor: h-bb1487a09d8bf151
任意输入、输出扩展伪度量上的零化内切半径。
正文在非空评估域 `U ⊆ dom ϕ` 和基点 `y ∈ U` 上使用此公式。
-/
noncomputable def metric_annihilation_radius (d_in d_out : X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) (y : X) : ENNReal :=
  ⨆ (r : ENNReal) (_ : FinitePositiveRadius r)
    (_ : {x | d_in x y < r} ∩ U ⊆ {x ∈ U | d_out (ϕ.func x) (ϕ.func y) = 0}), r

/--
OET anchor: h-bb1487a09d8bf151
一般伪度量版本的统一零化半径：评估域为 `U`，取下确界的基点集合为 `A`。
-/
noncomputable def metric_min_annihilation_radius_on (d_in d_out : X → X → ENNReal)
    (ϕ : Operator X bot) (U A : Set X) : ENNReal :=
  ⨅ y ∈ A, metric_annihilation_radius d_in d_out ϕ U y

/--
OET anchor: h-bb1487a09d8bf151
一般伪度量版本的同域简记，即取 `A = U`。
-/
noncomputable def metric_min_annihilation_radius (d_in d_out : X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : ENNReal :=
  metric_min_annihilation_radius_on d_in d_out ϕ U U

/-- 严格小于一般零化内切半径的点，在指定输出伪度量下零距。 -/
theorem output_zero_of_lt_metric_annihilation_radius
    (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (x y : X)
    (hx : x ∈ U) (h : d_in x y < metric_annihilation_radius d_in d_out ϕ U y) :
    d_out (ϕ.func x) (ϕ.func y) = 0 := by
  obtain ⟨r, hr⟩ := lt_iSup_iff.mp h
  obtain ⟨_, hr⟩ := lt_iSup_iff.mp hr
  obtain ⟨hsub, hxr⟩ := lt_iSup_iff.mp hr
  exact (hsub ⟨hxr, hx⟩).2

/--
OET anchor: h-bb1487a09d8bf151
**定义（零化内切半径）**
$r^{\mathrm N}_{\phi, i, J}(y \mid U) = \sup \{r > 0 \mid r \neq \infty \wedge B_i(y, r) \cap U \subseteq \operatorname{Fib}_{\phi, J}(\phi(y) \mid U)\}$
-/
noncomputable def annihilation_radius (ϕ : Operator X bot) (i : I) (J : NonemptyFinset I) (U : Set X) (y : X) : ENNReal :=
  ⨆ (r : ENNReal) (_ : FinitePositiveRadius r) (_ : OpenBall d i y r ∩ U ⊆ ComputationalFiber d ϕ J U (ϕ.func y)), r

/--
OET anchor: h-bb1487a09d8bf151
**定义（统一零化半径）**
$\underline{r}^{\mathrm N}_{\phi, i, J}(A\mid U) = \inf_{y \in A} r^{\mathrm N}_{\phi, i, J}(y \mid U)$。
正文取 $\emptyset\neq A\subseteq U\subseteq\operatorname{dom}(\phi)$；$U$ 为评估域，$A$ 为基点集合。
-/
noncomputable def min_annihilation_radius_on (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U A : Set X) : ENNReal :=
  ⨅ y ∈ A, annihilation_radius d ϕ i J U y

/--
OET anchor: h-bb1487a09d8bf151
**定义（统一零化半径的同域简记）**
$\underline{r}^{\mathrm N}_{\phi, i, J}\big|_U = \underline{r}^{\mathrm N}_{\phi, i, J}(U\mid U)$
-/
noncomputable def min_annihilation_radius (ϕ : Operator X bot) (i : I) (J : NonemptyFinset I) (U : Set X) : ENNReal :=
  min_annihilation_radius_on d ϕ i J U U

omit [Fintype I] in
/--
OET anchor: h-bb1487a09d8bf151
输入分量与输出子族版本，是一般零化内切半径的特化。
-/
theorem annihilation_radius_eq_metric (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U : Set X) (y : X) :
    annihilation_radius d ϕ i J U y =
      metric_annihilation_radius (d i) (comp_pseudo_metric d J) ϕ U y := rfl

omit [Fintype I] in
/--
OET anchor: h-bb1487a09d8bf151
单输出分量版本恰好使用 `d_i,d_j` 作为输入、输出伪度量。
-/
theorem annihilation_radius_singleton_eq_metric (ϕ : Operator X bot) (i j : I)
    (U : Set X) (y : X) :
    annihilation_radius d ϕ i (singleton_nonempty_finset j) U y =
      metric_annihilation_radius (d i) (d j) ϕ U y := by
  rw [annihilation_radius_eq_metric, comp_pseudo_metric_singleton]

omit [Fintype I] in
/--
OET anchor: h-bb1487a09d8bf151
在任意基点集合 `A` 上，分量版本的下确界与一般定义一致。
-/
theorem min_annihilation_radius_on_eq_metric (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U A : Set X) :
    min_annihilation_radius_on d ϕ i J U A =
      metric_min_annihilation_radius_on (d i) (comp_pseudo_metric d J) ϕ U A := rfl

omit [Fintype I] in
/--
OET anchor: h-bb1487a09d8bf151
同域简记的分量版本与一般定义一致。
-/
theorem min_annihilation_radius_eq_metric (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U : Set X) :
    min_annihilation_radius d ϕ i J U =
      metric_min_annihilation_radius (d i) (comp_pseudo_metric d J) ϕ U := rfl

lemma ennreal_le_of_forall_pos_lt {a b : ENNReal} (h : ∀ c, 0 < c → c < a → c ≤ b) : a ≤ b := by
  by_contra h_not
  have h_lt : b < a := not_le.mp h_not
  rcases exists_between h_lt with ⟨c, hc1, hc2⟩
  have hc_pos : 0 < c := lt_of_le_of_lt (zero_le _) hc1
  have h_le := h c hc_pos hc2
  have h_false := not_le.mpr hc1
  exact h_false h_le

omit [Fintype I] in
lemma ann_radius_downward (ϕ : Operator X bot) (i : I) (J : NonemptyFinset I) (U : Set X) (y : X) (r1 r2 : ENNReal)
    (h_le : r1 ≤ r2) (h_sub : OpenBall d i y r2 ∩ U ⊆ ComputationalFiber d ϕ J U (ϕ.func y)) :
    OpenBall d i y r1 ∩ U ⊆ ComputationalFiber d ϕ J U (ϕ.func y) := by
  intro x hx
  have h_in_r1 : d i x y < r1 := hx.1
  have h_in_r2 : d i x y < r2 := lt_of_lt_of_le h_in_r1 h_le
  exact h_sub ⟨h_in_r2, hx.2⟩

omit [Fintype I] in
/--
单个纤维上的零化半径满足交集律：
$r^{\mathrm N}_{\phi, i, J}(y \mid U) = \min_{j \in J} r^{\mathrm N}_{\phi, i, j}(y \mid U)$
-/
theorem annihilation_radius_eq_min (ϕ : Operator X bot) (i : I) (J : NonemptyFinset I) (U : Set X) (y : X) :
    annihilation_radius d ϕ i J U y = J.val.inf' J.prop (fun j => annihilation_radius d ϕ i (singleton_nonempty_finset j) U y) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro j hj
    dsimp [annihilation_radius]
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply iSup_le
    intro h_sub
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have h_sub_j : OpenBall d i y r ∩ U ⊆ ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func y) := by
      intro x hx_U_ball
      have hx_fib := h_sub hx_U_ball
      dsimp [ComputationalFiber] at *
      constructor
      · exact hx_fib.1
      · apply (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j) (ϕ.func x) (ϕ.func y)).mpr
        intro k hk
        have hk_eq : k = j := Finset.mem_singleton.mp hk
        rw [hk_eq]
        have h_all_zero := (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) (ϕ.func y)).mp hx_fib.2
        exact h_all_zero j hj
    exact le_iSup_of_le h_sub_j le_rfl
  · dsimp [annihilation_radius]
    apply ennreal_le_of_forall_pos_lt
    intro r' hr'_pos hr'
    have h_r'_ne_top : r' ≠ ⊤ := ne_top_of_lt hr'
    have h_fin_pos : FinitePositiveRadius r' := ⟨hr'_pos, h_r'_ne_top⟩
    apply le_iSup_of_le r'
    apply le_iSup_of_le h_fin_pos
    have h_sub_r' : OpenBall d i y r' ∩ U ⊆ ComputationalFiber d ϕ J U (ϕ.func y) := by
      intro x hx_ball
      dsimp [ComputationalFiber]
      constructor
      · exact hx_ball.2
      · apply (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) (ϕ.func y)).mpr
        intro k hk
        have hk_lt : r' < annihilation_radius d ϕ i (singleton_nonempty_finset k) U y := by
          have h_le_k := Finset.inf'_le (fun j => annihilation_radius d ϕ i (singleton_nonempty_finset j) U y) hk
          exact lt_of_lt_of_le hr' h_le_k
        have h_sup := lt_iSup_iff.mp hk_lt
        rcases h_sup with ⟨rk, hrk⟩
        have h_sup2 := lt_iSup_iff.mp hrk
        rcases h_sup2 with ⟨hrk_fin_pos, hrk2⟩
        have h_sup3 := lt_iSup_iff.mp hrk2
        rcases h_sup3 with ⟨hk_sub, hk_final⟩
        have h_r'_le_rk : r' ≤ rk := le_of_lt hk_final
        have hk_sub_r' := ann_radius_downward d ϕ i (singleton_nonempty_finset k) U y r' rk h_r'_le_rk hk_sub
        have hx_in_fib_k := hk_sub_r' hx_ball
        have hk_zero := (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset k) (ϕ.func x) (ϕ.func y)).mp hx_in_fib_k.2
        exact hk_zero k (Finset.mem_singleton.mpr rfl)
    apply le_iSup_of_le h_sub_r'
    exact le_rfl

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-2b53c51151014456
**命题（统一零化半径的分量最小值公式）**
$\underline{r}^{\mathrm N}_{\phi, i, J}\big|_U = \min_{j \in J} \underline{r}^{\mathrm N}_{\phi, i, j}\big|_U$。
-/
theorem min_annihilation_radius_eq_min (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U : Set X) (_hU : U.Nonempty)
    (_hU_dom : U ⊆ dom ϕ) :
    min_annihilation_radius d ϕ i J U = J.val.inf' J.prop (fun j => min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U) := by
  apply le_antisymm
  · apply Finset.le_inf'
    intro j hj
    dsimp [min_annihilation_radius]
    apply iInf₂_mono
    intro y hy
    rw [annihilation_radius_eq_min]
    exact Finset.inf'_le _ hj
  · dsimp [min_annihilation_radius]
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    rw [annihilation_radius_eq_min]
    apply Finset.le_inf'
    intro j hj
    have h_le1 := Finset.inf'_le (fun k => ⨅ y ∈ U, annihilation_radius d ϕ i (singleton_nonempty_finset k) U y) hj
    have h_le2 : (⨅ y ∈ U, annihilation_radius d ϕ i (singleton_nonempty_finset j) U y) ≤ annihilation_radius d ϕ i (singleton_nonempty_finset j) U y := iInf₂_le y hy
    exact le_trans h_le1 h_le2

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-2b53c51151014456
**命题（统一零化半径的分量最小值公式，子族单调性）**
若 `J ⊆ K`，则目标子族 `K` 的统一零化半径不大于 `J` 的统一零化半径。
-/
theorem min_annihilation_radius_antitone
    (ϕ : Operator X bot) (i : I) (J K : NonemptyFinset I) (U : Set X)
    (hU : U.Nonempty)
    (hU_dom : U ⊆ dom ϕ)
    (hJK : J.val ⊆ K.val) :
    min_annihilation_radius d ϕ i K U ≤
      min_annihilation_radius d ϕ i J U := by
  rw [min_annihilation_radius_eq_min d ϕ i K U hU hU_dom,
    min_annihilation_radius_eq_min d ϕ i J U hU hU_dom]
  apply Finset.le_inf'
  intro j hj
  exact Finset.inf'_le _ (hJK hj)

/--
OET anchor: h-bb1487a09d8bf151
**定义（零化矩阵）**
$[\mathbf{N}(\phi)\big|_U]_{ji} = \underline{r}^{\mathrm N}_{\phi, d_i, d_j}\big|_U$
-/
noncomputable def AnnihilationMatrix (ϕ : Operator X bot) (U : Set X) : I → I → ENNReal :=
  fun j i => min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-70882b889ff4ec94
**命题 #h-70882b889ff4ec94（纤维截断的单步判据，零化半径形式）**
若 $d_i(y,y')$ 严格小于零化内切半径，则 $y'$ 落入相应计算纤维，
从而输出端 $j$ 分量测距归零。
-/
theorem fiber_truncation_of_lt_annihilation_radius (ϕ : Operator X bot) (U : Set X) (i j : I) (y y' : X)
    (symm : ∀ (k : I) (x y : X), d k x y = d k y x)
    (hy' : y' ∈ U)
    (h_lt : d i y y' < annihilation_radius d ϕ i (singleton_nonempty_finset j) U y) :
    d j (ϕ.func y) (ϕ.func y') = 0 := by
  have h_input_lt : d i y' y < annihilation_radius d ϕ i (singleton_nonempty_finset j) U y := by
    rw [symm i y' y]
    exact h_lt
  have h_sup := lt_iSup_iff.mp h_input_lt
  rcases h_sup with ⟨r, h_r_lt⟩
  have h_sup2 := lt_iSup_iff.mp h_r_lt
  rcases h_sup2 with ⟨_, h_r_lt2⟩
  have h_sup3 := lt_iSup_iff.mp h_r_lt2
  rcases h_sup3 with ⟨h_sub, h_dist_lt_r⟩
  have hy'_ball : y' ∈ OpenBall d i y r ∩ U := ⟨h_dist_lt_r, hy'⟩
  have hy'_fiber :
      y' ∈ ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func y) :=
    h_sub hy'_ball
  exact fiber_truncates_distance_of_mem d ϕ U j y y' (symm j) hy'_fiber

/-- A valid Lip step preserves zero distance in every component. -/
theorem all_component_zero_preserved_by_lip_step (ϕ : Operator X bot) (U : Set X)
    (L : I → I → ENNReal) (x y : X)
    (hL : IsLipMatrix d ϕ U L)
    (hx : x ∈ U)
    (hy : y ∈ U)
    (hzero : ∀ i : I, d i x y = 0) :
    ∀ j : I, d j (ϕ.func x) (ϕ.func y) = 0 := by
  rcases hL with ⟨_, hineq⟩
  intro j
  have h_bound := hineq x hx y hy j
  have h_sum_zero : (∑ i : I, L i j * d i x y) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hzero i, mul_zero]
  rw [h_sum_zero] at h_bound
  exact le_antisymm h_bound (zero_le _)

/-- Iterating valid Lip steps preserves zero distance in every component. -/
theorem all_component_zero_preserved_along_lip_steps
    (x x' : Nat → X) (s q : Nat)
    (hsq : s ≤ q)
    (hstep :
      ∀ p, s ≤ p → p < q →
        ∃ (ϕ : Operator X bot) (U : Set X) (L : I → I → ENNReal),
          IsLipMatrix d ϕ U L ∧
            x p ∈ U ∧ x' p ∈ U ∧
            x (p + 1) = ϕ.func (x p) ∧ x' (p + 1) = ϕ.func (x' p))
    (hzero : ∀ l : I, d l (x s) (x' s) = 0) :
    ∀ l : I, d l (x q) (x' q) = 0 := by
  let P : Nat → Prop := fun t =>
    (∀ p, s ≤ p → p < t →
      ∃ (ϕ : Operator X bot) (U : Set X) (L : I → I → ENNReal),
        IsLipMatrix d ϕ U L ∧
          x p ∈ U ∧ x' p ∈ U ∧
          x (p + 1) = ϕ.func (x p) ∧ x' (p + 1) = ϕ.func (x' p)) →
    ∀ l : I, d l (x t) (x' t) = 0
  have hprop : P q := by
    refine Nat.le_induction ?base ?step q hsq
    · intro _
      exact hzero
    · intro n hsn ih hsteps l
      have hprev : ∀ l : I, d l (x n) (x' n) = 0 := by
        apply ih
        intro p hp_s hp_n
        exact hsteps p hp_s (Nat.lt_trans hp_n (Nat.lt_succ_self n))
      rcases hsteps n hsn (Nat.lt_succ_self n) with ⟨ϕ, U, L, hL, hx, hx', hx_next, hx'_next⟩
      rw [hx_next, hx'_next]
      exact all_component_zero_preserved_by_lip_step d ϕ U L (x n) (x' n) hL hx hx' hprev l
  exact hprop hstep

omit [Fintype I] in
/-- 零化内切半径下界的辅助引理。 -/
theorem ann_radius_ge (ϕ : Operator X bot) (i : I) (J : NonemptyFinset I) (U : Set X) (y : X) (M : ENNReal)
    (h_subset : ∀ r : ENNReal, FinitePositiveRadius r → r < M →
      OpenBall d i y r ∩ U ⊆ ComputationalFiber d ϕ J U (ϕ.func y)) :
    annihilation_radius d ϕ i J U y ≥ M := by
  apply ennreal_le_of_forall_pos_lt
  intro r hr_pos hr_lt
  have h_fin_pos : FinitePositiveRadius r := ⟨hr_pos, ne_top_of_lt hr_lt⟩
  dsimp [annihilation_radius]
  apply le_iSup_of_le r
  apply le_iSup_of_le h_fin_pos
  apply le_iSup_of_le (h_subset r h_fin_pos hr_lt)
  exact le_rfl

theorem composite_zero_radius_bound_1 (ϕ1 ϕ2 : Operator X bot) (U1 : Set X) (i j : I)
    (L2 : I → I → ENNReal) (hL2 : IsLipMatrix d ϕ2 (ϕ1.func '' U1) L2) :
    min_annihilation_radius d (OperatorChain [ϕ2, ϕ1]) i (singleton_nonempty_finset j) U1 ≥
    ⨅ l : I, min_annihilation_radius d ϕ1 i (singleton_nonempty_finset l) U1 := by
  dsimp [min_annihilation_radius]
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply ann_radius_ge
  intro r _ hr_lt x hx
  have hx_ball :
      d i x y <
        ⨅ l : I, (⨅ y ∈ U1, annihilation_radius d ϕ1 i (singleton_nonempty_finset l) U1 y) :=
    lt_trans hx.1 hr_lt
  have hx_U : x ∈ U1 := hx.2

  have h_eq_all_l : ∀ l : I, d l (ϕ1.func x) (ϕ1.func y) = 0 := by
    intro l
    have h_le_ann : (⨅ l : I, (⨅ y ∈ U1, annihilation_radius d ϕ1 i (singleton_nonempty_finset l) U1 y)) ≤ annihilation_radius d ϕ1 i (singleton_nonempty_finset l) U1 y := by
      have h1 : (⨅ l : I, (⨅ y ∈ U1, annihilation_radius d ϕ1 i (singleton_nonempty_finset l) U1 y)) ≤ ⨅ y ∈ U1, annihilation_radius d ϕ1 i (singleton_nonempty_finset l) U1 y := iInf_le _ l
      have h2 : (⨅ y ∈ U1, annihilation_radius d ϕ1 i (singleton_nonempty_finset l) U1 y) ≤ annihilation_radius d ϕ1 i (singleton_nonempty_finset l) U1 y := iInf₂_le y hy
      exact le_trans h1 h2
    have h_lt_ann : d i x y < annihilation_radius d ϕ1 i (singleton_nonempty_finset l) U1 y := lt_of_lt_of_le hx_ball h_le_ann
    have h_sup := lt_iSup_iff.mp h_lt_ann
    rcases h_sup with ⟨r, hr⟩
    have h_sup2 := lt_iSup_iff.mp hr
    rcases h_sup2 with ⟨hr_fin_pos, hr2⟩
    have h_sup3 := lt_iSup_iff.mp hr2
    rcases h_sup3 with ⟨h_sub, h_final⟩
    have hx_in_ball : x ∈ OpenBall d i y r ∩ U1 := ⟨h_final, hx_U⟩
    have h_in_fiber := h_sub hx_in_ball
    have h_fib := h_in_fiber.2
    have h_iff := comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset l) (ϕ1.func x) (ϕ1.func y)
    exact (h_iff.mp h_fib) l (Finset.mem_singleton.mpr rfl)

  dsimp [ComputationalFiber, comp_pseudo_metric]
  constructor
  · exact hx_U
  · have h_iff := Finset.sup_eq_bot_iff (fun k => d k ((OperatorChain [ϕ2, ϕ1]).func x) ((OperatorChain [ϕ2, ϕ1]).func y)) {j}
    apply h_iff.mpr
    intro k hk
    have hk_eq : k = j := Finset.mem_singleton.mp hk
    rw [hk_eq]
    dsimp [OperatorChain]
    rcases hL2 with ⟨_, hL_ineq⟩
    have h_im_x : ϕ1.func x ∈ ϕ1.func '' U1 := Set.mem_image_of_mem ϕ1.func hx_U
    have h_im_y : ϕ1.func y ∈ ϕ1.func '' U1 := Set.mem_image_of_mem ϕ1.func hy
    have h_bound := hL_ineq (ϕ1.func x) h_im_x (ϕ1.func y) h_im_y j
    have h_sum_zero : ∑ k : I, L2 k j * d k (ϕ1.func x) (ϕ1.func y) = 0 := by
      apply sum_eq_zero
      intro l _
      rw [h_eq_all_l l, mul_zero]
    rw [h_sum_zero] at h_bound
    exact le_antisymm h_bound (zero_le _)

omit [Fintype I] in
/--
辅助引理：受限混合级联下确界的内部不等式 (Internal helper)
-/
theorem composite_zero_radius_bound_two_step_helper (ϕ1 ϕ2 : Operator X bot) (U1 : Set X) (i j : I)
    (L1 : I → I → ENNReal) (h_lip : ∀ l, HasScalarLipBound d ϕ1 U1 i l (L1 i l)) :
    min_annihilation_radius d (OperatorChain [ϕ2, ϕ1]) i (singleton_nonempty_finset j) U1 ≥
    ⨆ l : I, min_annihilation_radius d ϕ2 l (singleton_nonempty_finset j) (ϕ1.func '' U1) / L1 i l := by
  dsimp [min_annihilation_radius]
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply iSup_le
  intro l
  apply ann_radius_ge
  intro r _ hr_lt x hx
  have hx_ball :
      d i x y <
        (⨅ z ∈ ϕ1.func '' U1,
          annihilation_radius d ϕ2 l (singleton_nonempty_finset j) (ϕ1.func '' U1) z) / L1 i l :=
    lt_trans hx.1 hr_lt
  have hx_U : x ∈ U1 := hx.2

  have hd_l : d l (ϕ1.func x) (ϕ1.func y) ≤ L1 i l * d i x y :=
    (h_lip l).2 x hx_U y hy

  have h_le_ann : (⨅ z ∈ ϕ1.func '' U1, annihilation_radius d ϕ2 l (singleton_nonempty_finset j) (ϕ1.func '' U1) z) ≤ annihilation_radius d ϕ2 l (singleton_nonempty_finset j) (ϕ1.func '' U1) (ϕ1.func y) := by
    have h_im_y : ϕ1.func y ∈ ϕ1.func '' U1 := Set.mem_image_of_mem ϕ1.func hy
    exact iInf₂_le (ϕ1.func y) h_im_y

  have h_lt : L1 i l * d i x y < annihilation_radius d ϕ2 l (singleton_nonempty_finset j) (ϕ1.func '' U1) (ϕ1.func y) := by
    have h_lt_ann_inf : L1 i l * d i x y < (⨅ z ∈ ϕ1.func '' U1, annihilation_radius d ϕ2 l (singleton_nonempty_finset j) (ϕ1.func '' U1) z) := ENNReal.mul_lt_of_lt_div' hx_ball
    exact lt_of_lt_of_le h_lt_ann_inf h_le_ann

  have h_lt_ann_direct : d l (ϕ1.func x) (ϕ1.func y) < annihilation_radius d ϕ2 l (singleton_nonempty_finset j) (ϕ1.func '' U1) (ϕ1.func y) := lt_of_le_of_lt hd_l h_lt

  have h_sup := lt_iSup_iff.mp h_lt_ann_direct
  rcases h_sup with ⟨r, hr⟩
  have h_sup2 := lt_iSup_iff.mp hr
  rcases h_sup2 with ⟨hr_fin_pos, hr2⟩
  have h_sup3 := lt_iSup_iff.mp hr2
  rcases h_sup3 with ⟨h_sub, h_final⟩

  have hx_im : ϕ1.func x ∈ ϕ1.func '' U1 := Set.mem_image_of_mem ϕ1.func hx_U
  have hx_in_ball : ϕ1.func x ∈ OpenBall d l (ϕ1.func y) r ∩ (ϕ1.func '' U1) := ⟨h_final, hx_im⟩

  have h_in_fiber := h_sub hx_in_ball
  dsimp [ComputationalFiber] at h_in_fiber ⊢
  constructor
  · exact hx_U
  · exact h_in_fiber.2


/-- 辅助定义：链上的 Lip 矩阵存在性 (剔除第一层) -/
def HasTailLipMatrices (d : I → X → X → ENNReal) (U : Set X) : List (Operator X bot) → Prop
  | [] => True
  | [_] => True
  | ϕ :: tail => HasTailLipMatrices d U tail ∧ ∃ L, IsLipMatrix d ϕ ((OperatorChain tail).func '' U) L

/-- 辅助函数：提取算子链的第一步（列表末尾） -/
def first_operator : List (Operator X bot) → Operator X bot
  | [] => ⟨id, rfl⟩
  | [ϕ] => ϕ
  | _ :: tail => first_operator tail

/-- Internal chain form of the lower bound for composite annihilation radii. -/
theorem composite_zero_radius_bound_1_chain_helper (ϕs : List (Operator X bot)) (U : Set X) (i j : I) :
    HasTailLipMatrices d U ϕs →
    min_annihilation_radius d (OperatorChain ϕs) i (singleton_nonempty_finset j) U ≥
    ⨅ l : I, min_annihilation_radius d (first_operator ϕs) i (singleton_nonempty_finset l) U := by
  intro h_chain
  induction ϕs generalizing j
  case nil =>
    dsimp [OperatorChain, first_operator]
    exact iInf_le (fun l => min_annihilation_radius d ⟨id, rfl⟩ i (singleton_nonempty_finset l) U) j
  case cons ϕ tail ih =>
    cases tail
    case nil =>
      dsimp [OperatorChain, first_operator]
      exact iInf_le (fun l => min_annihilation_radius d ϕ i (singleton_nonempty_finset l) U) j
    case cons ϕ_tail tail_tail =>
      dsimp [HasTailLipMatrices] at h_chain
      have h_tail_chain := h_chain.1
      have h_phi_lip := h_chain.2
      rcases h_phi_lip with ⟨L, hL⟩

      have h_first : first_operator (ϕ :: ϕ_tail :: tail_tail) = first_operator (ϕ_tail :: tail_tail) := rfl
      rw [h_first]

      have h_ann_comp : min_annihilation_radius d (OperatorChain (ϕ :: ϕ_tail :: tail_tail)) i (singleton_nonempty_finset j) U =
          min_annihilation_radius d (OperatorChain [ϕ, OperatorChain (ϕ_tail :: tail_tail)]) i (singleton_nonempty_finset j) U := by
        congr 1

      rw [h_ann_comp]

      have h_step := composite_zero_radius_bound_1 d (OperatorChain (ϕ_tail :: tail_tail)) ϕ U i j L hL

      have h_ih_all : ∀ l : I, min_annihilation_radius d (OperatorChain (ϕ_tail :: tail_tail)) i (singleton_nonempty_finset l) U ≥
          ⨅ k : I, min_annihilation_radius d (first_operator (ϕ_tail :: tail_tail)) i (singleton_nonempty_finset k) U := by
        intro l
        exact ih l h_tail_chain

      have h_inf_step : (⨅ l : I, min_annihilation_radius d (OperatorChain (ϕ_tail :: tail_tail)) i (singleton_nonempty_finset l) U) ≥
          ⨅ k : I, min_annihilation_radius d (first_operator (ϕ_tail :: tail_tail)) i (singleton_nonempty_finset k) U := by
        apply le_iInf_iff.mpr
        intro l
        exact h_ih_all l

      exact le_trans h_inf_step h_step

/-- Internal text-level wrapper retaining the chain-length and domain hypotheses. -/
theorem composite_zero_radius_bound_1_exact (ϕs : List (Operator X bot)) (U : Set X) (i j : I)
    (h_len : 2 ≤ ϕs.length)
    (h_dom : U ⊆ dom (OperatorChain ϕs))
    (h_U_nempty : U.Nonempty)
    (h_lip : HasTailLipMatrices d U ϕs) :
    min_annihilation_radius d (OperatorChain ϕs) i (singleton_nonempty_finset j) U ≥
    ⨅ l : I, min_annihilation_radius d (first_operator ϕs) i (singleton_nonempty_finset l) U := by
  -- Retained for text alignment
  have _ := h_len
  have _ := h_dom
  have _ := h_U_nempty
  exact composite_zero_radius_bound_1_chain_helper d ϕs U i j h_lip

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-fd32966bed4ea8d0
**命题（常值分量与统一零化半径）(i)**
若纤维等于整个受限域，则每个有限正半径开球都落在纤维内。
-/
theorem total_fiber_all_finite_radii_admissible (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U : Set X) (y : X)
    (h_fiber : ComputationalFiber d ϕ J U (ϕ.func y) = U) :
    ∀ r : ENNReal, FinitePositiveRadius r →
      OpenBall d i y r ∩ U ⊆ ComputationalFiber d ϕ J U (ϕ.func y) := by
  intro r _ x hx
  rw [h_fiber]
  exact hx.2

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-fd32966bed4ea8d0
**命题（常值分量与统一零化半径）(i)**
在上一条件下，任意有限正半径均不超过零化内切半径。
-/
theorem finite_radius_le_annihilation_radius_of_total_fiber (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U : Set X) (y : X)
    (h_fiber : ComputationalFiber d ϕ J U (ϕ.func y) = U) :
    ∀ r : ENNReal, (hr : FinitePositiveRadius r) →
      r ≤ annihilation_radius d ϕ i J U y := by
  intro r hr
  apply le_iSup_of_le r
  apply le_iSup_of_le hr
  exact le_iSup_of_le (total_fiber_all_finite_radii_admissible d ϕ i J U y h_fiber r hr) le_rfl

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-fd32966bed4ea8d0
**命题（常值分量与统一零化半径）(i)**
若目标子族 `J` 中每个分量都是常值分量，则对应计算纤维等于整个受限域。
-/
theorem const_components_computational_fiber_eq_univ (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U : Set X) (y : X)
    (hy : y ∈ U)
    (h_const : ∀ j ∈ J.val, j ∈ ConstComponent d ϕ U) :
    ComputationalFiber d ϕ J U (ϕ.func y) = U := by
  have _ := i
  ext x
  constructor
  · intro hx
    exact hx.1
  · intro hxU
    constructor
    · exact hxU
    · apply (comp_pseudo_metric_eq_zero_iff d J (ϕ.func x) (ϕ.func y)).mpr
      intro j hj
      exact (h_const j hj) x hxU y hy

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-fd32966bed4ea8d0
**命题（常值分量与统一零化半径）(i)**
若计算纤维等于整个受限域，则零化内切半径为 `⊤`。
-/
theorem annihilation_radius_eq_top_of_total_fiber (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U : Set X) (y : X)
    (h_fiber : ComputationalFiber d ϕ J U (ϕ.func y) = U) :
    annihilation_radius d ϕ i J U y = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  cases n with
  | zero =>
      simp
  | succ n =>
      have hr : FinitePositiveRadius ((Nat.succ n : ℕ) : ENNReal) := by
        constructor
        · exact_mod_cast Nat.succ_pos n
        · exact ENNReal.natCast_ne_top (Nat.succ n)
      exact finite_radius_le_annihilation_radius_of_total_fiber d ϕ i J U y h_fiber
        ((Nat.succ n : ℕ) : ENNReal) hr

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-fd32966bed4ea8d0
**命题（常值分量与统一零化半径）(i)**
目标子族常值退化推出该子族的统一零化半径为 `⊤`。
-/
theorem const_components_min_annihilation_radius_eq_top (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U : Set X)
    (h_const : ∀ j ∈ J.val, j ∈ ConstComponent d ϕ U) :
    min_annihilation_radius d ϕ i J U = ⊤ := by
  apply le_antisymm
  · exact le_top
  · dsimp [min_annihilation_radius]
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    rw [annihilation_radius_eq_top_of_total_fiber d ϕ i J U y
      (const_components_computational_fiber_eq_univ d ϕ i J U y hy h_const)]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-ff54b8d36fa86c90
**命题（恒等分量的纤维与零化半径）(ii) 的半径估计**
若某个有限正半径球已经落入相应计算纤维，则该半径不超过零化内切半径。
-/
theorem finite_radius_le_annihilation_radius_of_fiber_ball (ϕ : Operator X bot) (i : I)
    (J : NonemptyFinset I) (U : Set X) (y : X) (r : ENNReal)
    (hr : FinitePositiveRadius r)
    (h_sub : OpenBall d i y r ∩ U ⊆ ComputationalFiber d ϕ J U (ϕ.func y)) :
    r ≤ annihilation_radius d ϕ i J U y := by
  apply le_iSup_of_le r
  apply le_iSup_of_le hr
  exact le_iSup_of_le h_sub le_rfl

/--
OET anchor: h-ff54b8d36fa86c90
**命题（恒等分量的纤维与零化半径）(ii)**
在恒等分量上，若有限正半径球在受限域内落入基点的输入零距类，
则零化内切半径不小于该半径，因而严格为正。
-/
theorem id_component_annihilation_radius_ge_of_zero_class_ball
    (ϕ : Operator X bot) (U : Set X) (i : I) (y : X)
    (hy : y ∈ U) (h_id : i ∈ IdComponent d ϕ U)
    (symm : ∀ x y : X, d i x y = d i y x)
    (triangle : ∀ x y z : X, d i x z ≤ d i x y + d i y z)
    (r₀ : ENNReal) (hr : FinitePositiveRadius r₀)
    (h_ball : OpenBall d i y r₀ ∩ U ⊆ {x | x ∈ U ∧ d i x y = 0}) :
    r₀ ≤ annihilation_radius d ϕ i (singleton_nonempty_finset i) U y ∧
      0 < annihilation_radius d ϕ i (singleton_nonempty_finset i) U y := by
  have h_fiber := id_component_singleton_fiber_eq_zero_class d ϕ U i y hy h_id
    symm triangle
  have h_le : r₀ ≤ annihilation_radius d ϕ i (singleton_nonempty_finset i) U y := by
    apply finite_radius_le_annihilation_radius_of_fiber_ball d ϕ i
      (singleton_nonempty_finset i) U y r₀ hr
    rw [h_fiber]
    exact h_ball
  exact ⟨h_le, lt_of_lt_of_le hr.1 h_le⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-fd32966bed4ea8d0
**命题（常值分量与统一零化半径）(ii)**
若所有非纤维点与基点的源距离为 `⊤`，则任意有限半径球仍包含于该纤维。
-/
theorem finite_balls_avoid_infinite_nonfiber_points (ϕ : Operator X bot) (i j : I)
    (U : Set X) (y : X)
    (h_nonfiber_top :
      ∀ x ∈ U,
        x ∉ ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func y) →
          d i x y = ⊤) :
    ∀ r : ENNReal, FinitePositiveRadius r →
      OpenBall d i y r ∩ U ⊆
        ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func y) := by
  intro r _ x hx
  by_contra hx_not
  have htop := h_nonfiber_top x hx.2 hx_not
  have hlt : d i x y < r := hx.1
  rw [htop] at hlt
  exact False.elim (not_top_lt hlt)

set_option linter.unusedFintypeInType false in
/--
OET anchor: h-fd32966bed4ea8d0
**命题（常值分量与统一零化半径）(ii)**
若所有非纤维点与基点的源距离为 `⊤`，则该基点的零化半径为 `⊤`。
-/
theorem annihilation_radius_eq_top_of_infinite_nonfiber_points (ϕ : Operator X bot) (i j : I)
    (U : Set X) (y : X)
    (h_nonfiber_top :
      ∀ x ∈ U,
        x ∉ ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func y) →
          d i x y = ⊤) :
    annihilation_radius d ϕ i (singleton_nonempty_finset j) U y = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  cases n with
  | zero =>
      simp
  | succ n =>
      have hr : FinitePositiveRadius ((Nat.succ n : ℕ) : ENNReal) := by
        constructor
        · exact_mod_cast Nat.succ_pos n
        · exact ENNReal.natCast_ne_top (Nat.succ n)
      apply le_iSup_of_le (((Nat.succ n : ℕ) : ENNReal))
      apply le_iSup_of_le hr
      exact le_iSup_of_le
        (finite_balls_avoid_infinite_nonfiber_points d ϕ i j U y h_nonfiber_top
          ((Nat.succ n : ℕ) : ENNReal) hr)
        le_rfl

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-fd32966bed4ea8d0
**命题（常值分量与统一零化半径）(ii)**
一个反例模式：若每个基点的非纤维点都在源分量上距离 `⊤`，
但输出端仍存在正距离点对，则零化矩阵条目为 `⊤`，目标分量却不是常值分量。
-/
theorem annihilation_matrix_top_does_not_force_const_component_pattern (ϕ : Operator X bot) (i j : I)
    (U : Set X)
    (h_nonfiber_top :
      ∀ y ∈ U, ∀ x ∈ U,
        x ∉ ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func y) →
          d i x y = ⊤)
    (h_output_pos : ∃ x ∈ U, ∃ y ∈ U, 0 < d j (ϕ.func x) (ϕ.func y)) :
    AnnihilationMatrix d ϕ U j i = ⊤ ∧ j ∉ ConstComponent d ϕ U := by
  constructor
  · dsimp [AnnihilationMatrix, min_annihilation_radius]
    apply le_antisymm
    · exact le_top
    · apply le_iInf
      intro y
      apply le_iInf
      intro hy
      rw [annihilation_radius_eq_top_of_infinite_nonfiber_points d ϕ i j U y
        (h_nonfiber_top y hy)]
  · intro h_const
    rcases h_output_pos with ⟨x, hx, y, hy, hpos⟩
    have hzero := h_const x hx y hy
    exact (ne_of_gt hpos) hzero

end

end formal_oet.vol_01.ch_03_operator_local_degeneracy
