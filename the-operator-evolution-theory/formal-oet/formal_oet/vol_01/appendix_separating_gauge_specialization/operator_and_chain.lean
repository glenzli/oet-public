import formal_oet.vol_01.appendix_separating_gauge_specialization.full_gauge
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix
import formal_oet.vol_01.ch_04_operator_chain_calculus.decomposition_core

namespace formal_oet.vol_01.appendix_separating_gauge_specialization

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_04_operator_chain_calculus

noncomputable section

variable {X I A : Type} {bot : X} [Fintype I] [Nonempty I]
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-d855ee3b07cdd0e9
**推论（全分量零距与映射相等）**
一般映射的全分量逐点零距等价于映射相等。
-/
theorem funext_of_full_gauge_zero
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (f g : A → X) :
    f = g ↔ ∀ a i, d i (f a) (g a) = 0 := by
  constructor
  · intro hfg a i
    subst g
    exact hd_self i (f a)
  · intro hzero
    funext a
    exact hsep (f a) (g a) (hzero a)

/--
OET anchor: h-d855ee3b07cdd0e9
**推论（全分量零距与映射相等）**
-/
theorem restricted_eval_full_zero_iff
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ ψ : Operator X bot) (U : Set X) :
    (∀ i, restricted_eval (d i) φ ψ U = 0) ↔
      ∀ x ∈ U, φ.func x = ψ.func x := by
  constructor
  · intro hzero x hx
    apply hsep (φ.func x) (ψ.func x)
    intro i
    apply le_antisymm ?_ (zero_le _)
    calc
      d i (φ.func x) (ψ.func x) ≤ restricted_eval (d i) φ ψ U := by
        exact le_iSup_of_le x (le_iSup_of_le hx le_rfl)
      _ = 0 := hzero i
  · intro heq i
    apply le_antisymm ?_ (zero_le _)
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    rw [heq x hx]
    exact le_of_eq (hd_self i (ψ.func x))

/--
OET anchor: h-d855ee3b07cdd0e9
**推论（全分量零距与映射相等）**
在非空公共定义域内，受限全分量零距也等价于局部等价。
-/
theorem restricted_eval_full_zero_iff_local_equivalent
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ ψ : Operator X bot) (U : Set X)
    (hU : U.Nonempty) (hdom : U ⊆ dom φ ∩ dom ψ) :
    (∀ i, restricted_eval (d i) φ ψ U = 0) ↔ LocalEquivalent φ ψ U := by
  have _ := hU
  have _ := hdom
  rw [restricted_eval_full_zero_iff d hd_self hsep]
  rfl

/--
OET anchor: h-d855ee3b07cdd0e9
**推论（全分量零距与映射相等）**
分离规范族诱导的算子规范族以全分量零距判定算子相等。
-/
theorem operator_eq_iff_all_dist_zero
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ ψ : Operator X bot) :
    φ = ψ ↔ ∀ i, op_dist (d i) φ ψ = 0 := by
  constructor
  · intro h
    subst ψ
    intro i
    apply le_antisymm ?_ (zero_le _)
    apply iSup_le
    intro x
    exact le_of_eq (hd_self i (φ.func x))
  · intro hzero
    exact (op_dist_separating_iff d hd_self).mp hsep φ ψ hzero

/--
OET anchor: h-71c78680ea301971
**命题（算子规范族的分离性继承）**
算子规范族分离算子空间，当且仅当原规范族分离点空间。
-/
theorem operator_gauge_separating_iff
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    IsSeparating d ↔
      IsSeparating (fun i (φ ψ : Operator X bot) => op_dist (d i) φ ψ) := by
  exact op_dist_separating_iff d (fun i x => (hd i).dist_self x)

/--
OET anchor: h-014c35c64a75152a
**推论（分离空间中的 co-Lip 单射判据）**
正对角 co-Lip 证书在分离规范空间中推出限制域上的单射性。
-/
theorem positive_diagonal_colip_injective
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (hK : IsCoLipMatrix d φ U K)
    (hdiag : ∀ i, K i i > 0) :
    ∀ x ∈ U, ∀ y ∈ U, φ.func x = φ.func y → x = y := by
  intro x hx y hy hxy
  apply hsep x y
  exact (positive_colip_channels_preserve_distinguishability d φ U K hK).2 hdiag
    x hx y hy (fun i => by rw [hxy, hd_self])

/--
OET anchor: h-1d4e90ad08791619
**推论（算子局部性质的点值解释）**
全分量恒等等价于点值恒等且每个分量在限制域上有正直径。
-/
theorem all_id_components_iff_pointwise_id
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X) :
    IdComponent d φ U = Set.univ ↔
      (∀ x ∈ U, φ.func x = x) ∧ (∀ i, ∃ x ∈ U, ∃ y ∈ U, 0 < d i x y) := by
  constructor
  · intro hid
    have hpoint : ∀ x ∈ U, φ.func x = x := by
      intro x hx
      apply hsep (φ.func x) x
      intro i
      have hi : i ∈ IdComponent d φ U := by simp [hid]
      exact hi.2 x hx
    refine ⟨hpoint, ?_⟩
    intro i
    by_contra hn
    push_neg at hn
    have hi : i ∈ IdComponent d φ U := by simp [hid]
    apply hi.1
    intro x hx y hy
    rw [hpoint x hx, hpoint y hy]
    exact le_antisymm (hn x hx y hy) (zero_le _)
  · rintro ⟨hpoint, hpos⟩
    ext i
    simp only [Set.mem_univ, iff_true]
    constructor
    · intro hc
      rcases hpos i with ⟨x, hx, y, hy, hxy⟩
      have hz := hc x hx y hy
      rw [hpoint x hx, hpoint y hy] at hz
      exact (ne_of_gt hxy) hz
    · intro x hx
      rw [hpoint x hx]
      exact hd_self i x

/--
OET anchor: h-1d4e90ad08791619
**推论（算子局部性质的点值解释）**
非空限制域上，全分量输出零距等价于点值常值。
-/
theorem all_components_constant_iff_pointwise_constant
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X)
    (hU : U.Nonempty) :
    (∀ x ∈ U, ∀ y ∈ U, ∀ i, d i (φ.func x) (φ.func y) = 0) ↔
      ∃ z, ∀ x ∈ U, φ.func x = z := by
  constructor
  · intro hzero
    rcases hU with ⟨x0, hx0⟩
    refine ⟨φ.func x0, ?_⟩
    intro x hx
    exact hsep (φ.func x) (φ.func x0) (hzero x hx x0 hx0)
  · rintro ⟨z, hz⟩ x hx y hy i
    rw [hz x hx, hz y hy]
    exact hd_self i z

/--
OET anchor: h-1d4e90ad08791619
**推论（算子局部性质的点值解释）**
全族计算纤维就是点值原像在限制域上的截切。
-/
theorem full_fiber_eq_point_preimage
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X) (y : X) :
    ComputationalFiber d φ (full_nonempty_finset : NonemptyFinset I) U y =
      {x | x ∈ U ∧ φ.func x = y} := by
  ext x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    have hzero :=
      (comp_pseudo_metric_eq_zero_iff d
        (full_nonempty_finset : NonemptyFinset I) (φ.func x) y).mp hx.2
    exact hsep (φ.func x) y (fun i => hzero i (Finset.mem_univ i))
  · rintro ⟨hxU, hxy⟩
    refine ⟨hxU, ?_⟩
    apply (comp_pseudo_metric_eq_zero_iff d
      (full_nonempty_finset : NonemptyFinset I) (φ.func x) y).mpr
    intro i _
    rw [hxy]
    exact hd_self i y

/--
OET anchor: h-1d4e90ad08791619
**推论（算子局部性质的点值解释）**
全族纤维按像值覆盖限制域，且不同像值的纤维互不相交。
-/
theorem full_fibers_form_point_preimage_partition
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X) :
    (∀ x ∈ U,
      x ∈ ComputationalFiber d φ
        (full_nonempty_finset : NonemptyFinset I) U (φ.func x)) ∧
    (∀ y ∈ φ.func '' U, ∀ z ∈ φ.func '' U, y ≠ z →
      Disjoint
        (ComputationalFiber d φ
          (full_nonempty_finset : NonemptyFinset I) U y)
        (ComputationalFiber d φ
          (full_nonempty_finset : NonemptyFinset I) U z)) := by
  constructor
  · intro x hx
    rw [full_fiber_eq_point_preimage d hd_self hsep]
    exact ⟨hx, rfl⟩
  · intro y _ z _ hyz
    rw [full_fiber_eq_point_preimage d hd_self hsep,
      full_fiber_eq_point_preimage d hd_self hsep]
    exact Set.disjoint_left.mpr (by
      intro x hxy hxz
      exact hyz (hxy.2.symm.trans hxz.2))

/-- A radius defined with an arbitrary input pseudometric and the full output family. -/
def full_output_annihilation_radius
    (φ : Operator X bot) (d_in : X → X → ENNReal) (U : Set X) (y : X) : ENNReal :=
  ⨆ (r : ENNReal) (_ : FinitePositiveRadius r)
    (_ : ball d_in y r ∩ U ⊆
      ComputationalFiber d φ (full_nonempty_finset : NonemptyFinset I) U (φ.func y)), r

/-- Point-value form of the same candidate-radius supremum. -/
def local_constant_radius
    (φ : Operator X bot) (d_in : X → X → ENNReal) (U : Set X) (y : X) : ENNReal :=
  ⨆ (r : ENNReal) (_ : FinitePositiveRadius r)
    (_ : ball d_in y r ∩ U ⊆ {x | x ∈ U ∧ φ.func x = φ.func y}), r

/--
OET anchor: h-1d4e90ad08791619
**推论（算子局部性质的点值解释）**
全分量零化半径等于局部常值半径。
-/
theorem full_output_annihilation_radius_eq_local_constant_radius
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ : Operator X bot)
    (d_in : X → X → ENNReal) (U : Set X) (y : X) :
    full_output_annihilation_radius d φ d_in U y =
      local_constant_radius φ d_in U y := by
  unfold full_output_annihilation_radius local_constant_radius
  rw [full_fiber_eq_point_preimage d hd_self hsep]

/--
OET anchor: h-77a0d1aa13ceb857
**推论（分离规范下的链级零距传播）**
同一函数递推中的两个状态一旦全分量零距，随后各步点值相同。
-/
theorem chain_zero_distance_propagates
    (hsep : IsSeparating d) (k m : ℕ) (hmk : m ≤ k)
    (φ : ℕ → Operator X bot) (x x' : ℕ → X)
    (hx : ∀ r, r < k → x (r + 1) = (φ r).func (x r))
    (hx' : ∀ r, r < k → x' (r + 1) = (φ r).func (x' r))
    (hzero : ∀ i, d i (x m) (x' m) = 0) :
    ∀ r, m ≤ r → r ≤ k → x r = x' r := by
  have _ := hmk
  have hm : x m = x' m := hsep (x m) (x' m) hzero
  intro r hmr hrk
  induction r, hmr using Nat.le_induction with
  | base => exact hm
  | @succ r hmr ihr =>
      have hrlt : r < k := Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hrk
      rw [hx r hrlt, hx' r hrlt, ihr (Nat.le_of_succ_le hrk)]

end

end formal_oet.vol_01.appendix_separating_gauge_specialization
