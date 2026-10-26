import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X}
variable (d : I → X → X → ENNReal)

/-- OET anchor: h-273361882c9d8ace
常值分量：受限域上的输出两两零距。
-/
def ConstComponent (ϕ : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = 0}

/-- OET anchor: h-273361882c9d8ace
恒等分量：排除常值分量后，输出与输入逐点零距。
-/
def IdComponent (ϕ : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ ConstComponent d ϕ U ∧ ∀ x ∈ U, d i (ϕ.func x) x = 0}

/-- OET anchor: h-273361882c9d8ace
有效分量：既非常值分量，也非恒等分量。
-/
def ActComponent (ϕ : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ IdComponent d ϕ U ∧ i ∉ ConstComponent d ϕ U}

/-- 分划的有效部分同时排除逐点零距与输出两两零距。 -/
theorem act_component_iff (ϕ : Operator X bot) (U : Set X) (i : I) :
    i ∈ ActComponent d ϕ U ↔
      ¬ (∀ x ∈ U, d i (ϕ.func x) x = 0) ∧ i ∉ ConstComponent d ϕ U := by
  constructor
  · intro h
    exact ⟨fun hp => h.1 ⟨h.2, hp⟩, h.2⟩
  · intro h
    exact ⟨fun hid => h.1 hid.2, h.2⟩

/-- 逐点零距蕴含点对距离保持。 -/
theorem component_distance_of_pointwise_zero (ϕ : Operator X bot) (U : Set X) (i : I)
    (h_id : ∀ x ∈ U, d i (ϕ.func x) x = 0)
    (symm : ∀ x y, d i x y = d i y x)
    (triangle : ∀ x y z, d i x z ≤ d i x y + d i y z) :
    ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = d i x y := by
  intro x hx y hy
  have hx_zero : d i (ϕ.func x) x = 0 := h_id x hx
  have hy_zero : d i (ϕ.func y) y = 0 := h_id y hy
  have hx_zero_symm : d i x (ϕ.func x) = 0 := by
    rw [symm, hx_zero]
  have hy_zero_symm : d i y (ϕ.func y) = 0 := by
    rw [symm, hy_zero]
  have h_le₁ : d i (ϕ.func x) (ϕ.func y) ≤ d i x y := by
    have h1 := triangle (ϕ.func x) x (ϕ.func y)
    have h2 := triangle x y (ϕ.func y)
    calc
      d i (ϕ.func x) (ϕ.func y) ≤ d i (ϕ.func x) x + d i x (ϕ.func y) := h1
      _ ≤ d i (ϕ.func x) x + (d i x y + d i y (ϕ.func y)) := by gcongr
      _ = d i x y := by rw [hx_zero, hy_zero_symm, zero_add, add_zero]
  have h_le₂ : d i x y ≤ d i (ϕ.func x) (ϕ.func y) := by
    have h1 := triangle x (ϕ.func x) y
    have h2 := triangle (ϕ.func x) (ϕ.func y) y
    calc
      d i x y ≤ d i x (ϕ.func x) + d i (ϕ.func x) y := h1
      _ ≤ d i x (ϕ.func x) + (d i (ϕ.func x) (ϕ.func y) + d i (ϕ.func y) y) := by gcongr
      _ = d i (ϕ.func x) (ϕ.func y) := by rw [hx_zero_symm, hy_zero, zero_add, add_zero]
  exact le_antisymm h_le₁ h_le₂

/-- OET anchor: h-176471fbe0cf6b8c
恒等分量保持对应的点对距离。
-/
theorem id_component_preserves_component_distance (ϕ : Operator X bot) (U : Set X) (i : I)
    (h_id : i ∈ IdComponent d ϕ U)
    (symm : ∀ x y, d i x y = d i y x)
    (triangle : ∀ x y z, d i x z ≤ d i x y + d i y z) :
    ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = d i x y :=
  component_distance_of_pointwise_zero d ϕ U i h_id.2 symm triangle

/-- 两个逐点零距条件在复合下保持。 -/
theorem pointwise_zero_comp (ϕ ψ : Operator X bot) (U : Set X) (i : I)
    (hϕ : ∀ x ∈ U, d i (ϕ.func x) x = 0)
    (hψ : ∀ x ∈ ϕ.func '' U, d i (ψ.func x) x = 0)
    (triangle : ∀ x y z, d i x z ≤ d i x y + d i y z) :
    ∀ x ∈ U, d i ((OperatorChain [ψ, ϕ]).func x) x = 0 := by
  intro x hx
  apply le_antisymm ?_ (zero_le _)
  change d i (ψ.func (ϕ.func x)) x ≤ 0
  calc
    _ ≤ d i (ψ.func (ϕ.func x)) (ϕ.func x) + d i (ϕ.func x) x := triangle _ _ _
    _ = 0 := by rw [hψ _ (Set.mem_image_of_mem _ hx), hϕ x hx, add_zero]

/-- OET anchor: h-e1615fa20ede09bc
恒等分量在复合下保持；保距性质保证复合仍非常值。
-/
theorem id_comp_preservation_exact (ϕ1 ϕ2 : Operator X bot) (U : Set X)
    (h_U_dom : U ⊆ dom (OperatorChain [ϕ2, ϕ1]))
    (symm : ∀ i x y, d i x y = d i y x)
    (triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z) :
    IdComponent d ϕ1 U ∩ IdComponent d ϕ2 (ϕ1.func '' U) ⊆
    IdComponent d (OperatorChain [ϕ2, ϕ1]) U := by
  have _ := h_U_dom
  intro i hi
  refine ⟨?_, pointwise_zero_comp d ϕ1 ϕ2 U i hi.1.2 hi.2.2 (triangle i)⟩
  intro hc
  apply hi.1.1
  intro x hx y hy
  have heq := component_distance_of_pointwise_zero d ϕ2 (ϕ1.func '' U) i hi.2.2
    (symm i) (triangle i) _ (Set.mem_image_of_mem _ hx) _ (Set.mem_image_of_mem _ hy)
  exact heq.symm.trans (hc x hx y hy)

/-- OET anchor: h-2c5dc85febaac657
外侧常值分量直接传递到复合，无须源端正直径。
-/
theorem const_comp_outer_const_exact (ϕ ψ : Operator X bot) (U : Set X) (i : I)
    (h_const : i ∈ ConstComponent d ψ (ϕ.func '' U)) :
    i ∈ ConstComponent d (OperatorChain [ψ, ϕ]) U := by
  intro x hx y hy
  exact h_const _ (Set.mem_image_of_mem _ hx) _ (Set.mem_image_of_mem _ hy)

/-- 有效分量的两步包含律。 -/
theorem act_comp_inclusion_helper (ϕ1 ϕ2 : Operator X bot) (U : Set X)
    (symm : ∀ i x y, d i x y = d i y x)
    (triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z) :
    ActComponent d (OperatorChain [ϕ2, ϕ1]) U ⊆
    ActComponent d ϕ1 U ∪ ActComponent d ϕ2 (ϕ1.func '' U) := by
  intro i hi
  rw [act_component_iff] at hi
  by_contra hnot
  simp only [Set.mem_union, not_or] at hnot
  have h1 : (∀ x ∈ U, d i (ϕ1.func x) x = 0) ∨ i ∈ ConstComponent d ϕ1 U := by
    by_contra hn
    rw [not_or] at hn
    exact hnot.1 ((act_component_iff d ϕ1 U i).mpr hn)
  have h2 : (∀ x ∈ ϕ1.func '' U, d i (ϕ2.func x) x = 0) ∨
      i ∈ ConstComponent d ϕ2 (ϕ1.func '' U) := by
    by_contra hn
    rw [not_or] at hn
    exact hnot.2 ((act_component_iff d ϕ2 (ϕ1.func '' U) i).mpr hn)
  rcases h2 with hid2 | hc2
  · rcases h1 with hid1 | hc1
    · exact hi.1 (pointwise_zero_comp d ϕ1 ϕ2 U i hid1 hid2 (triangle i))
    · apply hi.2
      intro x hx y hy
      exact (component_distance_of_pointwise_zero d ϕ2 (ϕ1.func '' U) i hid2
        (symm i) (triangle i) _ (Set.mem_image_of_mem _ hx) _
        (Set.mem_image_of_mem _ hy)).trans (hc1 x hx y hy)
  · exact hi.2 (const_comp_outer_const_exact d ϕ1 ϕ2 U i hc2)

/-- OET anchor: h-e1615fa20ede09bc
复合算子的有效分量包含于两步各自有效分量的并。
-/
theorem act_comp_inclusion_exact (ϕ1 ϕ2 : Operator X bot) (U : Set X)
    (h_U_dom : U ⊆ dom (OperatorChain [ϕ2, ϕ1]))
    (symm : ∀ i x y, d i x y = d i y x)
    (triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z) :
    ActComponent d (OperatorChain [ϕ2, ϕ1]) U ⊆
    ActComponent d ϕ1 U ∪ ActComponent d ϕ2 (ϕ1.func '' U) := by
  have _ := h_U_dom
  exact act_comp_inclusion_helper d ϕ1 ϕ2 U symm triangle

/-- 链上各步在实际像域的有效分量之并。 -/
def chain_act_components (d : I → X → X → ENNReal) (U : Set X) : List (Operator X bot) → Set I
  | [] => ∅
  | ϕ :: tail => chain_act_components d U tail ∪ ActComponent d ϕ ((OperatorChain tail).func '' U)

/-- OET anchor: h-e1615fa20ede09bc
有限复合的有效分量包含律，包括零步情形。
-/
theorem act_comp_inclusion_chain (ϕs : List (Operator X bot)) (U : Set X)
    (dist_self : ∀ i x, d i x x = 0)
    (symm : ∀ i x y, d i x y = d i y x)
    (triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z) :
    U ⊆ dom (OperatorChain ϕs) →
    ActComponent d (OperatorChain ϕs) U ⊆ chain_act_components d U ϕs := by
  induction ϕs with
  | nil =>
    intro _ i hi
    exact False.elim (((act_component_iff d _ U i).mp hi).1 (fun x _ => dist_self i x))
  | cons ϕ tail ih =>
    intro hdom i hi
    have htail : U ⊆ dom (OperatorChain tail) := by
      intro x hx hb
      have h := hdom hx
      change ϕ.func ((OperatorChain tail).func x) ≠ bot at h
      exact h (by rw [hb, ϕ.preserves_bot])
    have hcases := act_comp_inclusion_helper d (OperatorChain tail) ϕ U symm triangle hi
    rcases hcases with h | h
    · exact Or.inl (ih htail h)
    · exact Or.inr h

/--
OET anchor: h-8f36f69dab71e689
**注 #h-8f36f69dab71e689（复合分量保持的逆向蕴含一般不成立）**
两点换位算子给出有效分量包含律与恒等分量保持律不可反向的共同反例。
-/
theorem swap_pair_factors_active_but_composite_identity (ϕ1 ϕ2 : Operator X bot) (i : I) (a b : X)
    (hϕ1a : ϕ1.func a = b)
    (hϕ1b : ϕ1.func b = a)
    (hϕ2a : ϕ2.func a = b)
    (hϕ2b : ϕ2.func b = a)
    (h_image : ϕ1.func '' ({a, b} : Set X) = ({a, b} : Set X))
    (h_ba_pos : 0 < d i b a)
    (h_self_a : d i a a = 0)
    (h_self_b : d i b b = 0) :
    i ∈ ActComponent d ϕ1 ({a, b} : Set X) ∧
      i ∈ ActComponent d ϕ2 (ϕ1.func '' ({a, b} : Set X)) ∧
      i ∈ IdComponent d (OperatorChain [ϕ2, ϕ1]) ({a, b} : Set X) ∧
      i ∉ ActComponent d (OperatorChain [ϕ2, ϕ1]) ({a, b} : Set X) := by
  have mem_a : a ∈ ({a, b} : Set X) := Set.mem_insert_iff.mpr (Or.inl rfl)
  have mem_b : b ∈ ({a, b} : Set X) := Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton b))
  have hϕ1_act : i ∈ ActComponent d ϕ1 ({a, b} : Set X) := by
    constructor
    · intro h_id
      have h_zero := h_id.2 a mem_a
      rw [hϕ1a] at h_zero
      exact (ne_of_gt h_ba_pos) h_zero
    · intro h_const
      have h_zero := h_const a mem_a b mem_b
      rw [hϕ1a, hϕ1b] at h_zero
      exact (ne_of_gt h_ba_pos) h_zero
  have hϕ2_act_on_U : i ∈ ActComponent d ϕ2 ({a, b} : Set X) := by
    constructor
    · intro h_id
      have h_zero := h_id.2 a mem_a
      rw [hϕ2a] at h_zero
      exact (ne_of_gt h_ba_pos) h_zero
    · intro h_const
      have h_zero := h_const a mem_a b mem_b
      rw [hϕ2a, hϕ2b] at h_zero
      exact (ne_of_gt h_ba_pos) h_zero
  have hϕ2_act : i ∈ ActComponent d ϕ2 (ϕ1.func '' ({a, b} : Set X)) := by
    rw [h_image]
    exact hϕ2_act_on_U
  have h_comp_id : i ∈ IdComponent d (OperatorChain [ϕ2, ϕ1]) ({a, b} : Set X) := by
    constructor
    · intro hc
      have hz := hc b mem_b a mem_a
      simp [OperatorChain, hϕ1a, hϕ1b, hϕ2a, hϕ2b] at hz
      exact (ne_of_gt h_ba_pos) hz
    · intro z hz
      rcases Set.mem_insert_iff.mp hz with hza | hzb_mem
      · simp [hza, OperatorChain, hϕ1a, hϕ2b, h_self_a]
      · have hzb : z = b := Set.mem_singleton_iff.mp hzb_mem
        simp [hzb, OperatorChain, hϕ1b, hϕ2a, h_self_b]
  have h_not_act : i ∉ ActComponent d (OperatorChain [ϕ2, ϕ1]) ({a, b} : Set X) := by
    intro h_act
    exact h_act.1 h_comp_id
  exact ⟨hϕ1_act, hϕ2_act, h_comp_id, h_not_act⟩

/--
OET anchor: h-176471fbe0cf6b8c
**命题 #h-176471fbe0cf6b8c（分量类型的矩阵约束）- 常值分量的 co-Lip 零条目**
常值输出分量使所有在源域上有正距离的 co-Lip 通道条目为零。
-/
theorem const_component_colip_entry_eq_zero (ϕ : Operator X bot) (U : Set X)
    [Fintype I]
    (K : I → I → ENNReal) (i k : I)
    (h_const : i ∈ ConstComponent d ϕ U)
    (hK : IsCoLipMatrix d ϕ U K)
    (hpos : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) :
    K k i = 0 := by
  rcases hpos with ⟨x, hx, y, hy, hxy_pos⟩
  have hout : d i (ϕ.func x) (ϕ.func y) = 0 := h_const x hx y hy
  exact
    _root_.formal_oet.vol_01.ch_02_operator_bounds.colip_entry_eq_zero_of_output_zero_input_pos
      d ϕ U K k i x y hK hx hy hout hxy_pos

/--
OET anchor: h-176471fbe0cf6b8c
**命题 #h-176471fbe0cf6b8c（分量类型的矩阵约束）- 常值分量的零 Lip 行**
常值输出分量的单行 Lip 上界可取零。
-/
theorem const_component_zero_lip_row_bound (ϕ : Operator X bot) (U : Set X) (i : I)
    [Fintype I]
    (h_const : i ∈ ConstComponent d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  rw [h_const x hx y hy]
  exact zero_le _

end formal_oet.vol_01.ch_03_operator_local_degeneracy
