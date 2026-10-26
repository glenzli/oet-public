import formal_oet.vol_01.ch_02_operator_bounds.matrix_composition
import formal_oet.vol_01.ch_02_operator_bounds.path_algebra
import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix

namespace formal_oet.vol_01.ch_04_operator_chain_calculus

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open Set


open scoped BigOperators

variable {X I : Type} {bot : X}

/--
OET anchor: h-92938f295a2b0333
**定义（恒等算子）**
-/
def id_operator : Operator X bot := ⟨id, rfl⟩

/--
OET anchor: h-92938f295a2b0333
**定义（代数因式分解）**
排除两个平凡恒等因子。
-/
def AlgebraicFactorization (ϕ : Operator X bot) : Prop :=
  ∃ ϕ₁ ϕ₂ : Operator X bot,
    ϕ₁ ≠ id_operator ∧ ϕ₂ ≠ id_operator ∧ OperatorChain [ϕ₂, ϕ₁] = ϕ

/-- 给定非平凡因子即给出代数因式分解。 -/
theorem algebraic_factorization_of_witness (ϕ ϕ₁ ϕ₂ : Operator X bot)
    (h₁ : ϕ₁ ≠ id_operator) (h₂ : ϕ₂ ≠ id_operator)
    (hcomp : OperatorChain [ϕ₂, ϕ₁] = ϕ) :
    AlgebraicFactorization ϕ := by
  exact ⟨ϕ₁, ϕ₂, h₁, h₂, hcomp⟩

/--
域限制算子：在 `U` 内等于原算子，在 `U` 外映到 `bot`。
-/
noncomputable def restrict_operator (ϕ : Operator X bot) (U : Set X) : Operator X bot := by
  classical
  exact
    ⟨fun x => if x ∈ U then ϕ.func x else bot, by
      by_cases hbot : bot ∈ U
      · simp [hbot, ϕ.preserves_bot]
      · simp [hbot]⟩

theorem restrict_operator_apply_of_mem (ϕ : Operator X bot) (U : Set X)
    {x : X} (hx : x ∈ U) :
    (restrict_operator ϕ U).func x = ϕ.func x := by
  classical
  simp [restrict_operator, hx]

theorem restrict_operator_apply_of_not_mem (ϕ : Operator X bot) (U : Set X)
    {x : X} (hx : x ∉ U) :
    (restrict_operator ϕ U).func x = bot := by
  classical
  simp [restrict_operator, hx]

/-- 若 `U ⊆ dom ϕ`，则限制算子的定义域正好是 `U`。 -/
theorem dom_restrict_operator_eq (ϕ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕ) :
    dom (restrict_operator ϕ U) = U := by
  classical
  ext x
  by_cases hx : x ∈ U
  · constructor
    · intro _; exact hx
    · intro _hx
      dsimp [dom]
      rw [restrict_operator_apply_of_mem ϕ U hx]
      exact hU hx
  · constructor
    · intro hdom
      dsimp [dom] at hdom
      rw [restrict_operator_apply_of_not_mem ϕ U hx] at hdom
      exact False.elim (hdom rfl)
    · intro h
      exact False.elim (hx h)

/--
OET anchor: h-a63623c9504af642
**命题 #h-a63623c9504af642（域限制与复合的相容性）**
域限制与二步复合在给定像域限制下相容。
-/
theorem restrict_comp_eq (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) :
    restrict_operator (OperatorChain [ϕ₂, ϕ₁]) U =
      OperatorChain [restrict_operator ϕ₂ (ϕ₁.func '' U), restrict_operator ϕ₁ U] := by
  classical
  ext x
  by_cases hx : x ∈ U
  · rw [restrict_operator_apply_of_mem (OperatorChain [ϕ₂, ϕ₁]) U hx]
    dsimp [OperatorChain]
    rw [restrict_operator_apply_of_mem ϕ₁ U hx]
    have him : ϕ₁.func x ∈ ϕ₁.func '' U := Set.mem_image_of_mem ϕ₁.func hx
    rw [restrict_operator_apply_of_mem ϕ₂ (ϕ₁.func '' U) him]
  · rw [restrict_operator_apply_of_not_mem (OperatorChain [ϕ₂, ϕ₁]) U hx]
    dsimp [OperatorChain]
    rw [restrict_operator_apply_of_not_mem ϕ₁ U hx]
    by_cases hbot : bot ∈ ϕ₁.func '' U
    · rw [restrict_operator_apply_of_mem ϕ₂ (ϕ₁.func '' U) hbot, ϕ₂.preserves_bot]
    · rw [restrict_operator_apply_of_not_mem ϕ₂ (ϕ₁.func '' U) hbot]

/-- 局部等价：两个算子在 `U` 上逐点相等。 -/
def LocalEquivalent (ϕ ψ : Operator X bot) (U : Set X) : Prop :=
  ∀ x ∈ U, ϕ.func x = ψ.func x

/-- 局部等价等价于域限制算子相等。 -/
theorem local_equivalent_iff_restrict_eq (ϕ ψ : Operator X bot) (U : Set X) :
    LocalEquivalent ϕ ψ U ↔ restrict_operator ϕ U = restrict_operator ψ U := by
  classical
  constructor
  · intro h
    ext x
    by_cases hx : x ∈ U
    · simp [restrict_operator, hx, h x hx]
    · simp [restrict_operator, hx]
  · intro h x hx
    have happ := congrArg Operator.func h
    have hpoint := congrFun happ x
    simpa [restrict_operator, hx] using hpoint

variable [Fintype I]
local instance instDecidableEqIDecompositionCore : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-3d5f909fa9f5d7da
**命题 #h-3d5f909fa9f5d7da(i)**
Lip 矩阵可从大域限制到小域。
-/
theorem lip_localization (ϕ : Operator X bot) (U V : Set X)
    (L : I → I → ENNReal)
    (hUV : U ⊆ V)
    (hL : IsLipMatrix d ϕ V L) :
    IsLipMatrix d ϕ U L := by
  exact restricted_lip_matrix_family_antitone d ϕ U V hUV hL

/--
OET anchor: h-3d5f909fa9f5d7da
**命题 #h-3d5f909fa9f5d7da(ii)**
co-Lip 矩阵可从大域限制到非空小域。
-/
theorem colip_localization (ϕ : Operator X bot) (U V : Set X)
    (K : I → I → ENNReal)
    (hU_ne : U.Nonempty)
    (hUV : U ⊆ V)
    (hK : IsCoLipMatrix d ϕ V K) :
    IsCoLipMatrix d ϕ U K := by
  exact restricted_colip_matrix_family_antitone d ϕ U V hU_ne hUV hK

/--
OET anchor: h-5846008cae9ea67d
**命题 #h-5846008cae9ea67d（分段合成的全域证书比较界，Lip 分块限制核心）**
分段算子的全域 Lip 矩阵限制到任一分块后，仍是该分块局域算子的 Lip 矩阵。
-/
theorem piecewise_lip_restricts_to_piece (ψ ϕm : Operator X bot) (U Um : Set X)
    (L : I → I → ENNReal)
    (hUmU : Um ⊆ U)
    (h_agree : LocalEquivalent ψ ϕm Um)
    (hL : IsLipMatrix d ψ U L) :
    IsLipMatrix d ϕm Um L := by
  refine ⟨?_, ?_⟩
  · intro x hx
    dsimp [dom]
    rw [← h_agree x hx]
    exact hL.1 (hUmU hx)
  · intro x hx y hy j
    rw [← h_agree x hx, ← h_agree y hy]
    exact hL.2 x (hUmU hx) y (hUmU hy) j

/--
OET anchor: h-5846008cae9ea67d
**命题 #h-5846008cae9ea67d（分段合成的全域证书比较界，co-Lip 分块限制核心）**
分段算子的全域 co-Lip 矩阵限制到任一非空分块后，仍是该分块局域算子的 co-Lip 矩阵。
-/
theorem piecewise_colip_restricts_to_piece (ψ ϕm : Operator X bot) (U Um : Set X)
    (K : I → I → ENNReal)
    (hUm_ne : Um.Nonempty)
    (hUmU : Um ⊆ U)
    (h_agree : LocalEquivalent ψ ϕm Um)
    (hK : IsCoLipMatrix d ψ U K) :
    IsCoLipMatrix d ϕm Um K := by
  refine ⟨hUm_ne, ?_, ?_⟩
  · intro x hx
    dsimp [dom]
    rw [← h_agree x hx]
    exact hK.2.1 (hUmU hx)
  · intro x hx y hy j
    rw [← h_agree x hx, ← h_agree y hy]
    exact hK.2.2 x (hUmU hx) y (hUmU hy) j

/--
OET anchor: h-5bedef30d593a0bc
**引理 #h-5bedef30d593a0bc(i)**
局部等价保持受限 Lip 矩阵族。
-/
theorem local_equiv_lip_matrix_iff (ϕ ψ : Operator X bot) (U : Set X)
    (L : I → I → ENNReal)
    (h_eq : LocalEquivalent ϕ ψ U) :
    IsLipMatrix d ϕ U L ↔ IsLipMatrix d ψ U L := by
  constructor
  · intro hL
    refine ⟨?_, ?_⟩
    · intro x hx
      dsimp [dom]
      rw [← h_eq x hx]
      exact hL.1 hx
    · intro x hx y hy j
      rw [← h_eq x hx, ← h_eq y hy]
      exact hL.2 x hx y hy j
  · intro hL
    refine ⟨?_, ?_⟩
    · intro x hx
      dsimp [dom]
      rw [h_eq x hx]
      exact hL.1 hx
    · intro x hx y hy j
      rw [h_eq x hx, h_eq y hy]
      exact hL.2 x hx y hy j

/--
OET anchor: h-5bedef30d593a0bc
**引理 #h-5bedef30d593a0bc(ii)**
局部等价保持受限 co-Lip 矩阵族。
-/
theorem local_equiv_colip_matrix_iff (ϕ ψ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal)
    (h_eq : LocalEquivalent ϕ ψ U) :
    IsCoLipMatrix d ϕ U K ↔ IsCoLipMatrix d ψ U K := by
  constructor
  · intro hK
    refine ⟨hK.1, ?_, ?_⟩
    · intro x hx
      dsimp [dom]
      rw [← h_eq x hx]
      exact hK.2.1 hx
    · intro x hx y hy j
      rw [← h_eq x hx, ← h_eq y hy]
      exact hK.2.2 x hx y hy j
  · intro hK
    refine ⟨hK.1, ?_, ?_⟩
    · intro x hx
      dsimp [dom]
      rw [h_eq x hx]
      exact hK.2.1 hx
    · intro x hx y hy j
      rw [h_eq x hx, h_eq y hy]
      exact hK.2.2 x hx y hy j

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-5bedef30d593a0bc
**引理 #h-5bedef30d593a0bc(iii) 的纤维核心**
局部等价使同一中心点诱导的计算纤维一致。
-/
theorem local_equiv_computational_fiber_eq (ϕ ψ : Operator X bot) (U : Set X)
    (J : NonemptyFinset I) (y : X)
    (h_eq : LocalEquivalent ϕ ψ U) (hy : y ∈ U) :
    ComputationalFiber d ϕ J U (ϕ.func y) =
      ComputationalFiber d ψ J U (ψ.func y) := by
  ext x
  constructor
  · rintro ⟨hx, hdist⟩
    refine ⟨hx, ?_⟩
    rwa [← h_eq x hx, ← h_eq y hy]
  · rintro ⟨hx, hdist⟩
    refine ⟨hx, ?_⟩
    rwa [h_eq x hx, h_eq y hy]

/-- A point with different outputs witnesses distinct operators. -/
theorem operator_ne_of_exists_point_ne (ϕ ψ : Operator X bot) (x₀ : X)
    (hneq : ϕ.func x₀ ≠ ψ.func x₀) :
    ϕ ≠ ψ := by
  intro h
  exact hneq (by rw [h])

/-- Replace one input value by `a` and leave every other point unchanged. -/
noncomputable def replace_at_operator (a b : X) (hb : b ≠ bot) : Operator X bot := by
  classical
  exact
    ⟨fun x => if x = b then a else x, by
      have hbotb : bot ≠ b := Ne.symm hb
      simp [hbotb]⟩

/--
OET anchor: h-11fd78baa402e538
**命题 #h-11fd78baa402e538（局部等价不蕴含全域等价）**
存在两个不同的非吸收点时，可构造定义域相同的两个算子，
使其在共同定义域的非空子集上局部等价，但并非同一算子。
-/
theorem local_equivalent_not_global_counterexample (a b : X)
    (ha : a ≠ bot) (hb : b ≠ bot) (hab : a ≠ b) :
    ∃ (ϕ ψ : Operator X bot) (U : Set X),
      dom ϕ = dom ψ ∧ U.Nonempty ∧ U ⊆ dom ϕ ∧
        LocalEquivalent ϕ ψ U ∧ ϕ ≠ ψ := by
  classical
  refine ⟨id_operator, replace_at_operator a b hb, {a}, ?_,
    Set.singleton_nonempty a, ?_, ?_, ?_⟩
  · ext x
    by_cases hxb : x = b
    · subst x
      simp [dom, id_operator, replace_at_operator, ha, hb]
    · simp [dom, id_operator, replace_at_operator, hxb]
  · intro x hx
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst x
    simpa [dom, id_operator] using ha
  · intro x hx
    have hxa : x = a := Set.mem_singleton_iff.mp hx
    subst x
    simp [id_operator, replace_at_operator, hab]
  · apply operator_ne_of_exists_point_ne (x₀ := b)
    simpa [id_operator, replace_at_operator] using Ne.symm hab

/--
OET anchor: h-a1caa879309ff2e3
**逐步局部等价的列表表示**
逐步局部等价数据。
列表顺序与 `OperatorChain` 一致：尾部先作用，表头后作用。
-/
inductive StepwiseLocalEquivalent :
    List (Operator X bot) → List (Operator X bot) → Set X → Prop
  | nil (U : Set X) : StepwiseLocalEquivalent [] [] U
  | cons {ϕ ψ : Operator X bot} {ϕs ψs : List (Operator X bot)} {U : Set X}
      (h_tail : StepwiseLocalEquivalent ϕs ψs U)
      (h_head : LocalEquivalent ϕ ψ ((OperatorChain ϕs).func '' U)) :
      StepwiseLocalEquivalent (ϕ :: ϕs) (ψ :: ψs) U

/--
OET anchor: h-95e7f90e21e41cae
**命题 #h-95e7f90e21e41cae(ii)**
逐步局部等价推出复合算子在初始域上局部等价。
-/
theorem stepwise_local_equiv_operator_chain :
    ∀ {ϕs ψs : List (Operator X bot)} {U : Set X},
      StepwiseLocalEquivalent ϕs ψs U →
        LocalEquivalent (OperatorChain ϕs) (OperatorChain ψs) U
  | [], [], U, StepwiseLocalEquivalent.nil _ => by
      intro x hx
      rfl
  | ϕ :: ϕs, ψ :: ψs, U, StepwiseLocalEquivalent.cons h_tail h_head => by
      intro x hx
      have h_tail_eq := stepwise_local_equiv_operator_chain h_tail x hx
      have h_head_eq :=
        h_head ((OperatorChain ϕs).func x) (Set.mem_image_of_mem _ hx)
      dsimp [OperatorChain]
      rw [← h_tail_eq]
      exact h_head_eq

/-- Internal predicate for an operator synthesized on a restricted domain. -/
def DomainSynthesis (ψ ϕ : Operator X bot) (U : Set X) : Prop :=
  LocalEquivalent ψ ϕ U ∧ dom ψ = U ∧ U ⊆ dom ϕ

/-- Equality criterion for the internal domain-synthesis predicate. -/
theorem domain_synthesis_eq_iff (ψ ϕ : Operator X bot) (U : Set X)
    (h_syn : DomainSynthesis ψ ϕ U) :
    ψ = ϕ ↔ U = dom ϕ := by
  constructor
  · intro h
    rw [← h_syn.2.1, h]
  · intro hU
    ext x
    by_cases hx : x ∈ U
    · exact h_syn.1 x hx
    · have hψ_not_dom : x ∉ dom ψ := by
        rw [h_syn.2.1]
        exact hx
      have hϕ_not_dom : x ∉ dom ϕ := by
        rw [← hU]
        exact hx
      have hψ_bot : ψ.func x = bot := by
        by_contra hne
        exact hψ_not_dom hne
      have hϕ_bot : ϕ.func x = bot := by
        by_contra hne
        exact hϕ_not_dom hne
      rw [hψ_bot, hϕ_bot]

end

end formal_oet.vol_01.ch_04_operator_chain_calculus
