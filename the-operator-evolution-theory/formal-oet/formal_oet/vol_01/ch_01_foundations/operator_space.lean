import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import formal_oet.vol_01.ch_01_foundations.gauge_space

namespace formal_oet.vol_01.ch_01_foundations

set_option linter.style.longLine false
set_option linter.style.emptyLine false

/--
OET anchor: h-57a1dc05727a3772
**定义（算子空间）**：指定吸收元 `bot`。
`Ω` 上的算子为满足 `ϕ(bot) = bot` 的函数。
-/
@[ext]
structure Operator (X : Type) (bot : X) where
  func : X → X
  preserves_bot : func bot = bot

/-- 指定 Ω 的吸收元 ⊥_Ω 为全未定义算子 -/
def bot_operator {X : Type} {bot : X} : Operator X bot :=
  ⟨fun _ => bot, rfl⟩

/-- 恒等函数保持吸收元，因而给出恒等算子。 -/
def operator_identity {X : Type} {bot : X} : Operator X bot := ⟨id, rfl⟩

/-- 算子复合保持吸收元；左侧算子在右侧算子之后作用。 -/
def operator_compose {X : Type} {bot : X} (ϕ ψ : Operator X bot) : Operator X bot :=
  ⟨ϕ.func ∘ ψ.func, by simp [ψ.preserves_bot, ϕ.preserves_bot]⟩

/--
OET anchor: h-57a1dc05727a3772
算子在函数复合下构成幺半群，单位元为恒等算子。
-/
instance operator_monoid {X : Type} {bot : X} : Monoid (Operator X bot) where
  one := operator_identity
  mul := operator_compose
  mul_assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- 全未定义算子在复合的左侧吸收任意算子。 -/
@[simp] theorem bot_operator_mul {X : Type} {bot : X} (ϕ : Operator X bot) :
    bot_operator * ϕ = bot_operator := rfl

/-- 全未定义算子在复合的右侧吸收任意算子。 -/
@[simp] theorem mul_bot_operator {X : Type} {bot : X} (ϕ : Operator X bot) :
    ϕ * bot_operator = bot_operator := by
  ext x
  exact ϕ.preserves_bot

/-- 算子的定义域：不映射到吸收元 `bot` 的集合 -/
def dom {X : Type} {bot : X} (ϕ : Operator X bot) : Set X :=
  { x | ϕ.func x ≠ bot }

/-- 吸收元不属于算子的定义域。 -/
@[simp] theorem bot_not_mem_dom {X : Type} {bot : X} (ϕ : Operator X bot) :
    bot ∉ dom ϕ := by
  simp [dom, ϕ.preserves_bot]

/--
**像集（Image Set）**
定义算子 `ϕ` 在子集 `U ⊆ dom(ϕ)` 上的像集为 `Im(ϕ)|_U`。
当 `U = dom(ϕ)` 时简记为 `Im(ϕ)`。
-/
def operator_image {X : Type} {bot : X} (ϕ : Operator X bot) (U : Set X) : Set X :=
  ϕ.func '' U

/-- 算子在自身定义域上的像集不含吸收元。 -/
@[simp] theorem bot_not_mem_operator_image_dom {X : Type} {bot : X} (ϕ : Operator X bot) :
    bot ∉ operator_image ϕ (dom ϕ) := by
  rintro ⟨x, hx, hbot⟩
  exact hx hbot

/-- 诱导算子度量 (取上确界 ⨆) -/
noncomputable def op_dist {X : Type} {bot : X} (d : X → X → ENNReal) (ϕ ψ : Operator X bot) : ENNReal :=
  ⨆ x : X, d (ϕ.func x) (ψ.func x)

/--
OET anchor: h-91e0e3c458eb7786
**命题 #h-91e0e3c458eb7786（算子规范空间）**
若底层空间存在非吸收点，则算子空间存在非吸收算子。
-/
theorem operator_space_nonabsorbing {X : Type} {bot : X}
    (hX : ∃ x : X, x ≠ bot) :
    ∃ ϕ : Operator X bot, ϕ ≠ bot_operator := by
  rcases hX with ⟨x, hx⟩
  refine ⟨⟨id, rfl⟩, ?_⟩
  intro h_eq
  have h_eval := congrArg (fun ϕ : Operator X bot => ϕ.func x) h_eq
  exact hx h_eval

/--
OET anchor: h-91e0e3c458eb7786
**命题 #h-91e0e3c458eb7786（算子规范空间）**
$d_{\mathrm{op},i}$ 是 $\mathcal{X}_{\mathrm{op}}$ 上的扩展伪度量。
-/
theorem op_dist_is_pseudo_metric {X : Type} {bot : X} (d : X → X → ENNReal)
    (dist_self : ∀ x : X, d x x = 0)
    (symm : ∀ x y : X, d x y = d y x)
    (triangle : ∀ x y z : X, d x z ≤ d x y + d y z)
    (dist_bot : ∀ x ≠ bot, d x bot = ⊤) :
    (∀ ϕ : Operator X bot, op_dist d ϕ ϕ = 0) ∧
    (∀ ϕ ψ : Operator X bot, op_dist d ϕ ψ = op_dist d ψ ϕ) ∧
    (∀ ϕ ψ χ : Operator X bot, op_dist d ϕ χ ≤ op_dist d ϕ ψ + op_dist d ψ χ) ∧
    (∀ ϕ : Operator X bot, ϕ ≠ bot_operator → op_dist d ϕ bot_operator = ⊤) := by
  constructor
  · -- 扩展规范空间公理 (i)
    intro ϕ
    dsimp [op_dist]
    have h : (fun x => d (ϕ.func x) (ϕ.func x)) = fun x => 0 := by
      ext x
      exact dist_self (ϕ.func x)
    rw [h]
    haveI : Nonempty X := ⟨bot⟩
    exact iSup_const
  constructor
  · -- 扩展规范空间公理 (ii)
    intro ϕ ψ
    dsimp [op_dist]
    have h : (fun x => d (ϕ.func x) (ψ.func x)) = (fun x => d (ψ.func x) (ϕ.func x)) := by
      ext x
      exact symm (ϕ.func x) (ψ.func x)
    rw [h]
  constructor
  · -- 扩展规范空间公理 (iii)
    intro ϕ ψ χ
    dsimp [op_dist]
    -- ⨆ x, d (ϕ x) (χ x) ≤ (⨆ x, d (ϕ x) (ψ x)) + (⨆ x, d (ψ x) (χ x))
    apply iSup_le
    intro x
    have h_tri := triangle (ϕ.func x) (ψ.func x) (χ.func x)
    -- ENNReal sum of sups is ≥ sup of sums
    have h1 : d (ϕ.func x) (ψ.func x) ≤ ⨆ y, d (ϕ.func y) (ψ.func y) := le_iSup (fun y => d (ϕ.func y) (ψ.func y)) x
    have h2 : d (ψ.func x) (χ.func x) ≤ ⨆ y, d (ψ.func y) (χ.func y) := le_iSup (fun y => d (ψ.func y) (χ.func y)) x
    exact le_trans h_tri (add_le_add h1 h2)
  · -- 扩展规范空间公理 (iv)
    intro ϕ h_ne
    have h_exists : ∃ x, ϕ.func x ≠ bot := by
      by_contra h
      push Not at h
      apply h_ne
      ext x
      exact h x
    rcases h_exists with ⟨x0, hx0⟩
    have h_top : d (ϕ.func x0) bot = ⊤ := dist_bot (ϕ.func x0) hx0
    apply le_antisymm le_top
    have h_le : d (ϕ.func x0) ((@bot_operator X bot).func x0) ≤ op_dist d ϕ (@bot_operator X bot) := by
      exact le_iSup (fun x => d (ϕ.func x) ((@bot_operator X bot).func x)) x0
    dsimp [bot_operator] at h_le
    rw [h_top] at h_le
    exact h_le

set_option linter.unusedFintypeInType false in
/--
OET anchor: h-91e0e3c458eb7786
**命题（算子规范空间，正文同形封装）**
保留正文中有限非空指标族的完整语境，并将诱导算子伪度量封装为
`ExtendedPseudoMetric` 实例所要求的全部性质。
-/
theorem operator_gauge_space_textbook
    {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    ∀ i : I, ExtendedPseudoMetric (Operator X bot) bot_operator (op_dist (d i)) := by
  intro i
  rcases op_dist_is_pseudo_metric (d i)
      (hd i).dist_self (hd i).symm (hd i).triangle (hd i).isolate_bot with
    ⟨hself, hsymm, htriangle, hisolate⟩
  exact
    { nonabsorbing := operator_space_nonabsorbing (hd i).nonabsorbing
      dist_self := hself
      symm := hsymm
      triangle := htriangle
      isolate_bot := hisolate }

/--
OET anchor: h-038952f7c6c1d6e5
**注（定义域隔离）**
$\mathrm{dom}(\phi) \neq \mathrm{dom}(\psi) \Rightarrow d_{\mathrm{op},i}(\phi, \psi) = +\infty$。
-/
theorem op_dist_eq_top_of_dom_ne {X : Type} {bot : X} (d : X → X → ENNReal) (ϕ ψ : Operator X bot)
    (dist_bot : ∀ x : X, x ≠ bot → d x bot = ⊤)
    (symm : ∀ x y : X, d x y = d y x)
    (h_dom : dom ϕ ≠ dom ψ) :
    op_dist d ϕ ψ = ⊤ := by
  have h_exists : ∃ x, (ϕ.func x ≠ bot ∧ ψ.func x = bot) ∨ (ϕ.func x = bot ∧ ψ.func x ≠ bot) := by
    by_contra h
    push Not at h
    apply h_dom
    ext x
    have hx := h x
    tauto

  rcases h_exists with ⟨x0, h1 | h2⟩
  · have h_phi_ne : ϕ.func x0 ≠ bot := h1.1
    have h_psi_eq : ψ.func x0 = bot := h1.2
    have h_d_top : d (ϕ.func x0) (ψ.func x0) = ⊤ := by
      rw [h_psi_eq]
      exact dist_bot (ϕ.func x0) h_phi_ne
    apply le_antisymm le_top
    rw [← h_d_top]
    exact le_iSup (fun x => d (ϕ.func x) (ψ.func x)) x0
  · have h_phi_eq : ϕ.func x0 = bot := h2.1
    have h_psi_ne : ψ.func x0 ≠ bot := h2.2
    have h_d_top : d (ϕ.func x0) (ψ.func x0) = ⊤ := by
      rw [h_phi_eq]
      rw [symm bot (ψ.func x0)]
      exact dist_bot (ψ.func x0) h_psi_ne
    apply le_antisymm le_top
    rw [← h_d_top]
    exact le_iSup (fun x => d (ϕ.func x) (ψ.func x)) x0

open scoped Classical in
/--
算子规范族分离当且仅当点空间规范族分离。
这是分离规范特化命题的通用代数核心。
-/
theorem op_dist_separating_iff {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (dist_self : ∀ i x, d i x x = 0) :
    IsSeparating d ↔ IsSeparating (fun i (ϕ ψ : Operator X bot) => op_dist (d i) ϕ ψ) := by
  constructor
  · intro h_sep ϕ ψ h_eq
    have h_func_eq : ϕ.func = ψ.func := by
      ext x
      apply h_sep
      intro i
      have h_sup : op_dist (d i) ϕ ψ = 0 := h_eq i
      have h_le := le_iSup (fun x => d i (ϕ.func x) (ψ.func x)) x
      rw [← op_dist, h_sup] at h_le
      exact le_antisymm h_le (zero_le _)
    cases ϕ
    cases ψ
    congr
  · intro h_op_sep a b h_eq
    let phi_a : Operator X bot := ⟨fun x => if x = bot then bot else a, if_pos rfl⟩
    let phi_b : Operator X bot := ⟨fun x => if x = bot then bot else b, if_pos rfl⟩
    have h_phi_eq : phi_a = phi_b := by
      apply h_op_sep
      intro i
      dsimp [op_dist]
      apply le_antisymm _ (zero_le _)
      apply iSup_le
      intro x
      by_cases hx : x = bot
      · dsimp [phi_a, phi_b]
        rw [if_pos hx, if_pos hx]
        rw [dist_self i bot]
      · dsimp [phi_a, phi_b]
        rw [if_neg hx, if_neg hx]
        have hd : d i a b = 0 := h_eq i
        rw [hd]
    have h_eval : phi_a.func b = phi_b.func b := by rw [h_phi_eq]
    by_cases hb : b = bot
    · by_cases ha : a = bot
      · rw [ha, hb]
      · have h_eval_a : phi_a.func a = phi_b.func a := by rw [h_phi_eq]
        dsimp [phi_a, phi_b] at h_eval_a
        rw [if_neg ha, if_neg ha] at h_eval_a
        exact h_eval_a
    · dsimp [phi_a, phi_b] at h_eval
      rw [if_neg hb, if_neg hb] at h_eval
      exact h_eval

/--
**定义（受限评估）**
$$d_{\mathrm{op},i}(\phi, \psi)\big|_U := \sup_{x \in U} d_i(\phi(x), \psi(x))$$
-/
noncomputable def restricted_eval {X : Type} {bot : X} (d : X → X → ENNReal) (ϕ ψ : Operator X bot) (U : Set X) : ENNReal :=
  ⨆ x ∈ U, d (ϕ.func x) (ψ.func x)

/--
OET anchor: h-1c441b84eff949c6
**注（受限评估的伪度量性质与局限）**
固定同一个 `U` 时，受限评估满足前三条伪度量公理，并被全域算子距离控制；
空限制域上它不保吸收元隔离。
-/
theorem restricted_eval_basic_properties {X : Type} {bot : X} (d : X → X → ENNReal)
    (dist_self : ∀ x : X, d x x = 0)
    (symm : ∀ x y : X, d x y = d y x)
    (triangle : ∀ x y z : X, d x z ≤ d x y + d y z) :
    (∀ ϕ : Operator X bot, ∀ U : Set X, restricted_eval d ϕ ϕ U = 0) ∧
    (∀ ϕ ψ : Operator X bot, ∀ U : Set X, restricted_eval d ϕ ψ U = restricted_eval d ψ ϕ U) ∧
    (∀ ϕ ψ χ : Operator X bot, ∀ U : Set X,
      restricted_eval d ϕ χ U ≤ restricted_eval d ϕ ψ U + restricted_eval d ψ χ U) ∧
    (∀ ϕ ψ : Operator X bot, ∀ U : Set X, restricted_eval d ϕ ψ U ≤ op_dist d ϕ ψ) ∧
    (∀ ϕ : Operator X bot, restricted_eval d ϕ bot_operator ∅ = 0) := by
  constructor
  · intro ϕ U
    dsimp [restricted_eval]
    apply le_antisymm
    · apply iSup_le
      intro x
      apply iSup_le
      intro _
      rw [dist_self]
    · exact zero_le _
  constructor
  · intro ϕ ψ U
    dsimp [restricted_eval]
    congr with x
    congr with _
    exact symm (ϕ.func x) (ψ.func x)
  constructor
  · intro ϕ ψ χ U
    dsimp [restricted_eval]
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    have h_tri := triangle (ϕ.func x) (ψ.func x) (χ.func x)
    have h1 : d (ϕ.func x) (ψ.func x) ≤ ⨆ y, ⨆ _ : y ∈ U, d (ϕ.func y) (ψ.func y) := by
      apply le_iSup_of_le x
      exact le_iSup_of_le hx le_rfl
    have h2 : d (ψ.func x) (χ.func x) ≤ ⨆ y, ⨆ _ : y ∈ U, d (ψ.func y) (χ.func y) := by
      apply le_iSup_of_le x
      exact le_iSup_of_le hx le_rfl
    exact le_trans h_tri (add_le_add h1 h2)
  constructor
  · intro ϕ ψ U
    dsimp [restricted_eval, op_dist]
    apply iSup_le
    intro x
    apply iSup_le
    intro _
    exact le_iSup (fun y => d (ϕ.func y) (ψ.func y)) x
  · intro ϕ
    dsimp [restricted_eval]
    apply le_antisymm
    · apply iSup_le
      intro x
      apply iSup_le
      intro hx
      exact False.elim hx
    · exact zero_le _

/--
Internal helper for finite composition of operators.
The textbook definition is anchored in the operator-chain calculus chapter.
-/
def OperatorChain {X : Type} {bot : X} (ϕs : List (Operator X bot)) : Operator X bot :=
  match ϕs with
  | [] => ⟨id, rfl⟩
  | ϕ :: tail => ⟨ϕ.func ∘ (OperatorChain tail).func, by
      -- (ϕ ∘ chain) bot = ϕ (chain bot) = ϕ bot = bot
      have h_tail : (OperatorChain tail).func bot = bot := (OperatorChain tail).preserves_bot
      simp [h_tail, ϕ.preserves_bot]⟩

/-- 既有有限复合实现等于算子幺半群中按同一顺序取的乘积。 -/
theorem operator_chain_eq_prod {X : Type} {bot : X} (ϕs : List (Operator X bot)) :
    OperatorChain ϕs = ϕs.prod := by
  induction ϕs with
  | nil => rfl
  | cons ϕ tail ih =>
      change operator_compose ϕ (OperatorChain tail) = ϕ * tail.prod
      rw [ih]
      rfl

end formal_oet.vol_01.ch_01_foundations
