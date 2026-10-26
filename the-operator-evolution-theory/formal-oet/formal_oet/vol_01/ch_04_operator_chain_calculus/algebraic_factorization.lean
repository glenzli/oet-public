import formal_oet.vol_01.ch_04_operator_chain_calculus.decomposition_core

namespace formal_oet.vol_01.ch_04_operator_chain_calculus.algebraic_factorization

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus

variable {X : Type} {bot : X}

/-- 交换两个非吸收点的算子。 -/
noncomputable def swap_operator (a b : X) (ha : a ≠ bot) (hb : b ≠ bot) : Operator X bot := by
  classical
  exact
    ⟨fun x => if x = a then b else if x = b then a else x, by
      simp [Ne.symm ha, Ne.symm hb]⟩

theorem swap_operator_involutive (a b : X) (ha : a ≠ bot) (hb : b ≠ bot)
    (hab : a ≠ b) :
    ∀ x : X, (swap_operator a b ha hb).func ((swap_operator a b ha hb).func x) = x := by
  classical
  intro x
  by_cases hxa : x = a
  · subst x
    simp [swap_operator, Ne.symm hab]
  · by_cases hxb : x = b
    · subst x
      simp [swap_operator, Ne.symm hab]
    · simp [swap_operator, hxa, hxb]

theorem swap_operator_ne_id (a b : X) (ha : a ≠ bot) (hb : b ≠ bot)
    (hab : a ≠ b) :
    swap_operator a b ha hb ≠ id_operator := by
  classical
  intro h
  have hfun := congrArg Operator.func h
  have ha_eval := congrFun hfun a
  have hba : b = a := by
    simpa [swap_operator, id_operator] using ha_eval
  exact hab hba.symm

/-- 若 `τ` 为自反置换，则 `ϕ ∘ τ` 是与右因子 `τ` 配对的左因子。 -/
noncomputable def compose_after_involution (ϕ τ : Operator X bot) : Operator X bot :=
  ⟨ϕ.func ∘ τ.func, by
    change ϕ.func (τ.func bot) = bot
    rw [τ.preserves_bot, ϕ.preserves_bot]⟩

theorem compose_after_involution_comp
    (ϕ τ : Operator X bot)
    (hinv : ∀ x : X, τ.func (τ.func x) = x) :
    OperatorChain [compose_after_involution ϕ τ, τ] = ϕ := by
  ext x
  dsimp [OperatorChain, compose_after_involution]
  rw [hinv x]

theorem compose_after_involution_ne_id
    (ϕ τ : Operator X bot)
    (hinv : ∀ x : X, τ.func (τ.func x) = x)
    (hτ_ne_ϕ : τ ≠ ϕ) :
    compose_after_involution ϕ τ ≠ id_operator := by
  intro h
  apply hτ_ne_ϕ
  ext x
  have hfun := congrArg Operator.func h
  have hx := congrFun hfun (τ.func x)
  dsimp [compose_after_involution, id_operator] at hx
  rw [hinv x] at hx
  exact hx.symm

/--
OET anchor: h-a09c6a96d9cd476a
**命题 #h-a09c6a96d9cd476a（算子的普遍可分解性）**
`|X| ≥ 4` 的 Lean 形式：除 `bot` 外存在三个互异点。
-/
structure UniversalDecomposabilitySpec (X : Type) (bot : X) where
  four_points :
    ∃ a b c : X,
      a ≠ bot ∧ b ≠ bot ∧ c ≠ bot ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c

/--
OET anchor: h-a09c6a96d9cd476a
**命题 #h-a09c6a96d9cd476a（算子的普遍可分解性）**
若除吸收元外存在三个互异点，则任意算子都有非平凡因式分解。
-/
theorem universal_decomposability
    (h : UniversalDecomposabilitySpec X bot) :
    ∀ ϕ : Operator X bot, AlgebraicFactorization ϕ := by
  classical
  rcases h.four_points with ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩
  intro ϕ
  let τab : Operator X bot := swap_operator a b ha hb
  let τac : Operator X bot := swap_operator a c ha hc
  have hτab_inv : ∀ x : X, τab.func (τab.func x) = x := by
    simpa [τab] using swap_operator_involutive a b ha hb hab
  have hτac_inv : ∀ x : X, τac.func (τac.func x) = x := by
    simpa [τac] using swap_operator_involutive a c ha hc hac
  have hτab_ne_id : τab ≠ id_operator := by
    simpa [τab] using swap_operator_ne_id a b ha hb hab
  have hτac_ne_id : τac ≠ id_operator := by
    simpa [τac] using swap_operator_ne_id a c ha hc hac
  have hτac_ne_τab : τac ≠ τab := by
    intro h_eq
    have hfun := congrArg Operator.func h_eq
    have hb_eval := congrFun hfun b
    have hba : b = a := by
      simp [τac, τab, swap_operator, Ne.symm hab, hbc] at hb_eval
    exact hab hba.symm
  by_cases hϕτab : ϕ = τab
  · have hτac_ne_ϕ : τac ≠ ϕ := by
      intro h_eq
      exact hτac_ne_τab (h_eq.trans hϕτab)
    exact algebraic_factorization_of_witness ϕ τac (compose_after_involution ϕ τac)
      hτac_ne_id
      (compose_after_involution_ne_id ϕ τac hτac_inv hτac_ne_ϕ)
      (compose_after_involution_comp ϕ τac hτac_inv)
  · have hτab_ne_ϕ : τab ≠ ϕ := by
      intro h_eq
      exact hϕτab h_eq.symm
    exact algebraic_factorization_of_witness ϕ τab (compose_after_involution ϕ τab)
      hτab_ne_id
      (compose_after_involution_ne_id ϕ τab hτab_inv hτab_ne_ϕ)
      (compose_after_involution_comp ϕ τab hτab_inv)

/--
OET anchor: h-a2b0697cd3c2decb
**注 #h-a2b0697cd3c2decb（小基数不可约边界）**
三点空间 `{bot, a, b}` 上的对换算子。
-/
noncomputable def fin3_swap_operator : Operator (Fin 3) 0 :=
  swap_operator (X := Fin 3) (bot := 0) 1 2 (by decide) (by decide)

/--
OET anchor: h-a2b0697cd3c2decb
**注 #h-a2b0697cd3c2decb（小基数不可约边界）**
三点空间上交换两个非吸收点的算子不可因式分解。
-/
theorem fin3_swap_operator_irreducible :
    ¬ AlgebraicFactorization fin3_swap_operator := by
  classical
  rintro ⟨ϕ₁, ϕ₂, hϕ₁_ne, hϕ₂_ne, hcomp⟩
  have hfun := congrArg Operator.func hcomp
  have hc1 := congrFun hfun (1 : Fin 3)
  have hc2 := congrFun hfun (2 : Fin 3)
  rcases hϕ₁_one : ϕ₁.func (1 : Fin 3) with ⟨n₁, hn₁⟩
  interval_cases n₁ <;>
    rcases hϕ₁_two : ϕ₁.func (2 : Fin 3) with ⟨n₂, hn₂⟩ <;>
      interval_cases n₂ <;>
        simp only [Fin.isValue, OperatorChain, CompTriple.comp_eq, Function.comp_apply,
          hϕ₁_one, hϕ₁_two, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
          ϕ₂.preserves_bot, fin3_swap_operator, swap_operator, ↓reduceIte,
          Fin.reduceEq, zero_ne_one] at hc1 hc2
  · exact (by decide : (2 : Fin 3) ≠ 1) (hc1.symm.trans hc2)
  · exact hϕ₁_ne (by
      ext x
      fin_cases x
      · simpa [id_operator] using congrArg Fin.val ϕ₁.preserves_bot
      · simpa [id_operator] using congrArg Fin.val hϕ₁_one
      · simpa [id_operator] using congrArg Fin.val hϕ₁_two)
  · exact hϕ₂_ne (by
      ext x
      fin_cases x
      · simpa [id_operator] using congrArg Fin.val ϕ₂.preserves_bot
      · simpa [id_operator] using congrArg Fin.val hc2
      · simpa [id_operator] using congrArg Fin.val hc1)
  · exact (by decide : (2 : Fin 3) ≠ 1) (hc1.symm.trans hc2)

end formal_oet.vol_01.ch_04_operator_chain_calculus.algebraic_factorization
