import formal_oet.vol_01.ch_04_operator_chain_calculus.decomposition_core
import formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_classification


namespace formal_oet.vol_01.ch_04_operator_chain_calculus

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy

variable {X I : Type} {bot : X} [Fintype I]
local instance instDecidableEqIDomainRestriction : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-e84832eedce36d68
**定义（域限制算子）**
域限制算子属于 Ω，且在 `U ⊆ dom ϕ` 时定义域正好为 `U`。
-/
theorem restrict_operator_domain_exact (ϕ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕ) :
    dom (restrict_operator ϕ U) = U := by
  exact dom_restrict_operator_eq ϕ U hU

/--
OET anchor: h-a63623c9504af642
**命题 #h-a63623c9504af642（域限制与复合的相容性）**
完整的 Ω 等式形式。
-/
theorem domain_restriction_comp_eq
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) :
    restrict_operator (OperatorChain [ϕ₂, ϕ₁]) U =
      OperatorChain [restrict_operator ϕ₂ (ϕ₁.func '' U), restrict_operator ϕ₁ U] := by
  exact restrict_comp_eq ϕ₁ ϕ₂ U

omit [Fintype I] in
/-- Domain data used by the reusable localization helper. -/
structure LocalizationTighteningSpec (U D : Set X) where
  subset : U ⊆ D
  nonempty : U.Nonempty

/-- Reusable localization helper on an arbitrary pair of nested domains. -/
theorem localization_tightening
    (ϕ : Operator X bot) (U D : Set X)
    (h : LocalizationTighteningSpec U D) :
    (∀ L : I → I → ENNReal,
      IsLipMatrix d ϕ D L → IsLipMatrix d ϕ U L) ∧
    (∀ K : I → I → ENNReal,
      IsCoLipMatrix d ϕ D K → IsCoLipMatrix d ϕ U K) ∧
    (∀ i j : I,
      min_annihilation_radius d ϕ i (singleton_nonempty_finset j) D ≤
        min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U) := by
  exact ⟨
    fun L hL => lip_localization d ϕ U D L h.subset hL,
    fun K hK => colip_localization d ϕ U D K h.nonempty h.subset hK,
    fun i j => annihilation_localization_radius_mono d ϕ U D i j h.subset⟩

/--
OET anchor: h-3d5f909fa9f5d7da
**命题（受限域上的证书单调性）**
对非空 `U ⊆ dom ϕ`，全定义域上的 Lip/co-Lip 证书限制到 `U` 后仍合法，
且逐通道统一零化半径不减。
-/
theorem restricted_domain_certificate_monotonicity
    (ϕ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕ) (hU_ne : U.Nonempty) :
    (∀ L : I → I → ENNReal,
      IsLipMatrix d ϕ (dom ϕ) L → IsLipMatrix d ϕ U L) ∧
    (∀ K : I → I → ENNReal,
      IsCoLipMatrix d ϕ (dom ϕ) K → IsCoLipMatrix d ϕ U K) ∧
    (∀ i j : I,
      min_annihilation_radius d ϕ i (singleton_nonempty_finset j) (dom ϕ) ≤
        min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U) := by
  exact localization_tightening d ϕ U (dom ϕ) ⟨hU, hU_ne⟩

end

end formal_oet.vol_01.ch_04_operator_chain_calculus
