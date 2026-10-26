import formal_oet.vol_01.appendix_separating_gauge_specialization.operator_and_chain
import formal_oet.vol_01.ch_05_operator_networks.network_extensional_space

namespace formal_oet.vol_01.appendix_separating_gauge_specialization

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks

noncomputable section

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-8c3b9b6221a633b6
**推论（网络零距商与外延商的一致性）**
该推论使用的网络全分量零距关系。
-/
def NetworkZeroEquivalent (N M : NetworkObject X bot) : Prop :=
  ∀ i, NetworkObject.extensional_dist (d i) N M = 0

/--
OET anchor: h-8c3b9b6221a633b6
**推论（网络零距商与外延商的一致性）**
在分离规范下，全分量外延零距等价于外延算子相等。
-/
theorem network_zero_equivalent_iff_extensional_equivalent
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (N M : NetworkObject X bot) :
    NetworkZeroEquivalent d N M ↔ NetworkObject.ExtensionalEquivalent N M := by
  change
    (∀ i, op_dist (d i) N.extensional_operator M.extensional_operator = 0) ↔
      N.extensional_operator = M.extensional_operator
  exact (operator_eq_iff_all_dist_zero d hd_self hsep
    N.extensional_operator M.extensional_operator).symm

/-- The setoid determined by all-component extensional zero distance. -/
def network_zero_setoid (bot : X)
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) : Setoid (NetworkObject X bot) where
  r := NetworkZeroEquivalent d
  iseqv := by
    constructor
    · intro N
      exact (network_zero_equivalent_iff_extensional_equivalent d hd_self hsep N N).mpr rfl
    · intro N M hNM
      apply (network_zero_equivalent_iff_extensional_equivalent d hd_self hsep M N).mpr
      exact ((network_zero_equivalent_iff_extensional_equivalent d hd_self hsep N M).mp hNM).symm
    · intro N M K hNM hMK
      apply (network_zero_equivalent_iff_extensional_equivalent d hd_self hsep N K).mpr
      exact ((network_zero_equivalent_iff_extensional_equivalent d hd_self hsep N M).mp hNM).trans
        ((network_zero_equivalent_iff_extensional_equivalent d hd_self hsep M K).mp hMK)

/-- Readout induced on the all-component zero-distance quotient. -/
def network_zero_quotient_readout (bot : X)
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) :
    Quotient (network_zero_setoid d bot hd_self hsep) → Operator X bot :=
  Quotient.lift NetworkObject.extensional_operator (by
    intro N M hNM
    exact (network_zero_equivalent_iff_extensional_equivalent d hd_self hsep N M).mp hNM)

/--
OET anchor: h-8c3b9b6221a633b6
**推论（网络零距商与外延商的一致性）**
零距关系给出的商读出与既有外延商读出相同，因而为双射。
-/
theorem network_zero_quotient_readout_bijective
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) :
    Function.Bijective (network_zero_quotient_readout d bot hd_self hsep) := by
  constructor
  · intro Q R hQR
    refine Quotient.inductionOn₂ Q R ?_ hQR
    intro N M hNM
    exact Quotient.sound
      ((network_zero_equivalent_iff_extensional_equivalent d hd_self hsep N M).mpr hNM)
  · intro φ
    rcases NetworkObject.extensional_operator_surjective (X := X) (bot := bot) φ with
      ⟨N, hN⟩
    exact ⟨Quotient.mk _ N, hN⟩

/-- Distance on the zero-distance quotient, pulled back from operator space. -/
def network_zero_quotient_dist (bot : X)
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (i : I)
    (Q R : Quotient (network_zero_setoid d bot hd_self hsep)) : ENNReal :=
  op_dist (d i) (network_zero_quotient_readout d bot hd_self hsep Q)
    (network_zero_quotient_readout d bot hd_self hsep R)

/--
OET anchor: h-8c3b9b6221a633b6
**推论（网络零距商与外延商的一致性）**
商上的外延距离等于商读出后的算子距离。
-/
theorem network_quotient_dist_eq_operator_dist
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (i : I) (N M : NetworkObject X bot) :
    network_zero_quotient_dist d bot hd_self hsep i
      (Quotient.mk _ N) (Quotient.mk _ M) =
      op_dist (d i)
        (network_zero_quotient_readout d bot hd_self hsep (Quotient.mk _ N))
        (network_zero_quotient_readout d bot hd_self hsep (Quotient.mk _ M)) :=
  rfl

end

end formal_oet.vol_01.appendix_separating_gauge_specialization
