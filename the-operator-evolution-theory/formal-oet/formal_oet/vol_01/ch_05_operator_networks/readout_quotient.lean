import formal_oet.vol_01.ch_05_operator_networks.network_extensional_space

namespace formal_oet.vol_01.ch_05_operator_networks.readout_quotient

variable {A P : Type}

/--
OET anchor: h-53884ec89a20d006
**推论（外延不变读出的商因子化）**
For a setoid relation, a readout is invariant when it is constant on
equivalent representatives. This formalizes the hypothesis used in the
quotient descent factorization.
-/
def SetoidInvariant (s : Setoid A) (Γ : A → P) : Prop :=
  ∀ {N M : A}, @Setoid.r A s N M → Γ N = Γ M

/--
OET anchor: h-53884ec89a20d006
**推论（外延不变读出的商因子化）**
An invariant readout factors through the quotient.
-/
noncomputable def quotient_factorized_readout (s : Setoid A) (Γ : A → P)
    (hΓ : SetoidInvariant s Γ) : Quotient s → P :=
  Quotient.lift Γ (by
    intro N M hNM
    exact hΓ hNM)

/--
OET anchor: h-53884ec89a20d006
**推论（外延不变读出的商因子化）**
The quotient-factorized readout composes with the quotient map to recover the original
readout.
-/
theorem quotient_factorized_readout_mk (s : Setoid A) (Γ : A → P)
    (hΓ : SetoidInvariant s Γ) (N : A) :
    quotient_factorized_readout s Γ hΓ (Quotient.mk s N) = Γ N :=
  rfl

/--
OET anchor: h-53884ec89a20d006
**推论（外延不变读出的商因子化）**
The quotient-factorized readout is unique among maps out of the quotient whose
composition with the quotient map is the original readout.
-/
theorem quotient_factorized_readout_unique (s : Setoid A) (Γ : A → P)
    (hΓ : SetoidInvariant s Γ) (barΓ : Quotient s → P)
    (hbarΓ : ∀ N : A, barΓ (Quotient.mk s N) = Γ N) :
    barΓ = quotient_factorized_readout s Γ hΓ := by
  funext q
  refine Quotient.inductionOn q ?_
  intro N
  rw [hbarΓ N]
  rfl

end formal_oet.vol_01.ch_05_operator_networks.readout_quotient
