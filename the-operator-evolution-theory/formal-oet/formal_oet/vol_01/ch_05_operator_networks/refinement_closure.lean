import Mathlib.Logic.Relation
import formal_oet.vol_01.ch_05_operator_networks.readout_quotient
import formal_oet.vol_01.ch_05_operator_networks.network_refinement

namespace formal_oet.vol_01.ch_05_operator_networks.refinement_closure

open formal_oet.vol_01.ch_05_operator_networks.readout_quotient

variable {A P : Type}

variable {s : Setoid A} {step : A → A → Prop}

/--
OET anchor: h-b4a8c0d22a3257e5
**定义（外延保持加细关系）**
A one-step refinement relation preserves the setoid relation when every
one-step move relates its endpoints.
-/
def StepPreservesSetoid (s : Setoid A) (step : A → A → Prop) : Prop :=
  ∀ {N M : A}, step N M → @Setoid.r A s N M

/--
OET anchor: h-b4a8c0d22a3257e5
**推论（有限次加细的外延保持）**
If every one-step refinement preserves the setoid relation, then every finite
refinement chain stays in the same equivalence class.
-/
theorem refl_trans_gen_preserves_setoid
    (hstep : StepPreservesSetoid s step)
    {N M : A} (hNM : Relation.ReflTransGen step N M) :
    @Setoid.r A s M N := by
  letI : Setoid A := s
  induction hNM with
  | refl =>
      exact Setoid.refl N
  | tail hNK hKM ih =>
      exact Setoid.trans (Setoid.symm (hstep hKM)) ih

/--
OET anchor: h-b4a8c0d22a3257e5
**推论（有限次加细的外延保持）：外延不变读出在加细闭包上常值。**
An invariant readout is constant along every finite refinement chain whose
steps preserve the setoid relation.
-/
theorem invariant_readout_constant_on_refinement_closure
    (hstep : StepPreservesSetoid s step) (hΓ : SetoidInvariant s Γ)
    {N M : A} (hNM : Relation.ReflTransGen step N M) :
    Γ M = Γ N :=
  hΓ (refl_trans_gen_preserves_setoid (s := s) hstep hNM)

end formal_oet.vol_01.ch_05_operator_networks.refinement_closure
