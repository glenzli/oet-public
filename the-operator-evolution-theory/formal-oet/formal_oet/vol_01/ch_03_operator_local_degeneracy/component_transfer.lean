import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_03_operator_local_degeneracy.component_partition

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

set_option linter.style.longLine false
set_option linter.style.emptyLine false

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Finset

variable {X I : Type} {bot : X}
local instance instDecidableEqIComponentTransfer : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/-- OET anchor: h-87c593824d28aa93
相应输出行的非对角项为零时，常值分量在复合中保持。
-/
theorem const_comp_maintaining_of_diagonal_row (ϕ ψ : Operator X bot) (U : Set X) (j : I)
    [Fintype I]
    (h_U_dom : U ⊆ dom (OperatorChain [ψ, ϕ]))
    (h_const : j ∈ ConstComponent d ϕ U)
    (L : I → I → ENNReal)
    (hL : IsLipMatrix d ψ (ϕ.func '' U) L)
    (h_row_zero : ∀ k, k ≠ j → L k j = 0) :
    j ∈ ConstComponent d (OperatorChain [ψ, ϕ]) U := by
  have _ := h_U_dom
  intro x hx y hy
  have h_bound := lip_bound_of_single_input_row d ψ (ϕ.func '' U) L j j hL h_row_zero
    (ϕ.func x) (Set.mem_image_of_mem _ hx) (ϕ.func y) (Set.mem_image_of_mem _ hy)
  rw [h_const x hx y hy, mul_zero] at h_bound
  exact le_antisymm h_bound (zero_le _)

end

end formal_oet.vol_01.ch_03_operator_local_degeneracy
