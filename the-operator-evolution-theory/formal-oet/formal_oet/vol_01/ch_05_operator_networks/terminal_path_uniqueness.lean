import formal_oet.vol_01.ch_05_operator_networks.operator_network

namespace formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork
open formal_oet.vol_01.ch_01_foundations
variable {X V : Type} {bot : X}

/-- Determinism of the choice map makes a terminal path from a fixed node and
state unique. -/
theorem terminal_path_from_unique
    {node_op : V → Operator X bot} {choice : V → X → OutputChoice V}
    {β : V} {z : X} {p₁ p₂ : List V}
    (h₁ : TerminalPathFrom node_op choice β z p₁)
    (h₂ : TerminalPathFrom node_op choice β z p₂) : p₁ = p₂ := by
  induction h₁ generalizing p₂ with
  | stop hstop =>
      cases h₂ with
      | stop _ => rfl
      | next hnext _ =>
          cases hstop.symm.trans hnext
  | next hnext hrest ih =>
      cases h₂ with
      | stop hstop =>
          cases hnext.symm.trans hstop
      | @next _ γ₂ _ _ hnext₂ hrest₂ =>
          have hγ : _ = γ₂ := OutputChoice.next.inj (hnext.symm.trans hnext₂)
          subst γ₂
          exact congrArg (List.cons _) (ih hrest₂)

end formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork
