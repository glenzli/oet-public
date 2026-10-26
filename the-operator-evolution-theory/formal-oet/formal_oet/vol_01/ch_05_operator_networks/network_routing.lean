import formal_oet.vol_01.ch_05_operator_networks.operator_network

namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations
variable {X V W : Type} {bot : X}

/-- Relabel the destination of a routing choice. -/
def map_output_choice (f : V → W) : OutputChoice V → OutputChoice W
  | .stop => .stop
  | .next v => .next (f v)

/-- A deterministic routing rule has at most one complete terminal node list
from a specified node and input state. -/
theorem terminal_path_unique {op : V → Operator X bot} {choice : V → X → OutputChoice V}
    {v x p q} (h : TerminalPathFrom op choice v x p)
    (hq : TerminalPathFrom op choice v x q) : p = q := by
  induction h generalizing q with
  | stop hs =>
    cases hq with
    | stop => rfl
    | next ht _ => simp [hs] at ht
  | @next v w x rest hs ht ih =>
    cases hq with
    | stop hstop => simp [hs] at hstop
    | @next _ w' _ rest' hs' ht' =>
      have hw : w = w' := OutputChoice.next.inj (hs.symm.trans hs')
      subst w'
      exact congrArg (v :: ·) (ih ht')

end formal_oet.vol_01.ch_05_operator_networks
