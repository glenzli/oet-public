import formal_oet.vol_01.ch_05_operator_networks.operator_network

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations
open FiniteOperatorNetwork

noncomputable section
variable {X V : Type} {bot : X}

/-- A finite terminating network before removal of unreachable nodes.
All routing and termination obligations are retained; only nonredundancy is absent. -/
structure FiniteNetworkPresentation (X : Type) (bot : X) (V : Type) where
  U : Set X
  bot_not_mem : bot ∉ U
  node_fintype : Fintype V
  node_op : V → Operator X bot
  node_dom_nonempty : ∀ β, (dom (node_op β)).Nonempty
  entry : U → V
  entry_mem : ∀ x : U, x.val ∈ dom (node_op (entry x))
  choice : V → X → OutputChoice V
  choice_next_mem : ∀ {β γ y}, y ∈ dom (node_op β) →
    choice β ((node_op β).func y) = .next γ → (node_op β).func y ∈ dom (node_op γ)
  depth_bound : Nat
  path_of : U → List V
  path_terminal : ∀ x : U, TerminalPathFrom node_op choice (entry x) x.val (path_of x)
  path_length_le_depth : ∀ x : U, (path_of x).length ≤ depth_bound

private theorem terminal_path_start_mem
    {op : V → Operator X bot} {choice : V → X → OutputChoice V}
    {v x p} (h : TerminalPathFrom op choice v x p) : v ∈ p := by
  cases h <;> simp

/-- Delete transitions whose destination was removed. -/
def prune_choice (P : V → Prop) (choice : V → X → OutputChoice V)
    (v : {v // P v}) (x : X) : OutputChoice {v // P v} := by
  classical
  exact match choice v.val x with
    | .stop => .stop
    | .next w => if h : P w then .next ⟨w, h⟩ else .stop

/-- Every edge between retained labels is preserved on its entire domain,
including values that never arise during entrance evaluation. -/
theorem prune_choice_next_iff (P : V → Prop) (choice : V → X → OutputChoice V)
    (v w : {v // P v}) (x : X) :
    prune_choice P choice v x = .next w ↔ choice v.val x = .next w.val := by
  classical
  cases hc : choice v.val x with
  | stop => simp [prune_choice, hc]
  | next u =>
    by_cases hu : P u
    · simp [prune_choice, hc, hu, Subtype.ext_iff]
    · simp only [prune_choice, hc, dif_neg hu, reduceCtorEq, false_iff,
        OutputChoice.next.injEq]
      intro heq
      exact hu (heq ▸ w.property)

private theorem terminal_path_prune
    (P : V → Prop) (op : V → Operator X bot) (choice : V → X → OutputChoice V)
    {v x p} (h : TerminalPathFrom op choice v x p) (hp : ∀ w ∈ p, P w) :
    TerminalPathFrom (fun w : {w // P w} => op w.val) (prune_choice P choice)
      ⟨v, hp v (terminal_path_start_mem h)⟩ x
      (p.pmap (fun w hw => (⟨w, hw⟩ : {w // P w})) hp) := by
  classical
  induction h with
  | stop hs =>
    apply TerminalPathFrom.stop
    simp [prune_choice, hs]
  | @next v w x rest hs ht ih =>
    have hrest : ∀ w ∈ rest, P w := fun w hw => hp w (by simp [hw])
    have hw : P w := hrest w (terminal_path_start_mem ht)
    apply TerminalPathFrom.next (γ := ⟨w, hw⟩)
    · simp [prune_choice, hs, hw]
    · exact ih hrest

namespace FiniteNetworkPresentation
variable (N : FiniteNetworkPresentation X bot V)

/-- A presentation whose nodes all occur is already a finite network.
This adds only the nonredundancy proof, without changing any operational data. -/
def to_finite_network (hreach : ∀ v, ∃ x : N.U, v ∈ N.path_of x) :
    FiniteOperatorNetwork X bot V where
  U := N.U
  bot_not_mem := N.bot_not_mem
  node_fintype := N.node_fintype
  node_op := N.node_op
  node_dom_nonempty := N.node_dom_nonempty
  entry := N.entry
  entry_mem := N.entry_mem
  choice := N.choice
  choice_next_mem := N.choice_next_mem
  depth_bound := N.depth_bound
  path_of := N.path_of
  path_terminal := N.path_terminal
  path_length_le_depth := N.path_length_le_depth
  node_reachable := hreach

/-- The output on the input domain, completed by the absorbing point outside it. -/
def extensional_operator : Operator X bot := by
  classical
  refine ⟨fun x => if hx : x ∈ N.U then
    chain_eval_nodes_core N.node_op (N.path_of ⟨x, hx⟩) x else bot, ?_⟩
  simp [N.bot_not_mem]

/-- Exactly the nodes visited by source inputs. -/
def Reached (v : V) : Prop := ∃ x : N.U, v ∈ N.path_of x

/-- OET anchor: h-ced8c7236326e104
Reachable-node pruning retains all original local operators and removes only
unreachable node labels and transitions to those labels. -/
def prune : FiniteOperatorNetwork X bot {v // N.Reached v} := by
  classical
  letI := N.node_fintype
  exact {
    U := N.U
    bot_not_mem := N.bot_not_mem
    node_fintype := inferInstance
    node_op := fun v => N.node_op v.val
    node_dom_nonempty := fun v => N.node_dom_nonempty v.val
    entry := fun x => ⟨N.entry x, x, terminal_path_start_mem (N.path_terminal x)⟩
    entry_mem := N.entry_mem
    choice := prune_choice N.Reached N.choice
    choice_next_mem := by
      intro v w y hy hc
      dsimp [prune_choice] at hc
      split at hc
      · contradiction
      · rename_i u heq
        split at hc
        · simp only [OutputChoice.next.injEq] at hc
          cases hc
          exact N.choice_next_mem hy heq
        · contradiction
    depth_bound := N.depth_bound
    path_of := fun x => (N.path_of x).pmap (fun v hv => ⟨v, hv⟩)
      (fun v hv => ⟨x, hv⟩)
    path_terminal := fun x => terminal_path_prune N.Reached N.node_op N.choice
      (N.path_terminal x) (fun v hv => ⟨x, hv⟩)
    path_length_le_depth := by intro x; simpa using N.path_length_le_depth x
    node_reachable := by
      rintro ⟨v, x, hv⟩
      refine ⟨x, ?_⟩
      simp only [List.mem_pmap]
      exact ⟨v, hv, rfl⟩
  }

/-- OET anchor: h-ced8c7236326e104
Pruning preserves the complete sequence of visited node labels. -/
@[simp] theorem prune_path_labels (x : N.U) :
    (N.prune.path_of x).map Subtype.val = N.path_of x := by
  simp [prune, List.map_pmap]

private theorem eval_pmap (p : List V) (hp : ∀ v ∈ p, N.Reached v) (x : X) :
    chain_eval_nodes_core (fun v : {v // N.Reached v} => N.node_op v.val)
      (p.pmap (fun v hv => ⟨v, hv⟩) hp) x = chain_eval_nodes_core N.node_op p x := by
  induction p generalizing x with
  | nil => rfl
  | cons v rest ih => exact ih _ _

/-- OET anchor: h-ced8c7236326e104
Pruning preserves each input's terminal output. -/
theorem prune_eval (x : N.U) :
    N.prune.eval x = chain_eval_nodes_core N.node_op (N.path_of x) x.val := by
  exact N.eval_pmap _ _ _

/-- OET anchor: h-ced8c7236326e104
Pruning preserves the absorbing-point-completed extensional operator. -/
theorem prune_extensional_operator_eq :
    N.prune.extensional_operator = N.extensional_operator := by
  classical
  apply Operator.ext
  funext x
  by_cases hx : x ∈ N.U
  · simpa only [FiniteOperatorNetwork.extensional_operator, extensional_operator,
      prune, dif_pos hx] using N.prune_eval ⟨x, hx⟩
  · simp [FiniteOperatorNetwork.extensional_operator, extensional_operator, prune, hx]

end FiniteNetworkPresentation
end
end formal_oet.vol_01.ch_05_operator_networks
