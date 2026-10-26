import formal_oet.vol_01.ch_05_operator_networks.network_routing
import formal_oet.vol_01.ch_05_operator_networks.network_relabeling

namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations
variable {X V : Type} {bot : X}

namespace OperatorTransitionGraph
variable (T : OperatorTransitionGraph X bot V)

/-- OET anchor: h-86752cb60c8e01e3
Graph acyclicity means absence of nonempty directed closed walks. It is
independent of any choice of a rank function. -/
def IsAcyclic : Prop := ∀ v, ¬ Relation.TransGen T.Edge v v

/-- The finite set of nodes reachable by a positive number of edges. -/
noncomputable def strict_successors (v : V) : Finset V := by
  classical
  letI := T.node_fintype
  exact Finset.univ.filter (Relation.TransGen T.Edge v)

@[simp] theorem mem_strict_successors {v w : V} :
    w ∈ T.strict_successors v ↔ Relation.TransGen T.Edge v w := by
  classical
  simp [strict_successors]

/-- A concrete topological rank: the number of strict successors. -/
noncomputable def acyclic_rank (v : V) : Nat := (T.strict_successors v).card

theorem acyclic_rank_lt_of_edge (hT : T.IsAcyclic) {v w : V} (hvw : T.Edge v w) :
    T.acyclic_rank w < T.acyclic_rank v := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro z hz
    exact T.mem_strict_successors.mpr
      ((Relation.TransGen.single hvw).trans (T.mem_strict_successors.mp hz))
  · intro heq
    have hw : w ∈ T.strict_successors v :=
      T.mem_strict_successors.mpr (Relation.TransGen.single hvw)
    rw [← heq] at hw
    exact hT w (T.mem_strict_successors.mp hw)

/-- The converse uses only strict descent along an actual edge. -/
theorem is_acyclic_of_rank (r : V → Nat)
    (hr : ∀ {v w}, T.Edge v w → r w < r v) : T.IsAcyclic := by
  intro v hcycle
  have descend : ∀ {a b}, Relation.TransGen T.Edge a b → r b < r a := by
    intro a b h
    induction h with
    | single h => exact hr h
    | tail _ h ih => exact lt_trans (hr h) ih
  exact Nat.lt_irrefl _ (descend hcycle)

/-- Finiteness converts the usual graph condition into the rank certificate
used by `OperatorNetwork`; neither implication defines acyclicity by rank. -/
theorem is_acyclic_iff_exists_rank :
    T.IsAcyclic ↔ ∃ r : V → Nat, ∀ {v w}, T.Edge v w → r w < r v := by
  constructor
  · intro h
    exact ⟨T.acyclic_rank, T.acyclic_rank_lt_of_edge h⟩
  · rintro ⟨r, hr⟩
    exact T.is_acyclic_of_rank r hr
end OperatorTransitionGraph

namespace FiniteOperatorNetwork
variable (N : FiniteOperatorNetwork X bot V)

/-- Topological rank descent holds on every valid operational transition. -/
theorem acyclic_choice_next_rank (hN : N.to_transition_graph.IsAcyclic)
    {v w : V} {x : X} (hx : x ∈ dom (N.node_op v))
    (hchoice : N.choice v ((N.node_op v).func x) = .next w) :
    N.to_transition_graph.acyclic_rank w < N.to_transition_graph.acyclic_rank v := by
  apply N.to_transition_graph.acyclic_rank_lt_of_edge hN
  exact ⟨(N.node_op v).func x, ⟨x, hx, rfl⟩, hchoice⟩

/-- Sufficient rank fuel records the existing complete path exactly, so the
conversion does not replace the graph by a different representation. -/
theorem path_with_acyclic_fuel_eq (hN : N.to_transition_graph.IsAcyclic)
    {v : V} {x : X} {p : List V}
    (hp : TerminalPathFrom N.node_op N.choice v x p)
    (hx : x ∈ dom (N.node_op v)) (n : Nat)
    (hn : N.to_transition_graph.acyclic_rank v ≤ n) :
    path_with_fuel_core N.node_op N.choice n v x = p := by
  induction hp generalizing n with
  | stop hs =>
    cases n <;> simp [path_with_fuel_core, hs]
  | @next v w x rest hs ht ih =>
    have hlt := N.acyclic_choice_next_rank hN hx hs
    cases n with
    | zero => omega
    | succ n =>
      simp only [path_with_fuel_core, hs]
      congr 1
      exact ih (N.choice_next_mem hx hs) n (by omega)

/-- OET anchor: h-86752cb60c8e01e3
Every finite network with an acyclic underlying directed graph has the
rank-carrying encoding, on the same nodes and with unchanged operational data. -/
noncomputable def to_acyclic (hN : N.to_transition_graph.IsAcyclic) :
    OperatorNetwork X bot V where
  U := N.U
  bot_not_mem := N.bot_not_mem
  node_fintype := N.node_fintype
  node_op := N.node_op
  node_dom_nonempty := N.node_dom_nonempty
  entry := N.entry
  entry_mem := N.entry_mem
  choice := N.choice
  choice_next_mem := N.choice_next_mem
  rank := N.to_transition_graph.acyclic_rank
  choice_next_rank := N.acyclic_choice_next_rank hN
  node_reachable := by
    intro v
    obtain ⟨x, hx⟩ := N.node_reachable v
    refine ⟨x, ?_⟩
    rw [N.path_with_acyclic_fuel_eq hN (N.path_terminal x) (N.entry_mem x) _ le_rfl]
    exact hx

@[simp] theorem to_acyclic_source (hN : N.to_transition_graph.IsAcyclic) :
    (N.to_acyclic hN).U = N.U := rfl
@[simp] theorem to_acyclic_node_op (hN : N.to_transition_graph.IsAcyclic) :
    (N.to_acyclic hN).node_op = N.node_op := rfl
@[simp] theorem to_acyclic_entry (hN : N.to_transition_graph.IsAcyclic) :
    (N.to_acyclic hN).entry = N.entry := rfl
@[simp] theorem to_acyclic_choice (hN : N.to_transition_graph.IsAcyclic) :
    (N.to_acyclic hN).choice = N.choice := rfl
@[simp] theorem to_acyclic_transition_graph (hN : N.to_transition_graph.IsAcyclic) :
    (N.to_acyclic hN).to_transition_graph = N.to_transition_graph := rfl
@[simp] theorem to_acyclic_edge_domain (hN : N.to_transition_graph.IsAcyclic) (v w : V) :
    (N.to_acyclic hN).to_transition_graph.edge_domain v w =
      N.to_transition_graph.edge_domain v w := rfl

@[simp] theorem to_acyclic_path (hN : N.to_transition_graph.IsAcyclic)
    (x : {x // x ∈ N.U}) : (N.to_acyclic hN).path_of x = N.path_of x := by
  exact N.path_with_acyclic_fuel_eq hN (N.path_terminal x) (N.entry_mem x) _ le_rfl

/-- OET anchor: h-13bcaf7893e917fe
An acyclic finite network's actual maximum evaluation depth is at most its
node count, independently of the possibly larger stored termination bound. -/
theorem evaluation_depth_le_node_count_of_acyclic
    (hN : N.to_transition_graph.IsAcyclic) : N.evaluation_depth ≤ N.node_count := by
  apply N.evaluation_depth_le_of_input_lengths
  intro x
  have h := (N.to_acyclic hN).path_of_length_le_node_count x
  rw [N.to_acyclic_path] at h
  exact h

/-- The conversion preserves the actual function, including its value off U. -/
theorem to_acyclic_extensional_operator_eq (hN : N.to_transition_graph.IsAcyclic) :
    (N.to_acyclic hN).extensional_operator = N.extensional_operator := by
  classical
  ext x
  by_cases hx : x ∈ N.U
  · calc
      (N.to_acyclic hN).extensional_operator.func x =
          (N.to_acyclic hN).chain_eval_nodes ((N.to_acyclic hN).path_of ⟨x, hx⟩) x :=
        (N.to_acyclic hN).extensional_apply_eq_chain_eval_path ⟨x, hx⟩
      _ = N.chain_eval_nodes (N.path_of ⟨x, hx⟩) x := by
        rw [N.to_acyclic_path]
        rfl
      _ = N.extensional_operator.func x :=
        (N.extensional_apply_eq_chain_eval_path ⟨x, hx⟩).symm
  · simp [OperatorNetwork.extensional_operator, extensional_operator, to_acyclic, hx]
end FiniteOperatorNetwork

namespace OperatorNetwork
variable (N : OperatorNetwork X bot V)

/-- The rank-carrying representation satisfies the usual directed graph
condition, even for edges outside all entrance trajectories. -/
theorem transition_graph_is_acyclic : N.to_transition_graph.IsAcyclic := by
  apply N.to_transition_graph.is_acyclic_of_rank N.rank
  intro v w h
  obtain ⟨z, ⟨x, hx, rfl⟩, hchoice⟩ := h
  exact N.choice_next_rank hx hchoice
end OperatorNetwork

end formal_oet.vol_01.ch_05_operator_networks
