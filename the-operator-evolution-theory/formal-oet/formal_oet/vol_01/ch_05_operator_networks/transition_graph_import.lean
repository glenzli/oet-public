import formal_oet.vol_01.ch_05_operator_networks.transition_trajectories
import formal_oet.vol_01.ch_05_operator_networks.network_presentation

namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations
variable {X V : Type} {bot : X}

namespace OperatorTransitionGraph
variable (T : OperatorTransitionGraph X bot V)

/-- OET anchor: h-86752cb60c8e01e3
The textbook's disjoint outgoing transition domains, stated on the raw graph. -/
def HasDisjointOutgoingDomains : Prop :=
  ∀ v w w' : V, w ≠ w' → Disjoint (T.edge_domain v w) (T.edge_domain v w')

/-- OET anchor: h-86752cb60c8e01e3
The entry pieces partition the source domain and lie in their node domains.
Empty pieces encode non-entry nodes; the entry-node set is exactly the nodes
with nonempty pieces, so no nonempty-node assumption excludes the empty network. -/
structure EntryPartition (U : Set X) (entrance : V → Set X) : Prop where
  subset_node_dom : ∀ v, entrance v ⊆ T.node_dom v
  cover : (⋃ v, entrance v) = U
  disjoint : ∀ v w, v ≠ w → Disjoint (entrance v) (entrance w)

/-- Choose an outgoing edge when one exists, and stop otherwise. -/
noncomputable def choice_of_edges (v : V) (y : X) : OutputChoice V := by
  classical
  exact if h : ∃ w, y ∈ T.edge_domain v w then .next h.choose else .stop

theorem choice_of_edges_next_iff (hdet : T.HasDisjointOutgoingDomains)
    {v w : V} {y : X} :
    T.choice_of_edges v y = .next w ↔ y ∈ T.edge_domain v w := by
  classical
  unfold choice_of_edges
  split_ifs with h
  · constructor
    · intro heq
      have hw := OutputChoice.next.inj heq
      simpa [hw] using h.choose_spec
    · intro hy
      have hw : h.choose = w := by
        by_contra hn
        exact Set.disjoint_left.mp (hdet v h.choose w hn) h.choose_spec hy
      simp [hw]
  · simp only [false_iff]
    exact fun hy => h ⟨w, hy⟩

theorem choice_of_edges_stop_iff {v : V} {y : X} :
    T.choice_of_edges v y = .stop ↔ ¬ ∃ w, y ∈ T.edge_domain v w := by
  classical
  unfold choice_of_edges
  split_ifs <;> simp_all

theorem terminal_trajectory_to_chosen_path (hdet : T.HasDisjointOutgoingDomains)
    {v x states} (h : T.TerminalTrajectoryFrom v x states) :
    TerminalPathFrom T.node_op T.choice_of_edges v x (states.map Prod.fst) := by
  induction h with
  | stop hx ht =>
    apply TerminalPathFrom.stop
    apply T.choice_of_edges_stop_iff.mpr
    rintro ⟨w, hw⟩
    exact ht.2 (Set.mem_iUnion.mpr ⟨w, hw⟩)
  | next step tail ih =>
    rw [step.2.1] at ih
    exact .next ((T.choice_of_edges_next_iff hdet).mpr (step.2.1 ▸ step.2.2)) ih

/-- Disjoint raw edge domains force uniqueness of the full labelled state
trajectory, before any operational finite network has been constructed. -/
theorem terminal_trajectory_unique_of_disjoint (hdet : T.HasDisjointOutgoingDomains)
    {v x states states'} (h : T.TerminalTrajectoryFrom v x states)
    (h' : T.TerminalTrajectoryFrom v x states') : states = states' := by
  have hp := terminal_path_unique (T.terminal_trajectory_to_chosen_path hdet h)
    (T.terminal_trajectory_to_chosen_path hdet h')
  rw [T.finite_trajectory_eq_state_trace (T.terminal_trajectory_finite h),
    T.finite_trajectory_eq_state_trace (T.terminal_trajectory_finite h'), hp]

namespace EntryPartition
variable {T} {U : Set X} {entrance : V → Set X}
variable (hpart : T.EntryPartition U entrance)
include hpart

theorem mem_unique_entry {x : X} (hx : x ∈ U) : ∃! v, x ∈ entrance v := by
  have hmem : x ∈ ⋃ v, entrance v := hpart.cover ▸ hx
  obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hmem
  refine ⟨v, hv, ?_⟩
  intro w hw
  by_contra hn
  exact Set.disjoint_left.mp (hpart.disjoint w v hn) hw hv

noncomputable def entry (x : {x // x ∈ U}) : V :=
  (hpart.mem_unique_entry x.property).exists.choose

theorem entry_mem (x : {x // x ∈ U}) : x.val ∈ entrance (hpart.entry x) :=
  (hpart.mem_unique_entry x.property).exists.choose_spec

theorem entry_eq_iff (x : {x // x ∈ U}) (v : V) :
    hpart.entry x = v ↔ x.val ∈ entrance v := by
  constructor
  · intro heq
    simpa [heq] using hpart.entry_mem x
  · intro hv
    exact ((hpart.mem_unique_entry x.property).unique hv (hpart.entry_mem x)).symm

theorem piece_subset_source (v : V) : entrance v ⊆ U := by
  intro x hx
  rw [← hpart.cover]
  exact Set.mem_iUnion.mpr ⟨v, hx⟩

theorem bot_not_mem : bot ∉ U := by
  intro hx
  have hdom := hpart.subset_node_dom _ (hpart.entry_mem ⟨bot, hx⟩)
  exact hdom (T.node_op _).preserves_bot

end EntryPartition

variable {U : Set X} {entrance : V → Set X}

/-- OET anchor: h-ced8c7236326e104
Import exactly raw conditions (i)–(iii), before deleting redundant nodes.
Entry selection, deterministic routing and bounded complete paths are constructed
from raw graph data. No node-reachability or nonempty-source assumption is used. -/
noncomputable def to_presentation (hpart : T.EntryPartition U entrance)
    (hdet : T.HasDisjointOutgoingDomains) (bound : Nat)
    (hterm : ∀ x v, x ∈ entrance v → ∃ states,
      T.TerminalTrajectoryFrom v x states ∧ states.length ≤ bound) :
    FiniteNetworkPresentation X bot V where
  U := U
  bot_not_mem := hpart.bot_not_mem
  node_fintype := T.node_fintype
  node_op := T.node_op
  node_dom_nonempty := T.node_dom_nonempty
  entry := hpart.entry
  entry_mem := fun x => hpart.subset_node_dom _ (hpart.entry_mem x)
  choice := T.choice_of_edges
  choice_next_mem := by
    intro v w y _ hc
    exact T.edge_domain_subset_node_dom v w ((T.choice_of_edges_next_iff hdet).mp hc)
  depth_bound := bound
  path_of := fun x => (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose.map Prod.fst
  path_terminal := fun x => T.terminal_trajectory_to_chosen_path hdet
    (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose_spec.1
  path_length_le_depth := by
    intro x
    simpa only [List.length_map] using
      (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose_spec.2

/-- OET anchor: h-86752cb60c8e01e3
The fourth raw condition promotes the same presentation to a finite network;
local operators, routing, entries and complete paths are unchanged. -/
noncomputable def to_finite_network (hpart : T.EntryPartition U entrance)
    (hdet : T.HasDisjointOutgoingDomains) (bound : Nat)
    (hterm : ∀ x v, x ∈ entrance v → ∃ states,
      T.TerminalTrajectoryFrom v x states ∧ states.length ≤ bound)
    (hreach : ∀ v, ∃ x w states, x ∈ entrance w ∧
      T.TerminalTrajectoryFrom w x states ∧ v ∈ states.map Prod.fst) :
    FiniteOperatorNetwork X bot V :=
  (T.to_presentation hpart hdet bound hterm).to_finite_network (by
    intro v
    obtain ⟨x, w, states, hx, ht, hv⟩ := hreach v
    let input : {x // x ∈ U} := ⟨x, hpart.piece_subset_source w hx⟩
    have he : hpart.entry input = w := (hpart.entry_eq_iff input w).mpr hx
    refine ⟨input, ?_⟩
    have ht' : T.TerminalTrajectoryFrom (hpart.entry input) x states := he ▸ ht
    have hs := T.terminal_trajectory_unique_of_disjoint hdet ht'
      (hterm input.val (hpart.entry input) (hpart.entry_mem input)).choose_spec.1
    simpa only [hs] using hv)

variable (hpart : T.EntryPartition U entrance) (hdet : T.HasDisjointOutgoingDomains)
  (bound : Nat)
  (hterm : ∀ x v, x ∈ entrance v → ∃ states,
    T.TerminalTrajectoryFrom v x states ∧ states.length ≤ bound)
  (hreach : ∀ v, ∃ x w states, x ∈ entrance w ∧
    T.TerminalTrajectoryFrom w x states ∧ v ∈ states.map Prod.fst)

@[simp] theorem to_presentation_source :
    (T.to_presentation hpart hdet bound hterm).U = U := rfl

/-- Any raw terminal trajectory, rather than just the chosen witness,
is represented by exactly its complete node list. -/
theorem to_presentation_path_of (x : {x // x ∈ U}) {states}
    (ht : T.TerminalTrajectoryFrom (hpart.entry x) x.val states) :
    (T.to_presentation hpart hdet bound hterm).path_of x = states.map Prod.fst := by
  change (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose.map Prod.fst = _
  rw [T.terminal_trajectory_unique_of_disjoint hdet
    (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose_spec.1 ht]

/-- The retained-node predicate is exactly occurrence on a raw entrance
terminal trajectory. It does not assume all original nodes occur. -/
theorem to_presentation_reached_iff (v : V) :
    (T.to_presentation hpart hdet bound hterm).Reached v ↔
      ∃ x w states, x ∈ entrance w ∧ T.TerminalTrajectoryFrom w x states ∧
        v ∈ states.map Prod.fst := by
  constructor
  · rintro ⟨x, hv⟩
    exact ⟨x.val, hpart.entry x,
      (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose,
      hpart.entry_mem x,
      (hterm x.val (hpart.entry x) (hpart.entry_mem x)).choose_spec.1, hv⟩
  · rintro ⟨x, w, states, hx, ht, hv⟩
    let input : {x // x ∈ U} := ⟨x, hpart.piece_subset_source w hx⟩
    have he : hpart.entry input = w := (hpart.entry_eq_iff input w).mpr hx
    refine ⟨input, ?_⟩
    rw [T.to_presentation_path_of hpart hdet bound hterm input (he ▸ ht)]
    exact hv

/-- OET anchor: h-ced8c7236326e104
Delete precisely the unused nodes from raw data satisfying (i)–(iii).
The result has all four network conditions, even if the source is empty. -/
noncomputable def prune_redundant_nodes :
    FiniteOperatorNetwork X bot
      {v // (T.to_presentation hpart hdet bound hterm).Reached v} :=
  (T.to_presentation hpart hdet bound hterm).prune

@[simp] theorem prune_redundant_nodes_source :
    (T.prune_redundant_nodes hpart hdet bound hterm).U = U := rfl

@[simp] theorem prune_redundant_nodes_node_op
    (v : {v // (T.to_presentation hpart hdet bound hterm).Reached v}) :
    (T.prune_redundant_nodes hpart hdet bound hterm).node_op v = T.node_op v.val := rfl

/-- Every retained entry piece is the original raw entry piece. -/
@[simp] theorem prune_redundant_nodes_entry_domain
    (v : {v // (T.to_presentation hpart hdet bound hterm).Reached v}) :
    (T.prune_redundant_nodes hpart hdet bound hterm).entry_domain v = entrance v.val := by
  ext x
  constructor
  · rintro ⟨hx, he⟩
    exact (hpart.entry_eq_iff ⟨x, hx⟩ v.val).mp (congrArg Subtype.val he)
  · intro hx
    refine ⟨hpart.piece_subset_source v.val hx, Subtype.ext ?_⟩
    exact (hpart.entry_eq_iff _ v.val).mpr hx

/-- OET anchor: h-ced8c7236326e104
The full raw edge domain is preserved between any two retained nodes.
This includes edges never used by any entrance trajectory. -/
@[simp] theorem prune_redundant_nodes_edge_domain
    (v w : {v // (T.to_presentation hpart hdet bound hterm).Reached v}) :
    (T.prune_redundant_nodes hpart hdet bound hterm).edge_domain v w =
      T.edge_domain v.val w.val := by
  ext y
  change (y ∈ (T.node_op v.val).func '' dom (T.node_op v.val) ∧
    prune_choice _ T.choice_of_edges v y = .next w) ↔ y ∈ T.edge_domain v.val w.val
  rw [prune_choice_next_iff, T.choice_of_edges_next_iff hdet]
  exact ⟨And.right, fun hy => ⟨T.edge_domain_subset_node_image v.val w.val hy, hy⟩⟩

/-- The terminal domain removes only outgoing edges to retained nodes. -/
theorem prune_redundant_nodes_terminal_domain
    (v : {v // (T.to_presentation hpart hdet bound hterm).Reached v}) :
    (T.prune_redundant_nodes hpart hdet bound hterm).terminal_domain v =
      T.node_image v.val \ ⋃ w : {w // (T.to_presentation hpart hdet bound hterm).Reached w},
        T.edge_domain v.val w.val := by
  change T.node_image v.val \ ⋃ w,
      (T.prune_redundant_nodes hpart hdet bound hterm).edge_domain v w = _
  simp only [T.prune_redundant_nodes_edge_domain hpart hdet bound hterm]

/-- Removing an outgoing edge may enlarge a terminal domain, so in
particular every original terminal output remains terminal after pruning. -/
theorem terminal_domain_subset_prune_redundant_nodes
    (v : {v // (T.to_presentation hpart hdet bound hterm).Reached v}) :
    T.terminal_domain v.val ⊆
      (T.prune_redundant_nodes hpart hdet bound hterm).terminal_domain v := by
  rw [T.prune_redundant_nodes_terminal_domain hpart hdet bound hterm]
  rintro y ⟨hy, hnot⟩
  refine ⟨hy, ?_⟩
  intro hmem
  obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hmem
  exact hnot (Set.mem_iUnion.mpr ⟨w.val, hw⟩)

/-- OET anchor: h-ced8c7236326e104
Every raw complete node list is unchanged after the retained subtype labels
are projected to the original graph labels. -/
theorem prune_redundant_nodes_path_labels (x : {x // x ∈ U}) {states}
    (ht : T.TerminalTrajectoryFrom (hpart.entry x) x.val states) :
    ((T.prune_redundant_nodes hpart hdet bound hterm).path_of x).map Subtype.val =
      states.map Prod.fst := by
  exact ((T.to_presentation hpart hdet bound hterm).prune_path_labels x).trans
    (T.to_presentation_path_of hpart hdet bound hterm x ht)

private theorem state_trace_project {P : V → Prop} (p : List {v // P v}) (x : X) :
    (state_trace (fun v : {v // P v} => T.node_op v.val) p x).map
      (fun s => (s.1.val, s.2)) = state_trace T.node_op (p.map Subtype.val) x := by
  induction p generalizing x with
  | nil => rfl
  | cons v rest ih => simp only [state_trace, List.map_cons, ih]

/-- OET anchor: h-ced8c7236326e104
The entire labelled input-state trajectory is unchanged, not only its labels
or endpoint. Projection merely forgets the retained-node subtype proof. -/
theorem prune_redundant_nodes_state_trajectory (x : {x // x ∈ U}) {states}
    (ht : T.TerminalTrajectoryFrom (hpart.entry x) x.val states) :
    (state_trace (T.prune_redundant_nodes hpart hdet bound hterm).node_op
      ((T.prune_redundant_nodes hpart hdet bound hterm).path_of x) x.val).map
        (fun s => (s.1.val, s.2)) = states := by
  change (state_trace (fun v => T.node_op v.val)
    ((T.prune_redundant_nodes hpart hdet bound hterm).path_of x) x.val).map
      (fun s => (s.1.val, s.2)) = states
  rw [T.state_trace_project, T.prune_redundant_nodes_path_labels hpart hdet bound hterm x ht]
  exact (T.finite_trajectory_eq_state_trace (T.terminal_trajectory_finite ht)).symm

/-- OET anchor: h-ced8c7236326e104
The output of every raw entrance trajectory is preserved by pruning. -/
theorem prune_redundant_nodes_eval (x : {x // x ∈ U}) {states}
    (ht : T.TerminalTrajectoryFrom (hpart.entry x) x.val states) :
    (T.prune_redundant_nodes hpart hdet bound hterm).eval x =
      chain_eval_nodes_core T.node_op (states.map Prod.fst) x.val := by
  calc
    _ = chain_eval_nodes_core T.node_op
        ((T.to_presentation hpart hdet bound hterm).path_of x) x.val :=
      (T.to_presentation hpart hdet bound hterm).prune_eval x
    _ = _ := by rw [T.to_presentation_path_of hpart hdet bound hterm x ht]

/-- OET anchor: h-ced8c7236326e104
The raw presentation's absorbing-point-completed operator is exactly that
of the pruned network, on and outside the input domain. -/
theorem prune_redundant_nodes_extensional_operator :
    (T.prune_redundant_nodes hpart hdet bound hterm).extensional_operator =
      (T.to_presentation hpart hdet bound hterm).extensional_operator :=
  (T.to_presentation hpart hdet bound hterm).prune_extensional_operator_eq

/-- Empty raw input deletes every original node, without requiring the
original graph itself to be empty. -/
theorem prune_redundant_nodes_is_empty (hU : U = ∅) :
    IsEmpty {v // (T.to_presentation hpart hdet bound hterm).Reached v} := by
  refine ⟨?_⟩
  rintro ⟨v, x, _⟩
  have hx : x.val ∈ U := x.property
  simp only [hU, Set.mem_empty_iff_false] at hx

@[simp] theorem to_finite_network_source :
    (T.to_finite_network hpart hdet bound hterm hreach).U = U := rfl

@[simp] theorem to_finite_network_node_op :
    (T.to_finite_network hpart hdet bound hterm hreach).node_op = T.node_op := rfl

/-- Every entry piece, including empty ones, is preserved exactly. -/
@[simp] theorem to_finite_network_entry_domain (v : V) :
    (T.to_finite_network hpart hdet bound hterm hreach).entry_domain v = entrance v := by
  ext x
  constructor
  · rintro ⟨hx, he⟩
    exact (hpart.entry_eq_iff ⟨x, hx⟩ v).mp he
  · intro hx
    exact ⟨hpart.piece_subset_source v hx,
      (hpart.entry_eq_iff ⟨x, hpart.piece_subset_source v hx⟩ v).mpr hx⟩

/-- Raw edge domains are retained even away from all entrance trajectories. -/
@[simp] theorem to_finite_network_edge_domain (v w : V) :
    (T.to_finite_network hpart hdet bound hterm hreach).edge_domain v w =
      T.edge_domain v w := by
  ext y
  change (y ∈ (T.node_op v).func '' dom (T.node_op v) ∧
    T.choice_of_edges v y = .next w) ↔ y ∈ T.edge_domain v w
  rw [T.choice_of_edges_next_iff hdet]
  exact ⟨And.right, fun hy => ⟨T.edge_domain_subset_node_image v w hy, hy⟩⟩

/-- OET anchor: h-86752cb60c8e01e3
The import followed by forgetting is exactly the original transition graph,
including local operators and unused transition domains. -/
@[simp] theorem to_finite_network_transition_graph :
    (T.to_finite_network hpart hdet bound hterm hreach).to_transition_graph = T := by
  have hedges :
      (T.to_finite_network hpart hdet bound hterm hreach).to_transition_graph.edge_domain =
        T.edge_domain := by
    funext v w
    exact T.to_finite_network_edge_domain hpart hdet bound hterm hreach v w
  cases T
  simp only [FiniteOperatorNetwork.to_transition_graph, to_finite_network,
    FiniteNetworkPresentation.to_finite_network, to_presentation] at hedges ⊢
  congr 1

/-- Each supplied terminal trajectory becomes the stored complete node list;
thus the arbitrary choice of termination witnesses does not alter paths. -/
theorem to_finite_network_path_of (x : {x // x ∈ U}) {states}
    (ht : T.TerminalTrajectoryFrom (hpart.entry x) x.val states) :
    (T.to_finite_network hpart hdet bound hterm hreach).path_of x =
      states.map Prod.fst := by
  exact T.to_presentation_path_of hpart hdet bound hterm x ht

end OperatorTransitionGraph
end formal_oet.vol_01.ch_05_operator_networks
