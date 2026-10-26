import formal_oet.vol_01.ch_05_operator_networks.transition_trajectories
import formal_oet.vol_01.ch_05_operator_networks.network_relabeling
import Mathlib.Data.Real.Sqrt

namespace formal_oet.vol_01.ch_05_operator_networks.five_node_examples

open formal_oet.vol_01.ch_01_foundations
open FiniteOperatorNetwork

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- The labels correspond in order to beta one through beta five. -/
inductive Node | first | second | third | fourth | fifth
  deriving DecidableEq, Fintype
open Node

abbrev Point := Option ℝ

def lift_operator (f : ℝ → ℝ) : Operator Point none := ⟨Option.map f, rfl⟩
def real_domain : Set Point := Set.range some

def node_operator : Node → Operator Point none
  | first => lift_operator id
  | second => lift_operator (fun x => 1 - x)
  | third => lift_operator id
  | fourth => lift_operator (fun x => x - 1)
  | fifth => lift_operator (fun x => x ^ 2)

@[simp] theorem dom_lift_operator (f : ℝ → ℝ) : dom (lift_operator f) = real_domain := by
  ext x
  cases x <;> simp [dom, lift_operator, real_domain]

@[simp] theorem dom_node_operator (v : Node) : dom (node_operator v) = real_domain := by
  cases v <;> exact dom_lift_operator _

private theorem real_output (v : Node) (x : ℝ) :
    (node_operator v).func (some x) ∈ real_domain := by
  cases v <;> simp [node_operator, lift_operator, real_domain]

private theorem local_next_mem (v w : Node) {x : Point}
    (hx : x ∈ dom (node_operator v)) : (node_operator v).func x ∈ dom (node_operator w) := by
  rw [dom_node_operator] at hx ⊢
  obtain ⟨x, rfl⟩ := hx
  exact real_output v x

def source : Set Point := {some (-2), some (-1), some 1, some 2, some 3}

def routing : Node → Point → OutputChoice Node
  | first, some y => if y < 0 then .next second else .next third
  | second, some _ => .next fourth
  | third, some y => if y < 2 then .next fourth else .next fifth
  | fourth, some y => if 0 < y then .next fourth else .next fifth
  | _, _ => .stop

def input_path (x : Point) : List Node :=
  if x = some (-2) then [first, second, fourth, fourth, fourth, fifth]
  else if x = some (-1) then [first, second, fourth, fourth, fifth]
  else if x = some 1 then [first, third, fourth, fifth]
  else if x = some 2 then [first, third, fifth]
  else [fourth, fourth, fourth, fifth]

def input_entry (x : Point) : Node := if x = some 3 then fourth else first

private theorem terminal_input_path {x : Point} (hx : x ∈ source) :
    TerminalPathFrom node_operator routing (input_entry x) x (input_path x) := by
  simp only [source, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [input_entry, input_path]
  all_goals
    repeat' first | apply TerminalPathFrom.stop | apply TerminalPathFrom.next
  all_goals norm_num [routing, node_operator, lift_operator]

/-- OET anchor: h-55d2487a68b2728e
The five-node network has precisely the five displayed inputs and preserves
all seven graph edges, including the loop at the fourth node. -/
def network : FiniteOperatorNetwork Point none Node where
  U := source
  bot_not_mem := by simp [source]
  node_fintype := inferInstance
  node_op := node_operator
  node_dom_nonempty := by intro v; rw [dom_node_operator]; exact ⟨some 0, 0, rfl⟩
  entry := fun x => input_entry x.val
  entry_mem := by
    rintro ⟨x, hx⟩
    rw [dom_node_operator]
    simp only [source, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [real_domain]
  choice := routing
  choice_next_mem := by intro v w x hx _; exact local_next_mem v w hx
  depth_bound := 6
  path_of := fun x => input_path x.val
  path_terminal := fun x => terminal_input_path x.property
  path_length_le_depth := by intro x; unfold input_path; split_ifs <;> simp
  node_reachable := by
    intro v
    cases v
    · exact ⟨⟨some (-2), by simp [source]⟩, by norm_num [input_path]⟩
    · exact ⟨⟨some (-2), by simp [source]⟩, by norm_num [input_path]⟩
    · exact ⟨⟨some 1, by simp [source]⟩, by norm_num [input_path]⟩
    · exact ⟨⟨some (-2), by simp [source]⟩, by norm_num [input_path]⟩
    · exact ⟨⟨some (-2), by simp [source]⟩, by norm_num [input_path]⟩

/-- OET anchor: h-55d2487a68b2728e
The paths for the inputs minus two, minus one, one, two, and three. -/
theorem five_input_paths :
    [input_path (some (-2)), input_path (some (-1)), input_path (some 1),
      input_path (some 2), input_path (some 3)] =
    [[first, second, fourth, fourth, fourth, fifth],
      [first, second, fourth, fourth, fifth], [first, third, fourth, fifth],
      [first, third, fifth], [fourth, fourth, fourth, fifth]] := by
  norm_num [input_path]

/-- OET anchor: h-55d2487a68b2728e
All five terminal outputs, in the same order as the displayed input set. -/
theorem five_input_outputs :
    [network.eval ⟨some (-2), by simp [network, source]⟩,
      network.eval ⟨some (-1), by simp [network, source]⟩,
      network.eval ⟨some 1, by simp [network, source]⟩,
      network.eval ⟨some 2, by simp [network, source]⟩,
      network.eval ⟨some 3, by simp [network, source]⟩] =
    [some 0, some 0, some 0, some 4, some 0] := by
  change [chain_eval_nodes_core node_operator (input_path (some (-2))) (some (-2)),
    chain_eval_nodes_core node_operator (input_path (some (-1))) (some (-1)),
    chain_eval_nodes_core node_operator (input_path (some 1)) (some 1),
    chain_eval_nodes_core node_operator (input_path (some 2)) (some 2),
    chain_eval_nodes_core node_operator (input_path (some 3)) (some 3)] = _
  norm_num [input_path, chain_eval_nodes_core, node_operator, lift_operator]

/-- OET anchor: h-55d2487a68b2728e
Length counts node occurrences, so three visits to beta four count separately. -/
theorem five_input_lengths :
    ([input_path (some (-2)), input_path (some (-1)), input_path (some 1),
      input_path (some 2), input_path (some 3)].map List.length) = [6, 5, 4, 3, 4] := by
  rw [five_input_paths]
  rfl

/-- OET anchor: h-55d2487a68b2728e
The bound six is attained, not just a chosen termination bound. -/
theorem network_evaluation_depth : network.evaluation_depth = 6 := by
  apply Nat.le_antisymm
  · exact network.evaluation_depth_le_of_input_lengths 6 network.path_length_le_depth
  · have h := network.input_path_length_le_evaluation_depth
      ⟨some (-2), by simp [network, source]⟩
    simpa [network, input_path] using h

/-- OET anchor: h-e196bfe1748b5dfe
The full state trace behind the expanded chain shown under the network. -/
theorem negative_two_state_trace :
    state_trace node_operator (input_path (some (-2))) (some (-2)) =
      [(first, some (-2)), (second, some (-2)), (fourth, some 3),
        (fourth, some 2), (fourth, some 1), (fifth, some 0)] := by
  norm_num [input_path, state_trace, node_operator, lift_operator]

/-- OET anchor: h-e196bfe1748b5dfe
The six-occurrence path drawn in the chain figure occurs exactly at input minus two. -/
theorem negative_two_path_domain :
    network.path_domain (input_path (some (-2))) = {some (-2)} := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    change input_path x = input_path (some (-2)) at hp
    simp only [network, source, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · rfl
    all_goals norm_num [input_path] at hp <;> simp at hp
  · rintro rfl
    exact ⟨by simp [network, source], rfl⟩

/-- OET anchor: h-e196bfe1748b5dfe
The drawn chain computes square after three decrements after one minus x. -/
theorem negative_two_path_chain (x : ℝ) :
    (network.path_chain (input_path (some (-2)))).func (some x) =
      some ((((1 - x) - 1) - 1 - 1) ^ 2) := by
  rw [network.path_chain_apply_eq_chain_eval_nodes]
  norm_num [network, input_path, FiniteOperatorNetwork.chain_eval_nodes,
    chain_eval_nodes_core, node_operator, lift_operator]

private theorem some_mem_node_image (v : Node) (hv : v ≠ fifth) (y : ℝ) :
    some y ∈ (node_operator v).func '' dom (node_operator v) := by
  rw [dom_node_operator]
  cases v
  · exact ⟨some y, ⟨y, rfl⟩, rfl⟩
  · refine ⟨some (1 - y), ⟨1 - y, rfl⟩, ?_⟩
    simp [node_operator, lift_operator]
  · exact ⟨some y, ⟨y, rfl⟩, rfl⟩
  · refine ⟨some (y + 1), ⟨y + 1, rfl⟩, ?_⟩
    simp [node_operator, lift_operator]
  · exact (hv rfl).elim

/-- Output-side edge conditions in the deterministic finite-network figure. -/
def network_condition : Node → Node → ℝ → Prop
  | first, second, y => y < 0
  | first, third, y => 0 ≤ y
  | second, fourth, _ => True
  | third, fourth, y => y < 2
  | third, fifth, y => 2 ≤ y
  | fourth, fourth, y => 0 < y
  | fourth, fifth, y => y ≤ 0
  | _, _, _ => False

private theorem routing_eq_next_iff (v w : Node) (y : ℝ) :
    routing v (some y) = .next w ↔ network_condition v w y := by
  cases v <;> cases w <;> simp [routing, network_condition] <;>
    split_ifs <;> simp_all

/-- OET anchor: h-55d2487a68b2728e
All deterministic edge domains agree exactly with the figure, including empty
pairs; they are not merely correct on the five chosen evaluations. -/
theorem network_edge_domains (v w : Node) :
    network.edge_domain v w = some '' {y | network_condition v w y} := by
  ext z
  change (z ∈ (node_operator v).func '' dom (node_operator v) ∧
    routing v z = .next w) ↔ _
  cases z with
  | none => cases v <;> simp [routing]
  | some y =>
    simp only [Set.mem_image, Set.mem_setOf_eq, Option.some.injEq, exists_eq_right]
    rw [routing_eq_next_iff]
    constructor
    · exact And.right
    · intro h
      refine ⟨some_mem_node_image v ?_ y, h⟩
      rintro rfl
      cases w <;> exact h

/-- OET anchor: h-55d2487a68b2728e
The only entry pieces are the four displayed inputs at beta one and three at beta four. -/
theorem network_entry_domains (v : Node) :
    network.entry_domain v = match v with
      | first => {some (-2), some (-1), some 1, some 2}
      | fourth => {some 3}
      | _ => ∅ := by
  cases v <;> ext x <;>
    simp only [FiniteOperatorNetwork.entry_domain, network, Set.mem_setOf_eq]
  all_goals
    simp only [source, Set.mem_insert_iff, Set.mem_singleton_iff, input_entry]
    split_ifs with h <;> simp_all
  all_goals norm_num at *

private theorem square_image :
    (node_operator fifth).func '' dom (node_operator fifth) = some '' Set.Ici (0 : ℝ) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [dom_node_operator] at hx
    obtain ⟨x, rfl⟩ := hx
    exact ⟨x ^ 2, sq_nonneg x, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨some (Real.sqrt y), ?_, ?_⟩
    · rw [dom_node_operator]; exact ⟨Real.sqrt y, rfl⟩
    · simp [node_operator, lift_operator, Real.sq_sqrt hy]

/-- OET anchor: h-55d2487a68b2728e
The square node's displayed termination domain is the entire nonnegative half-line. -/
theorem network_fifth_terminal_domain :
    network.terminal_domain fifth = some '' Set.Ici (0 : ℝ) := by
  change ((node_operator fifth).func '' dom (node_operator fifth)) \
    (⋃ w, network.edge_domain fifth w) = _
  rw [square_image]
  have hempty : (⋃ w, network.edge_domain fifth w) = ∅ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_exists]
    intro w
    rw [network_edge_domains]
    cases w <;> simp [network_condition]
  rw [hempty, Set.diff_empty]

/-- Output-side edge conditions in the nondeterministic transfer figure. -/
def transfer_condition : Node → Node → ℝ → Prop
  | first, second, y => y ≤ 1
  | first, third, y => -1 ≤ y
  | second, fourth, _ => True
  | third, fourth, y => y < 2
  | third, fifth, y => 2 ≤ y
  | fourth, fourth, _ => True
  | fourth, fifth, y => y ≤ 0
  | _, _, _ => False

/-- OET anchor: h-5b2a52dbf74952d6
A concrete raw transition graph with the seven displayed edges and real local domains.
OET anchor: h-f308ed879c3ceea5
Its edge domains permit branching and an indefinitely repeatable loop. -/
def transfer_graph : OperatorTransitionGraph Point none Node where
  node_fintype := inferInstance
  node_op := node_operator
  node_dom_nonempty := by intro v; rw [dom_node_operator]; exact ⟨some 0, 0, rfl⟩
  edge_domain := fun v w => some '' {y | transfer_condition v w y}
  edge_domain_subset_node_image := by
    rintro v w _ ⟨y, hy, rfl⟩
    apply some_mem_node_image v _ y
    rintro rfl
    cases w <;> exact hy
  edge_domain_subset_node_dom := by
    rintro v w _ ⟨y, _, rfl⟩
    rw [dom_node_operator]
    exact ⟨y, rfl⟩

def drawn_edges : Finset (Node × Node) :=
  {(first, second), (first, third), (second, fourth), (third, fourth),
    (third, fifth), (fourth, fourth), (fourth, fifth)}

/-- OET anchor: h-5b2a52dbf74952d6
The raw example has exactly the drawn branch, merging edges, and self-loop. -/
theorem transfer_graph_edges (v w : Node) :
    transfer_graph.Edge v w ↔ (v, w) ∈ drawn_edges := by
  cases v <;> cases w <;>
    simp [OperatorTransitionGraph.Edge, transfer_graph, transfer_condition,
      drawn_edges, Set.nonempty_def]
  · exact ⟨0, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨2, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- OET anchor: h-55d2487a68b2728e
Changing the edge domains as displayed preserves the entire underlying graph. -/
theorem network_same_underlying_graph (v w : Node) :
    network.to_transition_graph.Edge v w ↔ transfer_graph.Edge v w := by
  rw [transfer_graph_edges]
  change (network.edge_domain v w).Nonempty ↔ _
  rw [network_edge_domains]
  cases v <;> cases w <;>
    simp [network_condition, drawn_edges, Set.nonempty_def]
  · exact ⟨-1, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨0, by norm_num⟩
  · exact ⟨2, by norm_num⟩
  · exact ⟨1, by norm_num⟩
  · exact ⟨0, by norm_num⟩

/-- OET anchor: h-f308ed879c3ceea5
The terminal half-line drawn at beta five is unchanged in the raw transfer graph. -/
theorem transfer_fifth_terminal_domain :
    transfer_graph.terminal_domain fifth = some '' Set.Ici (0 : ℝ) := by
  change ((node_operator fifth).func '' dom (node_operator fifth)) \
    (⋃ w, transfer_graph.edge_domain fifth w) = _
  rw [square_image]
  have hempty : (⋃ w, transfer_graph.edge_domain fifth w) = ∅ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_empty_iff_false, iff_false, not_exists]
    intro w
    cases w <;> simp [transfer_graph, transfer_condition]
  rw [hempty, Set.diff_empty]

/-- OET anchor: h-f308ed879c3ceea5
The first displayed input admits two distinct legal next nodes. -/
theorem two_successors :
    transfer_graph.Step first second (some 1) (some 1) ∧
      transfer_graph.Step first third (some 1) (some 1) ∧ second ≠ third := by
  norm_num [OperatorTransitionGraph.Step, OperatorTransitionGraph.node_dom,
    transfer_graph, node_operator, lift_operator, real_domain, transfer_condition, dom]; simp

private theorem transfer_loop_step (x : ℝ) :
    transfer_graph.Step fourth fourth (some x) (some (x - 1)) := by
  norm_num [OperatorTransitionGraph.Step, OperatorTransitionGraph.node_dom,
    transfer_graph, node_operator, lift_operator, real_domain, transfer_condition, dom]; simp

/-- OET anchor: h-f308ed879c3ceea5
At beta four the stream one, zero, minus one, ... never exhausts legal loop steps. -/
theorem infinite_loop_steps (n : ℕ) :
    transfer_graph.Step fourth fourth (some (1 - (n : ℝ)))
      (some (1 - ((n + 1 : ℕ) : ℝ))) := by
  convert transfer_loop_step (1 - (n : ℝ)) using 1; simp only [Nat.cast_add, Nat.cast_one, sub_add_eq_sub_sub]

def loop_states : ℕ → ℝ → List (Node × Point)
  | 0, x => [(fourth, some x)]
  | n + 1, x => (fourth, some x) :: loop_states n (x - 1)

private theorem loop_states_legal (n : ℕ) (x : ℝ) :
    transfer_graph.FiniteTrajectoryFrom fourth (some x) (loop_states n x) := by
  induction n generalizing x with
  | zero =>
    apply OperatorTransitionGraph.FiniteTrajectoryFrom.single
    simp [OperatorTransitionGraph.node_dom, transfer_graph, node_operator, lift_operator, dom]
  | succ n ih =>
    exact .next (transfer_loop_step x) (ih (x - 1))

@[simp] theorem loop_states_length (n : ℕ) (x : ℝ) : (loop_states n x).length = n + 1 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [loop_states, ih]

/-- OET anchor: h-f308ed879c3ceea5
Arbitrarily long legal trajectories start at the figure's fixed input state. -/
theorem arbitrarily_long_trajectories (n : ℕ) :
    ∃ states, transfer_graph.FiniteTrajectoryFrom first (some 1) states ∧
      states.length = n + 3 := by
  refine ⟨(first, some 1) :: (third, some 1) :: loop_states n 1, ?_, by simp⟩
  apply OperatorTransitionGraph.FiniteTrajectoryFrom.next two_successors.2.1
  apply OperatorTransitionGraph.FiniteTrajectoryFrom.next (w := fourth) (y := some 1)
  · norm_num [OperatorTransitionGraph.Step, OperatorTransitionGraph.node_dom,
      transfer_graph, node_operator, lift_operator, real_domain, transfer_condition, dom]; simp
  · exact loop_states_legal n 1

private theorem fifth_terminal (x : ℝ) :
    (node_operator fifth).func (some x) ∈ transfer_graph.terminal_domain fifth := by
  constructor
  · exact ⟨some x, by simp [OperatorTransitionGraph.node_dom, transfer_graph,
      node_operator, lift_operator, dom], rfl⟩
  · simp only [Set.mem_iUnion, not_exists]
    intro w
    cases w <;> simp [transfer_graph, transfer_condition]

/-- OET anchor: h-f308ed879c3ceea5
At each nonpositive fourth-node output, the fifth node gives a terminal branch. -/
theorem terminal_branch (x : ℝ) (hx : x - 1 ≤ 0) :
    transfer_graph.TerminalTrajectoryFrom fourth (some x)
      [(fourth, some x), (fifth, some (x - 1))] := by
  apply OperatorTransitionGraph.TerminalTrajectoryFrom.next (w := fifth) (y := some (x - 1))
  · norm_num [OperatorTransitionGraph.Step, OperatorTransitionGraph.node_dom,
      transfer_graph, node_operator, lift_operator, real_domain, transfer_condition, dom, hx]; simp
  · exact .stop (by simp [OperatorTransitionGraph.node_dom, transfer_graph,
      node_operator, lift_operator, dom]) (fifth_terminal (x - 1))

/-- OET anchor: h-f308ed879c3ceea5
Choosing beta three and then the exit from beta four terminates from the same state
that also admits arbitrarily long loop trajectories. -/
theorem displayed_input_terminal_trajectory :
    transfer_graph.TerminalTrajectoryFrom first (some 1)
      [(first, some 1), (third, some 1), (fourth, some 1), (fifth, some 0)] := by
  apply OperatorTransitionGraph.TerminalTrajectoryFrom.next two_successors.2.1
  apply OperatorTransitionGraph.TerminalTrajectoryFrom.next (w := fourth) (y := some 1)
  · norm_num [OperatorTransitionGraph.Step, OperatorTransitionGraph.node_dom,
      transfer_graph, node_operator, lift_operator, real_domain, transfer_condition, dom]; simp
  · simpa using terminal_branch 1 (by norm_num)

end
end formal_oet.vol_01.ch_05_operator_networks.five_node_examples
