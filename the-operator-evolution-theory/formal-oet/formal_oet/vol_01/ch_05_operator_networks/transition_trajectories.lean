import formal_oet.vol_01.ch_05_operator_networks.network_routing

namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations
variable {X V : Type} {bot : X}

/-- The input state at every occurrence of a node in a specified node list.
This operation does not assert that the listed transitions are permitted. -/
def state_trace (op : V → Operator X bot) : List V → X → List (V × X)
  | [], _ => []
  | v :: rest, x => (v, x) :: state_trace op rest ((op v).func x)

@[simp] theorem state_trace_nodes (op : V → Operator X bot) (p : List V) (x : X) :
    (state_trace op p x).map Prod.fst = p := by
  induction p generalizing x with
  | nil => rfl
  | cons v rest ih => simp [state_trace, ih]

@[simp] theorem state_trace_length (op : V → Operator X bot) (p : List V) (x : X) :
    (state_trace op p x).length = p.length := by
  simpa only [List.length_map] using congrArg List.length (state_trace_nodes op p x)

namespace OperatorTransitionGraph
variable (T : OperatorTransitionGraph X bot V)

/-- OET anchor: h-86752cb60c8e01e3
A finite trajectory records node-labelled input states. A singleton has
length one and no transition; every extension uses the graph's actual Step.
Neither deterministic routing nor termination is assumed. -/
inductive FiniteTrajectoryFrom : V → X → List (V × X) → Prop where
  | single {v : V} {x : X} (hx : x ∈ T.node_dom v) :
      FiniteTrajectoryFrom v x [(v, x)]
  | next {v w : V} {x y : X} {rest : List (V × X)}
      (step : T.Step v w x y) (tail : FiniteTrajectoryFrom w y rest) :
      FiniteTrajectoryFrom v x ((v, x) :: rest)

/-- OET anchor: h-86752cb60c8e01e3
A terminal trajectory ends precisely when the last node output belongs to
that node's terminal domain. It may be one of several possible trajectories. -/
inductive TerminalTrajectoryFrom : V → X → List (V × X) → Prop where
  | stop {v : V} {x : X} (hx : x ∈ T.node_dom v)
      (terminal : (T.node_op v).func x ∈ T.terminal_domain v) :
      TerminalTrajectoryFrom v x [(v, x)]
  | next {v w : V} {x y : X} {rest : List (V × X)}
      (step : T.Step v w x y) (tail : TerminalTrajectoryFrom w y rest) :
      TerminalTrajectoryFrom v x ((v, x) :: rest)

theorem finite_trajectory_nonempty {v x states}
    (h : T.FiniteTrajectoryFrom v x states) : states ≠ [] := by
  cases h <;> simp

theorem finite_trajectory_head {v x states}
    (h : T.FiniteTrajectoryFrom v x states) : states.head? = some (v, x) := by
  cases h <;> rfl

theorem finite_trajectory_length_pos {v x states}
    (h : T.FiniteTrajectoryFrom v x states) : 0 < states.length := by
  cases h <;> simp

theorem finite_trajectory_states_valid {v x states}
    (h : T.FiniteTrajectoryFrom v x states) :
    ∀ s ∈ states, s.2 ∈ T.node_dom s.1 := by
  induction h with
  | single hx => simpa using hx
  | next step tail ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact step.1
    · exact ih s hs

/-- Two-state trajectories are exactly the previously defined labelled Step. -/
theorem finite_trajectory_two_iff (v w : V) (x y : X) :
    T.FiniteTrajectoryFrom v x [(v, x), (w, y)] ↔ T.Step v w x y := by
  constructor
  · intro h
    cases h with
    | next step tail =>
      cases tail with
      | single => exact step
      | next _ tail => exact False.elim ((T.finite_trajectory_nonempty tail) rfl)
  · intro h
    exact .next h (.single (T.edge_domain_subset_node_dom v w h.2.2))

theorem terminal_trajectory_finite {v x states}
    (h : T.TerminalTrajectoryFrom v x states) : T.FiniteTrajectoryFrom v x states := by
  induction h with
  | stop hx _ => exact .single hx
  | next step _ ih => exact .next step ih

/-- This equivalence relates the inductive terminal condition to the book's
last-state definition, including the singleton boundary case. -/
theorem terminal_trajectory_iff_finite_and_last {v x states} :
    T.TerminalTrajectoryFrom v x states ↔
      T.FiniteTrajectoryFrom v x states ∧
      ∃ w y, states.getLast? = some (w, y) ∧
        (T.node_op w).func y ∈ T.terminal_domain w := by
  constructor
  · intro h
    refine ⟨T.terminal_trajectory_finite h, ?_⟩
    induction h with
    | stop hx ht => exact ⟨_, _, rfl, ht⟩
    | @next v w x y rest step tail ih =>
      obtain ⟨w, y, hlast, ht⟩ := ih
      refine ⟨w, y, ?_, ht⟩
      cases hrest : rest with
      | nil =>
        exact False.elim ((T.finite_trajectory_nonempty
          (T.terminal_trajectory_finite tail)) hrest)
      | cons a rest => simpa [hrest] using hlast
  · rintro ⟨hfinite, hlast⟩
    induction hfinite with
    | @single v x hx =>
      obtain ⟨w, y, hlast, ht⟩ := hlast
      have heq : (v, x) = (w, y) := by simpa using hlast
      cases heq
      exact .stop hx ht
    | @next v w x y rest step tail ih =>
      apply TerminalTrajectoryFrom.next step
      apply ih
      cases rest with
      | nil => exact False.elim ((T.finite_trajectory_nonempty tail) rfl)
      | cons a rest => simpa using hlast

/-- State values are forced by the local operators once a node list and its
initial input are fixed, even when successor selection is nondeterministic. -/
theorem finite_trajectory_eq_state_trace {v x states}
    (h : T.FiniteTrajectoryFrom v x states) :
    states = state_trace T.node_op (states.map Prod.fst) x := by
  induction h with
  | single => rfl
  | @next v w x y rest step tail ih =>
    simp only [List.map_cons, state_trace]
    congr 1
    rw [← step.2.1]
    exact ih
end OperatorTransitionGraph

namespace FiniteOperatorNetwork
variable (N : FiniteOperatorNetwork X bot V)

/-- The derived deterministic graph has exactly the operational steps of
its choice map; the target value remains explicitly part of the state. -/
theorem graph_step_iff {v w : V} {x y : X} :
    N.to_transition_graph.Step v w x y ↔
      x ∈ dom (N.node_op v) ∧ y = (N.node_op v).func x ∧
        N.choice v y = .next w := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  · rintro ⟨hx, rfl, hc⟩
    exact ⟨hx, rfl, ⟨x, hx, rfl⟩, hc⟩

theorem graph_terminal_iff_stop {v : V} {x : X} (hx : x ∈ dom (N.node_op v)) :
    (N.node_op v).func x ∈ N.to_transition_graph.terminal_domain v ↔
      N.choice v ((N.node_op v).func x) = .stop := by
  constructor
  · intro ht
    cases hc : N.choice v ((N.node_op v).func x) with
    | stop => rfl
    | next w =>
      exact False.elim (ht.2 (Set.mem_iUnion.mpr
        ⟨w, ⟨x, hx, rfl⟩, hc⟩))
  · intro hc
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    intro hmem
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp hmem
    have hnext := hw.2
    simp [hc] at hnext

/-- Every complete deterministic node path expands to an actual terminal
trajectory in the underlying transition graph. -/
theorem terminal_path_to_graph_trajectory {v x p}
    (h : TerminalPathFrom N.node_op N.choice v x p)
    (hx : x ∈ dom (N.node_op v)) :
    N.to_transition_graph.TerminalTrajectoryFrom v x (state_trace N.node_op p x) := by
  induction h with
  | stop hs =>
    exact .stop hx ((N.graph_terminal_iff_stop hx).mpr hs)
  | next hs tail ih =>
    exact .next (N.graph_step_iff.mpr ⟨hx, rfl, hs⟩)
      (ih (N.choice_next_mem hx hs))

/-- Conversely, every actual graph-terminal trajectory follows the unique
choice map, so projecting node labels gives `TerminalPathFrom`. -/
theorem graph_trajectory_to_terminal_path {v x states}
    (h : N.to_transition_graph.TerminalTrajectoryFrom v x states) :
    TerminalPathFrom N.node_op N.choice v x (states.map Prod.fst) := by
  induction h with
  | stop hx ht => exact .stop ((N.graph_terminal_iff_stop hx).mp ht)
  | next step tail ih =>
    obtain ⟨hx, heq, hchoice⟩ := N.graph_step_iff.mp step
    rw [heq] at hchoice ih
    exact .next hchoice ih

/-- OET anchor: h-86752cb60c8e01e3
The deterministic representation agrees in both directions with the general
transition-graph notion on every valid starting state, not only entrances. -/
theorem terminal_path_iff_graph_trajectory {v x p}
    (hx : x ∈ dom (N.node_op v)) :
    TerminalPathFrom N.node_op N.choice v x p ↔
      N.to_transition_graph.TerminalTrajectoryFrom v x (state_trace N.node_op p x) := by
  constructor
  · exact fun h => N.terminal_path_to_graph_trajectory h hx
  · intro h
    simpa using N.graph_trajectory_to_terminal_path h

/-- Every prescribed entrance path is a terminal trajectory in the general
transition-graph sense, with exactly the same occurrence count. -/
theorem path_of_graph_terminal_trajectory (x : {x // x ∈ N.U}) :
    N.to_transition_graph.TerminalTrajectoryFrom (N.entry x) x.val
      (state_trace N.node_op (N.path_of x) x.val) :=
  N.terminal_path_to_graph_trajectory (N.path_terminal x) (N.entry_mem x)

/-- Choice determinism implies uniqueness of the full node-labelled state
trajectory, rather than merely uniqueness of its projected node list. -/
theorem graph_terminal_trajectory_unique {v x states states'}
    (h : N.to_transition_graph.TerminalTrajectoryFrom v x states)
    (h' : N.to_transition_graph.TerminalTrajectoryFrom v x states') : states = states' := by
  have hp := terminal_path_unique
    (N.graph_trajectory_to_terminal_path h) (N.graph_trajectory_to_terminal_path h')
  rw [N.to_transition_graph.finite_trajectory_eq_state_trace
      (N.to_transition_graph.terminal_trajectory_finite h),
    N.to_transition_graph.finite_trajectory_eq_state_trace
      (N.to_transition_graph.terminal_trajectory_finite h')]
  rw [hp]
end FiniteOperatorNetwork

end formal_oet.vol_01.ch_05_operator_networks
