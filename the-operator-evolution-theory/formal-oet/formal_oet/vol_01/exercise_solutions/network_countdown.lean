import formal_oet.vol_01.ch_05_operator_networks.transition_trajectories

namespace formal_oet.vol_01.exercise_solutions.network_countdown

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks

/-- CH5 习题“逐点终止与统一有限终止”：`none` is the absorbing point;
the normal state `some n` is sent to `some (n - 1)`. -/
def decrement : Operator (Option Nat) none where
  func := Option.map (fun n => n - 1)
  preserves_bot := rfl

def route : Unit → Option Nat → OutputChoice Unit
  | _, some (_ + 1) => .next ()
  | _, _ => .stop

def positive_source : Set (Option Nat)
  | some n => 0 < n
  | none => False

def bounded_source (m : Nat) : Set (Option Nat)
  | some n => 1 ≤ n ∧ n ≤ m
  | none => False

@[simp] theorem none_not_mem_positive_source : none ∉ positive_source := fun h => h

@[simp] theorem some_mem_positive_source (n : Nat) :
    some n ∈ positive_source ↔ 0 < n := Iff.rfl

@[simp] theorem none_not_mem_bounded_source (m : Nat) :
    none ∉ bounded_source m := fun h => h

@[simp] theorem some_mem_bounded_source (m n : Nat) :
    some n ∈ bounded_source m ↔ 1 ≤ n ∧ n ≤ m := Iff.rfl

@[simp] theorem decrement_some (n : Nat) :
    decrement.func (some n) = some (n - 1) := rfl

@[simp] theorem some_mem_dom_decrement (n : Nat) : some n ∈ dom decrement := by
  simp [dom, decrement]

/-- This is a terminal path for the actual routing rule, not merely a
sequence of arithmetic iterates. -/
theorem terminal_path (n : Nat) (hn : 0 < n) :
    TerminalPathFrom (fun _ : Unit => decrement) route () (some n)
      (List.replicate n ()) := by
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero => exact .stop rfl
      | succ n =>
          simpa [List.replicate_succ, decrement, route] using
            (TerminalPathFrom.next (β := ()) (γ := ())
              (y := some (n + 2)) (by rfl) (ih (by omega)))

theorem terminal_path_eq (n : Nat) (hn : 0 < n) {p : List Unit}
    (hp : TerminalPathFrom (fun _ : Unit => decrement) route () (some n) p) :
    p = List.replicate n () :=
  terminal_path_unique hp (terminal_path n hn)

theorem chain_output (n : Nat) :
    chain_eval_nodes_core (fun _ : Unit => decrement)
      (List.replicate n ()) (some n) = some 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [List.replicate_succ, chain_eval_nodes_core, decrement] using ih

/-- OET anchor: h-96bb1a4734f21c32
A genuine finite network on precisely the entrance states `1, ..., m`.
All path, transition-validity and nonredundancy obligations are proved here. -/
def finite_network (m : Nat) (hm : 1 ≤ m) :
    FiniteOperatorNetwork (Option Nat) none Unit where
  U := bounded_source m
  bot_not_mem := none_not_mem_bounded_source m
  node_fintype := inferInstance
  node_op := fun _ => decrement
  node_dom_nonempty := fun _ => ⟨some 0, some_mem_dom_decrement 0⟩
  entry := fun _ => ()
  entry_mem := by
    rintro ⟨x, hx⟩
    cases x with
    | none => exact False.elim hx
    | some n => exact some_mem_dom_decrement n
  choice := route
  choice_next_mem := by
    intro v w y hy _
    cases y with
    | none => simp [dom, decrement] at hy
    | some n => exact some_mem_dom_decrement (n - 1)
  depth_bound := m
  path_of := fun x => List.replicate (x.val.getD 0) ()
  path_terminal := by
    rintro ⟨x, hx⟩
    cases x with
    | none => exact False.elim hx
    | some n => exact terminal_path n hx.1
  path_length_le_depth := by
    rintro ⟨x, hx⟩
    cases x with
    | none => exact False.elim hx
    | some n => simpa using hx.2
  node_reachable := by
    intro v
    cases v
    exact ⟨⟨some 1, ⟨le_refl 1, hm⟩⟩, by simp⟩

/-- The underlying transition graph does not depend on the chosen finite
entrance truncation. Its local domain and self-loop domain remain unbounded. -/
def countdown_graph : OperatorTransitionGraph (Option Nat) none Unit :=
  (finite_network 1 (by omega)).to_transition_graph

theorem finite_network_graph (m : Nat) (hm : 1 ≤ m) :
    (finite_network m hm).to_transition_graph = countdown_graph := rfl

theorem graph_edge_domain : countdown_graph.edge_domain () () = positive_source := by
  ext x
  cases x with
  | none => simp [countdown_graph, finite_network,
      FiniteOperatorNetwork.to_transition_graph, route]
  | some n =>
      cases n with
      | zero => simp [countdown_graph, finite_network,
          FiniteOperatorNetwork.to_transition_graph, route]
      | succ n =>
          change ((some (n + 1) ∈ decrement.func '' dom decrement) ∧
            OutputChoice.next () = OutputChoice.next ()) ↔ 0 < n + 1
          constructor
          · intro _; omega
          · intro _
            exact ⟨⟨some (n + 2), some_mem_dom_decrement _, by simp⟩, rfl⟩

theorem graph_node_domain : countdown_graph.node_dom () = Set.range some := by
  ext x
  cases x <;> simp [countdown_graph, finite_network,
    FiniteOperatorNetwork.to_transition_graph, OperatorTransitionGraph.node_dom,
    dom, decrement]

theorem graph_node_image : countdown_graph.node_image () = Set.range some := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    cases y with
    | none =>
        rw [graph_node_domain] at hy
        simp at hy
    | some n => exact ⟨n - 1, rfl⟩
  · rintro ⟨n, rfl⟩
    exact ⟨some (n + 1), some_mem_dom_decrement _, by simp [countdown_graph,
      finite_network, FiniteOperatorNetwork.to_transition_graph]⟩

theorem graph_terminal_domain : countdown_graph.terminal_domain () = {some 0} := by
  have hedge : ∀ v : Unit, countdown_graph.edge_domain () v = positive_source := by
    intro v
    cases v
    exact graph_edge_domain
  ext x
  cases x with
  | none => simp [OperatorTransitionGraph.terminal_domain, graph_node_image, hedge]
  | some n =>
      simp [OperatorTransitionGraph.terminal_domain, graph_node_image, hedge]

/-- The general graph trajectory relation is witnessed by the actual state
trace. The finite-network bridge is valid at every normal starting state,
not only at that auxiliary network's entrance. -/
theorem graph_terminal_trajectory (n : Nat) (hn : 0 < n) :
    countdown_graph.TerminalTrajectoryFrom () (some n)
      (state_trace (fun _ : Unit => decrement) (List.replicate n ()) (some n)) :=
  (finite_network 1 (by omega)).terminal_path_to_graph_trajectory
    (terminal_path n hn) (some_mem_dom_decrement n)

theorem graph_terminal_trajectory_length (n : Nat) (hn : 0 < n)
    {states : List (Unit × Option Nat)}
    (hs : countdown_graph.TerminalTrajectoryFrom () (some n) states) :
    states.length = n := by
  have hp := (finite_network 1 (by omega)).graph_trajectory_to_terminal_path hs
  have heq := terminal_path_eq n hn hp
  simpa using congrArg List.length heq

/-- Every positive entrance has a terminal trajectory. -/
theorem pointwise_termination :
    ∀ x ∈ positive_source, ∃ states,
      countdown_graph.TerminalTrajectoryFrom () x states := by
  intro x hx
  cases x with
  | none => exact False.elim hx
  | some n => exact ⟨_, graph_terminal_trajectory n hx⟩

/-- OET anchor: h-96bb1a4734f21c32
Each positive input has exactly one complete terminal trajectory, with
uniqueness in the general graph semantics including every recorded state. -/
theorem pointwise_unique_termination :
    ∀ x ∈ positive_source, ∃! states,
      countdown_graph.TerminalTrajectoryFrom () x states := by
  intro x hx
  obtain ⟨states, hs⟩ := pointwise_termination x hx
  exact ⟨states, hs, fun _ hs' =>
    (finite_network 1 (by omega)).graph_terminal_trajectory_unique hs' hs⟩

/-- OET anchor: h-96bb1a4734f21c32
CH5 习题“逐点终止与统一有限终止”：even choosing a terminal
trajectory separately for each entrance cannot give a uniform finite bound. -/
theorem no_uniform_termination_bound :
    ¬ ∃ L : Nat, ∀ x ∈ positive_source, ∃ states,
      countdown_graph.TerminalTrajectoryFrom () x states ∧ states.length ≤ L := by
  rintro ⟨L, hL⟩
  obtain ⟨states, hs, hlen⟩ := hL (some (L + 1)) (by exact Nat.zero_lt_succ L)
  have hlength := graph_terminal_trajectory_length (L + 1) (by omega) hs
  omega

@[simp] theorem finite_path (m : Nat) (hm : 1 ≤ m) (n : Nat)
    (hn : some n ∈ bounded_source m) :
    (finite_network m hm).path_of ⟨some n, hn⟩ = List.replicate n () := rfl

theorem finite_output (m : Nat) (hm : 1 ≤ m) (n : Nat)
    (hn : some n ∈ bounded_source m) :
    (finite_network m hm).eval ⟨some n, hn⟩ = some 0 :=
  chain_output n

/-- OET anchor: h-96bb1a4734f21c32
The extensional operator sends precisely the bounded positive source to
the normal state zero, and sends every other state to the absorbing point. -/
theorem finite_extensional_apply (m : Nat) (hm : 1 ≤ m) (x : Option Nat) :
    (x ∈ bounded_source m →
      (finite_network m hm).extensional_operator.func x = some 0) ∧
    (x ∉ bounded_source m →
      (finite_network m hm).extensional_operator.func x = none) := by
  classical
  constructor
  · intro hx
    cases x with
    | none => exact False.elim hx
    | some n =>
        simpa only [FiniteOperatorNetwork.extensional_operator,
          show (finite_network m hm).U = bounded_source m from rfl,
          dif_pos hx] using finite_output m hm n hx
  · intro hx
    simp [FiniteOperatorNetwork.extensional_operator,
      show (finite_network m hm).U = bounded_source m from rfl, hx]

/-- Exact membership in every path domain, including unattainable lists. -/
theorem finite_path_domain_membership (m : Nat) (hm : 1 ≤ m)
    (x : Option Nat) (p : List Unit) :
    x ∈ (finite_network m hm).path_domain p ↔
      ∃ n : Nat, x = some n ∧ 1 ≤ n ∧ n ≤ m ∧ p = List.replicate n () := by
  constructor
  · rintro ⟨hx, hp⟩
    cases x with
    | none => exact False.elim hx
    | some n => exact ⟨n, rfl, hx.1, hx.2, hp.symm⟩
  · rintro ⟨n, rfl, hn, hnm, rfl⟩
    exact ⟨⟨hn, hnm⟩, rfl⟩

/-- OET anchor: h-96bb1a4734f21c32
Each reachable length has exactly one entrance point in its path domain. -/
theorem finite_path_domain (m : Nat) (hm : 1 ≤ m) (k : Nat)
    (hk : 1 ≤ k) (hkm : k ≤ m) :
    (finite_network m hm).path_domain (List.replicate k ()) = {some k} := by
  ext x
  rw [finite_path_domain_membership]
  constructor
  · rintro ⟨n, rfl, _, _, heq⟩
    have hnk : k = n := by simpa using congrArg List.length heq
    simp [hnk]
  · intro hx
    have hxk : x = some k := hx
    exact ⟨k, hxk, hk, hkm, rfl⟩

/-- OET anchor: h-96bb1a4734f21c32
The complete reachable path family consists precisely of the lists
of `k` copies of the single node, for `1 ≤ k ≤ m`. -/
theorem finite_reachable_paths (m : Nat) (hm : 1 ≤ m) (p : List Unit) :
    ((finite_network m hm).path_domain p).Nonempty ↔
      ∃ k : Nat, 1 ≤ k ∧ k ≤ m ∧ p = List.replicate k () := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨k, _, hk, hkm, hp⟩ := (finite_path_domain_membership m hm x p).mp hx
    exact ⟨k, hk, hkm, hp⟩
  · rintro ⟨k, hk, hkm, rfl⟩
    rw [finite_path_domain m hm k hk hkm]
    exact Set.singleton_nonempty _

/-- OET anchor: h-96bb1a4734f21c32
The actual maximum path length equals `m`, not merely the stored bound. -/
theorem finite_evaluation_depth (m : Nat) (hm : 1 ≤ m) :
    (finite_network m hm).evaluation_depth = m := by
  classical
  apply Nat.le_antisymm
  · unfold FiniteOperatorNetwork.evaluation_depth
    apply Finset.sup_le
    intro p _
    exact (finite_network m hm).reachable_path_nodes_length_le_depth p
  · have hdom : ((finite_network m hm).path_domain (List.replicate m ())).Nonempty :=
      (finite_reachable_paths m hm _).mpr ⟨m, hm, le_refl m, rfl⟩
    simpa using (finite_network m hm).reachable_path_nodes_length_le_evaluation_depth
      ⟨List.replicate m (), hdom⟩

end formal_oet.vol_01.exercise_solutions.network_countdown
