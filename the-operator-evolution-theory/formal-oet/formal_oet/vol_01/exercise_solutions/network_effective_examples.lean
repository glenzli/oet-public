import formal_oet.vol_01.ch_05_operator_networks.effective_equivalence
import formal_oet.vol_01.ch_05_operator_networks.acyclic_network_encoding

namespace formal_oet.vol_01.exercise_solutions.network_effective_examples
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open FiniteOperatorNetwork

abbrev Point := Option (Fin 3)
def a : Point := some 0
def b : Point := some 1
def c : Point := some 2

/-- The two nodes are alpha=false and beta=true. -/
def entrance_point : Bool → Point
  | false => a
  | true => b

def source : Set Point := {a, b}
def local_domain (v : Bool) : Set Point := {entrance_point v, c}

/-- Identity on {a,c} at alpha and on {b,c} at beta, absorbing elsewhere. -/
def local_operator (v : Bool) : Operator Point none :=
  ⟨fun x => if x = entrance_point v ∨ x = c then x else none, by
    cases v <;> simp [entrance_point, a, b, c]⟩

@[simp] theorem local_operator_apply_entrance (v : Bool) :
    (local_operator v).func (entrance_point v) = entrance_point v := by
  simp [local_operator]
@[simp] theorem local_operator_apply_c (v : Bool) :
    (local_operator v).func c = c := by simp [local_operator]

theorem local_operator_domain (v : Bool) : dom (local_operator v) = local_domain v := by
  ext x
  cases v <;> fin_cases x <;>
    simp [dom, local_operator, local_domain, entrance_point, a, b, c]

theorem local_operator_eq_restriction (v : Bool) :
    local_operator v = restrict_operator operator_identity (local_domain v) := by
  ext x
  simp [local_operator, restrict_operator, local_domain, operator_identity]

def entrance (x : Point) : Bool := if x = a then false else true

def routing (v : Bool) (z : Point) : OutputChoice Bool :=
  if z = c then .next (!v) else .stop

@[simp] theorem entrance_entrance_point (v : Bool) : entrance (entrance_point v) = v := by
  cases v <;> decide

theorem source_input_eq_entrance (x : Point) (hx : x ∈ source) :
    x = entrance_point (entrance x) := by
  rcases hx with rfl | hx
  · decide
  · have hxb : x = b := hx
    subst x
    decide

/-- OET anchor: h-171f4e850e8f1c36
Both source inputs stop after their own entrance node, although the local
operators and transition graph retain a separate two-cycle at c. -/
def network : FiniteOperatorNetwork Point none Bool where
  U := source
  bot_not_mem := by simp [source, a, b]
  node_fintype := inferInstance
  node_op := local_operator
  node_dom_nonempty := by
    intro v
    refine ⟨entrance_point v, ?_⟩
    rw [local_operator_domain]
    simp [local_domain]
  entry := fun x => entrance x.val
  entry_mem := by
    intro x
    rw [local_operator_domain, source_input_eq_entrance x.val x.property]
    simp [local_domain]
  choice := routing
  choice_next_mem := by
    intro v w y _ hnext
    by_cases hc : (local_operator v).func y = c
    · simp only [routing, if_pos hc, OutputChoice.next.injEq] at hnext
      subst w
      rw [hc, local_operator_domain]
      simp [local_domain]
    · simp [routing, hc] at hnext
  depth_bound := 1
  path_of := fun x => [entrance x.val]
  path_terminal := by
    intro x
    apply TerminalPathFrom.stop
    have hx := source_input_eq_entrance x.val x.property
    have hlocal : (local_operator (entrance x.val)).func x.val = x.val := by
      calc
        (local_operator (entrance x.val)).func x.val =
            (local_operator (entrance x.val)).func (entrance_point (entrance x.val)) :=
          congrArg (local_operator (entrance x.val)).func hx
        _ = entrance_point (entrance x.val) := local_operator_apply_entrance _
        _ = x.val := hx.symm
    rw [hlocal]
    have hxc : x.val ≠ c := by
      have hxU := x.property
      rcases hxU with hxa | hxb
      · rw [hxa]; decide
      · have hxb' : x.val = b := hxb
        rw [hxb']; decide
    simp [routing, hxc]
  path_length_le_depth := by intro x; rfl
  node_reachable := by
    intro v
    refine ⟨⟨entrance_point v, ?_⟩, ?_⟩
    · cases v <;> simp [source, entrance_point]
    · simp

theorem source_nonempty : network.U.Nonempty := ⟨a, by simp [network, source]⟩

theorem local_image (v : Bool) :
    (local_operator v).func '' dom (local_operator v) = local_domain v := by
  rw [local_operator_domain]
  have happly : ∀ x ∈ local_domain v, (local_operator v).func x = x := by
    intro x hx
    have hx' : x = entrance_point v ∨ x = c := hx
    simp [local_operator, hx']
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    exact ((happly x hx).symm.trans hxy) ▸ hx
  · intro hy
    exact ⟨y, hy, happly y hy⟩

/-- The specified entrance pieces are exactly {a} and {b}. -/
theorem entry_domains (v : Bool) : network.entry_domain v = {entrance_point v} := by
  ext x
  constructor
  · rintro ⟨hx, hentry⟩
    change x = entrance_point v
    exact (source_input_eq_entrance x hx).trans (congrArg entrance_point hentry)
  · intro hx
    have hx' : x = entrance_point v := hx
    subst x
    refine ⟨?_, ?_⟩
    · cases v <;> simp [network, source, entrance_point]
    · exact entrance_entrance_point v

/-- Every input has a one-occurrence terminal path. -/
theorem path_length_one (x : network.U) : (network.path_of x).length = 1 := rfl

/-- The maximum actual path length is one, not merely bounded by one. -/
theorem evaluation_depth_one : network.evaluation_depth = 1 := by
  apply Nat.le_antisymm
  · unfold evaluation_depth
    apply Finset.sup_le
    intro p _
    obtain ⟨x, hx, hp⟩ := p.nonempty_domain
    rw [← hp]
    exact Nat.le_refl 1
  · let xp : network.U := ⟨a, by simp [network, source]⟩
    let p : network.ReachablePath := ⟨network.path_of xp, ⟨a, xp.property, rfl⟩⟩
    exact network.reachable_path_nodes_length_le_evaluation_depth p

/-- Both source points are returned unchanged at termination. -/
theorem eval_eq_input (x : network.U) : network.eval x = x.val := by
  change (local_operator (entrance x.val)).func x.val = x.val
  rw [source_input_eq_entrance x.val x.property]
  simp

/-- OET anchor: h-171f4e850e8f1c36
The graph's two nonempty transition domains are both {c}. -/
theorem edge_domains (v w : Bool) :
    network.edge_domain v w = if w = !v then {c} else ∅ := by
  ext z
  change (z ∈ (local_operator v).func '' dom (local_operator v) ∧
    routing v z = .next w) ↔ _
  constructor
  · rintro ⟨_, hr⟩
    by_cases hzc : z = c
    · subst z
      simp [routing] at hr
      simp [hr]
    · simp [routing, hzc] at hr
  · intro hz
    by_cases hw : w = !v
    · simp only [if_pos hw, Set.mem_singleton_iff] at hz
      subst z
      refine ⟨⟨c, ?_, local_operator_apply_c v⟩, ?_⟩
      · rw [local_operator_domain]; simp [local_domain]
      · simp [routing, hw]
    · simp [hw] at hz

theorem terminal_domains (v : Bool) : network.terminal_domain v = {entrance_point v} := by
  ext z
  rw [network.mem_terminal_domain_iff_choice_stop]
  change (z ∈ (local_operator v).func '' dom (local_operator v) ∧
    routing v z = .stop) ↔ z ∈ {entrance_point v}
  rw [local_image]
  cases v <;> fin_cases z <;> simp [local_domain, routing, entrance_point, a, b, c]

/-- There is an actual positive-length closed directed walk alpha→beta→alpha. -/
theorem original_two_cycle :
    Relation.TransGen network.to_transition_graph.Edge false false := by
  have hedge (v : Bool) : network.to_transition_graph.Edge v (!v) := by
    change (network.edge_domain v (!v)).Nonempty
    rw [edge_domains]
    simp
  exact (Relation.TransGen.single (hedge false)).trans
    (Relation.TransGen.single (hedge true))

theorem original_not_acyclic : ¬ network.to_transition_graph.IsAcyclic := by
  intro h
  exact h false original_two_cycle

/-- OET anchor: h-171f4e850e8f1c36
The unused c-state does not occur in either actual node input domain. -/
theorem actual_input_domains (v : Bool) :
    network.node_actual_input_domain v = {entrance_point v} := by
  ext y
  constructor
  · rintro ⟨x, pref, suffix, hp, hy, _⟩
    have hlen := congrArg List.length hp
    simp only [path_length_one, List.length_append, List.length_cons] at hlen
    have hpref : pref = [] := List.length_eq_zero_iff.mp (by omega)
    have hlabel : entrance x.val = v := by
      simpa [hpref, network] using congrArg List.head? hp
    have hyx : y = x.val := by
      simpa [hpref, chain_eval_nodes, chain_eval_nodes_core] using hy
    change y = entrance_point v
    exact hyx.trans ((source_input_eq_entrance x.val x.property).trans
      (congrArg entrance_point hlabel))
  · intro hy
    have hy' : y = entrance_point v := hy
    subst y
    refine ⟨⟨entrance_point v, ?_⟩, [], [], ?_, rfl, ?_⟩
    · cases v <;> simp [network, source, entrance_point]
    · change [entrance (entrance_point v)] = [v]
      rw [entrance_entrance_point]
    · change entrance_point v ∈ dom (local_operator v)
      rw [local_operator_domain]
      simp [local_domain]

/-- OET anchor: h-171f4e850e8f1c36
Effective local operators are precisely id restricted to {a} and {b}. -/
theorem effective_local_operators (v : Bool) :
    network.effective_reduction.node_op v =
      restrict_operator operator_identity {entrance_point v} := by
  change restrict_operator (local_operator v) (network.node_actual_input_domain v) = _
  rw [actual_input_domains]
  ext x
  classical
  by_cases hx : x = entrance_point v
  · subst x
    simp [restrict_operator, operator_identity]
  · simp [restrict_operator, hx]

/-- No actual path contains two adjacent nodes, so every effective edge is empty. -/
theorem effective_edge_domains_empty (v w : Bool) :
    network.effective_edge_domain v w = ∅ := by
  ext z
  constructor
  · rintro ⟨x, pref, suffix, hp, _⟩
    have hlen := congrArg List.length hp
    simp only [path_length_one, List.length_append, List.length_cons] at hlen
    omega
  · simp

theorem effective_reduction_edges_empty (v w : Bool) :
    network.effective_reduction.edge_domain v w = ∅ := by
  rw [network.effective_reduction_edge_domain_eq, effective_edge_domains_empty]

theorem effective_node_domains (v : Bool) :
    network.effective_reduction.node_dom v = {entrance_point v} := by
  rw [network.effective_reduction_node_dom_eq, actual_input_domains]

theorem effective_entry_domains (v : Bool) :
    network.effective_reduction.entry_domain v = {entrance_point v} := by
  rw [network.effective_reduction_entry_domain_eq, entry_domains]

theorem effective_terminal_domains (v : Bool) :
    network.effective_reduction.terminal_domain v = {entrance_point v} := by
  rw [network.effective_reduction_terminal_domain_eq,
    network.effective_terminal_domain_eq_image_inter, actual_input_domains, terminal_domains]
  simp [network]

/-- OET anchor: h-171f4e850e8f1c36
The effective graph is edgeless, hence acyclic. The original graph is not. -/
theorem effective_reduction_acyclic :
    network.effective_reduction.to_transition_graph.IsAcyclic := by
  apply network.effective_reduction.to_transition_graph.is_acyclic_of_rank (fun _ => 0)
  intro v w h
  change (network.effective_reduction.edge_domain v w).Nonempty at h
  rw [effective_reduction_edges_empty] at h
  exact h.elim fun z hz => False.elim hz

/-- OET anchor: h-171f4e850e8f1c36
A concrete nonempty network uses both nodes, has a directed cycle, yet none
of its edges is used by an entrance trajectory and its effective graph is acyclic. -/
theorem unused_cyclic_edges_example :
    network.U.Nonempty ∧
    (∀ v, ∃ x : network.U, v ∈ network.path_of x) ∧
    ¬ network.to_transition_graph.IsAcyclic ∧
    (∀ v w, network.effective_edge_domain v w = ∅) ∧
    network.effective_reduction.to_transition_graph.IsAcyclic :=
  ⟨source_nonempty, network.node_reachable, original_not_acyclic,
    effective_edge_domains_empty, effective_reduction_acyclic⟩

end formal_oet.vol_01.exercise_solutions.network_effective_examples
