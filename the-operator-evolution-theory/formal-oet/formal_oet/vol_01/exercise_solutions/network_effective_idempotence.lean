import formal_oet.vol_01.ch_05_operator_networks.effective_equivalence
import formal_oet.vol_01.ch_05_operator_networks.network_identity

namespace formal_oet.vol_01.exercise_solutions.network_effective_idempotence
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open FiniteOperatorNetwork
variable {X V : Type} {bot : X}
variable (N : FiniteOperatorNetwork X bot V)

/-- OET anchor: h-082bb5a4fb2472b9
The first effective reduction preserves every actual input occurrence,
including its intermediate point value. -/
theorem actual_inputs_eq (v : V) :
    N.effective_reduction.node_actual_input_domain v = N.node_actual_input_domain v := by
  ext y
  constructor
  · intro hy
    have hd := N.effective_reduction.node_actual_input_domain_subset_node_dom v hy
    rwa [N.effective_reduction_node_dom_eq v] at hd
  · intro hy
    have hy_original := hy
    obtain ⟨x, pref, suffix, hpath, hvalue, _⟩ := hy
    let p : N.ReachablePath := ⟨N.path_of x, ⟨x.val, x.property, rfl⟩⟩
    have heval := N.effective_prefix_eval_eq p
      (show x.val ∈ N.path_domain p.nodes from ⟨x.property, rfl⟩)
      pref.length (by simp [p, hpath])
    have heval' : N.effective_reduction.chain_eval_nodes pref x.val =
        N.chain_eval_nodes pref x.val := by
      simpa [p, hpath, effective_reduction, effective_chain_eval_nodes,
        FiniteOperatorNetwork.chain_eval_nodes] using heval
    refine ⟨x, pref, suffix, hpath, hvalue.trans heval'.symm, ?_⟩
    rw [N.effective_reduction_node_dom_eq v]
    exact hy_original

/-- Restricting an already effective local operator makes no further change. -/
theorem node_operators_eq (v : V) :
    N.effective_reduction.effective_reduction.node_op v = N.effective_reduction.node_op v := by
  change restrict_operator (N.effective_node_operator v)
    (N.effective_reduction.node_actual_input_domain v) = N.effective_node_operator v
  rw [actual_inputs_eq N v]
  ext x
  classical
  by_cases hx : x ∈ N.node_actual_input_domain v <;>
    simp [effective_node_operator, restrict_operator, hx]

/-- The source and all entrance blocks are unchanged on the second pass. -/
theorem entry_domains_eq (v : V) :
    N.effective_reduction.effective_reduction.entry_domain v =
      N.effective_reduction.entry_domain v := rfl

/-- Local operators and the unchanged routing map give exactly the same edge domains. -/
theorem edge_domains_eq (v w : V) :
    N.effective_reduction.effective_reduction.edge_domain v w =
      N.effective_reduction.edge_domain v w := by
  change {z | z ∈ (N.effective_reduction.effective_reduction.node_op v).func ''
      dom (N.effective_reduction.effective_reduction.node_op v) ∧
      N.choice v z = .next w} =
    {z | z ∈ (N.effective_reduction.node_op v).func ''
      dom (N.effective_reduction.node_op v) ∧ N.choice v z = .next w}
  rw [node_operators_eq N v]

/-- The terminal domains, including all output points, are unchanged as well. -/
theorem terminal_domains_eq (v : V) :
    N.effective_reduction.effective_reduction.terminal_domain v =
      N.effective_reduction.terminal_domain v := by
  change (N.effective_reduction.effective_reduction.node_op v).func ''
      dom (N.effective_reduction.effective_reduction.node_op v) \
      (⋃ w, N.effective_reduction.effective_reduction.edge_domain v w) =
    (N.effective_reduction.node_op v).func '' dom (N.effective_reduction.node_op v) \
      (⋃ w, N.effective_reduction.edge_domain v w)
  simp only [node_operators_eq N, edge_domains_eq N]

/-- OET anchor: h-082bb5a4fb2472b9
Idempotence is equality of the original network data on the same node
labels; no node renaming or mere extensional equivalence is substituted. -/
theorem effective_reduction_idempotent_data :
    N.effective_reduction.effective_reduction.presentation_data =
      N.effective_reduction.presentation_data := by
  unfold presentation_data
  have hop : N.effective_reduction.effective_reduction.node_op =
      N.effective_reduction.node_op := funext (node_operators_eq N)
  have hedge : N.effective_reduction.effective_reduction.edge_domain =
      N.effective_reduction.edge_domain := funext fun v => funext (edge_domains_eq N v)
  rw [hop, hedge]
  rfl

end formal_oet.vol_01.exercise_solutions.network_effective_idempotence
