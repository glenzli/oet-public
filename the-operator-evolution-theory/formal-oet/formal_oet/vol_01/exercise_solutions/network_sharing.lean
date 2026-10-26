import formal_oet.vol_01.ch_05_operator_networks.network_expression_readouts
import formal_oet.vol_01.ch_05_operator_networks.effective_network_isomorphism

namespace formal_oet.vol_01.exercise_solutions.network_sharing

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Point := Option ℝ

def lift_operator (f : ℝ → ℝ) : Operator Point none := ⟨Option.map f, rfl⟩
def negative_piece : Set Point := {some (-2), some (-1)}
def positive_piece : Set Point := {some 1, some 2}
def source : Set Point := negative_piece ∪ positive_piece
def output_piece : Set Point := {some 1, some 4}
def real_domain : Set Point := Set.range some

def node_operator {n : Nat} (v : Fin n) : Operator Point none :=
  if v.val = 0 then lift_operator (fun x => -x)
  else if v.val = 1 then lift_operator id else lift_operator (fun x => x ^ 2)

@[simp] theorem dom_lift_operator (f : ℝ → ℝ) : dom (lift_operator f) = real_domain := by
  ext x
  cases x <;> simp [dom, lift_operator, real_domain]

@[simp] theorem dom_node_operator {n : Nat} (v : Fin n) :
    dom (node_operator v) = real_domain := by
  unfold node_operator
  split_ifs <;> exact dom_lift_operator _

private theorem local_next_mem {n : Nat} (v w : Fin n) {x : Point}
    (hx : x ∈ dom (node_operator v)) : (node_operator v).func x ∈ dom (node_operator w) := by
  rw [dom_node_operator] at hx ⊢
  obtain ⟨x, rfl⟩ := hx
  unfold node_operator
  split_ifs <;> simp [lift_operator, real_domain]

private theorem source_real {x : Point} (hx : x ∈ source) : x ∈ real_domain := by
  rcases hx with hx | hx <;> simp only [negative_piece, positive_piece, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hx <;> rcases hx with rfl | rfl <;> simp [real_domain]

def routing {n : Nat} (left right : Fin n) (v : Fin n) (z : Point) : OutputChoice (Fin n) :=
  if v.val = 0 then (if z ∈ positive_piece then .next left else .stop)
  else if v.val = 1 then (if z ∈ positive_piece then .next right else .stop)
  else .stop

/--
OET anchor: h-ff997c4726870929
Three nodes: 0 = alpha, 1 = beta, and one shared square node 2 = gamma.
-/
def shared_network : FiniteOperatorNetwork Point none (Fin 3) where
  U := source
  bot_not_mem := by simp [source, negative_piece, positive_piece]
  node_fintype := inferInstance
  node_op := node_operator
  node_dom_nonempty := by intro v; rw [dom_node_operator]; exact ⟨some 0, 0, rfl⟩
  entry := fun x => if x.val ∈ negative_piece then 0 else 1
  entry_mem := by intro x; rw [dom_node_operator]; exact source_real x.property
  choice := routing 2 2
  choice_next_mem := by intro v w x hx _; exact local_next_mem v w hx
  depth_bound := 2
  path_of := fun x => if x.val ∈ negative_piece then [0, 2] else [1, 2]
  path_terminal := by
    rintro ⟨x, hx⟩
    simp only [source, negative_piece, positive_piece, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl) | (rfl | rfl) <;>
      norm_num [negative_piece] <;>
      apply TerminalPathFrom.next (γ := 2)
    all_goals try norm_num [routing, positive_piece, node_operator, lift_operator]
    all_goals apply TerminalPathFrom.stop
    all_goals norm_num [routing, node_operator, lift_operator]
  path_length_le_depth := by intro x; split_ifs <;> simp
  node_reachable := by
    intro v
    fin_cases v
    · exact ⟨⟨some (-2), by simp [source, negative_piece]⟩, by norm_num [negative_piece]⟩
    · exact ⟨⟨some 1, by simp [source, positive_piece]⟩, by norm_num [negative_piece]⟩
    · exact ⟨⟨some (-2), by simp [source, negative_piece]⟩, by norm_num [negative_piece]; rfl⟩

/--
OET anchor: h-ff997c4726870929
Four nodes: the square node is duplicated into 2 and 3 for the two branches.
-/
def duplicated_network : FiniteOperatorNetwork Point none (Fin 4) where
  U := source
  bot_not_mem := by simp [source, negative_piece, positive_piece]
  node_fintype := inferInstance
  node_op := node_operator
  node_dom_nonempty := by intro v; rw [dom_node_operator]; exact ⟨some 0, 0, rfl⟩
  entry := fun x => if x.val ∈ negative_piece then 0 else 1
  entry_mem := by intro x; rw [dom_node_operator]; exact source_real x.property
  choice := routing 2 3
  choice_next_mem := by intro v w x hx _; exact local_next_mem v w hx
  depth_bound := 2
  path_of := fun x => if x.val ∈ negative_piece then [0, 2] else [1, 3]
  path_terminal := by
    rintro ⟨x, hx⟩
    simp only [source, negative_piece, positive_piece, Set.mem_union, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl) | (rfl | rfl) <;> norm_num [negative_piece]
    · apply TerminalPathFrom.next (γ := 2)
      · norm_num [routing, positive_piece, node_operator, lift_operator]
      · apply TerminalPathFrom.stop; norm_num [routing, node_operator, lift_operator]
    · apply TerminalPathFrom.next (γ := 2)
      · norm_num [routing, positive_piece, node_operator, lift_operator]
      · apply TerminalPathFrom.stop; norm_num [routing, node_operator, lift_operator]
    · apply TerminalPathFrom.next (γ := 3)
      · norm_num [routing, positive_piece, node_operator, lift_operator]
      · apply TerminalPathFrom.stop; norm_num [routing, node_operator, lift_operator]
    · apply TerminalPathFrom.next (γ := 3)
      · norm_num [routing, positive_piece, node_operator, lift_operator]
      · apply TerminalPathFrom.stop; norm_num [routing, node_operator, lift_operator]
  path_length_le_depth := by intro x; split_ifs <;> simp
  node_reachable := by
    intro v
    fin_cases v
    · exact ⟨⟨some (-2), by simp [source, negative_piece]⟩, by norm_num [negative_piece]⟩
    · exact ⟨⟨some 1, by simp [source, positive_piece]⟩, by norm_num [negative_piece]⟩
    · exact ⟨⟨some (-2), by simp [source, negative_piece]⟩, by norm_num [negative_piece]; rfl⟩
    · exact ⟨⟨some 1, by simp [source, positive_piece]⟩, by norm_num [negative_piece]; rfl⟩

private theorem positive_not_negative {x : Point} (hx : x ∈ positive_piece) :
    x ∉ negative_piece := by
  simp only [positive_piece, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl <;> norm_num [negative_piece]

/--
OET anchor: h-ff997c4726870929
The two complete path domains in the shared network.
-/
theorem shared_path_domain_negative : shared_network.path_domain [0, 2] = negative_piece := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    by_contra hn
    simp [shared_network, hn] at hp
  · intro hx
    exact ⟨Or.inl hx, by simp [shared_network, hx]⟩

/--
OET anchor: h-ff997c4726870929
The positive branch has exactly the positive source piece.
-/
theorem shared_path_domain_positive : shared_network.path_domain [1, 2] = positive_piece := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    have hn : x ∉ negative_piece := by
      intro hn
      simp [shared_network, hn] at hp
    exact hx.resolve_left hn
  · intro hx
    exact ⟨Or.inr hx, by simp [shared_network, positive_not_negative hx]⟩

/--
OET anchor: h-ff997c4726870929
Duplicating gamma preserves the negative path domain.
-/
theorem duplicated_path_domain_negative :
    duplicated_network.path_domain [0, 2] = negative_piece := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    by_contra hn
    simp [duplicated_network, hn] at hp
  · intro hx
    exact ⟨Or.inl hx, by simp [duplicated_network, hx]⟩

/--
OET anchor: h-ff997c4726870929
Duplicating gamma preserves the positive path domain.
-/
theorem duplicated_path_domain_positive :
    duplicated_network.path_domain [1, 3] = positive_piece := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    have hn : x ∉ negative_piece := by
      intro hn
      simp [duplicated_network, hn] at hp
    exact hx.resolve_left hn
  · intro hx
    exact ⟨Or.inr hx, by simp [duplicated_network, positive_not_negative hx]⟩

/--
OET anchor: h-ff997c4726870929
Every reachable complete path is one of the two displayed branches.
-/
theorem shared_path_cases (p : shared_network.ReachablePath) :
    p.nodes = [0, 2] ∨ p.nodes = [1, 2] := by
  obtain ⟨x, hx, hp⟩ := p.nonempty_domain
  by_cases hn : x ∈ negative_piece
  · exact Or.inl (by simpa [shared_network, hn] using hp.symm)
  · exact Or.inr (by simpa [shared_network, hn] using hp.symm)

/--
OET anchor: h-ff997c4726870929
Every reachable complete path uses its corresponding copy of gamma.
-/
theorem duplicated_path_cases (p : duplicated_network.ReachablePath) :
    p.nodes = [0, 2] ∨ p.nodes = [1, 3] := by
  obtain ⟨x, hx, hp⟩ := p.nonempty_domain
  by_cases hn : x ∈ negative_piece
  · exact Or.inl (by simpa [duplicated_network, hn] using hp.symm)
  · exact Or.inr (by simpa [duplicated_network, hn] using hp.symm)

private theorem shared_chain_negative :
    shared_network.path_chain [0, 2] = lift_operator (fun x => x ^ 2) := by
  ext x
  rw [shared_network.path_chain_apply_eq_chain_eval_nodes]
  cases x <;> simp [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
    shared_network, node_operator, lift_operator]

private theorem shared_chain_positive :
    shared_network.path_chain [1, 2] = lift_operator (fun x => x ^ 2) := by
  ext x
  rw [shared_network.path_chain_apply_eq_chain_eval_nodes]
  cases x <;> simp [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
    shared_network, node_operator, lift_operator]

private theorem duplicated_chain_negative :
    duplicated_network.path_chain [0, 2] = lift_operator (fun x => x ^ 2) := by
  ext x
  rw [duplicated_network.path_chain_apply_eq_chain_eval_nodes]
  cases x <;> simp [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
    duplicated_network, node_operator, lift_operator]

private theorem duplicated_chain_positive :
    duplicated_network.path_chain [1, 3] = lift_operator (fun x => x ^ 2) := by
  ext x
  rw [duplicated_network.path_chain_apply_eq_chain_eval_nodes]
  cases x <;> simp [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
    duplicated_network, node_operator, lift_operator]

/--
OET anchor: h-ff997c4726870929
Both real networks induce exactly the same two untagged path pieces.
-/
theorem shared_path_readout_pieces : shared_network.path_readout.pieces =
    {(negative_piece, lift_operator (fun x => x ^ 2)),
      (positive_piece, lift_operator (fun x => x ^ 2))} := by
  ext s
  constructor
  · rintro ⟨p, rfl⟩
    rcases shared_path_cases p with hp | hp
    · simp only [hp, shared_path_domain_negative, shared_chain_negative]
      exact Set.mem_insert _ _
    · simp only [hp, shared_path_domain_positive, shared_chain_positive]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · rintro (rfl | rfl)
    · refine ⟨⟨[0, 2], ?_⟩, ?_⟩
      · rw [shared_path_domain_negative]; exact ⟨some (-2), by simp [negative_piece]⟩
      · simp [shared_path_domain_negative, shared_chain_negative]
    · refine ⟨⟨[1, 2], ?_⟩, ?_⟩
      · rw [shared_path_domain_positive]; exact ⟨some 1, by simp [positive_piece]⟩
      · simp [shared_path_domain_positive, shared_chain_positive]

/--
OET anchor: h-ff997c4726870929
The copied network induces the same two untagged pieces.
-/
theorem duplicated_path_readout_pieces : duplicated_network.path_readout.pieces =
    {(negative_piece, lift_operator (fun x => x ^ 2)),
      (positive_piece, lift_operator (fun x => x ^ 2))} := by
  ext s
  constructor
  · rintro ⟨p, rfl⟩
    rcases duplicated_path_cases p with hp | hp
    · simp only [hp, duplicated_path_domain_negative, duplicated_chain_negative]
      exact Set.mem_insert _ _
    · simp only [hp, duplicated_path_domain_positive, duplicated_chain_positive]
      exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · rintro (rfl | rfl)
    · refine ⟨⟨[0, 2], ?_⟩, ?_⟩
      · rw [duplicated_path_domain_negative]; exact ⟨some (-2), by simp [negative_piece]⟩
      · simp [duplicated_path_domain_negative, duplicated_chain_negative]
    · refine ⟨⟨[1, 3], ?_⟩, ?_⟩
      · rw [duplicated_path_domain_positive]; exact ⟨some 1, by simp [positive_piece]⟩
      · simp [duplicated_path_domain_positive, duplicated_chain_positive]

/--
OET anchor: h-ff997c4726870929
Duplicating the shared node changes neither the untagged readout nor the operator.
-/
theorem same_path_readout : shared_network.path_readout = duplicated_network.path_readout := by
  apply FiniteSegmentExpression.ext
  rw [shared_path_readout_pieces, duplicated_path_readout_pieces]

/--
OET anchor: h-ff997c4726870929
The two actual network constructions induce the same external operator.
-/
theorem same_extensional_operator :
    shared_network.extensional_operator = duplicated_network.extensional_operator := by
  rw [← shared_network.path_readout_evaluate, ← duplicated_network.path_readout_evaluate,
    same_path_readout]

/--
OET anchor: h-ff997c4726870929
A global node-label bijection cannot identify three nodes with four nodes.
-/
theorem not_effective_equivalent : ¬ EffectiveEquivalent shared_network duplicated_network := by
  rintro ⟨h⟩
  have hcard := Fintype.card_congr h.node_equiv
  norm_num at hcard

/-- A complete two-step path admits no nonempty continuation. -/
private theorem prefix_domain_eq_path_domain (q : List (Fin 3)) (hq : q.length = 2) :
    shared_network.prefix_domain q = shared_network.path_domain q := by
  ext x
  constructor
  · rintro ⟨hx, tail, hp⟩
    have hlen := shared_network.path_length_le_depth ⟨x, hx⟩
    rw [hp, List.length_append, hq] at hlen
    have ht : tail = [] := List.length_eq_zero_iff.mp (by
      change 2 + tail.length ≤ 2 at hlen
      omega)
    refine ⟨hx, ?_⟩
    simpa [ht] using hp
  · rintro ⟨hx, hp⟩
    exact ⟨hx, [], by simpa using hp⟩

/--
OET anchor: h-ff997c4726870929
The initial-input domain of the negative complete prefix.
-/
theorem negative_prefix_domain : shared_network.prefix_domain [0, 2] = negative_piece := by
  rw [prefix_domain_eq_path_domain _ rfl, shared_path_domain_negative]

/--
OET anchor: h-ff997c4726870929
The initial-input domain of the positive complete prefix.
-/
theorem positive_prefix_domain : shared_network.prefix_domain [1, 2] = positive_piece := by
  rw [prefix_domain_eq_path_domain _ rfl, shared_path_domain_positive]

private theorem negative_image :
    (lift_operator (fun x => -x)).func '' negative_piece = positive_piece := by
  norm_num [negative_piece, positive_piece, lift_operator, Set.image_insert_eq,
    Set.image_singleton, Set.pair_comm]

/--
OET anchor: h-ff997c4726870929
The negative prefix reaches gamma with current input set {1,2}.
-/
theorem negative_prefix_input_domain :
    shared_network.prefix_input_domain [0, 2] = positive_piece := by
  rw [prefix_input_domain, negative_prefix_domain]
  simpa [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
    shared_network, node_operator] using negative_image

/--
OET anchor: h-ff997c4726870929
The positive prefix reaches gamma with current input set {1,2}.
-/
theorem positive_prefix_input_domain :
    shared_network.prefix_input_domain [1, 2] = positive_piece := by
  rw [prefix_input_domain, positive_prefix_domain]
  ext x
  cases x <;> simp [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
    shared_network, node_operator, lift_operator, positive_piece]

/--
OET anchor: h-ff997c4726870929
The negative prefix produces the output set {1,4}.
-/
theorem negative_prefix_output_domain :
    shared_network.prefix_output_domain [0, 2] = output_piece := by
  rw [prefix_output_domain, negative_prefix_domain]
  norm_num [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
    shared_network, node_operator, lift_operator, negative_piece, output_piece,
    Set.image_insert_eq, Set.image_singleton, Set.pair_comm]

/--
OET anchor: h-ff997c4726870929
The positive prefix produces the output set {1,4}.
-/
theorem positive_prefix_output_domain :
    shared_network.prefix_output_domain [1, 2] = output_piece := by
  rw [prefix_output_domain, positive_prefix_domain]
  norm_num [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
    shared_network, node_operator, lift_operator, positive_piece, output_piece,
    Set.image_insert_eq, Set.image_singleton]

private def negative_path : shared_network.ReachablePath :=
  ⟨[0, 2], by rw [shared_path_domain_negative]; exact ⟨some (-2), by simp [negative_piece]⟩⟩

private def positive_path : shared_network.ReachablePath :=
  ⟨[1, 2], by rw [shared_path_domain_positive]; exact ⟨some 1, by simp [positive_piece]⟩⟩

private theorem actual_input_membership (v : Fin 3) (y : Point) :
    y ∈ shared_network.node_actual_input_domain v ↔
      (v = 0 ∧ y ∈ negative_piece) ∨
      (v = 1 ∧ y ∈ positive_piece) ∨
      (v = 2 ∧ y ∈ positive_piece) := by
  rw [← shared_network.tagged_recovered_node_input_domain_eq]
  constructor
  · rintro ⟨p, n, hv, hy⟩
    rcases shared_path_cases p with hp | hp
    · have hn : n.val = 0 ∨ n.val = 1 := by
        have hlt := n.isLt
        simp [hp] at hlt
        omega
      rcases hn with hn | hn
      · left
        constructor
        · simpa [hp, hn] using hv.symm
        · simpa [path_factor_input_domain, hp, hn, shared_path_domain_negative,
            FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core] using hy
      · right; right
        constructor
        · simpa [hp, hn] using hv.symm
        · have hdom : shared_network.path_factor_input_domain p n = positive_piece := by
            simp only [path_factor_input_domain, hp, hn, shared_path_domain_negative]
            simpa [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
              shared_network, node_operator] using negative_image
          exact hdom ▸ hy
    · have hn : n.val = 0 ∨ n.val = 1 := by
        have hlt := n.isLt
        simp [hp] at hlt
        omega
      rcases hn with hn | hn
      · right; left
        constructor
        · simpa [hp, hn] using hv.symm
        · simpa [path_factor_input_domain, hp, hn, shared_path_domain_positive,
            FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core] using hy
      · right; right
        constructor
        · simpa [hp, hn] using hv.symm
        · simp only [path_factor_input_domain, hp, hn, shared_path_domain_positive] at hy
          simpa [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
            shared_network, node_operator, lift_operator] using hy
  · rintro (⟨rfl, hy⟩ | ⟨rfl, hy⟩ | ⟨rfl, hy⟩)
    · refine ⟨negative_path, ⟨0, by decide⟩, rfl, ?_⟩
      simpa [negative_path, path_factor_input_domain, shared_path_domain_negative,
        FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core] using hy
    · refine ⟨positive_path, ⟨0, by decide⟩, rfl, ?_⟩
      simpa [positive_path, path_factor_input_domain, shared_path_domain_positive,
        FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core] using hy
    · refine ⟨positive_path, ⟨1, by decide⟩, rfl, ?_⟩
      change y ∈ shared_network.chain_eval_nodes [1] '' shared_network.path_domain [1, 2]
      rw [shared_path_domain_positive]
      simpa [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
        shared_network, node_operator, lift_operator] using hy

/--
OET anchor: h-ff997c4726870929
The three actual node-input domains, with the two entrance branches combined at gamma.
-/
theorem node_actual_input_domains :
    shared_network.node_actual_input_domain 0 = negative_piece ∧
    shared_network.node_actual_input_domain 1 = positive_piece ∧
    shared_network.node_actual_input_domain 2 = positive_piece := by
  constructor
  · ext y; simp [actual_input_membership]
  constructor
  · ext y; simp [actual_input_membership]
  · ext y; simp [actual_input_membership]

/--
OET anchor: h-ff997c4726870929
Duplication retains every ordered operator factor, not merely its composite.
-/
theorem corresponding_factors (x : {x // x ∈ source}) :
    (shared_network.path_of x).map shared_network.node_op =
      (duplicated_network.path_of x).map duplicated_network.node_op := by
  change (if x.val ∈ negative_piece then [0, 2] else [1, 2]).map node_operator =
    (if x.val ∈ negative_piece then [0, 2] else [1, 3]).map node_operator
  split_ifs <;> rfl

/--
OET anchor: h-ff997c4726870929
Both corresponding paths contain exactly two nodes.
-/
theorem corresponding_path_lengths (x : {x // x ∈ source}) :
    (shared_network.path_of x).length = 2 ∧
      (duplicated_network.path_of x).length = 2 := by
  simp only [shared_network, duplicated_network]
  split_ifs <;> simp

/--
OET anchor: h-ff997c4726870929
The full external operator is square on the four source points and bottom elsewhere.
-/
theorem shared_extensional_formula :
    shared_network.extensional_operator =
      restrict_operator (lift_operator (fun x => x ^ 2)) source := by
  apply Operator.ext
  funext x
  by_cases hx : x ∈ source
  · rw [restrict_operator_apply_of_mem _ _ hx,
      shared_network.extensional_apply_eq_chain_eval_path ⟨x, hx⟩]
    change shared_network.chain_eval_nodes
      (if x ∈ negative_piece then [0, 2] else [1, 2]) x = _
    split_ifs <;> cases x <;>
      simp [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
        shared_network, node_operator, lift_operator]
  · rw [restrict_operator_apply_of_not_mem _ _ hx]
    simp [FiniteOperatorNetwork.extensional_operator, shared_network, hx]

/--
OET anchor: h-ff997c4726870929
The nonempty paths all have length two, so the actual maximum is two.
-/
theorem shared_evaluation_depth : shared_network.evaluation_depth = 2 := by
  apply le_antisymm
  · exact shared_network.evaluation_depth_le_of_input_lengths 2
      (fun x => shared_network.path_length_le_depth x)
  · exact shared_network.reachable_path_nodes_length_le_evaluation_depth negative_path

/--
OET anchor: h-ff997c4726870929
Disjoint source pieces may yield the same nonempty current input set.
-/
theorem initial_disjoint_current_overlap :
    Disjoint (shared_network.prefix_domain [0, 2]) (shared_network.prefix_domain [1, 2]) ∧
    ¬ Disjoint (shared_network.prefix_input_domain [0, 2])
      (shared_network.prefix_input_domain [1, 2]) := by
  rw [negative_prefix_domain, positive_prefix_domain,
    negative_prefix_input_domain, positive_prefix_input_domain]
  constructor
  · exact Set.disjoint_left.mpr (fun _ hn hp => positive_not_negative hp hn)
  · intro h
    have hx : (some 1 : Point) ∈ positive_piece := by simp [positive_piece]
    exact Set.disjoint_left.mp h hx hx

/--
OET anchor: h-ff997c4726870929
Both nonempty edge domains are precisely the displayed set {1,2}.
-/
theorem alpha_edge_domain : shared_network.edge_domain 0 2 = positive_piece := by
  ext z
  change ((∃ x ∈ dom (node_operator (0 : Fin 3)), (node_operator (0 : Fin 3)).func x = z) ∧
    routing (2 : Fin 3) 2 0 z = .next 2) ↔ z ∈ positive_piece
  constructor
  · rintro ⟨_, hc⟩
    by_contra hz
    simp [routing, hz] at hc
  · intro hz
    constructor
    · simp only [positive_piece, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨some (-1), by simp [dom_node_operator, real_domain], by
          norm_num [node_operator, lift_operator]⟩
      · exact ⟨some (-2), by simp [dom_node_operator, real_domain], by
          norm_num [node_operator, lift_operator]⟩
    · simp [routing, hz]

/--
OET anchor: h-ff997c4726870929
The identity branch transfers precisely the outputs {1,2}.
-/
theorem beta_edge_domain : shared_network.edge_domain 1 2 = positive_piece := by
  ext z
  change ((∃ x ∈ dom (node_operator (1 : Fin 3)), (node_operator (1 : Fin 3)).func x = z) ∧
    routing (2 : Fin 3) 2 1 z = .next 2) ↔ z ∈ positive_piece
  constructor
  · rintro ⟨_, hc⟩
    by_contra hz
    simp [routing, hz] at hc
  · intro hz
    constructor
    · exact ⟨z, by rw [dom_node_operator]; exact source_real (Or.inr hz), by
        cases z <;> simp [node_operator, lift_operator]⟩
    · simp [routing, hz]

/--
OET anchor: h-ff997c4726870929
The displayed two edges are all of the nonempty edge domains.
-/
theorem shared_edge_domains (v w : Fin 3) :
    shared_network.edge_domain v w =
      if (v = 0 ∨ v = 1) ∧ w = 2 then positive_piece else ∅ := by
  fin_cases v <;> fin_cases w <;> norm_num
  all_goals try first | exact alpha_edge_domain | exact beta_edge_domain
  all_goals
    ext z
    simp [FiniteOperatorNetwork.edge_domain, FiniteOperatorNetwork.to_transition_graph,
      shared_network, routing] <;> split_ifs <;> simp_all

/--
OET anchor: h-ff997c4726870929
The two prescribed entrance pieces, with no entrance at the square node.
-/
theorem shared_entry_domains (v : Fin 3) :
    shared_network.entry_domain v =
      if v = 0 then negative_piece else if v = 1 then positive_piece else ∅ := by
  fin_cases v <;> ext x <;> by_cases hn : x ∈ negative_piece <;>
    simp only [FiniteOperatorNetwork.entry_domain, shared_network, source, Fin.isValue,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceEq, hn, ↓reduceIte,
      Set.mem_union, Set.mem_setOf_eq, exists_const, exists_false, true_or, false_or,
      Set.mem_empty_iff_false, false_iff, iff_self, exists_prop, and_true]
  all_goals exact fun hp => positive_not_negative hp hn

end
end formal_oet.vol_01.exercise_solutions.network_sharing
