import formal_oet.vol_01.ch_05_operator_networks.operator_network

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations

variable {X V W : Type} {bot : X}

/-- Transport a successor label along one fixed bijection. -/
def relabel_output_choice (e : V ≃ W) : OutputChoice V → OutputChoice W
  | .stop => .stop
  | .next v => .next (e v)

@[simp] theorem relabel_output_choice_next_iff (e : V ≃ W)
    (c : OutputChoice V) (w : W) :
    relabel_output_choice e c = .next w ↔ c = .next (e.symm w) := by
  cases c with
  | stop => simp [relabel_output_choice]
  | next v =>
    simp only [relabel_output_choice, OutputChoice.next.injEq]
    constructor
    · intro h
      rw [← h]
      simp
    · intro h
      rw [h]
      simp

/--
OET anchor: h-b2fb8267687c8372
Relabeling leaves every intermediate point unchanged.
-/
theorem terminal_path_relabel {node_op : V → Operator X bot}
    {choice : V → X → OutputChoice V} (e : V ≃ W)
    {v : V} {x : X} {p : List V}
    (h : TerminalPathFrom node_op choice v x p) :
    TerminalPathFrom (fun w => node_op (e.symm w))
      (fun w y => relabel_output_choice e (choice (e.symm w) y))
      (e v) x (p.map e) := by
  induction h with
  | stop hs =>
    apply TerminalPathFrom.stop
    simpa [relabel_output_choice] using congrArg (relabel_output_choice e) hs
  | @next β γ y rest hs ht ih =>
    refine TerminalPathFrom.next (γ := e γ) ?_ ?_
    · simpa [relabel_output_choice] using congrArg (relabel_output_choice e) hs
    · simpa using ih

/--
OET anchor: h-b2fb8267687c8372
A single global bijection transports the whole finite network.
-/
noncomputable def FiniteOperatorNetwork.relabel
    (N : FiniteOperatorNetwork X bot V) (e : V ≃ W) :
    FiniteOperatorNetwork X bot W := by
  classical
  letI : Fintype V := N.node_fintype
  exact
    { U := N.U
      bot_not_mem := N.bot_not_mem
      node_fintype := Fintype.ofEquiv V e
      node_op := fun w => N.node_op (e.symm w)
      node_dom_nonempty := fun w => N.node_dom_nonempty (e.symm w)
      entry := fun x => e (N.entry x)
      entry_mem := by intro x; simpa using N.entry_mem x
      choice := fun w y => relabel_output_choice e (N.choice (e.symm w) y)
      choice_next_mem := by
        intro β γ y hy hchoice
        exact N.choice_next_mem hy ((relabel_output_choice_next_iff e _ γ).mp hchoice)
      depth_bound := N.depth_bound
      path_of := fun x => (N.path_of x).map e
      path_terminal := fun x => terminal_path_relabel e (N.path_terminal x)
      path_length_le_depth := by intro x; simpa using N.path_length_le_depth x
      node_reachable := by
        intro w
        rcases N.node_reachable (e.symm w) with ⟨x, hx⟩
        exact ⟨x, List.mem_map.mpr ⟨e.symm w, hx, e.apply_symm_apply w⟩⟩ }

namespace FiniteOperatorNetwork

variable (N : FiniteOperatorNetwork X bot V) (e : V ≃ W)

@[simp] theorem relabel_source : (N.relabel e).U = N.U := rfl

@[simp] theorem relabel_path (x : {x : X // x ∈ N.U}) :
    (N.relabel e).path_of x = (N.path_of x).map e := rfl

@[simp] theorem relabel_path_length (x : {x : X // x ∈ N.U}) :
    ((N.relabel e).path_of x).length = (N.path_of x).length := by
  simp

/--
OET anchor: h-b2fb8267687c8372
One global bijection preserves which occurrences share a node.
-/
theorem relabel_label_equality (v w : V) : e v = e w ↔ v = w := e.injective.eq_iff

/-- OET anchor: h-b2fb8267687c8372
The local operator at the renamed node is the original operator. -/
@[simp] theorem relabel_node_op (v : V) :
    (N.relabel e).node_op (e v) = N.node_op v := by
  simp [relabel]

/-- OET anchor: h-b2fb8267687c8372
Relabeling transports the actual initial-entry partition. -/
theorem relabel_entry_domain (v : V) :
    (N.relabel e).entry_domain (e v) = N.entry_domain v := by
  ext x
  simp [entry_domain, relabel, e.injective.eq_iff]

/-- OET anchor: h-b2fb8267687c8372
The full transition domain is preserved, including outputs not reached from U. -/
theorem relabel_edge_domain (v w : V) :
    (N.relabel e).edge_domain (e v) (e w) = N.edge_domain v w := by
  ext z
  simp [edge_domain, to_transition_graph, relabel, relabel_output_choice_next_iff]

/-- OET anchor: h-b2fb8267687c8372
Nonempty edge domains define exactly the renamed graph edges. -/
theorem relabel_edge_nonempty (v w : V) :
    ((N.relabel e).edge_domain (e v) (e w)).Nonempty ↔
      (N.edge_domain v w).Nonempty := by
  rw [N.relabel_edge_domain e]

/-- OET anchor: h-b2fb8267687c8372
Terminal output domains are preserved under the same global relabeling. -/
theorem relabel_terminal_domain (v : V) :
    (N.relabel e).terminal_domain (e v) = N.terminal_domain v := by
  ext z
  simp only [terminal_domain, OperatorTransitionGraph.terminal_domain,
    Set.mem_diff, Set.mem_iUnion, not_exists]
  have himage : (N.relabel e).to_transition_graph.node_image (e v) =
      N.to_transition_graph.node_image v := by
    simp [OperatorTransitionGraph.node_image, OperatorTransitionGraph.node_dom,
      to_transition_graph, relabel]
  rw [himage]
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun w hw => ?_⟩
    apply h (e w)
    change z ∈ (N.relabel e).edge_domain (e v) (e w)
    simpa only [N.relabel_edge_domain e] using hw
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun w hw => ?_⟩
    apply h (e.symm w)
    change z ∈ N.edge_domain v (e.symm w)
    rw [← N.relabel_edge_domain e]
    simpa only [e.apply_symm_apply] using hw

/-- The chain identity also covers lists that are not reachable paths. -/
theorem chain_eval_nodes_relabel (p : List V) (x : X) :
    (N.relabel e).chain_eval_nodes (p.map e) x = N.chain_eval_nodes p x := by
  induction p generalizing x with
  | nil => rfl
  | cons v p ih =>
    simpa [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core,
      FiniteOperatorNetwork.relabel] using ih ((N.node_op v).func x)

/-- OET anchor: h-b2fb8267687c8372
Every intermediate point, at every prefix length, is unchanged. -/
theorem relabel_intermediate_point (p : List V) (k : Nat) (x : X) :
    (N.relabel e).chain_eval_nodes ((p.map e).take k) x =
      N.chain_eval_nodes (p.take k) x := by
  rw [← List.map_take]
  exact N.chain_eval_nodes_relabel e (p.take k) x

/-- Actual evaluation is unchanged. -/
theorem relabel_eval (x : {x : X // x ∈ N.U}) :
    (N.relabel e).eval x = N.eval x :=
  N.chain_eval_nodes_relabel e (N.path_of x) x.val

/--
OET anchor: h-b2fb8267687c8372
Relabeling preserves the full absorbing-point extension.
-/
theorem relabel_extensional_operator :
    (N.relabel e).extensional_operator = N.extensional_operator := by
  classical
  ext x
  by_cases hx : x ∈ N.U
  · simpa [extensional_operator, hx] using N.relabel_eval e ⟨x, hx⟩
  · simp [extensional_operator, hx]

/--
OET anchor: h-b2fb8267687c8372
Source points follow the corresponding relabeled list.
-/
theorem relabel_path_domain (p : List V) :
    (N.relabel e).path_domain (p.map e) = N.path_domain p := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    refine ⟨hx, ?_⟩
    apply List.map_injective_iff.mpr e.injective
    exact hp
  · rintro ⟨hx, hp⟩
    exact ⟨hx, congrArg (List.map e) hp⟩

theorem evaluation_depth_le_of_input_lengths (k : Nat)
    (h : ∀ x : {x : X // x ∈ N.U}, (N.path_of x).length ≤ k) :
    N.evaluation_depth ≤ k := by
  classical
  unfold evaluation_depth
  apply Finset.sup_le
  intro p _
  rcases p.nonempty_domain with ⟨x, hx, hp⟩
  simpa only [hp] using h ⟨x, hx⟩

theorem input_path_length_le_evaluation_depth (x : {x : X // x ∈ N.U}) :
    (N.path_of x).length ≤ N.evaluation_depth :=
  N.reachable_path_nodes_length_le_evaluation_depth
    ⟨N.path_of x, ⟨x.val, x.property, rfl⟩⟩

/--
OET anchor: h-b2fb8267687c8372
Equality of the actual maximum path length, not only the stored fuel bound.
-/
theorem relabel_evaluation_depth :
    (N.relabel e).evaluation_depth = N.evaluation_depth := by
  apply le_antisymm
  · apply (N.relabel e).evaluation_depth_le_of_input_lengths
    intro x
    simpa using N.input_path_length_le_evaluation_depth x
  · apply N.evaluation_depth_le_of_input_lengths
    intro x
    simpa using (N.relabel e).input_path_length_le_evaluation_depth x

/-- An encoding choice, not an isomorphism quotient. -/
noncomputable def standard_node_equiv : V ≃ Fin N.node_count := by
  letI : Fintype V := N.node_fintype
  exact Fintype.equivFin V

noncomputable def standard_relabel :
    FiniteOperatorNetwork X bot (Fin N.node_count) :=
  N.relabel N.standard_node_equiv

/--
OET anchor: h-b2fb8267687c8372
Every finite-label network has a finite numbered encoding preserving its source,
terminal operator and all actual path domains.
-/
theorem standard_relabel_preserves :
    N.standard_relabel.U = N.U ∧
    N.standard_relabel.extensional_operator = N.extensional_operator ∧
    (∀ x : {x : X // x ∈ N.U},
      N.standard_relabel.path_of x = (N.path_of x).map N.standard_node_equiv) ∧
    (∀ p : List V,
      N.standard_relabel.path_domain (p.map N.standard_node_equiv) = N.path_domain p) :=
  ⟨rfl, N.relabel_extensional_operator N.standard_node_equiv,
    fun _ => rfl, fun p => N.relabel_path_domain N.standard_node_equiv p⟩

end FiniteOperatorNetwork
end formal_oet.vol_01.ch_05_operator_networks
