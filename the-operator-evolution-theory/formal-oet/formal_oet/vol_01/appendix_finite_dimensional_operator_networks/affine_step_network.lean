import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.affine_path_cells

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks
open FiniteOperatorNetwork
noncomputable section

abbrev StepReal := {x : ℝ // x ∈ (Set.univ : Set ℝ)}
def step_real (x : ℝ) : StepReal := ⟨x, Set.mem_univ x⟩
def step_value (v : Bool) : ℝ := if v then 1 else 0

def step_node (v : Bool) : Operator (Option StepReal) none where
  func := fun x => x.map (fun _ => step_real (step_value v))
  preserves_bot := rfl

@[simp] theorem step_node_dom (v : Bool) (x : Option StepReal) :
    x ∈ dom (step_node v) ↔ x ≠ none := by cases x <;> simp [dom, step_node]

def step_entry (x : Option StepReal) : Bool :=
  match x with
  | none => false
  | some a => if a.val < 0 then false else true

/-- Two constant affine nodes, no edges, with negative and nonnegative entry cells. -/
def affine_step_network : FiniteOperatorNetwork (Option StepReal) none Bool where
  U := {x | x ≠ none}
  bot_not_mem := by simp
  node_fintype := inferInstance
  node_op := step_node
  node_dom_nonempty := fun v => ⟨some (step_real 0), by simp⟩
  entry := fun x => step_entry x.val
  entry_mem := fun x => (step_node_dom _ _).mpr x.property
  choice := fun _ _ => .stop
  choice_next_mem := by intro _ _ _ _ h; cases h
  depth_bound := 1
  path_of := fun x => [step_entry x.val]
  path_terminal := fun _ => TerminalPathFrom.stop rfl
  path_length_le_depth := by intro x; simp
  node_reachable := by
    intro v
    cases v
    · exact ⟨⟨some (step_real (-1)), by simp⟩, by norm_num [step_entry, step_real]⟩
    · exact ⟨⟨some (step_real 0), by simp⟩, by norm_num [step_entry, step_real]⟩

def step_affine_map (v : Bool) : ℝ →ᵃ[ℝ] ℝ := AffineMap.const ℝ ℝ (step_value v)

theorem step_nodes_are_affine : AffineNodeRealization affine_step_network step_affine_map := by
  intro v a ha
  exact ⟨step_real (step_value v), rfl, rfl⟩

theorem step_entry_cell (v : Bool) :
    real_locus (affine_step_network.entry_domain v) =
      if v then {x : ℝ | 0 ≤ x} else {x : ℝ | x < 0} := by
  ext x
  have h := mem_real_locus (affine_step_network.entry_domain v) (step_real x)
  change (x ∈ real_locus (affine_step_network.entry_domain v) ↔ _) at h
  rw [h]
  cases v <;> simp [entry_domain, affine_step_network, step_entry, step_real]

theorem step_no_edges (v w : Bool) : affine_step_network.edge_domain v w = ∅ := by
  ext x
  simp [edge_domain, to_transition_graph,
    affine_step_network]

theorem step_terminal_cell (v : Bool) :
    real_locus (affine_step_network.terminal_domain v) = {step_value v} := by
  ext x
  rw [show x ∈ real_locus (affine_step_network.terminal_domain v) ↔
      some (step_real x) ∈ affine_step_network.terminal_domain v from
      mem_real_locus _ (step_real x)]
  simp only [terminal_domain, OperatorTransitionGraph.terminal_domain, to_transition_graph,
    OperatorTransitionGraph.node_image, OperatorTransitionGraph.node_dom,
    affine_step_network, Set.mem_diff, Set.mem_image, Set.mem_iUnion, Set.mem_setOf_eq,
    Set.mem_singleton_iff]
  have hstop : ∀ i : Bool, ¬ (OutputChoice.stop : OutputChoice Bool) = .next i :=
    fun _ h => by cases h
  simp only [hstop, and_false, exists_const, not_false_eq_true, and_true]
  constructor
  · rintro ⟨z, hz, heq⟩
    cases z with
    | none => simp [dom, step_node] at hz
    | some a => simpa [step_node, step_real] using (congrArg (fun z => z.map Subtype.val) heq).symm
  · intro hx
    subst x
    exact ⟨some (step_real 0), by simp, rfl⟩

private theorem affine_cell_one_constraint (c : ℝ → Prop) (hc : IsAffineConstraint c) :
    IsAffineCell {x | c x} := by
  exact ⟨[c], by simpa using hc, by ext x; simp⟩

theorem step_cells_are_linear :
    (∀ v, IsAffineCell (real_locus (affine_step_network.entry_domain v))) ∧
    (∀ v w, IsAffineCell (real_locus (affine_step_network.edge_domain v w))) ∧
    (∀ v, IsAffineCell (real_locus (affine_step_network.terminal_domain v))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [step_entry_cell]
    cases v
    · exact affine_cell_one_constraint _ (Or.inr (Or.inl ⟨AffineMap.id ℝ ℝ, rfl⟩))
    · apply affine_cell_one_constraint
      refine Or.inr (Or.inr ⟨-(AffineMap.id ℝ ℝ), ?_⟩)
      funext x
      change (0 ≤ x) = (-x ≤ 0)
      simp
  · intro v w
    rw [step_no_edges]
    have h : real_locus (∅ : Set (Option StepReal)) = (∅ : Set ℝ) := by simp [real_locus]
    rw [h]
    have hc : IsAffineConstraint (fun _ : ℝ => (1 : ℝ) = 0) :=
      Or.inl ⟨AffineMap.const ℝ ℝ 1, rfl⟩
    simpa using affine_cell_one_constraint _ hc
  · intro v
    rw [step_terminal_cell]
    have hc : IsAffineConstraint (fun x : ℝ => x = step_value v) := by
      refine Or.inl ⟨AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ (step_value v), ?_⟩
      funext x
      simp [sub_eq_zero]
    exact affine_cell_one_constraint _ hc

theorem step_network_eval (x : ℝ) :
    affine_step_network.extensional_operator.func (some (step_real x)) =
      some (step_real (affine_step x)) := by
  by_cases hx : x < 0 <;>
    simp [extensional_operator, affine_step_network, eval, chain_eval_nodes_core,
      step_entry, step_node, step_real, step_value, affine_step, hx]

/--
OET anchor: h-f2b0bcadc14fb5ac
**命题（分片仿射性不蕴含跨路径连续性）**
The step function is the actual extensional evaluation of a finite network
with affine nodes and the displayed entry/terminal cells.
-/
theorem affine_step_network_counterexample :
    AffineNodeRealization affine_step_network step_affine_map ∧
    ((∀ v, IsAffineCell (real_locus (affine_step_network.entry_domain v))) ∧
      (∀ v w, IsAffineCell (real_locus (affine_step_network.edge_domain v w))) ∧
      (∀ v, IsAffineCell (real_locus (affine_step_network.terminal_domain v)))) ∧
    (∀ x : ℝ, affine_step_network.extensional_operator.func (some (step_real x)) =
      some (step_real (affine_step x))) ∧
    ¬ ContinuousAt affine_step 0 :=
  ⟨step_nodes_are_affine, step_cells_are_linear, step_network_eval,
    piecewise_affine_does_not_imply_cross_path_continuity.2.2⟩

end
end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
