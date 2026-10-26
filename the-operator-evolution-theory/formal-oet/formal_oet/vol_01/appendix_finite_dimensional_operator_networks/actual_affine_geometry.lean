import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.restricted_affine_geometry
import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.affine_path_cells
import formal_oet.vol_01.ch_05_operator_networks.prefix_thresholds
import formal_oet.vol_01.ch_05_operator_networks.output_bounds
import Mathlib.Analysis.Convex.Basic

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks
open formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork
noncomputable section

section ConvexCells
variable {E : Type} [AddCommGroup E] [Module ℝ E]

private theorem affine_constraint_convex (c : E → Prop) (hc : IsAffineConstraint c) :
    Convex ℝ {x | c x} := by
  rcases hc with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩
  · exact (convex_singleton (0 : ℝ)).affine_preimage f
  · exact (convex_Iio (0 : ℝ)).affine_preimage f
  · exact (convex_Iic (0 : ℝ)).affine_preimage f

/-- Every stated affine cell, including cells defined with strict inequalities, is convex. -/
theorem affine_cell_convex {D : Set E} (hD : IsAffineCell D) : Convex ℝ D := by
  rcases hD with ⟨cs, hcs, rfl⟩
  have heq : {x | ∀ c ∈ cs, c x} = ⋂ c ∈ cs, {x | c x} := by ext x; simp
  rw [heq]
  exact convex_iInter₂ (fun c hc => affine_constraint_convex c (hcs c hc))
end ConvexCells

section PrefixRouting
variable {E V : Type} [AddCommGroup E] [Module ℝ E] {A : Set E}
variable (N : FiniteOperatorNetwork (Option A) none V)

private inductive TraversesPrefix : V → Option A → List V → Prop where
  | single {v x} : TraversesPrefix v x [v]
  | next {v w x rest} : N.choice v ((N.node_op v).func x) = .next w →
      TraversesPrefix w ((N.node_op v).func x) rest → TraversesPrefix v x (v :: rest)

omit [AddCommGroup E] [Module ℝ E] in
private theorem traverses_nonempty {v x q} (h : TraversesPrefix N v x q) : q ≠ [] := by
  cases h <;> simp

omit [AddCommGroup E] [Module ℝ E] in
private theorem traverses_of_prefix {v x p}
    (ht : TerminalPathFrom N.node_op N.choice v x p) {q : List V}
    (hne : q ≠ []) (hpref : is_prefix q p) : TraversesPrefix N v x q := by
  induction ht generalizing q with
  | @stop v x hs =>
    cases q with
    | nil => exact (hne rfl).elim
    | cons w qs =>
      obtain ⟨r, hr⟩ := hpref
      have hh : v = w := (List.cons.inj hr).1
      subst w
      have htail : [] = qs ++ r := (List.cons.inj hr).2
      have hqs := (List.append_eq_nil_iff.mp htail.symm).1
      subst qs
      exact .single
  | @next v w x rest hs ht ih =>
    cases q with
    | nil => exact (hne rfl).elim
    | cons u qs =>
      obtain ⟨r, hr⟩ := hpref
      have hh : v = u := (List.cons.inj hr).1
      subst u
      have htail : rest = qs ++ r := (List.cons.inj hr).2
      cases qs with
      | nil => exact .single
      | cons z zs => exact .next hs (ih (by simp) ⟨r, htail⟩)

omit [AddCommGroup E] [Module ℝ E] in
private theorem prefix_of_traverses {v x q} (hq : TraversesPrefix N v x q) :
    ∀ p, TerminalPathFrom N.node_op N.choice v x p → is_prefix q p := by
  induction hq with
  | single =>
    intro p ht
    cases ht
    · exact ⟨[], rfl⟩
    · exact ⟨_, rfl⟩
  | @next v w x rest hs hrest ih =>
    intro p ht
    cases ht with
    | stop hstop => simp [hstop] at hs
    | @next _ u _ ps hu hp =>
      have hw : u = w := OutputChoice.next.inj (hu.symm.trans hs)
      subst u
      obtain ⟨r, hr⟩ := ih ps hp
      exact ⟨r, by simp only [List.cons_append, hr]⟩

/-- Prefix routing imposes only the traversed edges, with no terminal condition. -/
def affine_prefix_route_cell (F : V → E →ᵃ[ℝ] E) : List V → Set E
  | [] => Set.univ
  | [_] => Set.univ
  | v :: w :: rest => F v ⁻¹' (real_locus (N.edge_domain v w) ∩
      affine_prefix_route_cell F (w :: rest))

private theorem traverses_iff_affine_prefix_cell (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (rest : List V) :
    ∀ v (a : A), some a ∈ N.node_dom v →
      (TraversesPrefix N v (some a) (v :: rest) ↔
        a.val ∈ affine_prefix_route_cell N F (v :: rest)) := by
  induction rest with
  | nil =>
    intro v a ha
    constructor
    · intro _; trivial
    · intro _; exact .single
  | cons w rest ih =>
    intro v a ha
    obtain ⟨b, hb, hFb⟩ := hF v a ha
    change TraversesPrefix N v (some a) (v :: w :: rest) ↔
      F v a.val ∈ real_locus (N.edge_domain v w) ∩ affine_prefix_route_cell N F (w :: rest)
    rw [← hFb]
    constructor
    · intro ht
      cases ht with
      | @next _ u _ _ hs ht =>
        have he : u = w := by cases ht <;> rfl
        subst u
        have hz : some b ∈ N.edge_domain v w := ⟨⟨some a, ha, hb⟩, by simpa [hb] using hs⟩
        have hw := N.edge_domain_subset_node_dom hz
        exact ⟨(mem_real_locus _ b).mpr hz, (ih w b hw).mp (by simpa [hb] using ht)⟩
    · rintro ⟨hz, ht⟩
      have hz' := (mem_real_locus _ b).mp hz
      have hw := N.edge_domain_subset_node_dom hz'
      exact .next (by simpa [hb] using hz'.2)
        (by simpa [hb] using (ih w b hw).mpr ht)

/-- The actual initial prefix domain is the entry cell intersected with the
successive affine preimages of precisely the prefix edge domains. -/
theorem real_prefix_domain_eq_affine_cell (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (v : V) (rest : List V) :
    real_locus (N.prefix_domain (v :: rest)) =
      real_locus (N.entry_domain v) ∩ affine_prefix_route_cell N F (v :: rest) := by
  ext x
  constructor
  · rintro ⟨a, ⟨hu, hpref⟩, rfl⟩
    have ht := N.path_terminal ⟨some a, hu⟩
    have htr := traverses_of_prefix N ht (List.cons_ne_nil v rest) hpref
    have he : N.entry ⟨some a, hu⟩ = v := by cases htr <;> rfl
    have hv : some a ∈ N.node_dom v := he ▸ N.entry_mem ⟨some a, hu⟩
    refine ⟨(mem_real_locus _ a).mpr ⟨hu, he⟩, ?_⟩
    exact (traverses_iff_affine_prefix_cell N F hF rest v a hv).mp (by simpa [he] using htr)
  · rintro ⟨⟨a, ⟨hu, he⟩, rfl⟩, hroute⟩
    have hv : some a ∈ N.node_dom v := he ▸ N.entry_mem ⟨some a, hu⟩
    have htr := (traverses_iff_affine_prefix_cell N F hF rest v a hv).mpr hroute
    refine ⟨a, ⟨hu, ?_⟩, rfl⟩
    exact prefix_of_traverses N htr _ (by simpa [he] using N.path_terminal ⟨some a, hu⟩)

private theorem affine_prefix_cell_is_linear (F : V → E →ᵃ[ℝ] E)
    (hedge : ∀ v w, IsAffineCell (real_locus (N.edge_domain v w))) (q : List V) :
    IsAffineCell (affine_prefix_route_cell N F q) := by
  induction q with
  | nil => exact affine_cell_univ
  | cons v rest ih =>
    cases rest with
    | nil => exact affine_cell_univ
    | cons w rest => exact affine_cell_preimage (F v) (affine_cell_inter (hedge v w) ih)

/-- Linear entry and edge cells make each actual reachable prefix initial domain convex. -/
theorem actual_prefix_initial_domain_convex (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F)
    (hentry : ∀ v, IsAffineCell (real_locus (N.entry_domain v)))
    (hedge : ∀ v w, IsAffineCell (real_locus (N.edge_domain v w)))
    (q : N.PrefixOccurrence) : Convex ℝ (real_locus (N.prefix_domain q.nodes)) := by
  cases hq : q.nodes with
  | nil => exact (q.nonempty_nodes hq).elim
  | cons v rest =>
    rw [real_prefix_domain_eq_affine_cell N F hF]
    exact affine_cell_convex (affine_cell_inter (hentry v) (affine_prefix_cell_is_linear N F hedge _))


private theorem terminal_prefix_eval_affine (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) {v x p}
    (ht : TerminalPathFrom N.node_op N.choice v x p) :
    ∀ q, is_prefix q p → ∀ a : A, x = some a → some a ∈ N.node_dom v →
      ∃ b : A, chain_eval_nodes_core N.node_op q (some a) = some b ∧
        b.val = affine_path_map F q a.val := by
  induction ht with
  | @stop v x hs =>
    intro q hq a hxa ha
    subst x
    cases q with
    | nil => exact ⟨a, rfl, rfl⟩
    | cons w qs =>
      obtain ⟨r, hr⟩ := hq
      have hh : v = w := (List.cons.inj hr).1
      subst w
      have htail : [] = qs ++ r := (List.cons.inj hr).2
      have hqs := (List.append_eq_nil_iff.mp htail.symm).1
      subst qs
      obtain ⟨b, hb, hFb⟩ := hF v a ha
      exact ⟨b, hb, by simpa [affine_path_map] using hFb⟩
  | @next v w x rest hs ht ih =>
    intro q hq a hxa ha
    subst x
    cases q with
    | nil => exact ⟨a, rfl, rfl⟩
    | cons u qs =>
      obtain ⟨r, hr⟩ := hq
      have hh : v = u := (List.cons.inj hr).1
      subst u
      have htail : rest = qs ++ r := (List.cons.inj hr).2
      obtain ⟨b, hb, hFb⟩ := hF v a ha
      have hw := N.choice_next_mem ha hs
      rw [hb] at hw
      obtain ⟨c, hc, hFc⟩ := ih qs ⟨r, htail⟩ b hb hw
      refine ⟨c, ?_, ?_⟩
      · simpa only [chain_eval_nodes_core, hb] using hc
      · simpa only [affine_path_map, AffineMap.coe_comp, Function.comp_apply, hFb] using hFc

private theorem real_chain_prefix_image (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (S : Set (Option A)) (r : List V)
    (hS : S ⊆ N.U)
    (hpref : ∀ x (hx : x ∈ S), is_prefix r (N.path_of ⟨x, hS hx⟩)) :
    real_locus (N.chain_eval_nodes r '' S) = affine_path_map F r '' real_locus S := by
  have hev (a : A) (ha : some a ∈ S) :
      ∃ b : A, N.chain_eval_nodes r (some a) = some b ∧ b.val = affine_path_map F r a.val :=
    terminal_prefix_eval_affine N F hF (N.path_terminal ⟨some a, hS ha⟩) r
      (hpref (some a) ha) a rfl (N.entry_mem ⟨some a, hS ha⟩)
  ext y
  constructor
  · rintro ⟨b, ⟨x, hx, heq⟩, rfl⟩
    cases x with
    | none => exact (N.bot_not_mem (hS hx)).elim
    | some a =>
      obtain ⟨c, hc, hval⟩ := hev a hx
      have hcb : c = b := Option.some.inj (hc.symm.trans heq)
      subst c
      exact ⟨a.val, (mem_real_locus _ a).mpr hx, hval.symm⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
    obtain ⟨b, hb, hval⟩ := hev a ha
    exact ⟨b, ⟨some a, ha, hb⟩, hval⟩

/-- OET anchor: h-e4b8f2d657424bba
The actual current input domain is the affine image of the initial prefix cell,
not the ambient domain of the node extension. -/
theorem real_prefix_input_domain_eq_affine_image (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (q : N.PrefixOccurrence) :
    real_locus (N.prefix_input_domain q.nodes) =
      affine_path_map F q.nodes.dropLast '' real_locus (N.prefix_domain q.nodes) := by
  apply real_chain_prefix_image N F hF _ _ (fun _ hx => hx.choose)
  intro x hx
  obtain ⟨hu, r, hr⟩ := hx
  obtain ⟨s, hs⟩ := List.dropLast_prefix q.nodes
  exact ⟨s ++ r, by rw [← List.append_assoc, hs]; exact hr⟩

/-- OET anchor: h-e4b8f2d657424bba
Actual occurrence input domains are nonempty convex sets under affine routing;
no ambient-interior assumption is required. -/
theorem actual_prefix_input_domain_convex_nonempty (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F)
    (hentry : ∀ v, IsAffineCell (real_locus (N.entry_domain v)))
    (hedge : ∀ v w, IsAffineCell (real_locus (N.edge_domain v w)))
    (q : N.PrefixOccurrence) :
    Convex ℝ (real_locus (N.prefix_input_domain q.nodes)) ∧
      (real_locus (N.prefix_input_domain q.nodes)).Nonempty := by
  rw [real_prefix_input_domain_eq_affine_image N F hF q]
  refine ⟨(actual_prefix_initial_domain_convex N F hF hentry hedge q).affine_image _, ?_⟩
  obtain ⟨x, hx⟩ := N.prefix_domain_nonempty q
  have hu : x ∈ N.U := hx.choose
  cases x with
  | none => exact (N.bot_not_mem hu).elim
  | some a => exact Set.Nonempty.image _ ⟨a.val, (mem_real_locus _ a).mpr hx⟩

/-- The fixed complete path's intermediate set is the actual affine-prefix image. -/
theorem real_path_intermediate_domain (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (p : N.ReachablePath) (s : ℕ) :
    real_locus (N.chain_eval_nodes (p.nodes.take s) '' N.path_domain p.nodes) =
      affine_path_map F (p.nodes.take s) '' real_locus (N.path_domain p.nodes) := by
  apply real_chain_prefix_image N F hF _ _ (fun _ hx => N.path_domain_subset_source hx)
  intro x hx
  refine ⟨p.nodes.drop s, ?_⟩
  rw [List.take_append_drop]
  exact hx.choose_spec


private theorem affine_path_map_append (F : V → E →ᵃ[ℝ] E) (p q : List V) :
    affine_path_map F (p ++ q) = (affine_path_map F q).comp (affine_path_map F p) := by
  induction p with
  | nil => ext x; rfl
  | cons v p ih =>
    ext x
    simp [affine_path_map, ih]

/-- The actual intermediate input/output set for a fixed complete path. -/
def path_intermediate_set (p : N.ReachablePath) (s : ℕ) : Set E :=
  real_locus (N.chain_eval_nodes (p.nodes.take s) '' N.path_domain p.nodes)

/-- OET anchor: h-e4b8f2d657424bba
Every intermediate set on a reachable complete path is nonempty. -/
theorem path_intermediate_set_nonempty (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (p : N.ReachablePath) (s : ℕ) :
    (path_intermediate_set N p s).Nonempty := by
  unfold path_intermediate_set
  rw [real_path_intermediate_domain N F hF]
  obtain ⟨x, hx⟩ := p.nonempty_domain
  cases x with
  | none => exact (N.bot_not_mem (N.path_domain_subset_source hx)).elim
  | some a => exact Set.Nonempty.image _ ⟨a.val, (mem_real_locus _ a).mpr hx⟩

/-- Each next intermediate set is the affine image of the preceding actual set. -/
theorem path_intermediate_set_succ (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (p : N.ReachablePath) (s : ℕ) (hs : s < p.nodes.length) :
    path_intermediate_set N p (s + 1) = F p.nodes[s] '' path_intermediate_set N p s := by
  unfold path_intermediate_set
  rw [real_path_intermediate_domain N F hF, real_path_intermediate_domain N F hF,
    List.take_succ_eq_append_getElem hs, affine_path_map_append]
  simp [affine_path_map, Set.image_image]

/-- OET anchor: h-e4b8f2d657424bba
Actual available directions propagate by the node's linear part. -/
theorem path_direction_span_succ (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (p : N.ReachablePath) (s : ℕ) (hs : s < p.nodes.length) :
    direction_span (path_intermediate_set N p (s + 1)) =
      (direction_span (path_intermediate_set N p s)).map (F p.nodes[s]).linear := by
  rw [path_intermediate_set_succ N F hF p s hs]
  have heq : (F p.nodes[s] : E → E) =
      fun x => (F p.nodes[s]).linear x + F p.nodes[s] 0 := by
    funext x
    exact congrFun (F p.nodes[s]).decomp x
  rw [heq]
  exact direction_span_affine_image _ _ _

/-- OET anchor: h-e4b8f2d657424bba
The available affine dimension cannot increase along a fixed complete path. -/
theorem path_direction_finrank_mono [Module.Finite ℝ E] (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (p : N.ReachablePath) (s : ℕ) (hs : s < p.nodes.length) :
    Module.finrank ℝ (direction_span (path_intermediate_set N p (s + 1))) ≤
      Module.finrank ℝ (direction_span (path_intermediate_set N p s)) := by
  rw [path_direction_span_succ N F hF p s hs]
  exact Submodule.finrank_map_le _ _

omit [AddCommGroup E] [Module ℝ E] in
private theorem traverses_last_input_mem {v x q} (ht : TraversesPrefix N v x q)
    (hx : x ∈ N.node_dom v) : ∀ hn : q ≠ [],
      N.chain_eval_nodes q.dropLast x ∈ N.node_dom (q.getLast hn) := by
  induction ht with
  | single => intro hn; simpa [chain_eval_nodes, chain_eval_nodes_core] using hx
  | @next v w x rest hs ht ih =>
    intro hn
    have hr := traverses_nonempty N ht
    simpa [List.dropLast_cons_of_ne_nil hr, List.getLast_cons hr,
      chain_eval_nodes, chain_eval_nodes_core] using ih (N.choice_next_mem hx hs) hr

omit [AddCommGroup E] [Module ℝ E] in
/-- Reachability guarantees that every actual current input belongs to the
last node's genuine domain, before any affine extension is chosen. -/
theorem actual_prefix_input_subset_node_domain (q : N.PrefixOccurrence) :
    N.prefix_input_domain q.nodes ⊆ N.node_dom (prefix_occurrence_last N q) := by
  rintro y ⟨x, ⟨hx, hpref⟩, rfl⟩
  exact traverses_last_input_mem N
    (traverses_of_prefix N (N.path_terminal ⟨x, hx⟩) q.nonempty_nodes hpref)
    (N.entry_mem ⟨x, hx⟩) q.nonempty_nodes

/-- The actual complete path image in coordinates. -/
theorem real_path_output_set_eq_affine_image (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (p : N.ReachablePath) :
    real_locus (N.path_output_set p) = affine_path_map F p.nodes '' real_locus (N.path_domain p.nodes) := by
  have heq : N.path_output_set p = N.chain_eval_nodes p.nodes '' N.path_domain p.nodes := by
    apply Set.image_congr
    intro x hx
    exact (N.local_equivalent_extensional_path_chain p x hx).trans
      (N.path_chain_apply_eq_chain_eval_nodes p.nodes x)
  rw [heq]
  apply real_chain_prefix_image N F hF _ _ (fun _ hx => N.path_domain_subset_source hx)
  intro x hx
  exact ⟨[], by simpa using hx.choose_spec⟩

/-- The range of the path linear map on the actual input directions equals
exactly the direction space of its actual output set. -/
theorem path_direction_range_eq_output (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (p : N.ReachablePath) :
    (direction_span (real_locus (N.path_domain p.nodes))).map (affine_path_map F p.nodes).linear =
      direction_span (real_locus (N.path_output_set p)) := by
  rw [real_path_output_set_eq_affine_image N F hF]
  have heq : (affine_path_map F p.nodes : E → E) =
      fun x => (affine_path_map F p.nodes).linear x + affine_path_map F p.nodes 0 := by
    funext x
    exact congrFun (affine_path_map F p.nodes).decomp x
  rw [heq, direction_span_affine_image]

/-- OET anchor: h-e4b8f2d657424bba
Only the restricted path range, and hence its dimension, is independent of
which affine extension realizes the same network. -/
theorem path_direction_range_extension_invariant (F G : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (hG : AffineNodeRealization N G) (p : N.ReachablePath) :
    (direction_span (real_locus (N.path_domain p.nodes))).map (affine_path_map F p.nodes).linear =
      (direction_span (real_locus (N.path_domain p.nodes))).map (affine_path_map G p.nodes).linear := by
  rw [path_direction_range_eq_output N F hF, path_direction_range_eq_output N G hG]

end PrefixRouting
end
end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
