import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.piecewise_affine
import formal_oet.vol_01.ch_05_operator_networks.network_routing
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork

noncomputable section

section Cells
variable {E G : Type} [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]

/-- An actual affine equality, strict inequality, or non-strict inequality. -/
def IsAffineConstraint (c : E → Prop) : Prop :=
  (∃ f : E →ᵃ[ℝ] ℝ, c = fun x => f x = 0) ∨
  (∃ f : E →ᵃ[ℝ] ℝ, c = fun x => f x < 0) ∨
  (∃ f : E →ᵃ[ℝ] ℝ, c = fun x => f x ≤ 0)

/-- Linear cells now use typed real affine forms, not an unspecified predicate. -/
def IsAffineCell (Q : Set E) : Prop := IsLinearCell IsAffineConstraint Q

theorem affine_constraint_preimage (F : E →ᵃ[ℝ] G) (c : G → Prop)
    (hc : IsAffineConstraint c) : IsAffineConstraint (fun x => c (F x)) := by
  rcases hc with ⟨f, rfl⟩ | ⟨f, rfl⟩ | ⟨f, rfl⟩
  · exact Or.inl ⟨f.comp F, rfl⟩
  · exact Or.inr (Or.inl ⟨f.comp F, rfl⟩)
  · exact Or.inr (Or.inr ⟨f.comp F, rfl⟩)

/--
OET anchor: h-f2b0bcadc14fb5ac
真实仿射等式与不等式的有限交及仿射原像封闭性。
-/
theorem affine_cells_closed_under_intersection_and_preimage
    (Qs : List (Set E)) (hQs : ∀ Q ∈ Qs, IsAffineCell Q)
    (F : E →ᵃ[ℝ] G) (Q : Set G) (hQ : IsAffineCell Q) :
    IsAffineCell (list_intersection Qs) ∧ IsAffineCell (F ⁻¹' Q) := by
  exact linear_cells_closed_under_intersection_and_affine_preimage
    IsAffineConstraint IsAffineConstraint Qs hQs F (affine_constraint_preimage F) Q hQ

theorem affine_cell_univ : IsAffineCell (Set.univ : Set E) := by
  exact ⟨[], by simp, by simp⟩

theorem affine_cell_inter {Q R : Set E} (hQ : IsAffineCell Q) (hR : IsAffineCell R) :
    IsAffineCell (Q ∩ R) := by
  have h := linear_cell_list_intersection IsAffineConstraint [Q, R]
    (by intro S hS; simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
        rcases hS with rfl | rfl <;> assumption)
  simpa [list_intersection] using h

theorem affine_cell_preimage (F : E →ᵃ[ℝ] G) {Q : Set G} (hQ : IsAffineCell Q) :
    IsAffineCell (F ⁻¹' Q) :=
  linear_cell_affine_preimage IsAffineConstraint IsAffineConstraint F
    (affine_constraint_preimage F) Q hQ
end Cells

section Paths
variable {E V : Type} [AddCommGroup E] [Module ℝ E] {A : Set E}
variable (N : FiniteOperatorNetwork (Option A) none V)

/-- Read a set of nonabsorbing model points in the ambient vector space. -/
def real_locus (S : Set (Option A)) : Set E :=
  Subtype.val '' ((fun a : A => some a) ⁻¹' S)

omit [AddCommGroup E] [Module ℝ E] in
@[simp] theorem mem_real_locus (S : Set (Option A)) (a : A) :
    a.val ∈ real_locus S ↔ some a ∈ S := by
  constructor
  · rintro ⟨b, hb, hba⟩
    have : b = a := Subtype.ext hba
    simpa [this] using hb
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- Compose the genuine affine node maps in execution order. -/
def affine_path_map (F : V → E →ᵃ[ℝ] E) : List V → E →ᵃ[ℝ] E
  | [] => AffineMap.id ℝ E
  | v :: rest => (affine_path_map F rest).comp (F v)

/-- The recursive form of the finite intersection of affine-prefix preimages. -/
def affine_route_cell (F : V → E →ᵃ[ℝ] E) : List V → Set E
  | [] => Set.univ
  | [v] => F v ⁻¹' real_locus (N.terminal_domain v)
  | v :: w :: rest => F v ⁻¹' (real_locus (N.edge_domain v w) ∩
      affine_route_cell F (w :: rest))

theorem affine_route_cell_is_linear (F : V → E →ᵃ[ℝ] E)
    (hedge : ∀ v w, IsAffineCell (real_locus (N.edge_domain v w)))
    (hterm : ∀ v, IsAffineCell (real_locus (N.terminal_domain v)))
    (p : List V) : IsAffineCell (affine_route_cell N F p) := by
  induction p with
  | nil => exact affine_cell_univ
  | cons v rest ih =>
    cases rest with
    | nil => exact affine_cell_preimage (F v) (hterm v)
    | cons w rest => exact affine_cell_preimage (F v) (affine_cell_inter (hedge v w) ih)

omit [AddCommGroup E] [Module ℝ E] in
private theorem terminal_domain_iff_stop (v : V) (z : Option A)
    (hz : z ∈ N.node_image v) : z ∈ N.terminal_domain v ↔ N.choice v z = .stop := by
  classical
  constructor
  · intro ht
    cases hc : N.choice v z with
    | stop => rfl
    | next w => exact (ht.2 (Set.mem_iUnion.mpr ⟨w, hz, hc⟩)).elim
  · intro hc
    refine ⟨hz, ?_⟩
    intro hmem
    rcases Set.mem_iUnion.mp hmem with ⟨w, hw⟩
    have heq := hw.2
    simp [hc] at heq

/-- The node hypotheses are exactly affine realization on the actual node domain. -/
def AffineNodeRealization (F : V → E →ᵃ[ℝ] E) : Prop :=
  ∀ v (a : A), some a ∈ N.node_dom v →
    ∃ b : A, (N.node_op v).func (some a) = some b ∧ b.val = F v a.val

theorem terminal_iff_affine_route_cell (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (rest : List V) :
    ∀ v (a : A), some a ∈ N.node_dom v →
      (TerminalPathFrom N.node_op N.choice v (some a) (v :: rest) ↔
        a.val ∈ affine_route_cell N F (v :: rest)) := by
  induction rest with
  | nil =>
    intro v a ha
    rcases hF v a ha with ⟨b, hb, hFb⟩
    have hz : some b ∈ N.node_image v := ⟨some a, ha, hb⟩
    change TerminalPathFrom N.node_op N.choice v (some a) [v] ↔
      F v a.val ∈ real_locus (N.terminal_domain v)
    rw [← hFb, mem_real_locus, terminal_domain_iff_stop N v (some b) hz]
    constructor
    · intro ht
      cases ht with
      | stop hs => simpa [hb] using hs
      | next hs ht => exact (terminal_path_nonempty ht rfl).elim
    · intro hs
      exact TerminalPathFrom.stop (by simpa [hb] using hs)
  | cons w rest ih =>
    intro v a ha
    rcases hF v a ha with ⟨b, hb, hFb⟩
    change TerminalPathFrom N.node_op N.choice v (some a) (v :: w :: rest) ↔
      F v a.val ∈ real_locus (N.edge_domain v w) ∩ affine_route_cell N F (w :: rest)
    rw [← hFb]
    constructor
    · intro ht
      cases ht with
      | @next _ u _ _ hs ht =>
        have he : u = w := by cases ht <;> rfl
        subst u
        have hz : some b ∈ N.edge_domain v w := ⟨⟨some a, ha, hb⟩, by simpa [hb] using hs⟩
        have hw := N.edge_domain_subset_node_dom hz
        exact ⟨(mem_real_locus _ b).mpr hz,
          (ih w b hw).mp (by simpa [hb] using ht)⟩
    · rintro ⟨hz, ht⟩
      have hz' := (mem_real_locus _ b).mp hz
      have hw := N.edge_domain_subset_node_dom hz'
      exact TerminalPathFrom.next (by simpa [hb] using hz'.2)
        (by simpa [hb] using (ih w b hw).mpr ht)

/--
OET anchor: h-f2b0bcadc14fb5ac
实际路径域由入口片与逐步仿射原像相交得到；该等式从实际路由推导。
-/
theorem real_path_domain_eq_affine_cell (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (v : V) (rest : List V) :
    real_locus (N.path_domain (v :: rest)) =
      real_locus (N.entry_domain v) ∩ affine_route_cell N F (v :: rest) := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨hu, hp⟩
    have ht := N.path_terminal ⟨some a, hu⟩
    rw [hp] at ht
    have he : N.entry ⟨some a, hu⟩ = v := by cases ht <;> rfl
    have hv : some a ∈ N.node_dom v := he ▸ N.entry_mem ⟨some a, hu⟩
    refine ⟨(mem_real_locus _ a).mpr ⟨hu, he⟩, ?_⟩
    apply (terminal_iff_affine_route_cell N F hF rest v a hv).mp
    simpa [he] using ht
  · rintro ⟨⟨a, ha, rfl⟩, hroute⟩
    rcases ha with ⟨hu, he⟩
    have hv : some a ∈ N.node_dom v := he ▸ N.entry_mem ⟨some a, hu⟩
    have ht := (terminal_iff_affine_route_cell N F hF rest v a hv).mpr hroute
    refine ⟨a, ?_, rfl⟩
    refine ⟨hu, terminal_path_unique (N.path_terminal ⟨some a, hu⟩) ?_⟩
    simpa [he] using ht

/--
OET anchor: h-f2b0bcadc14fb5ac
仿射节点及线性入口、边域、终止域使每个实际路径域成为真正的线性单元。
-/
theorem actual_affine_path_domains_are_linear (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F)
    (hentry : ∀ v, IsAffineCell (real_locus (N.entry_domain v)))
    (hedge : ∀ v w, IsAffineCell (real_locus (N.edge_domain v w)))
    (hterm : ∀ v, IsAffineCell (real_locus (N.terminal_domain v))) (p : N.ReachablePath) :
    IsAffineCell (real_locus (N.path_domain p.nodes)) := by
  cases hp : p.nodes with
  | nil =>
    rcases p.nonempty_domain with ⟨x, hx, heq⟩
    have hlen := terminal_path_nonempty (N.path_terminal ⟨x, hx⟩)
    simp [heq, hp] at hlen
  | cons v rest =>
    rw [real_path_domain_eq_affine_cell N F hF]
    exact affine_cell_inter (hentry v) (affine_route_cell_is_linear N F hedge hterm _)


/-- Composition is proved for the actual terminal computation, with a genuine
`AffineMap` as its coordinate realization. -/
theorem terminal_eval_affine (F : V → E →ᵃ[ℝ] E) (hF : AffineNodeRealization N F)
    {v x p} (ht : TerminalPathFrom N.node_op N.choice v x p) :
    ∀ a : A, x = some a → some a ∈ N.node_dom v →
      ∃ b : A, chain_eval_nodes_core N.node_op p (some a) = some b ∧
        b.val = affine_path_map F p a.val := by
  induction ht with
  | @stop v x hs =>
    intro a hxa ha
    subst x
    rcases hF v a ha with ⟨b, hb, hFb⟩
    exact ⟨b, hb, by simpa [affine_path_map] using hFb⟩
  | @next v w x rest hs ht ih =>
    intro a hxa ha
    subst x
    rcases hF v a ha with ⟨b, hb, hFb⟩
    have hw := N.choice_next_mem ha hs
    rw [hb] at hw
    rcases ih b hb hw with ⟨c, hc, hFc⟩
    refine ⟨c, ?_, ?_⟩
    · simpa only [chain_eval_nodes_core, hb] using hc
    · simpa only [affine_path_map, AffineMap.coe_comp, Function.comp_apply, hFb] using hFc

/--
OET anchor: h-f2b0bcadc14fb5ac
在每个实际路径域上，网络外延等于节点仿射映射按路径次序的真实仿射复合。
-/
theorem actual_path_output_is_affine (F : V → E →ᵃ[ℝ] E)
    (hF : AffineNodeRealization N F) (p : N.ReachablePath)
    (a : A) (ha : some a ∈ N.path_domain p.nodes) :
    ∃ b : A, N.extensional_operator.func (some a) = some b ∧
      b.val = affine_path_map F p.nodes a.val := by
  rcases ha with ⟨hu, hp⟩
  have ht := N.path_terminal ⟨some a, hu⟩
  rw [hp] at ht
  rcases terminal_eval_affine N F hF ht a rfl (N.entry_mem ⟨some a, hu⟩) with ⟨b, hb, hFb⟩
  refine ⟨b, ?_, hFb⟩
  rw [N.extensional_apply_eq_chain_eval_path ⟨some a, hu⟩]
  simpa only [hp] using hb

omit [AddCommGroup E] [Module ℝ E] in
/--
OET anchor: h-f2b0bcadc14fb5ac
线性路径单元覆盖实际输入坐标域，且不同路径的单元互不相交。
-/
theorem real_path_domains_partition :
    (⋃ p : N.ReachablePath, real_locus (N.path_domain p.nodes)) = real_locus N.U ∧
    (∀ p q : N.ReachablePath, p.nodes ≠ q.nodes →
      Disjoint (real_locus (N.path_domain p.nodes)) (real_locus (N.path_domain q.nodes))) := by
  constructor
  · ext x
    constructor
    · intro hx
      rcases Set.mem_iUnion.mp hx with ⟨p, a, ha, rfl⟩
      exact ⟨a, N.path_domain_subset_source ha, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      have hc : some a ∈ ⋃ p : N.ReachablePath, N.path_domain p.nodes := by
        rw [N.reachable_path_domains_cover]
        exact ha
      rcases Set.mem_iUnion.mp hc with ⟨p, hp⟩
      exact Set.mem_iUnion.mpr ⟨p, a, hp, rfl⟩
  · intro p q hpq
    apply Set.disjoint_left.mpr
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab : a = b := Subtype.ext (hax.trans hbx.symm)
    subst b
    exact Set.disjoint_left.mp (N.disjoint_path_domain_of_ne hpq) ha hb

end Paths
end
end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
