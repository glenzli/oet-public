import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.affine_path_cells
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks
open FiniteOperatorNetwork

noncomputable section

variable {E : Type} [AddCommGroup E] [Module ℝ E]

/--
OET anchor: h-292cbcc4dd47c8cc
An affine subspace of a finite-dimensional real vector space is a linear cell.
-/
theorem affine_range_is_cell [FiniteDimensional ℝ E] (F : E →ᵃ[ℝ] E) :
    IsAffineCell (Set.range F) := by
  classical
  let S := F.linear.range
  let b := Module.finBasis ℝ (E ⧸ S)
  let T : E →ᵃ[ℝ] E := AffineMap.id ℝ E - AffineMap.const ℝ E (F 0)
  let c (i : Fin (Module.finrank ℝ (E ⧸ S))) : E →ᵃ[ℝ] ℝ :=
    ((b.coord i).comp S.mkQ).toAffineMap.comp T
  have hzero (y : E) : (∀ i, c i y = 0) ↔ y ∈ Set.range F := by
    change (∀ i, b.coord i (S.mkQ (y - F 0)) = 0) ↔ _
    rw [b.forall_coord_eq_zero_iff]
    have hker : S.mkQ (y - F 0) = 0 ↔ y - F 0 ∈ S := by
      change y - F 0 ∈ LinearMap.ker S.mkQ ↔ _
      rw [Submodule.ker_mkQ]
    rw [hker]
    change (∃ x, F.linear x = y - F 0) ↔ ∃ x, F x = y
    have hF (x : E) : F x = F.linear x + F 0 := congrFun F.decomp x
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [hF, hx, sub_add_cancel]⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [← hx, hF, add_sub_cancel_right]⟩
  refine ⟨List.ofFn (fun i => fun y => c i y = 0), ?_, ?_⟩
  · intro d hd
    rcases List.mem_ofFn.mp hd with ⟨i, rfl⟩
    exact Or.inl ⟨c i, rfl⟩
  · ext y
    simpa using (hzero y).symm

/-- Full real part, with the same subtype presentation used by Appendix E. -/
abbrev FullReal (E : Type) := (Set.univ : Set E)

def full_real (x : E) : FullReal E := ⟨x, Set.mem_univ x⟩

def full_affine_operator (F : E →ᵃ[ℝ] E) : Operator (Option (FullReal E)) none where
  func := fun x => x.map (fun a => full_real (F a.val))
  preserves_bot := rfl

@[simp] theorem full_affine_operator_dom (F : E →ᵃ[ℝ] E)
    (x : Option (FullReal E)) : x ∈ dom (full_affine_operator F) ↔ x ≠ none := by
  cases x <;> simp [dom, full_affine_operator]

section CellNetwork

variable {I : Type} [Fintype I]
variable (Q : I → Set E) (H : I → E →ᵃ[ℝ] E)

def cell_source : Set (Option (FullReal E)) :=
  {z | ∃ a : FullReal E, z = some a ∧ ∃ i, a.val ∈ Q i}

def cell_input (x : cell_source Q) : FullReal E := x.property.choose

omit [AddCommGroup E] [Module ℝ E] [Fintype I] in
theorem cell_input_spec (x : cell_source Q) :
    x.val = some (cell_input Q x) ∧ ∃ i, (cell_input Q x).val ∈ Q i :=
  x.property.choose_spec

def cell_entry (x : cell_source Q) : I := (cell_input_spec Q x).2.choose

omit [AddCommGroup E] [Module ℝ E] [Fintype I] in
theorem cell_entry_mem (x : cell_source Q) :
    (cell_input Q x).val ∈ Q (cell_entry Q x) := (cell_input_spec Q x).2.choose_spec

variable (hdisj : ∀ i j, i ≠ j → Disjoint (Q i) (Q j))
variable (hne : ∀ i, (Q i).Nonempty)

include hdisj in
omit [AddCommGroup E] [Module ℝ E] [Fintype I] in
theorem cell_entry_eq (x : cell_source Q) (i : I) (hi : (cell_input Q x).val ∈ Q i) :
    cell_entry Q x = i := by
  by_contra hh
  exact Set.disjoint_left.mp (hdisj _ _ hh) (cell_entry_mem Q x) hi

/-- One full-domain affine node per nonempty disjoint cell, with no outgoing edges. -/
def affine_cell_network : FiniteOperatorNetwork (Option (FullReal E)) none I where
  U := cell_source Q
  bot_not_mem := by rintro ⟨a, ha, _⟩; cases ha
  node_fintype := inferInstance
  node_op := full_affine_operator ∘ H
  node_dom_nonempty := fun i => ⟨some (full_real 0), by simp⟩
  entry := cell_entry Q
  entry_mem := fun x => by
    change x.val ∈ dom (full_affine_operator (H (cell_entry Q x)))
    rw [(cell_input_spec Q x).1]
    simp
  choice := fun _ _ => .stop
  choice_next_mem := by intro _ _ _ _ h; cases h
  depth_bound := 1
  path_of := fun x => [cell_entry Q x]
  path_terminal := fun _ => TerminalPathFrom.stop rfl
  path_length_le_depth := by intro x; simp
  node_reachable := by
    intro i
    rcases hne i with ⟨a, ha⟩
    let x : cell_source Q := ⟨some (full_real a), ⟨full_real a, rfl, i, ha⟩⟩
    refine ⟨x, ?_⟩
    have hx : (cell_input Q x).val = a := by
      exact congrArg Subtype.val (Option.some.inj (cell_input_spec Q x).1).symm
    have he := cell_entry_eq Q hdisj x i (by simpa [hx] using ha)
    simp [he]

theorem affine_cell_network_nodes :
    AffineNodeRealization (affine_cell_network Q H hdisj hne) H := by
  intro i a _
  exact ⟨full_real (H i a.val), rfl, rfl⟩

theorem affine_cell_network_entry (i : I) :
    real_locus ((affine_cell_network Q H hdisj hne).entry_domain i) = Q i := by
  ext a
  rw [show a ∈ real_locus ((affine_cell_network Q H hdisj hne).entry_domain i) ↔
      some (full_real a) ∈ (affine_cell_network Q H hdisj hne).entry_domain i from
      mem_real_locus _ (full_real a)]
  constructor
  · rintro ⟨ha, hi⟩
    let x : cell_source Q := ⟨some (full_real a), ha⟩
    have hx : (cell_input Q x).val = a :=
      congrArg Subtype.val (Option.some.inj (cell_input_spec Q x).1).symm
    have hm := cell_entry_mem Q x
    change cell_entry Q x = i at hi
    simpa [hi, hx] using hm
  · intro ha
    let x : cell_source Q := ⟨some (full_real a), ⟨full_real a, rfl, i, ha⟩⟩
    refine ⟨x.property, ?_⟩
    have hx : (cell_input Q x).val = a :=
      congrArg Subtype.val (Option.some.inj (cell_input_spec Q x).1).symm
    exact cell_entry_eq Q hdisj x i (by simpa [hx] using ha)

theorem affine_cell_network_no_edges (i j : I) :
    (affine_cell_network Q H hdisj hne).edge_domain i j = ∅ := by
  ext x
  simp [edge_domain, to_transition_graph, affine_cell_network]

theorem affine_cell_network_terminal (i : I) :
    real_locus ((affine_cell_network Q H hdisj hne).terminal_domain i) = Set.range (H i) := by
  ext a
  rw [show a ∈ real_locus ((affine_cell_network Q H hdisj hne).terminal_domain i) ↔
      some (full_real a) ∈ (affine_cell_network Q H hdisj hne).terminal_domain i from
      mem_real_locus _ (full_real a)]
  simp only [terminal_domain, OperatorTransitionGraph.terminal_domain, to_transition_graph,
    OperatorTransitionGraph.node_image, OperatorTransitionGraph.node_dom,
    affine_cell_network, Set.mem_diff, Set.mem_image, Set.mem_iUnion, Set.mem_setOf_eq]
  have hstop : ∀ j : I, ¬ (OutputChoice.stop : OutputChoice I) = .next j :=
    fun _ h => by cases h
  simp only [hstop, and_false, not_exists, not_false_eq_true, forall_true_iff, and_true]
  constructor
  · rintro ⟨z, hz, heq⟩
    cases z with
    | none => simp [dom, full_affine_operator] at hz
    | some x =>
        refine ⟨x.val, ?_⟩
        exact congrArg Subtype.val (Option.some.inj heq)
  · rintro ⟨x, rfl⟩
    exact ⟨some (full_real x), by simp, rfl⟩

theorem affine_cell_network_apply (i : I) (a : E) (ha : a ∈ Q i) :
    (affine_cell_network Q H hdisj hne).extensional_operator.func (some (full_real a)) =
      some (full_real (H i a)) := by
  let x : cell_source Q := ⟨some (full_real a), ⟨full_real a, rfl, i, ha⟩⟩
  have hx : (cell_input Q x).val = a :=
    congrArg Subtype.val (Option.some.inj (cell_input_spec Q x).1).symm
  have he := cell_entry_eq Q hdisj x i (by simpa [hx] using ha)
  change (affine_cell_network Q H hdisj hne).extensional_operator.func x.val = _
  rw [(affine_cell_network Q H hdisj hne).extensional_apply_eq_chain_eval_path x]
  change some (full_real (H (cell_entry Q x) a)) = _
  rw [he]

theorem affine_cell_network_full_domains (i : I) :
    real_locus ((affine_cell_network Q H hdisj hne).node_dom i) = Set.univ := by
  ext a
  rw [show a ∈ real_locus ((affine_cell_network Q H hdisj hne).node_dom i) ↔
      some (full_real a) ∈ (affine_cell_network Q H hdisj hne).node_dom i from
      mem_real_locus _ (full_real a)]
  simp [node_dom, affine_cell_network, to_transition_graph,
    OperatorTransitionGraph.node_dom]

theorem affine_cell_network_linear_cells [FiniteDimensional ℝ E]
    (hQ : ∀ i, IsAffineCell (Q i)) :
    (∀ i, IsAffineCell (real_locus ((affine_cell_network Q H hdisj hne).entry_domain i))) ∧
    (∀ i j, IsAffineCell
      (real_locus ((affine_cell_network Q H hdisj hne).edge_domain i j))) ∧
    (∀ i, IsAffineCell (real_locus ((affine_cell_network Q H hdisj hne).terminal_domain i))) := by
  refine ⟨fun i => ?_, fun i j => ?_, fun i => ?_⟩
  · rw [affine_cell_network_entry]
    exact hQ i
  · rw [affine_cell_network_no_edges]
    have hempty : real_locus (∅ : Set (Option (FullReal E))) = (∅ : Set E) := by
      simp [real_locus]
    rw [hempty]
    refine ⟨[fun _ : E => (1 : ℝ) = 0], ?_, ?_⟩
    · intro c hc
      have hc' : c = (fun _ : E => (1 : ℝ) = 0) := by simpa using hc
      subst c
      exact Or.inl ⟨AffineMap.const ℝ E 1, rfl⟩
    · ext a
      simp
  · rw [affine_cell_network_terminal]
    exact affine_range_is_cell (H i)

end CellNetwork

section Composition

variable {V W : Type}
variable (N : FiniteOperatorNetwork (Option (FullReal E)) none V)
variable (M : FiniteOperatorNetwork (Option (FullReal E)) none W)
variable (F : V → E →ᵃ[ℝ] E) (G : W → E →ᵃ[ℝ] E)

def composition_domain : Set (Option (FullReal E)) :=
  N.U ∩ N.extensional_operator.func ⁻¹' M.U

def path_pair_cell (r : N.ReachablePath × M.ReachablePath) : Set E :=
  real_locus (N.path_domain r.1.nodes) ∩
    (affine_path_map F r.1.nodes) ⁻¹' real_locus (M.path_domain r.2.nodes)

def path_pair_map (r : N.ReachablePath × M.ReachablePath) : E →ᵃ[ℝ] E :=
  (affine_path_map G r.2.nodes).comp (affine_path_map F r.1.nodes)

theorem path_pair_cells_disjoint (r s : N.ReachablePath × M.ReachablePath) (hrs : r ≠ s) :
    Disjoint (path_pair_cell N M F r) (path_pair_cell N M F s) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  by_cases hp : r.1 = s.1
  · have hq : r.2.nodes ≠ s.2.nodes := by
      intro h
      exact hrs (Prod.ext hp (M.reachable_path_ext h))
    have hd := (real_path_domains_partition M).2 r.2 s.2 hq
    exact Set.disjoint_left.mp hd hx.2 (by simpa [hp] using hy.2)
  · have hp' : r.1.nodes ≠ s.1.nodes := fun h => hp (N.reachable_path_ext h)
    exact Set.disjoint_left.mp ((real_path_domains_partition N).2 r.1 s.1 hp') hx.1 hy.1

variable (hF : AffineNodeRealization N F) (hG : AffineNodeRealization M G)

include hF in
theorem path_pair_cell_subset_domain (r : N.ReachablePath × M.ReachablePath)
    {x : E} (hx : x ∈ path_pair_cell N M F r) :
    some (full_real x) ∈ composition_domain N M := by
  have hp := (mem_real_locus (N.path_domain r.1.nodes) (full_real x)).mp hx.1
  rcases actual_path_output_is_affine N F hF r.1 (full_real x) hp with ⟨b, hb, hbval⟩
  have hq : some b ∈ M.path_domain r.2.nodes :=
    (mem_real_locus _ b).mp (by simpa [hbval] using hx.2)
  exact ⟨N.path_domain_subset_source hp, by simpa [hb] using M.path_domain_subset_source hq⟩

include hF in
theorem path_pair_cells_cover :
    (⋃ r : N.ReachablePath × M.ReachablePath, path_pair_cell N M F r) =
      real_locus (composition_domain N M) := by
  ext x
  rw [show x ∈ real_locus (composition_domain N M) ↔
      some (full_real x) ∈ composition_domain N M from
      mem_real_locus _ (full_real x)]
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨r, hr⟩
    exact path_pair_cell_subset_domain N M F hF r hr
  · rintro ⟨hxN, hxM⟩
    have hp : some (full_real x) ∈ ⋃ p : N.ReachablePath, N.path_domain p.nodes := by
      rwa [N.reachable_path_domains_cover]
    rcases Set.mem_iUnion.mp hp with ⟨p, hp⟩
    rcases actual_path_output_is_affine N F hF p (full_real x) hp with ⟨b, hb, hbval⟩
    have hbu : some b ∈ M.U := by simpa [hb] using hxM
    rw [← M.reachable_path_domains_cover] at hbu
    rcases Set.mem_iUnion.mp hbu with ⟨q, hq⟩
    apply Set.mem_iUnion.mpr
    refine ⟨(p, q), (mem_real_locus _ (full_real x)).mpr hp, ?_⟩
    have hh := (mem_real_locus _ b).mpr hq
    simpa [hbval] using hh

include hF hG in
/--
OET anchor: h-292cbcc4dd47c8cc
The actual composite agrees with the composed affine path expressions on each cell.
-/
theorem path_pair_composition_apply (r : N.ReachablePath × M.ReachablePath)
    {x : E} (hx : x ∈ path_pair_cell N M F r) :
    (M.extensional_operator * N.extensional_operator).func (some (full_real x)) =
      some (full_real (path_pair_map N M F G r x)) := by
  have hp := (mem_real_locus (N.path_domain r.1.nodes) (full_real x)).mp hx.1
  rcases actual_path_output_is_affine N F hF r.1 (full_real x) hp with ⟨b, hb, hbval⟩
  have hq : some b ∈ M.path_domain r.2.nodes :=
    (mem_real_locus _ b).mp (by simpa [hbval] using hx.2)
  rcases actual_path_output_is_affine M G hG r.2 b hq with ⟨c, hc, hcval⟩
  change M.extensional_operator.func (N.extensional_operator.func _) = _
  rw [hb, hc]
  congr 1
  apply Subtype.ext
  simpa [path_pair_map, hbval] using hcval

omit [AddCommGroup E] [Module ℝ E] in
theorem composition_operator_domain :
    dom (M.extensional_operator * N.extensional_operator) = composition_domain N M := by
  ext x
  change M.extensional_operator.func (N.extensional_operator.func x) ≠ none ↔ _
  rw [← show N.extensional_operator.func x ∈ dom M.extensional_operator ↔
      M.extensional_operator.func (N.extensional_operator.func x) ≠ none from Iff.rfl,
    M.dom_extensional_operator_eq]
  constructor
  · intro hxM
    refine ⟨?_, hxM⟩
    rw [← N.dom_extensional_operator_eq]
    change N.extensional_operator.func x ≠ none
    intro hh
    exact M.bot_not_mem (by simpa [hh] using hxM)
  · exact fun h => h.2

abbrev ActivePathPair :=
  {r : N.ReachablePath × M.ReachablePath // (path_pair_cell N M F r).Nonempty}

instance active_path_pair_fintype : Fintype (ActivePathPair N M F) := Fintype.ofFinite _

theorem active_pair_disjoint (r s : ActivePathPair N M F) (hrs : r ≠ s) :
    Disjoint (path_pair_cell N M F r.val) (path_pair_cell N M F s.val) :=
  path_pair_cells_disjoint N M F r.val s.val (fun h => hrs (Subtype.ext h))

/-- An actual network realizing the composite: every nonempty path-pair cell is one node. -/
def affine_composition_network :
    FiniteOperatorNetwork (Option (FullReal E)) none (ActivePathPair N M F) :=
  affine_cell_network (fun r => path_pair_cell N M F r.val)
    (fun r => path_pair_map N M F G r.val)
    (active_pair_disjoint N M F) (fun r => r.property)

include hF in
theorem affine_composition_source :
    (affine_composition_network N M F G).U = composition_domain N M := by
  ext z
  change (∃ a : FullReal E, z = some a ∧
    ∃ r : ActivePathPair N M F, a.val ∈ path_pair_cell N M F r.val) ↔ _
  constructor
  · rintro ⟨a, rfl, r, hr⟩
    exact path_pair_cell_subset_domain N M F hF r.val hr
  · intro hz
    cases z with
    | none => exact False.elim (N.bot_not_mem hz.1)
    | some a =>
        have hx := (mem_real_locus (composition_domain N M) a).mpr hz
        rw [← path_pair_cells_cover N M F hF] at hx
        rcases Set.mem_iUnion.mp hx with ⟨r, hr⟩
        exact ⟨a, rfl, ⟨r, a.val, hr⟩, hr⟩

include hF hG in
theorem affine_composition_extensional :
    (affine_composition_network N M F G).extensional_operator =
      M.extensional_operator * N.extensional_operator := by
  apply Operator.ext
  funext z
  by_cases hz : z ∈ composition_domain N M
  · cases z with
    | none => exact False.elim (N.bot_not_mem hz.1)
    | some a =>
        have hx := (mem_real_locus (composition_domain N M) a).mpr hz
        rw [← path_pair_cells_cover N M F hF] at hx
        rcases Set.mem_iUnion.mp hx with ⟨r, hr⟩
        let i : ActivePathPair N M F := ⟨r, a.val, hr⟩
        exact (affine_cell_network_apply _ (fun r => path_pair_map N M F G r.val)
          (active_pair_disjoint N M F)
          (fun r => r.property) i a.val hr).trans
          (path_pair_composition_apply N M F G hF hG r hr).symm
  · have hleft : z ∉ (affine_composition_network N M F G).U := by
      rwa [affine_composition_source N M F G hF]
    have hright : z ∉ dom (M.extensional_operator * N.extensional_operator) := by
      rwa [composition_operator_domain]
    have heq : (M.extensional_operator * N.extensional_operator).func z = none :=
      not_not.mp hright
    rw [heq]
    simp [FiniteOperatorNetwork.extensional_operator, hleft]

/--
OET anchor: h-292cbcc4dd47c8cc
The affine path-pair expression has linear part BA and translation Bb+d.
-/
theorem path_pair_affine_coefficients (r : N.ReachablePath × M.ReachablePath) :
    (path_pair_map N M F G r).linear =
      (affine_path_map G r.2.nodes).linear.comp (affine_path_map F r.1.nodes).linear ∧
    (∀ x, path_pair_map N M F G r x =
      (affine_path_map G r.2.nodes).linear ((affine_path_map F r.1.nodes).linear x) +
      ((affine_path_map G r.2.nodes).linear (affine_path_map F r.1.nodes 0) +
        affine_path_map G r.2.nodes 0)) := by
  refine ⟨rfl, fun x => ?_⟩
  change affine_path_map G r.2.nodes (affine_path_map F r.1.nodes x) = _
  rw [congrFun (affine_path_map G r.2.nodes).decomp,
    congrFun (affine_path_map F r.1.nodes).decomp]
  simp [add_assoc]

include hF hG in
/--
OET anchor: h-292cbcc4dd47c8cc
Every path-pair intersection is a linear cell under the original network assumptions.
-/
theorem path_pair_cell_is_linear
    (hentryN : ∀ v, IsAffineCell (real_locus (N.entry_domain v)))
    (hedgeN : ∀ v w, IsAffineCell (real_locus (N.edge_domain v w)))
    (htermN : ∀ v, IsAffineCell (real_locus (N.terminal_domain v)))
    (hentryM : ∀ v, IsAffineCell (real_locus (M.entry_domain v)))
    (hedgeM : ∀ v w, IsAffineCell (real_locus (M.edge_domain v w)))
    (htermM : ∀ v, IsAffineCell (real_locus (M.terminal_domain v)))
    (r : N.ReachablePath × M.ReachablePath) :
    IsAffineCell (path_pair_cell N M F r) :=
  affine_cell_inter
    (actual_affine_path_domains_are_linear N F hF hentryN hedgeN htermN r.1)
    (affine_cell_preimage (affine_path_map F r.1.nodes)
      (actual_affine_path_domains_are_linear M G hG hentryM hedgeM htermM r.2))

include hF in
/--
OET anchor: h-292cbcc4dd47c8cc
The nonempty path-pair cells, indexed by a finite type, partition the natural domain.
-/
theorem active_path_pair_cells_partition :
    ((⋃ r : ActivePathPair N M F, path_pair_cell N M F r.val) =
      real_locus (composition_domain N M)) ∧
    (∀ r : ActivePathPair N M F, (path_pair_cell N M F r.val).Nonempty) ∧
    (∀ r s : ActivePathPair N M F, r ≠ s →
      Disjoint (path_pair_cell N M F r.val) (path_pair_cell N M F s.val)) := by
  refine ⟨?_, fun r => r.property, active_pair_disjoint N M F⟩
  rw [← path_pair_cells_cover N M F hF]
  ext x
  constructor
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨r, hr⟩
    exact Set.mem_iUnion.mpr ⟨r.val, hr⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨r, hr⟩
    exact Set.mem_iUnion.mpr ⟨⟨r, x, hr⟩, hr⟩

include hF in
theorem active_path_pairs_empty_iff :
    IsEmpty (ActivePathPair N M F) ↔ composition_domain N M = ∅ := by
  constructor
  · intro h
    letI := h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    cases z with
    | none => exact N.bot_not_mem hz.1
    | some a =>
        have hx := (mem_real_locus (composition_domain N M) a).mpr hz
        rw [← (active_path_pair_cells_partition N M F hF).1] at hx
        rcases Set.mem_iUnion.mp hx with ⟨r, _⟩
        exact isEmptyElim r
  · intro h
    refine ⟨fun r => ?_⟩
    rcases r.property with ⟨x, hx⟩
    have hd := path_pair_cell_subset_domain N M F hF r.val hx
    simp [h] at hd

include hF in
/--
OET anchor: h-292cbcc4dd47c8cc
An empty effective domain gives no nodes and the everywhere absorbing extensional operator.
-/
theorem affine_composition_empty_domain
    (hD : composition_domain N M = ∅) :
    (affine_composition_network N M F G).U = ∅ ∧
    (affine_composition_network N M F G).node_count = 0 ∧
    (affine_composition_network N M F G).extensional_operator = bot_operator := by
  have hempty := (active_path_pairs_empty_iff N M F hF).mpr hD
  letI := hempty
  refine ⟨by rw [affine_composition_source N M F G hF, hD], ?_, ?_⟩
  · exact Fintype.card_eq_zero
  · apply Operator.ext
    funext z
    have hz : z ∉ (affine_composition_network N M F G).U := by
      rw [affine_composition_source N M F G hF, hD]
      simp
    simp [FiniteOperatorNetwork.extensional_operator, hz, bot_operator]

include hF hG in
/--
OET anchor: h-292cbcc4dd47c8cc
Affine networks are closed under extensional composition on the natural effective domain.
The witness has one full-domain affine node for every nonempty path-pair cell; its
entry, edge and terminal loci satisfy the same linear-cell assumptions.
-/
theorem affine_networks_closed_under_composition [FiniteDimensional ℝ E]
    (hentryN : ∀ v, IsAffineCell (real_locus (N.entry_domain v)))
    (hedgeN : ∀ v w, IsAffineCell (real_locus (N.edge_domain v w)))
    (htermN : ∀ v, IsAffineCell (real_locus (N.terminal_domain v)))
    (hentryM : ∀ v, IsAffineCell (real_locus (M.entry_domain v)))
    (hedgeM : ∀ v w, IsAffineCell (real_locus (M.edge_domain v w)))
    (htermM : ∀ v, IsAffineCell (real_locus (M.terminal_domain v))) :
    ∃ (C : FiniteOperatorNetwork (Option (FullReal E)) none (ActivePathPair N M F))
      (H : ActivePathPair N M F → E →ᵃ[ℝ] E),
      C.U = composition_domain N M ∧
      C.extensional_operator = M.extensional_operator * N.extensional_operator ∧
      AffineNodeRealization C H ∧
      (∀ i, real_locus (C.node_dom i) = Set.univ) ∧
      (∀ i, real_locus (C.entry_domain i) = path_pair_cell N M F i.val) ∧
      (∀ i j, C.edge_domain i j = ∅) ∧
      (∀ i, real_locus (C.terminal_domain i) = Set.range (H i)) ∧
      (∀ i, IsAffineCell (real_locus (C.entry_domain i))) ∧
      (∀ i j, IsAffineCell (real_locus (C.edge_domain i j))) ∧
      (∀ i, IsAffineCell (real_locus (C.terminal_domain i))) := by
  let C := affine_composition_network N M F G
  let H := fun r : ActivePathPair N M F => path_pair_map N M F G r.val
  have hlinear := affine_cell_network_linear_cells
    (fun r : ActivePathPair N M F => path_pair_cell N M F r.val) H
    (active_pair_disjoint N M F) (fun r => r.property)
    (fun r => path_pair_cell_is_linear N M F G hF hG
      hentryN hedgeN htermN hentryM hedgeM htermM r.val)
  refine ⟨C, H, affine_composition_source N M F G hF,
    affine_composition_extensional N M F G hF hG,
    affine_cell_network_nodes _ _ _ _, affine_cell_network_full_domains _ _ _ _,
    affine_cell_network_entry _ _ _ _, affine_cell_network_no_edges _ _ _ _,
    affine_cell_network_terminal _ _ _ _, hlinear.1, hlinear.2.1, hlinear.2.2⟩

end Composition

end
end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
