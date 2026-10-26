import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.open_differential_chain
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.model_radius
import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.path_differential

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open Filter Topology
noncomputable section
variable {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The nonabsorbing point in the original ambient-state model. -/
def ambient_point (x : E) : Option (Set.univ : Set E) := some ⟨x, Set.mem_univ x⟩

/-- Total readout; all uses in path differentiation are on nonabsorbing outputs. -/
def ambient_readout : Option (Set.univ : Set E) → E
  | none => 0
  | some x => x.val

theorem full_node_realization_at
    (φ : Operator (Option (Set.univ : Set E)) none)
    (F : E → E) (O : Set (E))
    (S : Set (Option (Set.univ : Set E))) (h : ModelRealizationOn φ F O S)
    (x : E) (hx : ambient_point x ∈ S) :
    x ∈ O ∧ φ.func (ambient_point x) = ambient_point (F x) := by
  rcases h _ hx with ⟨a, b, he, ho, hp, hb⟩
  have ha : x = a.val := congrArg Subtype.val (Option.some.inj he)
  refine ⟨ha ▸ ho, ?_⟩
  rw [he, hp]
  apply congrArg some
  apply Subtype.ext
  exact hb.trans (congrArg F ha.symm)

def node_extension_steps (F : V → DifferentialFunction (E))
    (O : V → Set (E)) (nodes : List V) :=
  (nodes.map (fun v => (F v, O v))).reverse

@[simp] theorem node_extension_steps_functions
    (F : V → DifferentialFunction (E))
    (O : V → Set (E)) (nodes : List V) :
    (node_extension_steps F O nodes).map Prod.fst = (nodes.map F).reverse := by
  simp [node_extension_steps, List.map_map, Function.comp_def]

/-- Pointwise prefix legality comes from actual network evaluation. It implies
both agreement with the ambient composition and membership in its exact domain. -/
theorem realized_path_chain
    (N : FiniteOperatorNetwork (Option (Set.univ : Set E)) none V)
    (F : V → DifferentialFunction (E)) (O : V → Set (E))
    (hreal : ∀ v, ModelRealizationOn (N.node_op v) (F v).func (O v) (N.node_dom v))
    (nodes : List V) (x : E)
    (hinput : ∀ k (hk : k < nodes.length),
      (N.path_chain (nodes.take k)).func (ambient_point x) ∈ N.node_dom (nodes.get ⟨k, hk⟩)) :
    (N.path_chain nodes).func (ambient_point x) =
      ambient_point (differential_function_chain ((nodes.map F).reverse) x) ∧
    x ∈ extension_chain_domain (node_extension_steps F O nodes) := by
  induction nodes using List.reverseRecOn with
  | nil => exact ⟨rfl, Set.mem_univ _⟩
  | append_singleton nodes v ih =>
    have hprefix : ∀ k (hk : k < nodes.length),
        (N.path_chain (nodes.take k)).func (ambient_point x) ∈
          N.node_dom (nodes.get ⟨k, hk⟩) := by
      intro k hk
      have h := hinput k (lt_trans hk (by simp))
      rw [List.take_append_of_le_length hk.le] at h
      simpa [List.get_eq_getElem, hk] using h
    have ht := ih hprefix
    have hlast : (N.path_chain nodes).func (ambient_point x) ∈ N.node_dom v := by
      simpa using hinput nodes.length (by simp)
    rw [ht.1] at hlast
    have hs := full_node_realization_at (N.node_op v) (F v).func (O v) (N.node_dom v)
      (hreal v) _ hlast
    constructor
    · simpa [FiniteOperatorNetwork.path_chain, OperatorChain, differential_function_chain]
        using congrArg (N.node_op v).func ht.1 |>.trans hs.2
    · simpa [node_extension_steps, extension_chain_domain, List.map_map, Function.comp_def]
        using And.intro ht.2 hs.1

theorem reachable_path_extension_domain
    (N : FiniteOperatorNetwork (Option (Set.univ : Set E)) none V) (p : N.ReachablePath)
    (F : V → DifferentialFunction (E)) (O : V → Set (E))
    (hreal : ∀ v, ModelRealizationOn (N.node_op v) (F v).func (O v) (N.node_dom v))
    (x : E) (hx : ambient_point x ∈ N.path_domain p.nodes) :
    (N.path_chain p.nodes).func (ambient_point x) =
      ambient_point (differential_function_chain ((p.nodes.map F).reverse) x) ∧
    x ∈ extension_chain_domain (node_extension_steps F O p.nodes) := by
  apply realized_path_chain N F O hreal p.nodes x
  intro k hk
  exact N.path_prefix_image_subset_node_dom p ⟨k, hk⟩ (Set.mem_image_of_mem _ hx)

/--
OET anchor: h-6de8b6950c13065a
The actual path lies in the ambient composition domain and the ordered actual
derivatives give its derivative. Pointwise differentiability on the open node
extensions suffices; the textbook C1 hypothesis implies it.
-/
theorem actual_path_jacobian_product
    (N : FiniteOperatorNetwork (Option (Set.univ : Set E)) none V) (p : N.ReachablePath)
    (F : V → DifferentialFunction (E)) (O : V → Set (E))
    (hreal : ∀ v, ModelRealizationOn (N.node_op v) (F v).func (O v) (N.node_dom v))
    (hO : ∀ v, IsOpen (O v))
    (hD : ∀ v z, z ∈ O v → HasFDerivAt (F v).func ((F v).differential z) z)
    (x : E) (hx : ambient_point x ∈ N.path_domain p.nodes) :
    (∃ W : Set (E), IsOpen W ∧ x ∈ W ∧
      W ⊆ extension_chain_domain (node_extension_steps F O p.nodes)) ∧
    HasFDerivAt (differential_function_chain ((p.nodes.map F).reverse))
      (continuous_linear_chain (occurrence_differentials ((p.nodes.map F).reverse) x)) x := by
  have hd := (reachable_path_extension_domain N p F O hreal x hx).2
  have hs : ∀ step ∈ node_extension_steps F O p.nodes, IsOpen step.2 ∧
      ∀ z ∈ step.2, HasFDerivAt step.1.func (step.1.differential z) z := by
    intro step hstep
    rcases List.mem_map.mp (List.mem_reverse.mp hstep) with ⟨v, _, rfl⟩
    exact ⟨hO v, hD v⟩
  refine ⟨open_extension_chain_neighborhood _ hs x hd, ?_⟩
  have hc := (open_extension_chain_at _ hs x hd).1
  rw [node_extension_steps_functions] at hc
  exact differential_chain_has_fderiv _ x hc

/-- Ambient readout is used only locally on an actual nonabsorbing path piece. -/
def network_real_readout
    (N : FiniteOperatorNetwork (Option (Set.univ : Set E)) none V) (x : E) :
    E := ambient_readout (N.extensional_operator.func (ambient_point x))

/--
OET anchor: h-6de8b6950c13065a
When the actual path is fixed on a neighborhood, the extensional network has
the path derivative. No regularity across a path boundary is assumed.
-/
theorem actual_extensional_derivative_on_open_path
    (N : FiniteOperatorNetwork (Option (Set.univ : Set E)) none V) (p : N.ReachablePath)
    (F : V → DifferentialFunction (E)) (O : V → Set (E))
    (hreal : ∀ v, ModelRealizationOn (N.node_op v) (F v).func (O v) (N.node_dom v))
    (hO : ∀ v, IsOpen (O v))
    (hD : ∀ v z, z ∈ O v → HasFDerivAt (F v).func ((F v).differential z) z)
    (W : Set (E)) (hW : IsOpen W)
    (hpath : ∀ z ∈ W, ambient_point z ∈ N.path_domain p.nodes)
    (x : E) (hx : x ∈ W) :
    Set.EqOn (network_real_readout N) (differential_function_chain ((p.nodes.map F).reverse)) W ∧
    HasFDerivAt (network_real_readout N)
      (continuous_linear_chain (occurrence_differentials ((p.nodes.map F).reverse) x)) x := by
  have he : Set.EqOn (network_real_readout N)
      (differential_function_chain ((p.nodes.map F).reverse)) W := by
    intro z hz
    unfold network_real_readout
    rw [N.local_equivalent_extensional_path_chain p _ (hpath z hz),
      (reachable_path_extension_domain N p F O hreal z (hpath z hz)).1]
    rfl
  refine ⟨he, ?_⟩
  apply (actual_path_jacobian_product N p F O hreal hO hD x (hpath x hx)).2.congr_of_eventuallyEq
  filter_upwards [hW.mem_nhds hx] with z hz
  exact he hz

end
end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
