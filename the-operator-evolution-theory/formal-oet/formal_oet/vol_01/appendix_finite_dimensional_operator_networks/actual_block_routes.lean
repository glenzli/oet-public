import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.actual_path_derivative
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_geometry
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.euclidean_matrix_bound

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks
open formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open scoped BigOperators
noncomputable section
variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype H]

def projected_operator (W : H → Submodule ℝ E) (T : E →L[ℝ] E) (a b : H) : E →L[ℝ] E :=
  (W b).starProjection.comp (T.comp (W a).starProjection)

/-- The nested finite sum over the actual intermediate orthogonal blocks.
The empty list is unused: reachable network paths contain at least one node. -/
def block_route_sum (W : H → Submodule ℝ E) : List (E →L[ℝ] E) → H → H → E →L[ℝ] E
  | [], _, _ => 0
  | [T], a, b => projected_operator W T a b
  | T :: U :: Ts, a, b =>
      ∑ k, (projected_operator W T k b).comp (block_route_sum W (U :: Ts) a k)

def block_route_norm_sum (W : H → Submodule ℝ E) : List (E →L[ℝ] E) → H → H → ℝ
  | [], _, _ => 0
  | [T], a, b => ‖projected_operator W T a b‖
  | T :: U :: Ts, a, b =>
      ∑ k, ‖projected_operator W T k b‖ * block_route_norm_sum W (U :: Ts) a k

/-- A block index sequence whose every actual projected derivative is nonzero. -/
def NonzeroBlockRoute (W : H → Submodule ℝ E) : List (E →L[ℝ] E) → H → H → Prop
  | [], _, _ => False
  | [T], a, b => projected_operator W T a b ≠ 0
  | T :: U :: Ts, a, b =>
      ∃ k, projected_operator W T k b ≠ 0 ∧ NonzeroBlockRoute W (U :: Ts) a k

theorem projected_operator_comp_expansion
    (W : H → Submodule ℝ E)
    (hW : OrthogonalFamily ℝ (fun a => W a) (fun a => (W a).subtypeₗᵢ))
    (hspan : iSup W = ⊤) (T U : E →L[ℝ] E) (a b : H) :
    projected_operator W (T.comp U) a b =
      ∑ k, (projected_operator W T k b).comp (projected_operator W U a k) := by
  ext v
  have hp (k : H) (z : E) : (W k).starProjection ((W k).starProjection z) =
      (W k).starProjection z :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  simp only [projected_operator, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, hp]
  rw [← map_sum, ← map_sum]
  rw [← (orthogonal_projection_decomposition W hW hspan (U ((W a).starProjection v))).1]

theorem actual_block_channel_expansion
    (W : H → Submodule ℝ E)
    (hW : OrthogonalFamily ℝ (fun a => W a) (fun a => (W a).subtypeₗᵢ))
    (hspan : iSup W = ⊤) (Ts : List (E →L[ℝ] E)) (hne : Ts ≠ []) (a b : H) :
    projected_operator W (continuous_linear_chain Ts) a b = block_route_sum W Ts a b := by
  induction Ts generalizing a b with
  | nil => exact (hne rfl).elim
  | cons T Ts ih =>
    cases Ts with
    | nil => simp [continuous_linear_chain, block_route_sum]
    | cons U Us =>
      rw [continuous_linear_chain, projected_operator_comp_expansion W hW hspan, block_route_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [ih (by simp)]

theorem absent_block_route_sum_zero (W : H → Submodule ℝ E)
    (Ts : List (E →L[ℝ] E)) (a b : H) (h : ¬ NonzeroBlockRoute W Ts a b) :
    block_route_sum W Ts a b = 0 := by
  classical
  induction Ts generalizing a b with
  | nil => rfl
  | cons T Ts ih =>
    cases Ts with
    | nil => exact not_not.mp h
    | cons U Us =>
      rw [block_route_sum]
      apply Finset.sum_eq_zero
      intro k _
      by_cases hk : projected_operator W T k b = 0
      · rw [hk, ContinuousLinearMap.zero_comp]
      · rw [ih a k (fun hr => h ⟨k, hk, hr⟩), ContinuousLinearMap.comp_zero]

theorem block_route_sum_norm_le (W : H → Submodule ℝ E)
    (Ts : List (E →L[ℝ] E)) (a b : H) :
    ‖block_route_sum W Ts a b‖ ≤ block_route_norm_sum W Ts a b := by
  induction Ts generalizing a b with
  | nil => simp [block_route_sum, block_route_norm_sum]
  | cons T Ts ih =>
    cases Ts with
    | nil => exact le_rfl
    | cons U Us =>
      rw [block_route_sum, block_route_norm_sum]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_left (ih a k) (norm_nonneg _))

/-- Shared support for the block-route corollary and the norm-bound exercise:
the exact expansion, its zero-route consequence, and its norm estimate. -/
theorem actual_orthogonal_block_routes
    (W : H → Submodule ℝ E)
    (hW : OrthogonalFamily ℝ (fun a => W a) (fun a => (W a).subtypeₗᵢ))
    (hspan : iSup W = ⊤) (Ts : List (E →L[ℝ] E)) (hne : Ts ≠ []) (a b : H) :
    projected_operator W (continuous_linear_chain Ts) a b = block_route_sum W Ts a b ∧
    (¬ NonzeroBlockRoute W Ts a b → projected_operator W (continuous_linear_chain Ts) a b = 0) ∧
    ‖projected_operator W (continuous_linear_chain Ts) a b‖ ≤ block_route_norm_sum W Ts a b := by
  rw [actual_block_channel_expansion W hW hspan Ts hne]
  exact ⟨rfl, absent_block_route_sum_zero W Ts a b, block_route_sum_norm_le W Ts a b⟩

/-- Instantiate the shared block expansion on an actual reachable network path.
The corollary and exercise below select their respective conclusions. -/
theorem network_path_block_routes {V : Type}
    (N : formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork
      (Option (Set.univ : Set E)) none V) (p : N.ReachablePath)
    (F : V → DifferentialFunction E) (O : V → Set E)
    (hreal : ∀ v, ModelRealizationOn (N.node_op v) (F v).func (O v) (N.node_dom v))
    (hO : ∀ v, IsOpen (O v))
    (hD : ∀ v z, z ∈ O v → HasFDerivAt (F v).func ((F v).differential z) z)
    (x : E) (hx : ambient_point x ∈ N.path_domain p.nodes)
    (W : H → Submodule ℝ E)
    (hW : OrthogonalFamily ℝ (fun a => W a) (fun a => (W a).subtypeₗᵢ))
    (hspan : iSup W = ⊤) (a b : H) :
    let Ts := occurrence_differentials ((p.nodes.map F).reverse) x
    let Dp := fderiv ℝ (differential_function_chain ((p.nodes.map F).reverse)) x
    projected_operator W Dp a b = block_route_sum W Ts a b ∧
    (¬ NonzeroBlockRoute W Ts a b → projected_operator W Dp a b = 0) ∧
    ‖projected_operator W Dp a b‖ ≤ block_route_norm_sum W Ts a b := by
  dsimp only
  rw [(actual_path_jacobian_product N p F O hreal hO hD x hx).2.fderiv]
  apply actual_orthogonal_block_routes W hW hspan
  have hfs : (p.nodes.map F).reverse ≠ [] := by
    simpa using N.reachable_path_nodes_nonempty p
  cases he : (p.nodes.map F).reverse with
  | nil => exact (hfs he).elim
  | cons f fs => simp [occurrence_differentials]

/--
OET anchor: h-f8dabd5aec160cd3
Nonzero path block derivatives require a route of nonzero occurrence blocks.
The converse fails, as witnessed by `actual_block_route_cancellation` below.
-/
theorem network_path_nonzero_block_requires_route {V : Type}
    (N : formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork
      (Option (Set.univ : Set E)) none V) (p : N.ReachablePath)
    (F : V → DifferentialFunction E) (O : V → Set E)
    (hreal : ∀ v, ModelRealizationOn (N.node_op v) (F v).func (O v) (N.node_dom v))
    (hO : ∀ v, IsOpen (O v))
    (hD : ∀ v z, z ∈ O v → HasFDerivAt (F v).func ((F v).differential z) z)
    (x : E) (hx : ambient_point x ∈ N.path_domain p.nodes)
    (W : H → Submodule ℝ E)
    (hW : OrthogonalFamily ℝ (fun a => W a) (fun a => (W a).subtypeₗᵢ))
    (hspan : iSup W = ⊤) (a b : H)
    (hblock : projected_operator W
      (fderiv ℝ (differential_function_chain ((p.nodes.map F).reverse)) x) a b ≠ 0) :
    NonzeroBlockRoute W (occurrence_differentials ((p.nodes.map F).reverse) x) a b := by
  classical
  by_contra hroute
  exact hblock ((network_path_block_routes N p F O hreal hO hD x hx W hW hspan a b).2.1 hroute)

/--
OET anchor: h-64877d77e522a25b
Exercise (i): the actual path block derivative is bounded by the finite sum
of products of occurrence-block norms. No path derivative bound is assumed.
-/
theorem network_path_block_norm_bound {V : Type}
    (N : formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork
      (Option (Set.univ : Set E)) none V) (p : N.ReachablePath)
    (F : V → DifferentialFunction E) (O : V → Set E)
    (hreal : ∀ v, ModelRealizationOn (N.node_op v) (F v).func (O v) (N.node_dom v))
    (hO : ∀ v, IsOpen (O v))
    (hD : ∀ v z, z ∈ O v → HasFDerivAt (F v).func ((F v).differential z) z)
    (x : E) (hx : ambient_point x ∈ N.path_domain p.nodes)
    (W : H → Submodule ℝ E)
    (hW : OrthogonalFamily ℝ (fun a => W a) (fun a => (W a).subtypeₗᵢ))
    (hspan : iSup W = ⊤) (a b : H) :
    ‖projected_operator W
      (fderiv ℝ (differential_function_chain ((p.nodes.map F).reverse)) x) a b‖ ≤
      block_route_norm_sum W (occurrence_differentials ((p.nodes.map F).reverse) x) a b :=
  (network_path_block_routes N p F O hreal hO hD x hx W hW hspan a b).2.2

theorem standard_projected_operator_apply {n : ℕ}
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (a b : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    projected_operator standard_coordinate_subspace T a b v =
      (v a * T (EuclideanSpace.single a 1) b) • EuclideanSpace.single b 1 := by
  simp [projected_operator, standard_coordinate_projection, map_smul, smul_smul]

theorem standard_projected_operator_zero_iff {n : ℕ} [NeZero n]
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (a b : Fin n) :
    projected_operator standard_coordinate_subspace T a b = 0 ↔ euclidean_linear_entry T a b = 0 := by
  constructor
  · intro h
    have he := congrArg (fun U : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) =>
      U (EuclideanSpace.single a 1) b) h
    simpa [standard_projected_operator_apply, euclidean_linear_entry] using he
  · intro h
    change T (EuclideanSpace.single a 1) b = 0 at h
    ext v
    simp [standard_projected_operator_apply, h]

theorem euclidean_certificate_entry {n : ℕ} [NeZero n] (M : RealCertificate (Fin n)) (a b : Fin n) :
    euclidean_linear_entry (euclidean_certificate_operator M) a b = M a b := by
  change (∑ i, M i b * (EuclideanSpace.single a 1) i) = _
  simp

/--
OET anchor: h-f8dabd5aec160cd3
The displayed two actual linear maps have two nonzero routes and a zero
composite block. Their entries use the OET input/output index convention.
-/
theorem actual_block_route_cancellation :
    let A := euclidean_certificate_operator cancellation_first
    let B := euclidean_certificate_operator cancellation_second
    NonzeroBlockRoute standard_coordinate_subspace [B, A] 0 0 ∧
    projected_operator standard_coordinate_subspace (B.comp A) 0 0 = 0 ∧
    projected_operator standard_coordinate_subspace B 1 0 ≠ 0 ∧
    projected_operator standard_coordinate_subspace A 0 1 ≠ 0 := by
  dsimp only
  have hn (M : RealCertificate (Fin 2)) (a b : Fin 2) :
      projected_operator standard_coordinate_subspace (euclidean_certificate_operator M) a b ≠ 0 ↔
        M a b ≠ 0 := by
    rw [ne_eq, standard_projected_operator_zero_iff, euclidean_certificate_entry]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨0, (hn _ _ _).mpr ?_, (hn _ _ _).mpr ?_⟩
    · norm_num [cancellation_second]
    · norm_num [cancellation_first]
  · rw [standard_projected_operator_zero_iff, euclidean_entry_comp]
    have he (M : RealCertificate (Fin 2)) : euclidean_linear_entry (euclidean_certificate_operator M) = M :=
      funext (fun a => funext (fun b => euclidean_certificate_entry M a b))
    rw [he, he]
    exact cancellation_channel_values.1
  · apply (hn _ _ _).mpr
    norm_num [cancellation_second]
  · apply (hn _ _ _).mpr
    norm_num [cancellation_first]

namespace BlockCancellation

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks
open FiniteOperatorNetwork

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Point := Option (Set.univ : Set Plane)

def node_map (v : Bool) : Plane →L[ℝ] Plane :=
  if v then euclidean_certificate_operator cancellation_second
  else euclidean_certificate_operator cancellation_first

def node_operator (v : Bool) : Operator Point none where
  func := Option.map (fun a => ⟨node_map v a.val, Set.mem_univ _⟩)
  preserves_bot := rfl

@[simp] theorem node_operator_dom (v : Bool) (x : Point) :
    x ∈ dom (node_operator v) ↔ x ≠ none := by
  cases x <;> simp [dom, node_operator]

def routing (v : Bool) (_ : Point) : OutputChoice Bool :=
  if v then .stop else .next true

/-- The two displayed linear maps are nodes in an actual full-domain serial
network. Every input visits both nodes and terminates after two evaluations. -/
def network : FiniteOperatorNetwork Point none Bool where
  U := {x | x ≠ none}
  bot_not_mem := by simp
  node_fintype := inferInstance
  node_op := node_operator
  node_dom_nonempty := fun _ => ⟨ambient_point 0, by simp [ambient_point]⟩
  entry := fun _ => false
  entry_mem := fun x => (node_operator_dom _ _).mpr x.property
  choice := routing
  choice_next_mem := by
    intro v w x hx _
    rw [node_operator_dom] at hx ⊢
    cases x <;> simp_all [node_operator]
  depth_bound := 2
  path_of := fun _ => [false, true]
  path_terminal := fun _ => TerminalPathFrom.next rfl (TerminalPathFrom.stop rfl)
  path_length_le_depth := by intro x; simp
  node_reachable := by
    intro v
    refine ⟨⟨ambient_point 0, by simp [ambient_point]⟩, ?_⟩
    cases v <;> simp

def path : network.ReachablePath :=
  ⟨[false, true], ⟨ambient_point 0, ⟨by simp [network, ambient_point], rfl⟩⟩⟩

theorem path_domain_full (x : Plane) : ambient_point x ∈ network.path_domain path.nodes :=
  ⟨by simp [network, ambient_point], rfl⟩

def node_extension (v : Bool) : DifferentialFunction Plane :=
  ⟨node_map v, fun _ => node_map v⟩

theorem node_realization (v : Bool) :
    ModelRealizationOn (network.node_op v) (node_extension v).func Set.univ
      (network.node_dom v) := by
  intro x hx
  have hx' : x ≠ none := (node_operator_dom v x).mp hx
  cases x with
  | none => exact (hx' rfl).elim
  | some a => exact ⟨a, ⟨node_map v a.val, Set.mem_univ _⟩, rfl, Set.mem_univ _, rfl, rfl⟩

theorem network_derivative (x : Plane) :
    HasFDerivAt (network_real_readout network)
      ((euclidean_certificate_operator cancellation_second).comp
        (euclidean_certificate_operator cancellation_first)) x := by
  have h := (actual_extensional_derivative_on_open_path network path node_extension
    (fun _ => Set.univ) node_realization (fun _ => isOpen_univ)
    (fun v z _ => (node_map v).hasFDerivAt)
    Set.univ isOpen_univ (fun z _ => path_domain_full z) x (Set.mem_univ x)).2
  simpa [path, node_extension, node_map, occurrence_differentials,
    continuous_linear_chain] using h

/-- OET anchor: h-f8dabd5aec160cd3
The converse fails on a genuine full-domain two-node network, not just a
formal matrix product. Its reachable path has both nonzero block routes,
while the actual extensional derivative has zero input-0/output-0 block. -/
theorem network_block_route_counterexample (x : Plane) :
    ambient_point x ∈ network.path_domain path.nodes ∧
    NonzeroBlockRoute standard_coordinate_subspace
      (occurrence_differentials ((path.nodes.map node_extension).reverse) x) 0 0 ∧
    projected_operator standard_coordinate_subspace
      (fderiv ℝ (network_real_readout network) x) 0 0 = 0 ∧
    projected_operator standard_coordinate_subspace (node_map true) 1 0 ≠ 0 ∧
    projected_operator standard_coordinate_subspace (node_map false) 0 1 ≠ 0 := by
  refine ⟨path_domain_full x, ?_, ?_, ?_, ?_⟩
  · simpa [path, node_extension, node_map, occurrence_differentials] using
      actual_block_route_cancellation.1
  · rw [(network_derivative x).fderiv]
    exact actual_block_route_cancellation.2.1
  · exact actual_block_route_cancellation.2.2.1
  · exact actual_block_route_cancellation.2.2.2

end BlockCancellation

end
end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
