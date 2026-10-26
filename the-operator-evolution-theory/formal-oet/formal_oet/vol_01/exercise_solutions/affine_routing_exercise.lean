import formal_oet.vol_01.exercise_solutions.extension_and_block_examples

namespace formal_oet.vol_01.exercise_solutions.affine_routing_exercise

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork
open formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.appendix_finite_dimensional_operator_networks
open formal_oet.vol_01.exercise_solutions.extension_and_block_examples
open scoped BigOperators

noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev Point := CoordinatePoint 2 Set.univ
/-- The root is `none`; `some false` and `some true` are the two projection nodes. -/
abbrev Node := Option Bool

def square : Set Plane := {x | -1 ≤ x 0 ∧ x 0 ≤ 1 ∧ -1 ≤ x 1 ∧ x 1 ≤ 1}
def source : Set Point := {x | match x with | none => False | some a => a.val ∈ square}
def point (x : Plane) : Point := full_coordinate_point x

def projection (b : Bool) : Plane →L[ℝ] Plane :=
  if b then second_projection else first_projection

def node_map : Node → Plane →L[ℝ] Plane
  | none => identity_map
  | some b => projection b

def node_operator (v : Node) : Operator Point none where
  func := Option.map (fun a => ⟨node_map v a.val, Set.mem_univ _⟩)
  preserves_bot := rfl

@[simp] theorem node_operator_apply (v : Node) (x : Plane) :
    (node_operator v).func (point x) = point (node_map v x) := rfl

@[simp] theorem node_operator_dom (v : Node) (x : Point) :
    x ∈ dom (node_operator v) ↔ x ≠ none := by
  cases x <;> simp [dom, node_operator]

def branch : Point → Bool
  | none => false
  | some a => decide (0 ≤ a.val 0)

def routing : Node → Point → OutputChoice Node
  | none, z => .next (some (branch z))
  | some _, _ => .stop

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the actual three-node network with one affine routing split. -/
def network : FiniteOperatorNetwork Point none Node where
  U := source
  bot_not_mem := by simp [source]
  node_fintype := inferInstance
  node_op := node_operator
  node_dom_nonempty := fun v => ⟨point 0, by simp [point, full_coordinate_point]⟩
  entry := fun _ => none
  entry_mem := by
    rintro ⟨x, hx⟩
    cases x with
    | none => exact hx.elim
    | some a => simp
  choice := routing
  choice_next_mem := by
    intro v w x hx _
    rw [node_operator_dom] at hx ⊢
    cases x <;> simp_all [node_operator]
  depth_bound := 2
  path_of := fun x => [none, some (branch x.val)]
  path_terminal := by
    rintro ⟨x, hx⟩
    cases x with
    | none => simp [source] at hx
    | some a =>
      apply TerminalPathFrom.next
      · rfl
      · exact TerminalPathFrom.stop rfl
  path_length_le_depth := by intro x; simp
  node_reachable := by
    intro v
    cases v with
    | none => exact ⟨⟨point 0, by norm_num [source, point, full_coordinate_point, square]⟩, by simp⟩
    | some b =>
      cases b
      · exact ⟨⟨point ![-1,0], by norm_num [source, point, full_coordinate_point, square]⟩,
          by norm_num [branch, point, full_coordinate_point]⟩
      · exact ⟨⟨point 0, by norm_num [source, point, full_coordinate_point, square]⟩,
          by norm_num [branch, point, full_coordinate_point]⟩

def node_affine (v : Node) : Plane →ᵃ[ℝ] Plane := (node_map v).toLinearMap.toAffineMap

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： all three actual local operators have the displayed affine realization. -/
theorem nodes_are_affine : AffineNodeRealization network node_affine := by
  intro v a _
  exact ⟨⟨node_map v a.val, Set.mem_univ _⟩, rfl, rfl⟩

def branch_domain (b : Bool) : Set Plane :=
  square ∩ {x | if b then 0 ≤ x 0 else x 0 < 0}

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the actual path domains are the two half-squares. -/
theorem path_domain_formula (b : Bool) :
    real_locus (network.path_domain [none, some b]) = branch_domain b := by
  ext x
  rw [show x ∈ real_locus (network.path_domain [none, some b]) ↔
    point x ∈ network.path_domain [none, some b] from mem_real_locus _ ⟨x, Set.mem_univ _⟩]
  cases b <;> simp [path_domain, network, source, point, full_coordinate_point,
    branch, branch_domain]

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the two actual root transition domains are the stated
negative and nonnegative half-spaces in the output coordinates. -/
theorem edge_domain_formula (b : Bool) :
    real_locus (network.edge_domain none (some b)) =
      {x : Plane | if b then 0 ≤ x 0 else x 0 < 0} := by
  ext x
  rw [show x ∈ real_locus (network.edge_domain none (some b)) ↔
    point x ∈ network.edge_domain none (some b) from mem_real_locus _ ⟨x, Set.mem_univ _⟩]
  have him : point x ∈ network.node_image none := by
    refine ⟨point x, ?_, rfl⟩
    change point x ∈ dom (node_operator none)
    simp [point, full_coordinate_point]
  change (point x ∈ network.node_image none ∧ routing none (point x) = .next (some b)) ↔ _
  simp only [him, true_and]
  cases b <;> simp [routing, branch, point, full_coordinate_point]

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the two projection nodes have no outgoing transition domains. -/
theorem terminal_nodes_have_no_edges (b : Bool) (v : Node) :
    network.edge_domain (some b) v = ∅ := by
  ext x
  simp [edge_domain, to_transition_graph, network, routing]

private theorem no_edge_to_root (v : Node) : network.edge_domain v none = ∅ := by
  cases v <;> ext x <;> simp [edge_domain, to_transition_graph, network, routing]

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： these are all reachable complete paths. -/
theorem path_cases (p : network.ReachablePath) :
    p.nodes = [none, some false] ∨ p.nodes = [none, some true] := by
  obtain ⟨x, hx, hp⟩ := p.nonempty_domain
  cases hb : branch x
  · exact Or.inl (by simpa [network, hb] using hp.symm)
  · exact Or.inr (by simpa [network, hb] using hp.symm)

def path (b : Bool) : network.ReachablePath :=
  ⟨[none, some b], by
    have h : (branch_domain b).Nonempty := by
      cases b
      · exact ⟨![-1,0], by norm_num [branch_domain, square]⟩
      · exact ⟨0, by norm_num [branch_domain, square]⟩
    rw [← path_domain_formula b] at h
    rcases h with ⟨_, ⟨a, ha, rfl⟩⟩
    exact ⟨some a, ha⟩⟩

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： each affine path map is its terminal coordinate projection. -/
theorem path_affine_formula (b : Bool) :
    affine_path_map node_affine (path b).nodes = (projection b).toLinearMap.toAffineMap := by
  ext x i
  rfl

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the actual path chain, not only its affine realization,
is the prescribed coordinate projection. -/
theorem path_chain_formula (b : Bool) (x : Plane) :
    (network.path_chain (path b).nodes).func (point x) = point (projection b x) := by
  rw [network.path_chain_apply_eq_chain_eval_nodes]
  rfl

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the actual network output on each input follows the prescribed branch. -/
theorem network_eval (x : Plane) (hx : x ∈ square) :
    network.extensional_operator.func (point x) = point (projection (decide (0 ≤ x 0)) x) := by
  simp [extensional_operator, network, eval, chain_eval_nodes_core, source, point,
    full_coordinate_point, hx, node_operator, node_map, identity_map, branch]


private theorem path_injective : Function.Injective path := by
  intro b c h
  have hnodes := congrArg (fun p : network.ReachablePath => p.nodes) h
  simpa [path] using hnodes

private theorem path_eq_cases (p : network.ReachablePath) : p = path false ∨ p = path true := by
  rcases path_cases p with hp | hp
  · left; cases p; cases hp; rfl
  · right; cases p; cases hp; rfl

private theorem paths_univ : (Finset.univ : Finset network.ReachablePath) =
    {path false, path true} := by
  ext p
  simpa using path_eq_cases p

private theorem euclidean_norm_sq (x : Plane) :
    ‖euclidean_coordinates x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  rfl

private theorem projection_euclidean_apply (b : Bool) (x : Plane) :
    euclidean_affine_linear (projection b).toLinearMap.toAffineMap (euclidean_coordinates x) =
      euclidean_coordinates (projection b x) := by
  simp [euclidean_affine_linear]

private theorem projection_rank (b : Bool) :
    Module.finrank ℝ (projection b).toLinearMap.range = 1 := by
  cases b
  · exact ranks.1
  · change second_matrix.rank = 1
    rw [second_matrix, Matrix.rank_diagonal]
    have heq : (Finset.univ.filter (fun i : Fin 2 => ![(0 : ℝ), 1] i ≠ 0)) = {1} := by
      ext i; fin_cases i <;> simp
    rw [Fintype.card_subtype, heq]
    simp

private theorem projection_norm (b : Bool) :
    ‖euclidean_affine_linear (projection b).toLinearMap.toAffineMap‖ = 1 := by
  let T := euclidean_affine_linear (projection b).toLinearMap.toAffineMap
  have hle : ‖T‖ ≤ 1 := by
    apply T.opNorm_le_bound (by norm_num)
    intro z
    obtain ⟨x, rfl⟩ := euclidean_coordinates.surjective z
    rw [one_mul, projection_euclidean_apply]
    have h1 := euclidean_norm_sq x
    have h2 := euclidean_norm_sq (projection b x)
    cases b <;>
      simp only [projection, Bool.false_eq_true, ↓reduceIte, first_projection_apply,
        second_projection_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] at h2 ⊢ <;>
      nlinarith [norm_nonneg (euclidean_coordinates x), sq_nonneg (x 0), sq_nonneg (x 1)]
  have hge : 1 ≤ ‖T‖ := by
    let x : Plane := if b then ![0,1] else ![1,0]
    have hx : ‖euclidean_coordinates x‖ = 1 := by
      have hsq : ‖euclidean_coordinates x‖ ^ 2 = 1 := by
        rw [euclidean_norm_sq]
        cases b <;> norm_num [x]
      nlinarith [norm_nonneg (euclidean_coordinates x)]
    have hfix : projection b x = x := by
      cases b <;> simp [x, projection, first_projection_apply, second_projection_apply]
    have h := T.le_opNorm (euclidean_coordinates x)
    dsimp only [T] at h
    rw [projection_euclidean_apply, hfix, hx, mul_one] at h
    exact h
  exact le_antisymm hle hge

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the actual path linear maps both have rank one and Euclidean norm one. -/
theorem path_rank_and_norm (b : Bool) :
    Module.finrank ℝ (euclidean_affine_linear
      (affine_path_map node_affine (path b).nodes)).toLinearMap.range = 1 ∧
    ‖euclidean_affine_linear (affine_path_map node_affine (path b).nodes)‖ = 1 := by
  rw [path_affine_formula]
  exact ⟨by rw [euclidean_rank]; exact projection_rank b, projection_norm b⟩

def branch_center (b : Bool) : Plane := if b then ![1/2,0] else ![-1/2,0]

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the chosen center belongs to its actual path domain. -/
theorem center_mem_path_domain (b : Bool) :
    branch_center b ∈ real_locus (network.path_domain (path b).nodes) := by
  rw [show (path b).nodes = [none, some b] from rfl, path_domain_formula]
  cases b <;> norm_num [branch_domain, square, branch_center]

/-- OET anchor: h-b3f71b0e8b87fbf0
The differences in each actual half-square span the full input plane. -/
theorem path_direction_span (b : Bool) :
    direction_span (real_locus (network.path_domain (path b).nodes)) = ⊤ := by
  rw [show (path b).nodes = [none, some b] from rfl, path_domain_formula]
  have hc : branch_center b ∈ branch_domain b := by
    cases b <;> norm_num [branch_domain, square, branch_center]
  have hx : (![branch_center b 0 + 1/4, 0] : Plane) ∈ branch_domain b := by
    cases b <;> norm_num [branch_domain, square, branch_center]
  have hy : (![branch_center b 0, 1] : Plane) ∈ branch_domain b := by
    cases b <;> norm_num [branch_domain, square, branch_center]
  have he₀ : (![(1 : ℝ), 0] : Plane) ∈ direction_span (branch_domain b) := by
    have h := (direction_span (branch_domain b)).smul_mem (4 : ℝ)
      (sub_mem_direction_span hx hc)
    convert h using 1
    ext i
    fin_cases i <;> cases b <;> norm_num [branch_center]
  have he₁ : (![(0 : ℝ), 1] : Plane) ∈ direction_span (branch_domain b) := by
    have h := sub_mem_direction_span hy hc
    convert h using 1
    ext i
    fin_cases i <;> cases b <;> norm_num [branch_center]
  apply eq_top_iff.mpr
  intro v _
  have h := (direction_span (branch_domain b)).add_mem
    ((direction_span (branch_domain b)).smul_mem (v 0) he₀)
    ((direction_span (branch_domain b)).smul_mem (v 1) he₁)
  convert h using 1
  ext i
  fin_cases i <;> simp

/-- OET anchor: h-b3f71b0e8b87fbf0
The revised covering theorem reads the actual restricted rank, which is one
on each half-square because its direction space is the full plane. -/
theorem path_restricted_rank (b : Bool) :
    Module.finrank ℝ ((affine_path_map node_affine (path b).nodes).linear.domRestrict
      (direction_span (real_locus (network.path_domain (path b).nodes)))).range = 1 := by
  rw [path_direction_span, LinearMap.range_domRestrict, Submodule.map_top, path_affine_formula]
  exact projection_rank b

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the Euclidean radius bound on each actual half-square. -/
theorem path_radius_bound (b : Bool) (x : Plane)
    (hx : x ∈ real_locus (network.path_domain (path b).nodes)) :
    ‖euclidean_coordinates (x - branch_center b)‖ ≤ Real.sqrt 5 / 2 := by
  rw [show (path b).nodes = [none, some b] from rfl, path_domain_formula] at hx
  have hx1 : (x 1) ^ 2 ≤ 1 := by
    have h := hx.1
    dsimp [square] at h
    nlinarith [mul_nonneg (by linarith : 0 ≤ x 1 + 1) (by linarith : 0 ≤ 1 - x 1)]
  have hx0 : (x 0 - branch_center b 0) ^ 2 ≤ 1/4 := by
    rcases hx with ⟨hlo, hb⟩
    dsimp [square] at hlo
    cases b <;> norm_num [branch_center, branch_domain] at hb ⊢ <;>
      nlinarith [mul_nonneg (by linarith : 0 ≤ x 0 + 1) (by linarith : 0 ≤ 1 - x 0)]
  have hn := euclidean_norm_sq (x - branch_center b)
  have hzero : branch_center b 1 = 0 := by cases b <;> norm_num [branch_center]
  simp only [Pi.sub_apply, hzero, sub_zero] at hn
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith [Real.sqrt_nonneg (5 : ℝ), norm_nonneg (euclidean_coordinates (x - branch_center b))]


private theorem real_network_output :
    real_locus (network.extensional_operator.func '' network.U) =
      (fun x => projection (decide (0 ≤ x 0)) x) '' square := by
  ext x
  rw [show x ∈ real_locus (network.extensional_operator.func '' network.U) ↔
    point x ∈ network.extensional_operator.func '' network.U from mem_real_locus _ ⟨x, Set.mem_univ _⟩]
  constructor
  · rintro ⟨z, hz, heq⟩
    cases z with
    | none => exact hz.elim
    | some a =>
      have ha : a.val ∈ square := hz
      have h := network_eval a.val ha
      change network.extensional_operator.func (point a.val) = point x at heq
      rw [h] at heq
      have hh : projection (decide (0 ≤ a.val 0)) a.val = x := by
        simpa [point, full_coordinate_point] using heq
      exact ⟨a.val, ha, hh⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨point x, hx, network_eval x hx⟩

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the actual network image is the union of the displayed horizontal
half-segment and vertical segment. -/
theorem network_output_formula :
    real_locus (network.extensional_operator.func '' network.U) =
      {x : Plane | (-1 ≤ x 0 ∧ x 0 < 0 ∧ x 1 = 0) ∨
        (x 0 = 0 ∧ -1 ≤ x 1 ∧ x 1 ≤ 1)} := by
  rw [real_network_output]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases h : 0 ≤ y 0
    · simp only [h, decide_true, projection, ↓reduceIte, second_projection_apply]
      exact Or.inr ⟨by simp, hy.2.2⟩
    · simp only [h, decide_false, projection, Bool.false_eq_true, ↓reduceIte,
        first_projection_apply]
      exact Or.inl ⟨hy.1, lt_of_not_ge h, by simp⟩
  · rintro (h | h)
    · refine ⟨x, ?_, ?_⟩
      · exact ⟨h.1, h.2.1.le.trans (by norm_num), by linarith [h.2.2], by linarith [h.2.2]⟩
      · have hn : ¬ 0 ≤ x 0 := not_le.mpr h.2.1
        simp only [hn, decide_false, projection, Bool.false_eq_true, ↓reduceIte,
          first_projection_apply]
        ext i; fin_cases i <;> simp_all
    · refine ⟨x, ?_, ?_⟩
      · exact ⟨by linarith [h.1], by linarith [h.1], h.2⟩
      · have hp : 0 ≤ x 0 := by linarith [h.1]
        simp only [hp, decide_true, projection, ↓reduceIte, second_projection_apply]
        ext i; fin_cases i <;> simp_all

private def center (p : network.ReachablePath) : Plane :=
  branch_center (decide (p.nodes = [none, some true]))

private theorem center_path (b : Bool) : center (path b) = branch_center b := by
  cases b <;> simp [center, path]

/-- OET anchor: h-b3f71b0e8b87fbf0
仿射路由与路径秩： the general rank-cover theorem applied to this actual network,
with both actual path products and both half-square radius estimates evaluated. -/
theorem network_covering_bound (ε : ℝ) (hε : 0 < ε) :
    covering_number euclidean_distance (ENNReal.ofReal ε)
      (network.extensional_operator.func '' network.U) ≤
      ENNReal.ofReal (2 * (1 + Real.sqrt 5 / ε)) := by
  have hdom : ∀ p : network.ReachablePath,
      ∀ x ∈ real_locus (network.path_domain p.nodes),
        ‖euclidean_coordinates (x - center p)‖ ≤ Real.sqrt 5 / 2 := by
    intro p x hx
    rcases path_eq_cases p with rfl | rfl <;>
      rw [center_path] <;> exact path_radius_bound _ x hx
  have hc : ∀ p : network.ReachablePath,
      center p ∈ real_locus (network.path_domain p.nodes) := by
    intro p
    rcases path_eq_cases p with rfl | rfl <;>
      rw [center_path] <;> exact center_mem_path_domain _
  have h := actual_affine_network_direction_rank_cover network node_affine nodes_are_affine
    center (fun _ => Real.sqrt 5 / 2) hc (fun _ => by positivity) hdom ε hε
  have hne : path false ≠ path true := fun h => Bool.false_ne_true (path_injective h)
  rw [paths_univ, Finset.sum_insert (by simpa using hne), Finset.sum_singleton] at h
  rw [path_restricted_rank false, (path_rank_and_norm false).2,
    path_restricted_rank true, (path_rank_and_norm true).2] at h
  have heq : (1 + 2 * (1 : ℝ) * (Real.sqrt 5 / 2) / ε) ^ 1 =
      1 + Real.sqrt 5 / ε := by ring
  rw [heq, ← ENNReal.ofReal_add (by positivity) (by positivity)] at h
  convert h using 1
  congr 1
  ring

end
end formal_oet.vol_01.exercise_solutions.affine_routing_exercise
