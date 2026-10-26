import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.actual_path_covering
import formal_oet.vol_01.ch_05_operator_networks.network_extensional_space
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace formal_oet.vol_01.exercise_solutions.extension_and_block_examples

noncomputable section
open scoped Matrix

abbrev Plane := Fin 2 → ℝ

def first_matrix : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![1, 0]
def second_matrix : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![0, 1]
def first_projection : Plane →L[ℝ] Plane := first_matrix.mulVecLin.toContinuousLinearMap
def identity_map : Plane →L[ℝ] Plane := ContinuousLinearMap.id ℝ Plane
def second_projection : Plane →L[ℝ] Plane := second_matrix.mulVecLin.toContinuousLinearMap

def segment : Set Plane := {x | -1 ≤ x 0 ∧ x 0 ≤ 1 ∧ x 1 = 0}

lemma first_projection_apply (x : Plane) : first_projection x = ![x 0, 0] := by
  ext i; fin_cases i <;> simp [first_projection, first_matrix, Matrix.mulVec]
lemma identity_map_apply (x : Plane) : identity_map x = x := rfl
lemma second_projection_apply (x : Plane) : second_projection x = ![0, x 1] := by
  ext i; fin_cases i <;> simp [second_projection, second_matrix, Matrix.mulVec]

/-- OET anchor: h-84ef8daaa0e28176
The two ambient affine extensions agree on the entire segment. -/
theorem extensions_agree : Set.EqOn first_projection identity_map segment := by
  intro x hx
  rw [first_projection_apply, identity_map_apply]
  ext i; fin_cases i <;> simp_all [segment]

/-- OET anchor: h-84ef8daaa0e28176
Both extensions have the same output set, namely the original segment. -/
theorem images_eq : first_projection '' segment = segment ∧ identity_map '' segment = segment := by
  have hf : first_projection '' segment = identity_map '' segment := Set.EqOn.image_eq extensions_agree
  constructor
  · simpa [identity_map] using hf
  · simp [identity_map]

/-- OET anchor: h-84ef8daaa0e28176
These are actual derivatives of the specified extensions, not assumed matrices. -/
theorem derivatives (x : Plane) : fderiv ℝ first_projection x = first_projection ∧ fderiv ℝ identity_map x = identity_map := by
  exact ⟨first_projection.fderiv, identity_map.fderiv⟩

/-- OET anchor: h-84ef8daaa0e28176
The two ambient derivative ranks are 1 and 2; the restricted ranks below agree. -/
theorem ranks : Module.finrank ℝ (LinearMap.range first_projection.toLinearMap) = 1 ∧
    Module.finrank ℝ (LinearMap.range identity_map.toLinearMap) = 2 := by
  constructor
  · change first_matrix.rank = 1
    rw [first_matrix, Matrix.rank_diagonal]
    have heq : (Finset.univ.filter (fun i : Fin 2 => ![(1 : ℝ), 0] i ≠ 0)) = {0} := by
      ext i; fin_cases i <;> simp
    rw [Fintype.card_subtype, heq]
    simp
  · change Module.finrank ℝ (LinearMap.range (LinearMap.id : Plane →ₗ[ℝ] Plane)) = 2
    rw [LinearMap.range_id]
    simp [Plane]

/-- OET anchor: h-84ef8daaa0e28176
The derivative rank really differs although the restricted maps agree. -/
theorem derivative_ranks (x : Plane) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ first_projection x).toLinearMap) = 1 ∧
    Module.finrank ℝ (LinearMap.range (fderiv ℝ identity_map x).toLinearMap) = 2 := by
  rw [(derivatives x).1, (derivatives x).2]
  exact ranks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.appendix_finite_dimensional_operator_networks

abbrev ModelPoint := CoordinatePoint 2 Set.univ

local instance (x : Plane) : Decidable (x ∈ segment) := Classical.propDecidable _

def restricted_node : Operator ModelPoint none where
  func
    | none => none
    | some a => if a.val ∈ segment then some a else none
  preserves_bot := rfl

lemma restricted_node_nonempty : restricted_node ≠ bot_operator := by
  intro h
  have heq := congrArg (fun T : Operator ModelPoint none => T.func (some ⟨0, Set.mem_univ _⟩)) h
  simp [restricted_node, segment, bot_operator] at heq

/-- OET anchor: h-84ef8daaa0e28176
The actual single-node network used in the exercise. -/
def segment_network : FiniteOperatorNetwork ModelPoint none Unit :=
  NetworkObject.single_node_network restricted_node restricted_node_nonempty

/-- OET anchor: h-84ef8daaa0e28176
Both chosen affine maps realize exactly the same restricted node. -/
theorem realizations :
    AffineNodeRealization segment_network (fun _ => first_projection.toLinearMap.toAffineMap) ∧
    AffineNodeRealization segment_network (fun _ => identity_map.toLinearMap.toAffineMap) := by
  have h : ∀ (T : Plane →L[ℝ] Plane), Set.EqOn T id segment →
      AffineNodeRealization segment_network (fun _ => T.toLinearMap.toAffineMap) := by
    intro T hT v a ha
    have ha' : a.val ∈ segment := by
      change (if a.val ∈ segment then some a else none) ≠ none at ha
      by_contra hnot
      simp [hnot] at ha
    refine ⟨a, ?_, (hT ha').symm⟩
    change (if a.val ∈ segment then some a else none) = some a
    simp [ha']
  exact ⟨h first_projection extensions_agree, h identity_map (fun _ _ => rfl)⟩

/-- A change between the sup-norm and Euclidean coordinate models preserves rank. -/
lemma euclidean_rank (T : Plane →L[ℝ] Plane) :
    Module.finrank ℝ (euclidean_affine_linear T.toLinearMap.toAffineMap).toLinearMap.range =
      Module.finrank ℝ T.toLinearMap.range := by
  let e : Plane ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) := euclidean_coordinates.toLinearEquiv
  have heq : (euclidean_affine_linear T.toLinearMap.toAffineMap).toLinearMap.range =
      T.toLinearMap.range.map e.toLinearMap := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨T (e.symm x), ⟨e.symm x, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨e x, ?_⟩
      change e (T (e.symm (e x))) = e (T x)
      rw [e.symm_apply_apply]
  rw [heq]
  exact e.finrank_map_eq _

lemma segment_path (p : segment_network.ReachablePath) : p.nodes = [()] := by
  rcases p.nonempty_domain with ⟨x, hx, hp⟩
  exact hp.symm

/-- OET anchor: h-84ef8daaa0e28176
The segment's available directions are exactly the first coordinate line. -/
theorem segment_direction_span : direction_span segment = Submodule.span ℝ {![1, 0]} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨x, hx, y, hy, rfl⟩
    have heq : x - y = (x 0 - y 0) • ![(1 : ℝ), 0] := by
      ext i
      fin_cases i <;> simp_all [segment]
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro x rfl
    have he : (![(1 : ℝ), 0] : Plane) ∈ segment := by norm_num [segment]
    have hz : (0 : Plane) ∈ segment := by norm_num [segment]
    simpa using sub_mem_direction_span he hz

lemma projection_range_span : first_projection.toLinearMap.range = Submodule.span ℝ {![1, 0]} := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    have heq : first_projection y = (y 0) • ![(1 : ℝ), 0] := by
      rw [first_projection_apply]
      ext i; fin_cases i <;> simp
    change first_projection y ∈ Submodule.span ℝ {(![1, 0] : Plane)}
    rw [heq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro x rfl
    exact ⟨![1, 0], by simp [first_projection_apply]⟩

/-- OET anchor: h-84ef8daaa0e28176
Restricting to the actual segment directions removes the artificial ambient rank difference. -/
theorem restricted_ranks :
    Module.finrank ℝ (first_projection.toLinearMap.domRestrict (direction_span segment)).range = 1 ∧
    Module.finrank ℝ (identity_map.toLinearMap.domRestrict (direction_span segment)).range = 1 := by
  have hf : (direction_span segment).map first_projection.toLinearMap =
      Submodule.span ℝ {(![1, 0] : Plane)} := by
    rw [segment_direction_span, Submodule.map_span]
    simp [first_projection_apply]
  have hi : (direction_span segment).map identity_map.toLinearMap =
      Submodule.span ℝ {(![1, 0] : Plane)} := by
    rw [segment_direction_span, Submodule.map_span]
    simp [identity_map]
  rw [LinearMap.range_domRestrict, LinearMap.range_domRestrict, hf, hi, ← projection_range_span]
  exact ⟨ranks.1, ranks.1⟩

/-- OET anchor: h-84ef8daaa0e28176
The two restricted derivatives agree as maps, not only in rank. -/
theorem restricted_maps_eq :
    first_projection.toLinearMap.domRestrict (direction_span segment) =
      identity_map.toLinearMap.domRestrict (direction_span segment) := by
  apply affine_linear_eq_on_direction_span _ _ (0 : Plane) 0 segment
  intro x hx
  simpa using extensions_agree hx

/-- OET anchor: h-84ef8daaa0e28176
For these two particular extensions even the full Euclidean norm agrees. -/
theorem extension_euclidean_norms :
    ‖euclidean_affine_linear first_projection.toLinearMap.toAffineMap‖ = 1 ∧
    ‖euclidean_affine_linear identity_map.toLinearMap.toAffineMap‖ = 1 := by
  have hsq (x : Plane) : ‖euclidean_coordinates x‖ ^ 2 = (x 0)^2 + (x 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    rfl
  constructor
  · let T := euclidean_affine_linear first_projection.toLinearMap.toAffineMap
    have hT (x : Plane) : T (euclidean_coordinates x) = euclidean_coordinates (first_projection x) := by
      simp [T, euclidean_affine_linear]
    apply le_antisymm
    · apply T.opNorm_le_bound (by norm_num)
      intro z
      obtain ⟨x, rfl⟩ := euclidean_coordinates.surjective z
      rw [one_mul, hT]
      have ha := hsq x
      have hb := hsq (first_projection x)
      rw [first_projection_apply] at hb ⊢
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hb
      nlinarith [sq_nonneg (x 1), norm_nonneg (euclidean_coordinates x),
        norm_nonneg (euclidean_coordinates (![x 0, 0] : Plane))]
    · have hx : ‖euclidean_coordinates (![(1 : ℝ), 0] : Plane)‖ = 1 := by
        have h : ‖euclidean_coordinates (![(1 : ℝ), 0] : Plane)‖ ^ 2 = 1 := by
          simpa using hsq ![1, 0]
        nlinarith [norm_nonneg (euclidean_coordinates (![(1 : ℝ), 0] : Plane))]
      have h := T.le_opNorm (euclidean_coordinates ![1, 0])
      rw [hT, first_projection_apply] at h
      norm_num [hx] at h
      exact h
  · have hi : euclidean_affine_linear identity_map.toLinearMap.toAffineMap =
        ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
      ext x i
      simp [euclidean_affine_linear, identity_map]
    rw [hi, ContinuousLinearMap.norm_id]

lemma segment_path_domain (p : segment_network.ReachablePath) :
    real_locus (segment_network.path_domain p.nodes) = segment := by
  rw [segment_path]
  ext x
  have hm := mem_real_locus (segment_network.path_domain [()])
    (⟨x, Set.mem_univ _⟩ : (Set.univ : Set Plane))
  rw [hm]
  change (∃ hx : (some ⟨x, Set.mem_univ _⟩ : ModelPoint) ∈ segment_network.U, [()] = [()]) ↔ x ∈ segment
  simp [segment_network, NetworkObject.single_node_network, restricted_node, dom]

/-- OET anchor: h-84ef8daaa0e28176
Both actual rank exponents read by the revised path covering theorem are one. -/
theorem covering_exponents (p : segment_network.ReachablePath) :
    Module.finrank ℝ ((affine_path_map
      (fun _ : Unit => first_projection.toLinearMap.toAffineMap) p.nodes).linear.domRestrict
      (direction_span (real_locus (segment_network.path_domain p.nodes)))).range = 1 ∧
    Module.finrank ℝ ((affine_path_map
      (fun _ : Unit => identity_map.toLinearMap.toAffineMap) p.nodes).linear.domRestrict
      (direction_span (real_locus (segment_network.path_domain p.nodes)))).range = 1 := by
  rw [segment_path_domain, segment_path]
  exact restricted_ranks

/-- OET anchor: h-64877d77e522a25b
Both displayed projection maps are nonzero. -/
theorem factors_nonzero : first_projection ≠ 0 ∧ second_projection ≠ 0 := by
  constructor
  · intro h
    have heq := congrArg (fun T : Plane →L[ℝ] Plane => T ![1,0] 0) h
    norm_num [first_projection_apply] at heq
  · intro h
    have heq := congrArg (fun T : Plane →L[ℝ] Plane => T ![0,1] 1) h
    norm_num [second_projection_apply] at heq

/-- OET anchor: h-64877d77e522a25b
The only block route has zero composite even though its two factors are nonzero. -/
theorem composite_zero : second_projection.comp first_projection = 0 := by
  ext x i
  fin_cases i <;> simp [ContinuousLinearMap.comp_apply, first_projection_apply, second_projection_apply]

/-- OET anchor: h-64877d77e522a25b
The first projection's image is exactly the second projection's kernel. -/
theorem image_kernel : LinearMap.range first_projection.toLinearMap = LinearMap.ker second_projection.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change second_projection (first_projection y) = 0
    have h := congrArg (fun T : Plane →L[ℝ] Plane => T y) composite_zero
    exact h
  · intro hx
    have hx1 : x 1 = 0 := by
      have h : second_projection x = 0 := hx
      have := congrArg (fun y : Plane => y 1) h
      simpa [second_projection_apply] using this
    refine ⟨x, ?_⟩
    change first_projection x = x
    rw [first_projection_apply]
    ext i; fin_cases i <;> simp_all

/-- The actual Euclidean operator used by the block-route definitions. -/
def euclidean_version (T : Plane →L[ℝ] Plane) :=
  euclidean_affine_linear T.toLinearMap.toAffineMap

lemma euclidean_nonzero (T : Plane →L[ℝ] Plane) (hT : T ≠ 0) :
    euclidean_version T ≠ 0 := by
  intro h
  apply hT
  ext x i
  have heq := congrArg (fun L => L (euclidean_coordinates x)) h
  have hx : T x = 0 := by
    apply euclidean_coordinates.injective
    simpa [euclidean_version, euclidean_affine_linear] using heq
  exact congrFun hx i

lemma euclidean_composite_zero :
    (euclidean_version second_projection).comp (euclidean_version first_projection) = 0 := by
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun L : Plane →L[ℝ] Plane => L (euclidean_coordinates.symm x)) composite_zero
  change second_projection (first_projection (euclidean_coordinates.symm x)) = 0 at h
  have heq := congrArg euclidean_coordinates h
  simpa only [euclidean_version, euclidean_affine_linear, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.symm_apply_apply, map_zero] using heq

/-- The support for the single whole-plane orthogonal block, using the actual
projected-operator definition from the finite-dimensional network appendix. -/
def one_block_support (T : Plane →L[ℝ] Plane) : Set (Unit × Unit) :=
  {ij | projected_operator (fun _ : Unit => (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))))
    (euclidean_version T) ij.1 ij.2 ≠ 0}

/-- OET anchor: h-64877d77e522a25b
The two supports are the unique block pair, whereas the composite support is empty. -/
theorem supports : one_block_support first_projection = Set.univ ∧
    one_block_support second_projection = Set.univ ∧
    one_block_support (second_projection.comp first_projection) = ∅ := by
  have hz : euclidean_version 0 = 0 := by
    ext x; simp [euclidean_version, euclidean_affine_linear]
  simp [one_block_support, projected_operator, Submodule.starProjection_top,
    euclidean_nonzero _ factors_nonzero.1, euclidean_nonzero _ factors_nonzero.2,
    composite_zero, hz]

/-- OET anchor: h-64877d77e522a25b
An actual nonzero block route exists, but its operator product is zero. -/
theorem block_route_without_nonzero_product :
    NonzeroBlockRoute (fun _ : Unit => (⊤ : Submodule ℝ (EuclideanSpace ℝ (Fin 2))))
      [euclidean_version second_projection, euclidean_version first_projection] () () ∧
    (euclidean_version second_projection).comp (euclidean_version first_projection) = 0 := by
  refine ⟨?_, euclidean_composite_zero⟩
  simp [NonzeroBlockRoute, projected_operator, Submodule.starProjection_top,
    euclidean_nonzero _ factors_nonzero.1, euclidean_nonzero _ factors_nonzero.2]

end
end formal_oet.vol_01.exercise_solutions.extension_and_block_examples
