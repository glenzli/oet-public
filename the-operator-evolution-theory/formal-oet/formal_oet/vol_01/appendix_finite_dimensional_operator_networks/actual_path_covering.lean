import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.actual_euclidean_covering
import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.actual_affine_geometry
import formal_oet.vol_01.ch_05_operator_networks.output_bounds

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork
open formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open scoped BigOperators
noncomputable section
variable {n : ℕ} {V : Type}

/-- The linear part of an actual affine map, expressed in Euclidean coordinates.
Conjugation changes the norm model, not the linear map or its rank. -/
def euclidean_affine_linear (G : CoordinateVector n →ᵃ[ℝ] CoordinateVector n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  euclidean_coordinates.toContinuousLinearMap.comp
    (G.linear.toContinuousLinearMap.comp euclidean_coordinates.symm.toContinuousLinearMap)

theorem euclidean_affine_decomposition (G : CoordinateVector n →ᵃ[ℝ] CoordinateVector n)
    (x : CoordinateVector n) :
    euclidean_coordinates (G x) =
      euclidean_affine_linear G (euclidean_coordinates x) + euclidean_coordinates (G 0) := by
  have h := congrFun G.decomp x
  change G x = G.linear x + G 0 at h
  rw [h, map_add]
  simp [euclidean_affine_linear]

variable (N : FiniteOperatorNetwork (CoordinatePoint n Set.univ) none V)

/-- This equality connects the actual path output to the image used in the
rank estimate, using the already proved node-to-path affine composition. -/
theorem actual_path_output_euclidean_image
    (F : V → CoordinateVector n →ᵃ[ℝ] CoordinateVector n)
    (hF : AffineNodeRealization N F) (p : N.ReachablePath) :
    N.path_output_set p = euclidean_model_point ''
      ((fun x => euclidean_affine_linear (affine_path_map F p.nodes) x +
        euclidean_coordinates (affine_path_map F p.nodes 0)) ''
        (euclidean_coordinates '' real_locus (N.path_domain p.nodes))) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    cases x with
    | none => exact (N.bot_not_mem (N.path_domain_subset_source hx)).elim
    | some a =>
      obtain ⟨b, hb, hval⟩ := actual_path_output_is_affine N F hF p a hx
      refine ⟨euclidean_coordinates b.val, ?_, ?_⟩
      · refine ⟨euclidean_coordinates a.val,
          ⟨a.val, (mem_real_locus _ a).mpr hx, rfl⟩, ?_⟩
        dsimp only
        rw [← euclidean_affine_decomposition, hval]
      · rw [hb]
        simp [euclidean_model_point]
  · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    let a : (Set.univ : Set (CoordinateVector n)) := ⟨x, Set.mem_univ _⟩
    have ha : some a ∈ N.path_domain p.nodes := (mem_real_locus _ a).mp hx
    obtain ⟨b, hb, hval⟩ := actual_path_output_is_affine N F hF p a ha
    refine ⟨some a, ha, ?_⟩
    dsimp only
    rw [hb, ← euclidean_affine_decomposition]
    simp [euclidean_model_point, ← hval, a]

/--
Actual affine node maps determine the path product, its Euclidean norm and its
range dimension. The only geometric premise is the stated radius bound on
the actual path domain; no pathwise covering conclusion is an input.
-/
theorem actual_affine_network_rank_cover
    (F : V → CoordinateVector n →ᵃ[ℝ] CoordinateVector n)
    (hF : AffineNodeRealization N F)
    (center : N.ReachablePath → CoordinateVector n) (R : N.ReachablePath → ℝ)
    (hR : ∀ p, 0 ≤ R p)
    (hdom : ∀ p, ∀ x ∈ real_locus (N.path_domain p.nodes),
      ‖euclidean_coordinates (x - center p)‖ ≤ R p)
    (ε : ℝ) (hε : 0 < ε) :
    covering_number euclidean_distance (ENNReal.ofReal ε)
      (N.extensional_operator.func '' N.U) ≤
      ∑ p : N.ReachablePath,
        ENNReal.ofReal ((1 + 2 * ‖euclidean_affine_linear (affine_path_map F p.nodes)‖ * R p / ε) ^
          Module.finrank ℝ (euclidean_affine_linear (affine_path_map F p.nodes)).toLinearMap.range) := by
  rw [N.network_output_eq_iunion_path_outputs]
  apply (covering_number_i_union_finite_le euclidean_distance (ENNReal.ofReal ε)
    N.path_output_set).trans
  apply Finset.sum_le_sum
  intro p _
  rw [actual_path_output_euclidean_image N F hF p, actual_euclidean_cover_eq]
  apply internal_affine_image_rank_bound _ _ (euclidean_coordinates (center p)) _ _ (hR p) hε
  rintro _ ⟨x, hx, rfl⟩
  simpa [map_sub] using hdom p x hx

/-- A local affine image cover with the dimension of its actual input directions.
The full ambient operator norm is retained. -/
theorem affine_actual_direction_cover
    (G : CoordinateVector n →ᵃ[ℝ] CoordinateVector n) (D : Set (CoordinateVector n))
    (center : CoordinateVector n) (hc : center ∈ D) (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    (hdom : ∀ x ∈ D, ‖euclidean_coordinates (x - center)‖ ≤ R) :
    covering_number edist (ENNReal.ofReal ε)
      ((fun x => euclidean_affine_linear G x + euclidean_coordinates (G 0)) ''
        (euclidean_coordinates '' D)) ≤
      ENNReal.ofReal ((1 + 2 * ‖euclidean_affine_linear G‖ * R / ε) ^
        Module.finrank ℝ ((direction_span D).map G.linear)) := by
  let e := (euclidean_coordinates (n := n)).toLinearEquiv
  let W := (direction_span D).map G.linear
  let T := euclidean_affine_linear G
  have hdim : Module.finrank ℝ (W.map e.toLinearMap) = Module.finrank ℝ W :=
    e.finrank_map_eq W
  have hcover := internal_affine_subspace_cover
    (T (euclidean_coordinates center) + euclidean_coordinates (G 0)) (W.map e.toLinearMap)
    ((fun x => T x + euclidean_coordinates (G 0)) '' (euclidean_coordinates '' D))
    (‖T‖ * R) ε (mul_nonneg (norm_nonneg _) hR) hε
  have hdisp (x : CoordinateVector n) :
      T (euclidean_coordinates x) + euclidean_coordinates (G 0) -
        (T (euclidean_coordinates center) + euclidean_coordinates (G 0)) =
      euclidean_coordinates (G.linear (x - center)) := by
    simp [T, euclidean_affine_linear, ← map_sub]
  refine (hcover ?_).trans_eq ?_
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    constructor
    · rw [hdisp]
      exact ⟨G.linear (x - center), ⟨x - center, sub_mem_direction_span hx hc, rfl⟩, rfl⟩
    · rw [hdisp]
      have heq : euclidean_coordinates (G.linear (x - center)) =
          T (euclidean_coordinates (x - center)) := by simp [T, euclidean_affine_linear]
      rw [heq]
      exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hdom x hx) (norm_nonneg _))
  · rw [hdim]
    simp only [W, T, mul_assoc]

/-- OET anchor: h-c9e4b6fb4f7e4e59
The exponent is the rank of the path map restricted to the span of differences
of the actual path domain. The center belongs to that domain; the norm remains
the norm of the chosen full affine extension. -/
theorem actual_affine_network_direction_rank_cover
    (F : V → CoordinateVector n →ᵃ[ℝ] CoordinateVector n)
    (hF : AffineNodeRealization N F)
    (center : N.ReachablePath → CoordinateVector n) (R : N.ReachablePath → ℝ)
    (hc : ∀ p, center p ∈ real_locus (N.path_domain p.nodes))
    (hR : ∀ p, 0 ≤ R p)
    (hdom : ∀ p, ∀ x ∈ real_locus (N.path_domain p.nodes),
      ‖euclidean_coordinates (x - center p)‖ ≤ R p)
    (ε : ℝ) (hε : 0 < ε) :
    covering_number euclidean_distance (ENNReal.ofReal ε)
      (N.extensional_operator.func '' N.U) ≤
      ∑ p : N.ReachablePath,
        ENNReal.ofReal ((1 + 2 * ‖euclidean_affine_linear (affine_path_map F p.nodes)‖ * R p / ε) ^
          Module.finrank ℝ ((affine_path_map F p.nodes).linear.domRestrict
            (direction_span (real_locus (N.path_domain p.nodes)))).range) := by
  rw [N.network_output_eq_iunion_path_outputs]
  apply (covering_number_i_union_finite_le euclidean_distance (ENNReal.ofReal ε)
    N.path_output_set).trans
  apply Finset.sum_le_sum
  intro p _
  rw [actual_path_output_euclidean_image N F hF p, actual_euclidean_cover_eq,
    LinearMap.range_domRestrict]
  exact affine_actual_direction_cover _ _ (center p) (hc p) (R p) ε (hR p) hε (hdom p)

/-- OET anchor: h-c9e4b6fb4f7e4e59
A zero restricted rank gives an actual singleton path image and internal covering
number one, even when the chosen full affine matrix has positive rank. -/
theorem actual_path_restricted_rank_zero
    (F : V → CoordinateVector n →ᵃ[ℝ] CoordinateVector n)
    (hF : AffineNodeRealization N F) (p : N.ReachablePath)
    (center : CoordinateVector n) (hc : center ∈ real_locus (N.path_domain p.nodes))
    (hz : Module.finrank ℝ ((affine_path_map F p.nodes).linear.domRestrict
      (direction_span (real_locus (N.path_domain p.nodes)))).range = 0)
    (ε : ℝ) (hε : 0 < ε) :
    N.path_output_set p =
      {euclidean_model_point (euclidean_coordinates (affine_path_map F p.nodes center))} ∧
    covering_number euclidean_distance (ENNReal.ofReal ε) (N.path_output_set p) = 1 := by
  let G := affine_path_map F p.nodes
  let D := real_locus (N.path_domain p.nodes)
  let W := direction_span D
  let L := G.linear.domRestrict W
  haveI : Subsingleton L.range := (Module.finrank_eq_zero_iff_of_free ℝ L.range).mp hz
  have heq (x : CoordinateVector n) (hx : x ∈ D) : G x = G center := by
    let v : W := ⟨x - center, sub_mem_direction_span hx hc⟩
    have hL : L v = 0 := congrArg Subtype.val
      (Subsingleton.elim (⟨L v, ⟨v, rfl⟩⟩ : L.range) 0)
    have hlin : G.linear x = G.linear center := by
      apply sub_eq_zero.mp
      simpa only [L, LinearMap.domRestrict_apply, v, map_sub] using hL
    calc
      G x = G.linear x + G 0 := congrFun G.decomp x
      _ = G.linear center + G 0 := by rw [hlin]
      _ = G center := (congrFun G.decomp center).symm
  let c := euclidean_coordinates (G center)
  have himage : ((fun x => euclidean_affine_linear G x + euclidean_coordinates (G 0)) ''
      (euclidean_coordinates '' D)) = {c} := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change euclidean_affine_linear G (euclidean_coordinates x) + euclidean_coordinates (G 0) = c
      rw [← euclidean_affine_decomposition, heq x hx]
    · rintro rfl
      refine ⟨euclidean_coordinates center, ⟨center, hc, rfl⟩, ?_⟩
      exact (euclidean_affine_decomposition G center).symm
  have hout : N.path_output_set p = {euclidean_model_point c} := by
    rw [actual_path_output_euclidean_image N F hF p, himage, Set.image_singleton]
  refine ⟨hout, ?_⟩
  rw [hout, ← Set.image_singleton]
  exact (actual_euclidean_affine_subspace_cover c ⊥ {c} 0 ε le_rfl hε
    (Set.singleton_nonempty c) (by intro y hy; rcases hy with rfl; simp)).2 (by simp) |>.2

end
end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
