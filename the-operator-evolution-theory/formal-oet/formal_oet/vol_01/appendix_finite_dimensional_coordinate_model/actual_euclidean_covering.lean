import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.rank_image_covering
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.euclidean_geometry

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
noncomputable section
variable {n : ℕ}

/-- Embed Euclidean coordinates into the original model with A = R^n. -/
def euclidean_model_point (x : EuclideanSpace ℝ (Fin n)) :
    CoordinatePoint n Set.univ := some ⟨euclidean_coordinates.symm x, Set.mem_univ _⟩

theorem euclidean_model_distance (x y : EuclideanSpace ℝ (Fin n)) :
    euclidean_distance (euclidean_model_point x) (euclidean_model_point y) = edist x y := by
  rw [euclidean_model_point, euclidean_model_point, euclidean_distance_some,
    map_sub, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [edist_dist, dist_eq_norm]

theorem actual_euclidean_cover_eq (S : Set (EuclideanSpace ℝ (Fin n))) (ε : ENNReal) :
    covering_number euclidean_distance ε (euclidean_model_point '' S) =
      covering_number edist ε S :=
  internal_cover_image_eq edist euclidean_distance euclidean_model_point S ε
    (fun x _ y _ => euclidean_model_distance x y)

/--
OET anchor: h-a57e9e873735ed63
**命题（欧氏覆盖数的维数估计）**
Every nonempty bounded subset of a translated subspace has an internal OPEN-ball
cover controlled by the subspace dimension. Closedness and compactness of S are
not assumed. Dimension zero gives the actual singleton and covering number one;
the radius-zero case is allowed throughout.
-/
theorem actual_euclidean_affine_subspace_cover
    (center : EuclideanSpace ℝ (Fin n)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (S : Set (EuclideanSpace ℝ (Fin n))) (R ε : ℝ)
    (hR : 0 ≤ R) (hε : 0 < ε) (hne : S.Nonempty)
    (hS : ∀ y ∈ S, y - center ∈ W ∧ ‖y - center‖ ≤ R) :
    covering_number euclidean_distance (ENNReal.ofReal ε) (euclidean_model_point '' S) ≤
      ENNReal.ofReal ((1 + 2 * R / ε) ^ Module.finrank ℝ W) ∧
    (Module.finrank ℝ W = 0 → S = {center} ∧
      covering_number euclidean_distance (ENNReal.ofReal ε) (euclidean_model_point '' S) = 1) := by
  have hcover := internal_affine_subspace_cover center W S R ε hR hε hS
  rw [← actual_euclidean_cover_eq] at hcover
  refine ⟨hcover, ?_⟩
  intro hzero
  haveI : Subsingleton W := (Module.finrank_eq_zero_iff_of_free ℝ W).mp hzero
  have hevery : ∀ y ∈ S, y = center := by
    intro y hy
    have hz : y - center = 0 := congrArg Subtype.val
      (Subsingleton.elim (⟨y - center, (hS y hy).1⟩ : W) 0)
    exact sub_eq_zero.mp hz
  have hsingleton : S = {center} := by
    ext y
    constructor
    · intro hy
      exact Set.mem_singleton_iff.mpr (hevery y hy)
    · rintro rfl
      obtain ⟨z, hz⟩ := hne
      rw [← hevery z hz]
      exact hz
  refine ⟨hsingleton, le_antisymm ?_ ?_⟩
  · simpa [hzero] using hcover
  · exact one_le_covering_number_of_nonempty _ _ _ (hne.image euclidean_model_point)

/--
OET anchor: h-a57e9e873735ed63
Both volume bounds for the actual Euclidean distance on the original model.
-/
theorem actual_euclidean_ball_cover (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ENNReal.ofReal ((R / ε) ^ n) ≤
      covering_number euclidean_distance (ENNReal.ofReal ε)
        (euclidean_model_point '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ∧
    covering_number euclidean_distance (ENNReal.ofReal ε)
        (euclidean_model_point '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) ≤
      ENNReal.ofReal ((1 + 2 * R / ε) ^ n) := by
  rw [actual_euclidean_cover_eq]
  constructor
  · simpa using internal_closed_ball_volume_lower (E := EuclideanSpace ℝ (Fin n)) R ε hR hε
  · simpa using internal_cover_volume_upper R ε hR.le hε
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
      (fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hx)

/--
OET anchor: h-a57e9e873735ed63
The exponent is the dimension of the actual linear range, and the factor is
the actual Euclidean operator norm. The radius-zero case is allowed as well.
-/
theorem actual_euclidean_rank_image_cover
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε) :
    covering_number euclidean_distance (ENNReal.ofReal ε)
      (euclidean_model_point '' (T '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) ≤
      ENNReal.ofReal ((1 + 2 * ‖T‖ * R / ε) ^ Module.finrank ℝ T.toLinearMap.range) := by
  rw [actual_euclidean_cover_eq]
  simpa only [add_zero, sub_zero] using internal_affine_image_rank_bound T 0 0 R ε hR hε
    (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
    (fun x hx => by simpa [Metric.mem_closedBall, dist_zero_right] using hx)

/--
OET anchor: h-a57e9e873735ed63
Rank zero gives the actual singleton image, including the degenerate R = 0 case.
-/
theorem actual_rank_zero_image
    (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (hT : Module.finrank ℝ T.toLinearMap.range = 0) (R : ℝ) (hR : 0 ≤ R) :
    euclidean_model_point '' (T '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) =
      {euclidean_model_point (0 : EuclideanSpace ℝ (Fin n))} := by
  have h := rank_zero_affine_image T 0 hT (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
    ⟨0, by simpa [Metric.mem_closedBall] using hR⟩
  simpa only [add_zero, h, Set.image_singleton] using congrArg (Set.image euclidean_model_point) h

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
