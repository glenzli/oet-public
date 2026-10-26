import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_geometry
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.jacobi_block_bridge
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.jacobi_coordinate_bridge

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
noncomputable section
variable {n : ℕ}

/-- Change only the normed-space presentation of the actual linear derivative. -/
def euclidean_linear_map (T : CoordinateVector n →L[ℝ] CoordinateVector n) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  euclidean_coordinates.toContinuousLinearMap.comp
    (T.comp euclidean_coordinates.symm.toContinuousLinearMap)

theorem standard_projected_map_eq_rank_one
    (T : CoordinateVector n →L[ℝ] CoordinateVector n) (i j : Fin n) :
    (standard_coordinate_subspace j).starProjection.comp
        ((euclidean_linear_map T).comp (standard_coordinate_subspace i).starProjection) =
      (T (Pi.single i 1) j) • InnerProductSpace.rankOne ℝ
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  apply ContinuousLinearMap.ext
  intro v
  have hi : inner ℝ (EuclideanSpace.single i 1) v = v i := by
    simpa using EuclideanSpace.inner_single_left (𝕜 := ℝ) i 1 v
  simp [ContinuousLinearMap.comp_apply, standard_coordinate_projection,
    euclidean_linear_map, euclidean_coordinates, InnerProductSpace.rankOne_apply,
    hi, PiLp.coe_continuousLinearEquiv, map_smul, smul_smul, mul_comm]

/--
OET anchor: h-460dce986b592798
The genuine one-dimensional projected Euclidean operator norm is the absolute
value of the actual input-to-output derivative entry.
-/
theorem standard_projected_map_norm
    (T : CoordinateVector n →L[ℝ] CoordinateVector n) (i j : Fin n) :
    ‖(standard_coordinate_subspace j).starProjection.comp
        ((euclidean_linear_map T).comp (standard_coordinate_subspace i).starProjection)‖ =
      |T (Pi.single i 1) j| := by
  rw [standard_projected_map_eq_rank_one]
  simp [norm_smul, Real.norm_eq_abs]

def euclidean_derivative
    (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (z : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  euclidean_linear_map (D (euclidean_coordinates.symm z))

/--
OET anchor: h-460dce986b592798
The block Lip supremum L^V equals the coordinate Lip supremum L for the standard
one-dimensional orthogonal decomposition, with the same comparison set.
-/
theorem standard_jacobi_block_sup_eq_coordinate_sup
    (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (Q : Set (CoordinateVector n)) (i j : Fin n) :
    jacobi_block_sup standard_coordinate_subspace (euclidean_derivative D)
      (euclidean_coordinates '' Q) i j = jacobi_entry_sup D Q i j := by
  unfold jacobi_block_sup jacobi_entry_sup
  rw [Set.image_image]
  simp only [jacobi_block_map, euclidean_derivative,
    ContinuousLinearEquiv.symm_apply_apply, standard_projected_map_norm, jacobi_entry]

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
