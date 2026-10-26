import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_block_model
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.appendix_separating_gauge_specialization
open scoped BigOperators
noncomputable section

variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype H]

/--
OET anchor: h-5258752592a614bf
The actual orthogonal projections reconstruct the vector and satisfy Pythagoras.
-/
theorem orthogonal_projection_decomposition
    (V : H → Submodule ℝ E)
    (hV : OrthogonalFamily ℝ (fun a => V a) (fun a => (V a).subtypeₗᵢ))
    (hspan : iSup V = ⊤) (v : E) :
    v = ∑ a, (V a).starProjection v ∧
      ‖v‖ ^ 2 = ∑ a, ‖(V a).starProjection v‖ ^ 2 := by
  have hsum := hV.sum_projection_of_mem_iSup v (by rw [hspan]; trivial)
  refine ⟨hsum.symm, ?_⟩
  have h := hV.norm_sum (fun a => (V a).orthogonalProjection v) Finset.univ
  change ‖∑ a, (V a).starProjection v‖ ^ 2 = ∑ a, ‖(V a).starProjection v‖ ^ 2 at h
  rwa [hsum] at h

/--
OET anchor: h-5258752592a614bf
Separation of the original absorbing-point model by all actual block distances.
-/
theorem orthogonal_block_family_separates [Nonempty H]
    {A : Set E} (V : H → Submodule ℝ E)
    (hV : OrthogonalFamily ℝ (fun a => V a) (fun a => (V a).subtypeₗᵢ))
    (hspan : iSup V = ⊤) : IsSeparating (orthogonal_block_dist (A := A) V) := by
  intro x y hxy
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => simpa [orthogonal_block_dist] using hxy (Classical.arbitrary H)
  | some x =>
    cases y with
    | none => simpa [orthogonal_block_dist] using hxy (Classical.arbitrary H)
    | some y =>
      have hp (a : H) : (V a).starProjection (x.val - y.val) = 0 := by
        have h := hxy a
        simp only [orthogonal_block_dist, ENNReal.ofReal_eq_zero] at h
        exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
      have h := (orthogonal_projection_decomposition V hV hspan (x.val - y.val)).1
      simp only [hp, Finset.sum_const_zero] at h
      exact congrArg some (Subtype.ext (sub_eq_zero.mp h))

/--
OET anchor: h-5258752592a614bf
The block distances form an actual separating extended gauge family.
-/
theorem orthogonal_block_gauge [Nonempty H] {A : Set E} (hA : A.Nonempty)
    (V : H → Submodule ℝ E)
    (hV : OrthogonalFamily ℝ (fun a => V a) (fun a => (V a).subtypeₗᵢ))
    (hspan : iSup V = ⊤) :
    (∀ a, ExtendedPseudoMetric (Option A) none (orthogonal_block_dist V a)) ∧
      IsSeparating (orthogonal_block_dist (A := A) V) :=
  ⟨orthogonal_block_dist_is_extended_pseudo_metric hA V,
    orthogonal_block_family_separates V hV hspan⟩

section Coordinates
variable {n : ℕ}

/-- The same finite coordinate vector, equipped with the Euclidean norm. -/
def euclidean_coordinates : CoordinateVector n ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm

def standard_coordinate_subspace (i : Fin n) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  ℝ ∙ EuclideanSpace.single i 1

theorem standard_coordinate_projection (i : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    (standard_coordinate_subspace i).starProjection v =
      v i • EuclideanSpace.single i 1 := by
  have hi : inner ℝ (EuclideanSpace.single i 1) v = v i := by
    simpa using EuclideanSpace.inner_single_left (𝕜 := ℝ) i 1 v
  have h := Submodule.starProjection_unit_singleton ℝ
    (v := EuclideanSpace.single i (1 : ℝ)) (by simp) v
  rw [hi] at h
  exact h

theorem standard_coordinate_projection_norm (i : Fin n) (v : EuclideanSpace ℝ (Fin n)) :
    ‖(standard_coordinate_subspace i).starProjection v‖ = |v i| := by
  rw [standard_coordinate_projection]
  simp [norm_smul, Real.norm_eq_abs]

def euclidean_state_set (A : Set (CoordinateVector n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  euclidean_coordinates.symm ⁻¹' A

def euclidean_point {A : Set (CoordinateVector n)} :
    CoordinatePoint n A → Option (euclidean_state_set A)
  | none => none
  | some x => some ⟨euclidean_coordinates x.val, by simpa [euclidean_state_set] using x.property⟩

/--
OET anchor: h-5258752592a614bf
The standard one-dimensional block distance equals the original coordinate
distance, including pairs involving the absorbing point.
-/
theorem standard_block_distance_eq_coordinate {A : Set (CoordinateVector n)}
    (i : Fin n) (x y : CoordinatePoint n A) :
    orthogonal_block_dist standard_coordinate_subspace i (euclidean_point x) (euclidean_point y) =
      coordinate_dist i x y := by
  cases x with
  | none => cases y <;> rfl
  | some x =>
    cases y with
    | none => rfl
    | some y =>
      change ENNReal.ofReal ‖(standard_coordinate_subspace i).starProjection
        (euclidean_coordinates x.val - euclidean_coordinates y.val)‖ = _
      rw [standard_coordinate_projection_norm]
      rfl

end Coordinates
end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
