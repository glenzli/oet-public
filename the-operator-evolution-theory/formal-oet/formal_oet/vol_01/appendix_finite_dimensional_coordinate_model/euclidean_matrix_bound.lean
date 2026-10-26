import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.finite_matrix_model
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open WithLp
open scoped BigOperators
noncomputable section
variable {n : ℕ} [NeZero n]

def euclidean_certificate_operator (L : RealCertificate (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n) (fun j i => L i j)

def coordinate_euclidean_norm (v : CoordinateVector n) : ℝ := ‖toLp 2 v‖

theorem euclidean_abs_norm_mono (u v : EuclideanSpace ℝ (Fin n))
    (h : ∀ i, |u i| ≤ |v i|) : ‖u‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg u) (norm_nonneg v)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  exact (sq_le_sq).mpr (h i)

theorem coordinate_euclidean_norm_abs (v : CoordinateVector n) :
    coordinate_euclidean_norm (fun i => |v i|) = coordinate_euclidean_norm v := by
  unfold coordinate_euclidean_norm
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp [coordinate_euclidean_norm, EuclideanSpace.real_norm_sq_eq, PiLp.toLp_apply, sq_abs]

/-- Construct the Euclidean interface from the actual matrix on Euclidean space.
The OET indexing is transposed when passed to Mathlib's output-row convention. -/
def actual_euclidean_matrix_certificate (L : RealCertificate (Fin n)) :
    EuclideanMatrixNormCertificate L where
  operator_norm := ‖euclidean_certificate_operator L‖
  euclidean_norm := coordinate_euclidean_norm
  component_bound_to_norm := by
    intro u v _ hv h
    have hmono : ‖toLp 2 v‖ ≤ ‖euclidean_certificate_operator L (toLp 2 u)‖ := by
      apply euclidean_abs_norm_mono
      intro j
      change |v j| ≤ |∑ i, L i j * u i|
      rw [abs_of_nonneg (hv j)]
      exact (h j).trans (le_abs_self _)
    exact hmono.trans ((euclidean_certificate_operator L).le_opNorm (toLp 2 u))

/--
OET anchor: h-5386499e20ce893d
All three norm branches use the original finite ENNReal Lip certificate and an
actual Euclidean matrix operator; no norm-aggregation conclusion is an input.
-/
theorem finite_lip_matrix_actual_norm_aggregation
    {A : Set (CoordinateVector n)} (φ : Operator (CoordinatePoint n A) none)
    (S : Set (CoordinatePoint n A)) (L : Fin n → Fin n → ENNReal)
    (hfinite : ∀ i j, L i j ≠ ⊤) (hL : IsLipMatrix coordinate_dist φ S L)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (x y : CoordinatePoint n A) (hx : x ∈ S) (hy : y ∈ S) :
    vector_sup_abs (coordinate_readout (φ.func x) - coordinate_readout (φ.func y)) ≤
        matrix_infinity_bound (real_realization L) *
          vector_sup_abs (coordinate_readout x - coordinate_readout y) ∧
    weighted_one_norm w (coordinate_readout (φ.func x) - coordinate_readout (φ.func y)) ≤
        weighted_one_bound (real_realization L) w *
          weighted_one_norm w (coordinate_readout x - coordinate_readout y) ∧
    coordinate_euclidean_norm (coordinate_readout (φ.func x) - coordinate_readout (φ.func y)) ≤
        ‖euclidean_certificate_operator (real_realization L)‖ *
          coordinate_euclidean_norm (coordinate_readout x - coordinate_readout y) := by
  have h := coordinate_lip_matrix_norm_aggregation (real_realization L) coordinate_readout
    (fun x => coordinate_readout (φ.func x)) S w hw (fun _ _ => ENNReal.toReal_nonneg)
    (finite_is_lip_matrix_real_bound φ S L hfinite hL)
    (actual_euclidean_matrix_certificate (real_realization L)) x y hx hy
  refine ⟨h.1, h.2.1, ?_⟩
  have he := h.2.2
  change coordinate_euclidean_norm (fun i => |(coordinate_readout (φ.func x) -
      coordinate_readout (φ.func y)) i|) ≤
    ‖euclidean_certificate_operator (real_realization L)‖ *
      coordinate_euclidean_norm (fun i => |(coordinate_readout x - coordinate_readout y) i|) at he
  simpa only [coordinate_euclidean_norm_abs] using he

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
