import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.coordinate_fiber_bridge
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.real_matrix_bounds

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open scoped BigOperators
noncomputable section
variable {n : ℕ} [NeZero n] {A : Set (CoordinateVector n)}

theorem coordinate_distance_readout (i : Fin n) (x y : CoordinatePoint n A)
    (hx : x ≠ none) (hy : y ≠ none) :
    coordinate_dist i x y = ENNReal.ofReal |coordinate_readout x i - coordinate_readout y i| := by
  cases x <;> cases y <;> simp_all [coordinate_dist, coordinate_readout]

theorem finite_certificate_sum (L : Fin n → Fin n → ENNReal)
    (hL : ∀ i j, L i j ≠ ⊤) (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (j : Fin n) :
    (∑ i, L i j * ENNReal.ofReal (u i)) =
      ENNReal.ofReal (∑ i, real_realization L i j * u i) := by
  unfold real_realization
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg ENNReal.toReal_nonneg (hu i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  simp only [real_realization, ENNReal.ofReal_toReal (hL i j)]

theorem domain_point_ne_bot (φ : Operator (CoordinatePoint n A) none)
    (x : CoordinatePoint n A) (hx : x ∈ dom φ) : x ≠ none := by
  intro h
  subst x
  exact hx φ.preserves_bot

/--
OET anchor: h-5386499e20ce893d
The actual finite ENNReal Lip matrix gives the real coordinate inequality.
Nonabsorbing inputs and outputs follow from its original domain premise.
-/
theorem finite_is_lip_matrix_real_bound
    (φ : Operator (CoordinatePoint n A) none) (S : Set (CoordinatePoint n A))
    (L : Fin n → Fin n → ENNReal) (hfinite : ∀ i j, L i j ≠ ⊤)
    (hL : IsLipMatrix coordinate_dist φ S L) :
    CoordinateMapLipBound (real_realization L) coordinate_readout
      (fun x => coordinate_readout (φ.func x)) S := by
  intro x hx y hy j
  have h := hL.2 x hx y hy j
  rw [coordinate_distance_readout j _ _ (hL.1 hx) (hL.1 hy)] at h
  simp_rw [coordinate_distance_readout _ x y (domain_point_ne_bot φ x (hL.1 hx))
    (domain_point_ne_bot φ y (hL.1 hy))] at h
  rw [finite_certificate_sum L hfinite _ (fun i => abs_nonneg _) j] at h
  exact (ENNReal.ofReal_le_ofReal_iff
    (Finset.sum_nonneg (fun i _ => mul_nonneg ENNReal.toReal_nonneg (abs_nonneg _)))).mp h

/--
OET anchor: h-69edb7c1cac5d49b
The actual finite ENNReal co-Lip matrix gives the real coordinate lower inequality.
-/
theorem finite_is_colip_matrix_real_bound
    (φ : Operator (CoordinatePoint n A) none) (S : Set (CoordinatePoint n A))
    (K : Fin n → Fin n → ENNReal) (hfinite : ∀ i j, K i j ≠ ⊤)
    (hK : IsCoLipMatrix coordinate_dist φ S K) :
    CoordinateCoLipBound (real_realization K) coordinate_readout
      (fun x => coordinate_readout (φ.func x)) S := by
  intro x hx y hy j
  have h := hK.2.2 x hx y hy j
  rw [coordinate_distance_readout j _ _ (hK.2.1 hx) (hK.2.1 hy)] at h
  simp_rw [coordinate_distance_readout _ x y (domain_point_ne_bot φ x (hK.2.1 hx))
    (domain_point_ne_bot φ y (hK.2.1 hy))] at h
  rw [finite_certificate_sum K hfinite _ (fun i => abs_nonneg _) j] at h
  exact (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp h

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
