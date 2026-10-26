import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.euclidean_matrix_bound
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.euclidean_geometry

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open scoped BigOperators
noncomputable section
variable {n : ℕ} [NeZero n]

theorem vector_sup_abs_eq_norm (v : CoordinateVector n) : vector_sup_abs v = ‖v‖ := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i _
    exact norm_le_pi_norm v i
  · apply (pi_norm_le_iff_of_nonneg
      ((abs_nonneg (v 0)).trans (Finset.le_sup' (fun i => |v i|) (Finset.mem_univ 0)))).mpr
    intro i
    exact Finset.le_sup' (fun i => |v i|) (Finset.mem_univ i)

def seminorm_comparison (p : Seminorm ℝ (CoordinateVector n)) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ v, a * ‖v‖ ≤ p v) (hu : ∀ v, p v ≤ b * ‖v‖) :
    FiniteNormComparison (I := Fin n) where
  norm := p
  lower_constant := a
  upper_constant := b
  lower_positive := ha
  upper_positive := hb
  lower_bound := by simpa only [vector_sup_abs_eq_norm] using hl
  upper_bound := by simpa only [vector_sup_abs_eq_norm] using hu

theorem coordinate_norm_distance_readout {A : Set (CoordinateVector n)}
    (p : Seminorm ℝ (CoordinateVector n)) (x y : CoordinatePoint n A)
    (hx : x ≠ none) (hy : y ≠ none) :
    coordinate_norm_distance p x y = ENNReal.ofReal (p (coordinate_readout x - coordinate_readout y)) := by
  cases x <;> cases y <;> simp_all [coordinate_norm_distance, coordinate_readout]

/--
OET anchor: h-5386499e20ce893d
The arbitrary norm branch in the original extended distance model. The only
comparison assumptions are the stated positive two-sided norm constants.
-/
theorem finite_lip_matrix_actual_norm_distance
    {A : Set (CoordinateVector n)} (φ : Operator (CoordinatePoint n A) none)
    (S : Set (CoordinatePoint n A)) (L : Fin n → Fin n → ENNReal)
    (hfinite : ∀ i j, L i j ≠ ⊤) (hL : IsLipMatrix coordinate_dist φ S L)
    (p : Seminorm ℝ (CoordinateVector n)) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ v, a * ‖v‖ ≤ p v) (hu : ∀ v, p v ≤ b * ‖v‖)
    (x y : CoordinatePoint n A) (hx : x ∈ S) (hy : y ∈ S) :
    coordinate_norm_distance p (φ.func x) (φ.func y) ≤
      ENNReal.ofReal ((b / a) * matrix_infinity_bound (real_realization L)) *
        coordinate_norm_distance p x y := by
  have h := coordinate_lip_arbitrary_norm_aggregation (real_realization L) coordinate_readout
    (fun x => coordinate_readout (φ.func x)) S (fun _ _ => ENNReal.toReal_nonneg)
    (finite_is_lip_matrix_real_bound φ S L hfinite hL)
    (seminorm_comparison p a b ha hb hl hu) x y hx hy
  rw [coordinate_norm_distance_readout p _ _ (hL.1 hx) (hL.1 hy),
    coordinate_norm_distance_readout p _ _ (domain_point_ne_bot φ x (hL.1 hx))
      (domain_point_ne_bot φ y (hL.1 hy)), ← ENNReal.ofReal_mul' (apply_nonneg p _)]
  exact ENNReal.ofReal_le_ofReal h

theorem coordinate_readout_injective_on_domain {A : Set (CoordinateVector n)}
    (φ : Operator (CoordinatePoint n A) none) (S : Set (CoordinatePoint n A))
    (hS : S ⊆ dom φ) : Function.Injective (fun x : S => coordinate_readout x.val) := by
  intro x y h
  apply Subtype.ext
  have hx := domain_point_ne_bot φ x.val (hS x.property)
  have hy := domain_point_ne_bot φ y.val (hS y.property)
  rcases x with ⟨x, hxs⟩
  rcases y with ⟨y, hys⟩
  cases x <;> cases y <;> simp_all [coordinate_readout, Subtype.ext_iff]

/--
OET anchor: h-69edb7c1cac5d49b
The norm lower bound and injectivity are proved on the actual OET domain.
Readout injectivity is used only there, after excluding the absorbing point.
-/
theorem finite_colip_matrix_actual_norm_distance
    {A : Set (CoordinateVector n)} (φ : Operator (CoordinatePoint n A) none)
    (S : Set (CoordinatePoint n A)) (K : Fin n → Fin n → ENNReal)
    (hfinite : ∀ i j, K i j ≠ ⊤) (hK : IsCoLipMatrix coordinate_dist φ S K)
    (p : Seminorm ℝ (CoordinateVector n)) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hl : ∀ v, a * ‖v‖ ≤ p v) (hu : ∀ v, p v ≤ b * ‖v‖) :
    (∀ x ∈ S, ∀ y ∈ S,
      ENNReal.ofReal ((a / b) * coordinate_colip_modulus (real_realization K)) *
          coordinate_norm_distance p x y ≤ coordinate_norm_distance p (φ.func x) (φ.func y)) ∧
    (0 < coordinate_colip_modulus (real_realization K) → Set.InjOn φ.func S) := by
  have hreal := finite_is_colip_matrix_real_bound φ S K hfinite hK
  have h := coordinate_colip_arbitrary_norm_and_injective (real_realization K)
    (fun x : S => coordinate_readout x.val) (fun x : S => coordinate_readout (φ.func x.val))
    Set.univ (fun _ _ => ENNReal.toReal_nonneg)
    (fun x _ y _ j => hreal x.val x.property y.val y.property j)
    (seminorm_comparison p a b ha hb hl hu)
    (coordinate_readout_injective_on_domain φ S hK.2.1)
  constructor
  · intro x hx y hy
    rw [coordinate_norm_distance_readout p _ _ (hK.2.1 hx) (hK.2.1 hy),
      coordinate_norm_distance_readout p _ _ (domain_point_ne_bot φ x (hK.2.1 hx))
        (domain_point_ne_bot φ y (hK.2.1 hy)), ← ENNReal.ofReal_mul' (apply_nonneg p _)]
    exact ENNReal.ofReal_le_ofReal (h.1 ⟨x, hx⟩ (Set.mem_univ _) ⟨y, hy⟩ (Set.mem_univ _))
  · intro hpos x hx y hy heq
    have he := h.2 hpos (Set.mem_univ ⟨x, hx⟩) (Set.mem_univ ⟨y, hy⟩)
      (congrArg coordinate_readout heq)
    exact congrArg Subtype.val he

def weighted_coordinate_seminorm (w : Fin n → ℝ) : Seminorm ℝ (CoordinateVector n) :=
  ∑ i, (normSeminorm ℝ ℝ).comp (w i • (LinearMap.proj i))

theorem weighted_coordinate_seminorm_eq (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (v : CoordinateVector n) : weighted_coordinate_seminorm w v = weighted_one_norm w v := by
  change (Seminorm.coeFnAddMonoidHom ℝ (CoordinateVector n)
    (∑ i, (normSeminorm ℝ ℝ).comp (w i • LinearMap.proj i))) v = _
  rw [map_sum, Finset.sum_apply]
  simp [weighted_one_norm, Seminorm.comp_apply, abs_mul, abs_of_pos (hw _)]

/--
OET anchor: h-5386499e20ce893d
The weighted-one and Euclidean bounds as inequalities of the actual extended
distances, including the finite real constant's embedding into ENNReal.
-/
theorem finite_lip_matrix_weighted_and_euclidean_distance
    {A : Set (CoordinateVector n)} (φ : Operator (CoordinatePoint n A) none)
    (S : Set (CoordinatePoint n A)) (L : Fin n → Fin n → ENNReal)
    (hfinite : ∀ i j, L i j ≠ ⊤) (hL : IsLipMatrix coordinate_dist φ S L)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (x y : CoordinatePoint n A) (hx : x ∈ S) (hy : y ∈ S) :
    coordinate_norm_distance (weighted_coordinate_seminorm w) (φ.func x) (φ.func y) ≤
        ENNReal.ofReal (weighted_one_bound (real_realization L) w) *
          coordinate_norm_distance (weighted_coordinate_seminorm w) x y ∧
    euclidean_distance (φ.func x) (φ.func y) ≤
        ENNReal.ofReal ‖euclidean_certificate_operator (real_realization L)‖ *
          euclidean_distance x y := by
  have h := finite_lip_matrix_actual_norm_aggregation φ S L hfinite hL w hw x y hx hy
  constructor
  · rw [coordinate_norm_distance_readout _ _ _ (hL.1 hx) (hL.1 hy),
      coordinate_norm_distance_readout _ _ _ (domain_point_ne_bot φ x (hL.1 hx))
        (domain_point_ne_bot φ y (hL.1 hy)),
      ← ENNReal.ofReal_mul' (apply_nonneg (weighted_coordinate_seminorm w) _)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [weighted_coordinate_seminorm_eq w hw] using h.2.1
  · unfold euclidean_distance
    rw [coordinate_norm_distance_readout _ _ _ (hL.1 hx) (hL.1 hy),
      coordinate_norm_distance_readout _ _ _ (domain_point_ne_bot φ x (hL.1 hx))
        (domain_point_ne_bot φ y (hL.1 hy)),
      ← ENNReal.ofReal_mul' (apply_nonneg euclidean_seminorm _)]
    exact ENNReal.ofReal_le_ofReal h.2.2

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
