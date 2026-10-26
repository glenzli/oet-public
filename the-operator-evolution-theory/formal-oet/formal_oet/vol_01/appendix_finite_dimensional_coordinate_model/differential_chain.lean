import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.singular_geometry
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.chain_propagation

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open scoped BigOperators
noncomputable section

section GeneralChain
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Only the function and its proposed pointwise differential are data. -/
structure DifferentialFunction (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  func : E → E
  differential : E → E →L[ℝ] E

/-- Lists are written outermost first, consistently with OET operator chains. -/
def differential_function_chain : List (DifferentialFunction E) → E → E
  | [], x => x
  | f :: fs, x => f.func (differential_function_chain fs x)

def occurrence_differentials : List (DifferentialFunction E) → E → List (E →L[ℝ] E)
  | [], _ => []
  | f :: fs, x => f.differential (differential_function_chain fs x) :: occurrence_differentials fs x

/-- The hypotheses concern individual derivatives at actual intermediate points. -/
def ChainDifferentiableAt : List (DifferentialFunction E) → E → Prop
  | [], _ => True
  | f :: fs, x => ChainDifferentiableAt fs x ∧
      HasFDerivAt f.func (f.differential (differential_function_chain fs x))
        (differential_function_chain fs x)

def continuous_linear_chain : List (E →L[ℝ] E) → E →L[ℝ] E
  | [] => ContinuousLinearMap.id ℝ E
  | T :: Ts => T.comp (continuous_linear_chain Ts)

/--
OET anchor: h-8b08064a80bd8c55
The actual derivative of the composite is the ordered product of derivatives
evaluated at actual intermediate inputs. C1 open-domain assumptions imply these
individual HasFDerivAt hypotheses; no composite derivative identity is assumed.
-/
theorem differential_chain_has_fderiv (fs : List (DifferentialFunction E)) (x : E)
    (h : ChainDifferentiableAt fs x) :
    HasFDerivAt (differential_function_chain fs)
      (continuous_linear_chain (occurrence_differentials fs x)) x := by
  induction fs with
  | nil => exact hasFDerivAt_id x
  | cons f fs ih => exact h.2.comp x (ih h.1)

end GeneralChain

section SingularChain
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [NeZero n] (hn : Module.finrank ℝ E = n)

include hn in
theorem singular_values_comp_bounds (T U : E →L[ℝ] E) :
    (T.comp U).toLinearMap.singularValues 0 ≤
        T.toLinearMap.singularValues 0 * U.toLinearMap.singularValues 0 ∧
    T.toLinearMap.singularValues (n - 1) * U.toLinearMap.singularValues (n - 1) ≤
        (T.comp U).toLinearMap.singularValues (n - 1) := by
  constructor
  · let v := singular_basis (T.comp U).toLinearMap hn ⟨0, NeZero.pos n⟩
    have hv : ‖v‖ = 1 := (singular_basis (T.comp U).toLinearMap hn).norm_eq_one _
    have ht := (singular_value_norm_bounds T.toLinearMap hn (U v)).2
    have hu := (singular_value_norm_bounds U.toLinearMap hn v).2
    have h := ht.trans (mul_le_mul_of_nonneg_left hu (T.toLinearMap.singularValues_nonneg 0))
    rw [hv, mul_one] at h
    have he : ‖T (U v)‖ = (T.comp U).toLinearMap.singularValues 0 :=
      norm_singular_basis (T.comp U).toLinearMap hn ⟨0, NeZero.pos n⟩
    exact he.symm.le.trans h
  · let i : Fin n := ⟨n - 1, by have := NeZero.pos n; omega⟩
    let v := singular_basis (T.comp U).toLinearMap hn i
    have hv : ‖v‖ = 1 := (singular_basis (T.comp U).toLinearMap hn).norm_eq_one _
    have ht := (singular_value_norm_bounds T.toLinearMap hn (U v)).1
    have hu := (singular_value_norm_bounds U.toLinearMap hn v).1
    have h := (mul_le_mul_of_nonneg_left hu
      (T.toLinearMap.singularValues_nonneg (n - 1))).trans ht
    rw [hv, mul_one] at h
    have he : ‖T (U v)‖ = (T.comp U).toLinearMap.singularValues (n - 1) :=
      norm_singular_basis (T.comp U).toLinearMap hn i
    exact h.trans he.le

include hn in
theorem singular_chain_bounds (Ts : List (E →L[ℝ] E)) :
    (continuous_linear_chain Ts).toLinearMap.singularValues 0 ≤
        (Ts.map (fun T => T.toLinearMap.singularValues 0)).prod ∧
    (Ts.map (fun T => T.toLinearMap.singularValues (n - 1))).prod ≤
        (continuous_linear_chain Ts).toLinearMap.singularValues (n - 1) := by
  induction Ts with
  | nil =>
    have hs (i : Fin n) : (ContinuousLinearMap.id ℝ E).toLinearMap.singularValues i = 1 :=
      singular_values_of_norm_scaling (ContinuousLinearMap.id ℝ E).toLinearMap hn 1
        (fun v => by simp) i
    constructor
    · exact (hs ⟨0, NeZero.pos n⟩).le
    · exact (hs ⟨n - 1, by have := NeZero.pos n; omega⟩).ge
  | cons T Ts ih =>
    have h := singular_values_comp_bounds hn T (continuous_linear_chain Ts)
    constructor
    · exact h.1.trans (mul_le_mul_of_nonneg_left ih.1 (T.toLinearMap.singularValues_nonneg 0))
    · exact (mul_le_mul_of_nonneg_left ih.2
        (T.toLinearMap.singularValues_nonneg (n - 1))).trans h.2

include hn in
/--
Library result: singular value product bounds for a differential chain,
using Mathlib's canonical singular values.
-/
theorem differential_chain_singular_bounds (fs : List (DifferentialFunction E)) (x : E)
    (h : ChainDifferentiableAt fs x) :
    (fderiv ℝ (differential_function_chain fs) x).toLinearMap.singularValues 0 ≤
        ((occurrence_differentials fs x).map (fun T => T.toLinearMap.singularValues 0)).prod ∧
    ((occurrence_differentials fs x).map (fun T => T.toLinearMap.singularValues (n - 1))).prod ≤
        (fderiv ℝ (differential_function_chain fs) x).toLinearMap.singularValues (n - 1) := by
  rw [(differential_chain_has_fderiv fs x h).fderiv]
  exact singular_chain_bounds hn _

end SingularChain

section Entries
variable {n : ℕ} [NeZero n]

def euclidean_linear_entry (T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    RealCertificate (Fin n) := fun i j => T (EuclideanSpace.single i 1) j

theorem euclidean_entry_comp (T U : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    euclidean_linear_entry (T.comp U) =
      real_certificate_mul (euclidean_linear_entry T) (euclidean_linear_entry U) := by
  funext i j
  have hsum : (∑ k : Fin n, (U (EuclideanSpace.single i 1)) k • EuclideanSpace.single k 1) =
      U (EuclideanSpace.single i 1) := by
    ext k; simp [Pi.single_apply]
  change (T (U (EuclideanSpace.single i 1))) j = _
  rw [← hsum, map_sum]
  simp [real_certificate_mul, euclidean_linear_entry, mul_comm]

theorem euclidean_entry_chain
    (Ts : List (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :
    euclidean_linear_entry (continuous_linear_chain Ts) =
      real_certificate_list_mul (Ts.map euclidean_linear_entry) := by
  induction Ts with
  | nil =>
    funext i j
    simp [continuous_linear_chain, euclidean_linear_entry, real_certificate_list_mul,
      EuclideanSpace.single, Pi.single_apply, eq_comm]
  | cons T Ts ih =>
    simp only [continuous_linear_chain, List.map_cons, real_certificate_list_mul,
      euclidean_entry_comp, ih]

theorem abs_real_certificate_list_mul_le (As : List (RealCertificate (Fin n))) (i j : Fin n) :
    |real_certificate_list_mul As i j| ≤
      real_certificate_list_mul (As.map certificate_abs) i j := by
  induction As generalizing j with
  | nil =>
    simp only [real_certificate_list_mul, List.map_nil]
    split_ifs <;> norm_num
  | cons A As ih =>
    apply (abs_real_certificate_mul_le A (real_certificate_list_mul As) i j).trans
    apply Finset.sum_le_sum
    intro k _
    exact mul_le_mul_of_nonneg_left (ih k) (abs_nonneg _)

/--
OET anchor: h-8b08064a80bd8c55
Signed entries of the actual composite derivative expand over channels. Taking
absolute values bounds them by the nonnegative matrix product, whose positive
entries can still represent cancelling signed contributions.
-/
theorem differential_chain_signed_entries
    (fs : List (DifferentialFunction (EuclideanSpace ℝ (Fin n)))) (x : EuclideanSpace ℝ (Fin n))
    (h : ChainDifferentiableAt fs x) (i j : Fin n) :
    euclidean_linear_entry (fderiv ℝ (differential_function_chain fs) x) i j =
        coordinate_channel_sum ((occurrence_differentials fs x).map euclidean_linear_entry) i j ∧
    |euclidean_linear_entry (fderiv ℝ (differential_function_chain fs) x) i j| ≤
        real_certificate_list_mul
          (((occurrence_differentials fs x).map euclidean_linear_entry).map certificate_abs) i j ∧
    real_certificate_mul cancellation_second cancellation_first 0 0 = 0 ∧
    real_certificate_mul (certificate_abs cancellation_second)
      (certificate_abs cancellation_first) 0 0 = 2 := by
  rw [(differential_chain_has_fderiv fs x h).fderiv, euclidean_entry_chain]
  exact ⟨certificate_product_coordinate_channel_expansion _ i j,
    abs_real_certificate_list_mul_le _ i j, cancellation_channel_values⟩

end Entries
end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
