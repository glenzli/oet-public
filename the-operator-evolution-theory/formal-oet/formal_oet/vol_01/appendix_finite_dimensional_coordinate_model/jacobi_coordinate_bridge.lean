import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.nonlinear_colip
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.model_realization
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.ENNReal.BigOperators

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open scoped BigOperators
noncomputable section
variable {n : ℕ} [NeZero n]

/-- The derivative entry in the original input-to-output convention. -/
def jacobi_entry (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (z : CoordinateVector n) (i j : Fin n) : ℝ := D z (Pi.single i 1) j

def jacobi_entry_sup (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (Q : Set (CoordinateVector n)) (i j : Fin n) : ℝ :=
  sSup ((fun z => |jacobi_entry D z i j|) '' Q)

omit [NeZero n] in
theorem jacobi_entry_le_sup
    (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (Q : Set (CoordinateVector n))
    (hfinite : ∀ i j, BddAbove ((fun z => |jacobi_entry D z i j|) '' Q))
    (z : CoordinateVector n) (hz : z ∈ Q) (i j : Fin n) :
    |jacobi_entry D z i j| ≤ jacobi_entry_sup D Q i j :=
  le_csSup (hfinite i j) ⟨z, hz, rfl⟩

omit [NeZero n] in
theorem jacobi_coordinate_direction_bound
    (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (Q : Set (CoordinateVector n))
    (hfinite : ∀ i j, BddAbove ((fun z => |jacobi_entry D z i j|) '' Q))
    (z : CoordinateVector n) (hz : z ∈ Q) (v : CoordinateVector n) (j : Fin n) :
    |D z v j| ≤ ∑ i, jacobi_entry_sup D Q i j * |v i| := by
  have hsum : (∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : CoordinateVector n)) = v := by
    ext k
    simp [Pi.single_apply]
  have heq : D z v j = ∑ i, jacobi_entry D z i j * v i := by
    conv_lhs => rw [← hsum]
    simp [jacobi_entry, map_sum, map_smul, Finset.sum_apply, mul_comm]
  rw [heq]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (jacobi_entry_le_sup D Q hfinite z hz i j) (abs_nonneg _)

theorem jacobi_coordinate_sup_gives_bound
    (F : CoordinateVector n → CoordinateVector n)
    (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (Q : Set (CoordinateVector n)) (hC1 : C1DerivativeOnOpenNeighborhood F D Q)
    (hQ : Convex ℝ Q)
    (hfinite : ∀ i j, BddAbove ((fun z => |jacobi_entry D z i j|) '' Q)) :
    CoordinateMapLipBound (jacobi_entry_sup D Q) id F Q := by
  rcases hC1 with ⟨O, hO, hQO, hcont, hderiv⟩
  intro x hx y hy j
  let g : ℝ → ℝ := fun t => F (AffineMap.lineMap y x t) j
  let g' : ℝ → ℝ := fun t => D (AffineMap.lineMap y x t) (x - y) j
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt g (g' t) t := by
    have hf := (hderiv _ (hQ.lineMap_mem hy hx ht)).comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := y) (b := x))
    exact (ContinuousLinearMap.proj j).hasFDerivAt.comp_hasDerivAt t hf
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ‖g' t‖ ≤ ∑ i, jacobi_entry_sup D Q i j * |x i - y i| := by
    exact jacobi_coordinate_direction_bound D Q hfinite _
      (hQ.lineMap_mem hy hx ⟨ht.1, ht.2.le⟩) (x - y) j
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hg t ht).hasDerivWithinAt) hbound
  simpa [g, Real.norm_eq_abs] using h

/-- The subset of the original absorbing-point model represented by `Q`. -/
def coordinate_model_set (A Q : Set (CoordinateVector n)) : Set (CoordinatePoint n A) :=
  {x | ∃ a : A, a.val ∈ Q ∧ x = some a}

/-- The textbook operator: `F` on `Q`, absorbing outside `Q`. -/
def coordinate_model_operator (A Q : Set (CoordinateVector n))
    (F : CoordinateVector n → CoordinateVector n) (hF : Set.MapsTo F Q A) :
    Operator (CoordinatePoint n A) none := by
  classical
  exact {
    func := fun x => match x with
      | none => none
      | some a => if ha : a.val ∈ Q then some ⟨F a.val, hF ha⟩ else none
    preserves_bot := rfl
  }

omit [NeZero n] in
theorem coordinate_model_operator_dom (A Q : Set (CoordinateVector n))
    (F : CoordinateVector n → CoordinateVector n) (hF : Set.MapsTo F Q A) :
    dom (coordinate_model_operator A Q F hF) = coordinate_model_set A Q := by
  classical
  ext x
  cases x with
  | none => simp [dom, coordinate_model_operator, coordinate_model_set]
  | some a =>
    by_cases ha : a.val ∈ Q <;>
      simp [dom, coordinate_model_operator, coordinate_model_set, ha]

/--
OET anchor: h-454cb30cfc37f08c
The actual coordinate operator has the finite Jacobi-supremum Lip matrix.
The derivative estimate and the ENNReal coordinate-model identification are both proved.
-/
theorem jacobi_coordinate_sup_is_lip_matrix
    (A Q : Set (CoordinateVector n)) (_hQA : Q ⊆ A) (hne : Q.Nonempty)
    (F : CoordinateVector n → CoordinateVector n) (hF : Set.MapsTo F Q A)
    (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (hC1 : C1DerivativeOnOpenNeighborhood F D Q) (hQ : Convex ℝ Q)
    (hfinite : ∀ i j, BddAbove ((fun z => |jacobi_entry D z i j|) '' Q)) :
    IsLipMatrix coordinate_dist (coordinate_model_operator A Q F hF)
      (coordinate_model_set A Q) (fun i j => ENNReal.ofReal (jacobi_entry_sup D Q i j)) := by
  classical
  have hM (i j : Fin n) : 0 ≤ jacobi_entry_sup D Q i j :=
    (abs_nonneg _).trans (jacobi_entry_le_sup D Q hfinite hne.choose hne.choose_spec i j)
  refine ⟨(coordinate_model_operator_dom A Q F hF).symm.subset, ?_⟩
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ j
  simp only [coordinate_model_operator, dif_pos ha, dif_pos hb, coordinate_dist]
  have hreal := jacobi_coordinate_sup_gives_bound F D Q hC1 hQ hfinite a.val ha b.val hb j
  apply (ENNReal.ofReal_le_ofReal hreal).trans_eq
  rw [ENNReal.ofReal_sum_of_nonneg (by intro i _; exact mul_nonneg (hM i j) (abs_nonneg _))]
  apply Finset.sum_congr rfl
  intro i _
  exact ENNReal.ofReal_mul (hM i j)

/-- OET anchor: h-454cb30cfc37f08c
The derivative estimate also applies to an existing operator on its actual
input set. In particular, no `F(Q) ⊆ A` condition is imposed on a convex cover
of a node occurrence domain. -/
theorem jacobi_coordinate_sup_on_realized_set
    {A : Set (CoordinateVector n)} (φ : Operator (CoordinatePoint n A) none)
    (S : Set (CoordinatePoint n A)) (Q : Set (CoordinateVector n)) (hne : Q.Nonempty)
    (F : CoordinateVector n → CoordinateVector n)
    (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (hreal : ModelRealizationOn φ F Q S)
    (hC1 : C1DerivativeOnOpenNeighborhood F D Q) (hQ : Convex ℝ Q)
    (hfinite : ∀ i j, BddAbove ((fun z => |jacobi_entry D z i j|) '' Q)) :
    IsLipMatrix coordinate_dist φ S
      (fun i j => ENNReal.ofReal (jacobi_entry_sup D Q i j)) := by
  have hM (i j : Fin n) : 0 ≤ jacobi_entry_sup D Q i j :=
    (abs_nonneg _).trans (jacobi_entry_le_sup D Q hfinite hne.choose hne.choose_spec i j)
  refine ⟨hreal.subset_dom, ?_⟩
  intro x hx y hy j
  rcases hreal x hx with ⟨a, a', rfl, ha, hfa, ha'⟩
  rcases hreal y hy with ⟨b, b', rfl, hb, hfb, hb'⟩
  simp only [hfa, hfb, coordinate_dist, ha', hb']
  have h := jacobi_coordinate_sup_gives_bound F D Q hC1 hQ hfinite a.val ha b.val hb j
  apply (ENNReal.ofReal_le_ofReal h).trans_eq
  rw [ENNReal.ofReal_sum_of_nonneg (by intro i _; exact mul_nonneg (hM i j) (abs_nonneg _))]
  exact Finset.sum_congr rfl (fun i _ => ENNReal.ofReal_mul (hM i j))

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
