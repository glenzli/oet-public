import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.model_realization
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_block_bridge
import Mathlib.Data.ENNReal.BigOperators

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open scoped BigOperators
noncomputable section
variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual extended pseudometric of an orthogonal block, including the
absorbing point. No separation of a single block is assumed. -/
def orthogonal_block_dist {A : Set E} (V : H → Submodule ℝ E) (a : H) :
    Option A → Option A → ENNReal
  | some x, some y => ENNReal.ofReal ‖(V a).starProjection (x.val - y.val)‖
  | none, none => 0
  | _, _ => ⊤

theorem orthogonal_block_dist_is_extended_pseudo_metric
    {A : Set E} (hA : A.Nonempty) (V : H → Submodule ℝ E) (a : H) :
    ExtendedPseudoMetric (Option A) none (orthogonal_block_dist V a) := by
  refine {
    nonabsorbing := ⟨some ⟨hA.choose, hA.choose_spec⟩, by simp⟩
    dist_self := ?_
    symm := ?_
    triangle := ?_
    isolate_bot := ?_
  }
  · intro x
    cases x <;> simp [orthogonal_block_dist]
  · intro x y
    cases x <;> cases y <;> simp [orthogonal_block_dist, map_sub, norm_sub_rev]
  · intro x y z
    cases x with
    | none => cases y <;> cases z <;> simp [orthogonal_block_dist]
    | some x =>
      cases y with
      | none => cases z <;> simp [orthogonal_block_dist]
      | some y =>
        cases z with
        | none => simp [orthogonal_block_dist]
        | some z =>
          simp only [orthogonal_block_dist, map_sub]
          rw [← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (norm_sub_le_norm_sub_add_norm_sub _ _ _)
  · intro x hx
    cases x with
    | none => exact False.elim (hx rfl)
    | some x => rfl

/-- Translate an actual vector-block estimate to the original ENNReal Lip
matrix predicate on a realized input set. -/
theorem orthogonal_block_bound_is_lip_matrix [Fintype H]
    {A : Set E} (V : H → Submodule ℝ E) (B : H → H → ℝ)
    (hB : ∀ a b, 0 ≤ B a b) (φ : Operator (Option A) none)
    (F : E → E) (Q : Set E) (S : Set (Option A))
    (hreal : ModelRealizationOn φ F Q S) (hbound : OrthogonalBlockLipBound V B F Q) :
    IsLipMatrix (orthogonal_block_dist V) φ S (fun a b => ENNReal.ofReal (B a b)) := by
  refine ⟨hreal.subset_dom, ?_⟩
  intro x hx y hy b
  rcases hreal x hx with ⟨x, x', rfl, hx, hfx, hx'⟩
  rcases hreal y hy with ⟨y, y', rfl, hy, hfy, hy'⟩
  simp only [hfx, hfy, orthogonal_block_dist, hx', hy']
  apply (ENNReal.ofReal_le_ofReal (hbound x.val hx y.val hy b)).trans_eq
  rw [ENNReal.ofReal_sum_of_nonneg (by intro a _; exact mul_nonneg (hB a b) (norm_nonneg _))]
  exact Finset.sum_congr rfl (fun a _ => ENNReal.ofReal_mul (hB a b))

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
