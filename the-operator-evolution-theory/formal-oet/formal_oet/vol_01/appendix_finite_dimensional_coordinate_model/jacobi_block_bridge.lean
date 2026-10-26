import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_block_bridge
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_block_model
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.nonlinear_colip
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.model_realization
import Mathlib.Analysis.Calculus.MeanValue

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
open scoped BigOperators
variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype H]

/-- The genuine projected Jacobi operator from block `a` to block `b`. -/
def jacobi_block_map (V : H → Submodule ℝ E) (D : E → E →L[ℝ] E)
    (z : E) (a b : H) : E →L[ℝ] E :=
  (V b).starProjection.comp ((D z).comp (V a).starProjection)

/-- The real supremum in the text. Boundedness of the norm image is stated
explicitly when this supremum is used as an upper bound. -/
def jacobi_block_sup (V : H → Submodule ℝ E) (D : E → E →L[ℝ] E)
    (Q : Set E) (a b : H) : ℝ :=
  sSup ((fun z => ‖jacobi_block_map V D z a b‖) '' Q)

omit [Fintype H] in
theorem jacobi_block_norm_le_sup
    (V : H → Submodule ℝ E) (D : E → E →L[ℝ] E) (Q : Set E)
    (hfinite : ∀ a b, BddAbove ((fun z => ‖jacobi_block_map V D z a b‖) '' Q))
    (z : E) (hz : z ∈ Q) (a b : H) :
    ‖jacobi_block_map V D z a b‖ ≤ jacobi_block_sup V D Q a b :=
  le_csSup (hfinite a b) ⟨z, hz, rfl⟩

/-- Decompose the actual input vector into its orthogonal projections and use
operator norm bounds on each projected Jacobi operator. -/
theorem jacobi_projected_direction_bound
    (V : H → Submodule ℝ E)
    (hV : OrthogonalFamily ℝ (fun a => V a) (fun a => (V a).subtypeₗᵢ))
    (hspan : iSup V = ⊤) (D : E → E →L[ℝ] E) (Q : Set E)
    (hfinite : ∀ a b, BddAbove ((fun z => ‖jacobi_block_map V D z a b‖) '' Q))
    (z : E) (hz : z ∈ Q) (v : E) (b : H) :
    ‖(V b).starProjection (D z v)‖ ≤
      ∑ a, jacobi_block_sup V D Q a b * ‖(V a).starProjection v‖ := by
  have hsum := hV.sum_projection_of_mem_iSup v (by rw [hspan]; trivial)
  have heq : (V b).starProjection (D z v) =
      ∑ a, (V b).starProjection (D z ((V a).starProjection v)) := by
    conv_lhs => rw [← hsum]
    rw [map_sum, map_sum]
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  have hp : (V a).starProjection ((V a).starProjection v) = (V a).starProjection v :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ _)
  have h := (jacobi_block_map V D z a b).le_opNorm ((V a).starProjection v)
  simp only [jacobi_block_map, ContinuousLinearMap.comp_apply, hp] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (jacobi_block_norm_le_sup V D Q hfinite z hz a b) (norm_nonneg _))

/--
OET anchor: h-460dce986b592798
Actual vector-block Jacobi supremum estimate on a convex domain.
The standard one-dimensional specialization is proved in `jacobi_standard_blocks.lean`.
-/
theorem jacobi_block_sup_gives_lip
    (V : H → Submodule ℝ E)
    (hV : OrthogonalFamily ℝ (fun a => V a) (fun a => (V a).subtypeₗᵢ))
    (hspan : iSup V = ⊤) (F : E → E) (D : E → E →L[ℝ] E) (Q : Set E)
    (hC1 : C1DerivativeOnOpenNeighborhood F D Q) (hQ : Convex ℝ Q)
    (hfinite : ∀ a b, BddAbove ((fun z => ‖jacobi_block_map V D z a b‖) '' Q)) :
    OrthogonalBlockLipBound V (jacobi_block_sup V D Q) F Q := by
  rcases hC1 with ⟨O, hO, hQO, hcont, hderiv⟩
  intro x hx y hy b
  let g : ℝ → E := fun t => (V b).starProjection (F (AffineMap.lineMap y x t))
  let g' : ℝ → E := fun t =>
    (V b).starProjection (D (AffineMap.lineMap y x t) (x - y))
  have hg (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : HasDerivAt g (g' t) t := by
    have hf := (hderiv _ (hQ.lineMap_mem hy hx ht)).comp_hasDerivAt t
      (AffineMap.hasDerivAt_lineMap (a := y) (b := x))
    exact (V b).starProjection.hasFDerivAt.comp_hasDerivAt t hf
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ‖g' t‖ ≤ ∑ a, jacobi_block_sup V D Q a b * ‖(V a).starProjection (x - y)‖ :=
    jacobi_projected_direction_bound V hV hspan D Q hfinite _
      (hQ.lineMap_mem hy hx ⟨ht.1, ht.2.le⟩) (x - y) b
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t ht => (hg t ht).hasDerivWithinAt) hbound
  simpa [g, ← map_sub] using h

/--
OET anchor: h-460dce986b592798
The actual block Jacobi supremum is an ENNReal Lip matrix for the actual block
pseudometrics. The one-dimensional identity is proved in `jacobi_standard_blocks.lean`.
-/
theorem jacobi_block_sup_is_lip_matrix
    {A : Set E} (V : H → Submodule ℝ E)
    (hV : OrthogonalFamily ℝ (fun a => V a) (fun a => (V a).subtypeₗᵢ))
    (hspan : iSup V = ⊤) (φ : Operator (Option A) none)
    (F : E → E) (D : E → E →L[ℝ] E) (Q : Set E) (hne : Q.Nonempty)
    (S : Set (Option A)) (hreal : ModelRealizationOn φ F Q S)
    (hC1 : C1DerivativeOnOpenNeighborhood F D Q) (hQ : Convex ℝ Q)
    (hfinite : ∀ a b, BddAbove ((fun z => ‖jacobi_block_map V D z a b‖) '' Q)) :
    IsLipMatrix (orthogonal_block_dist V) φ S
      (fun a b => ENNReal.ofReal (jacobi_block_sup V D Q a b)) := by
  have hB (a b : H) : 0 ≤ jacobi_block_sup V D Q a b :=
    (norm_nonneg _).trans
      (jacobi_block_norm_le_sup V D Q hfinite hne.choose hne.choose_spec a b)
  exact orthogonal_block_bound_is_lip_matrix V _ hB φ F Q S hreal
    (jacobi_block_sup_gives_lip V hV hspan F D Q hC1 hQ hfinite)

/--
OET anchor: h-4f0e5a8aa7221640
**习题（零块证书下的分量解耦）**
Zero-block decoupling now follows from the actual C1 realization and the
finite projected Jacobi suprema, without a derivative-to-Lip certificate.
-/
theorem jacobi_zero_block_decouples
    (V : H → Submodule ℝ E)
    (hV : OrthogonalFamily ℝ (fun a => V a) (fun a => (V a).subtypeₗᵢ))
    (hspan : iSup V = ⊤) (F : E → E) (D : E → E →L[ℝ] E) (Q : Set E)
    (hC1 : C1DerivativeOnOpenNeighborhood F D Q) (hQ : Convex ℝ Q)
    (hfinite : ∀ a b, BddAbove ((fun z => ‖jacobi_block_map V D z a b‖) '' Q))
    (a b : H) (x y : E) (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x - y ∈ V a)
    (hzero : jacobi_block_sup V D Q a b = 0) :
    (V b).starProjection (F x) = (V b).starProjection (F y) :=
  zero_orthogonal_block_decouples V hV _ F Q
    (jacobi_block_sup_gives_lip V hV hspan F D Q hC1 hQ hfinite) a b x y hx hy hxy hzero

/--
OET anchor: h-4f0e5a8aa7221640
**习题（零块证书下的分量解耦）**
Vanishing off-block Jacobi suprema force the output difference to lie in the input block.
-/
theorem jacobi_zero_off_blocks_preserve_subspace
    (V : H → Submodule ℝ E)
    (hV : OrthogonalFamily ℝ (fun a => V a) (fun a => (V a).subtypeₗᵢ))
    (hspan : iSup V = ⊤) (F : E → E) (D : E → E →L[ℝ] E) (Q : Set E)
    (hC1 : C1DerivativeOnOpenNeighborhood F D Q) (hQ : Convex ℝ Q)
    (hfinite : ∀ a b, BddAbove ((fun z => ‖jacobi_block_map V D z a b‖) '' Q))
    (a : H) (x y : E) (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x - y ∈ V a)
    (hoff : ∀ b, b ≠ a → jacobi_block_sup V D Q a b = 0) : F x - F y ∈ V a :=
  zero_off_orthogonal_blocks_preserve_subspace V hV hspan _ F Q
    (jacobi_block_sup_gives_lip V hV hspan F D Q hC1 hQ hfinite) a x y hx hy hxy hoff

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
