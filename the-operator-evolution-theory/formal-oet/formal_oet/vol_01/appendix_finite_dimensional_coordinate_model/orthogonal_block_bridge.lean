import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_and_calculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model

noncomputable section
open scoped BigOperators

variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype H]

/-- A block Lip bound uses norms of vector differences, not differences of norms. -/
def OrthogonalBlockLipBound (V : H → Submodule ℝ E) (B : H → H → ℝ)
    (F : E → E) (Q : Set E) : Prop :=
  ∀ x ∈ Q, ∀ y ∈ Q, ∀ b,
    ‖(V b).starProjection (F x - F y)‖ ≤
      ∑ a, B a b * ‖(V a).starProjection (x - y)‖

/--
OET anchor: h-4f0e5a8aa7221640
**习题（零块证书下的分量解耦）**
零块证书下的向量块解耦。正交性直接使其余输入块投影为零。
This proves the vector-block step from an actual block Lip inequality.
`jacobi_block_bridge` supplies that inequality from the actual projected derivative.
-/
theorem zero_orthogonal_block_decouples
    (V : H → Submodule ℝ E)
    (hV : OrthogonalFamily ℝ (fun a => V a) (fun a => (V a).subtypeₗᵢ))
    (B : H → H → ℝ) (F : E → E) (Q : Set E)
    (hB : OrthogonalBlockLipBound V B F Q)
    (a b : H) (x y : E) (hx : x ∈ Q) (hy : y ∈ Q)
    (hxy : x - y ∈ V a) (hzero : B a b = 0) :
    (V b).starProjection (F x) = (V b).starProjection (F y) := by
  classical
  have hsum : (∑ c, B c b * ‖(V c).starProjection (x - y)‖) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_cases hca : c = a
    · simp [hca, hzero]
    · have hp : (V c).starProjection (x - y) = 0 := by
        rw [Submodule.starProjection_apply,
          Submodule.orthogonalProjection_mem_subspace_orthogonalComplement_eq_zero,
          Submodule.coe_zero]
        exact hV.isOrtho (Ne.symm hca) hxy
      simp [hp]
  have hnorm := hB x hx y hy b
  rw [hsum] at hnorm
  have hp : (V b).starProjection (F x - F y) = 0 :=
    norm_eq_zero.mp (le_antisymm hnorm (norm_nonneg _))
  simpa only [map_sub, sub_eq_zero] using hp

/--
OET anchor: h-4f0e5a8aa7221640
**习题（零块证书下的分量解耦）**
正交直和分解下，全部外块为零使输出差属于原输入块；
投影求和恒等式由正交族及其张成全空间推导。
-/
theorem zero_off_orthogonal_blocks_preserve_subspace
    (V : H → Submodule ℝ E)
    (hV : OrthogonalFamily ℝ (fun a => V a) (fun a => (V a).subtypeₗᵢ))
    (hspan : iSup V = ⊤) (B : H → H → ℝ) (F : E → E) (Q : Set E)
    (hB : OrthogonalBlockLipBound V B F Q)
    (a : H) (x y : E) (hx : x ∈ Q) (hy : y ∈ Q)
    (hxy : x - y ∈ V a) (hoff : ∀ b, b ≠ a → B a b = 0) :
    F x - F y ∈ V a := by
  classical
  have hproj (b : H) (hba : b ≠ a) : (V b).starProjection (F x - F y) = 0 := by
    rw [map_sub, zero_orthogonal_block_decouples V hV B F Q hB a b x y hx hy hxy
      (hoff b hba), sub_self]
  have hsum := hV.sum_projection_of_mem_iSup (F x - F y) (by rw [hspan]; trivial)
  have hsingle : (∑ b, (V b).starProjection (F x - F y)) =
      (V a).starProjection (F x - F y) := by
    apply Finset.sum_eq_single a
    · intro b _ hba
      exact hproj b hba
    · simp
  rw [hsingle] at hsum
  rw [← hsum]
  exact Submodule.starProjection_apply_mem _ _

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
