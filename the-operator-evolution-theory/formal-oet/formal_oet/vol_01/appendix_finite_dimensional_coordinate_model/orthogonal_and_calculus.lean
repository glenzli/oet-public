import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.real_matrix_bounds
import Mathlib.Tactic

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model

noncomputable section

open scoped BigOperators

/--
**推论（零块证书下的分量解耦）**
单一输入块上的差异经零证书块不会到达相应输出块。
-/
theorem zero_block_certificate_decouples
    {H X : Type} [Fintype H]
    (B : RealCertificate H) (source target : X → H → ℝ) (Q : Set X)
    (hB_nonneg : ∀ a b, 0 ≤ B a b)
    (hB : CoordinateMapLipBound B source target Q)
    (a b : H) (x y : X) (hx : x ∈ Q) (hy : y ∈ Q)
    (hsource : ∀ c, c ≠ a → source x c = source y c)
    (hzero : B a b = 0) :
    target x b = target y b := by
  have _ := hB_nonneg
  have hbound := hB x hx y hy b
  have hsum : (∑ c : H, B c b * |source x c - source y c|) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_cases hca : c = a
    · subst c
      simp [hzero]
    · simp [hsource c hca]
  rw [hsum] at hbound
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _)))

/--
**推论（零块证书下的分量解耦，全部外块）**
-/
theorem zero_off_diagonal_blocks_preserve_source_block
    {H X : Type} [Fintype H]
    (B : RealCertificate H) (source target : X → H → ℝ) (Q : Set X)
    (hB_nonneg : ∀ a b, 0 ≤ B a b)
    (hB : CoordinateMapLipBound B source target Q)
    (a : H) (x y : X) (hx : x ∈ Q) (hy : y ∈ Q)
    (hsource : ∀ c, c ≠ a → source x c = source y c)
    (hoff : ∀ b, b ≠ a → B a b = 0) :
    ∀ b, b ≠ a → target x b = target y b := by
  intro b hba
  exact zero_block_certificate_decouples B source target Q hB_nonneg hB
    a b x y hx hy hsource (hoff b hba)

/-- Ratios of output and input distances over distinct pairs. -/
def pair_distance_ratio_set {X : Type} (distance : X → X → ℝ)
    (F : X → X) : Set ℝ :=
  {ratio | ∃ x y, x ≠ y ∧ 0 < distance x y ∧
    ratio = distance (F x) (F y) / distance x y}


end

end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
