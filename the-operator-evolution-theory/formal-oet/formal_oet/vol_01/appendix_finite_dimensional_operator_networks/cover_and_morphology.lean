import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.piecewise_affine
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.fibers_and_derivatives
import formal_oet.vol_01.ch_05_operator_networks.prefix_thresholds

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.appendix_finite_dimensional_coordinate_model

open scoped BigOperators

noncomputable section

variable {X Y P : Type}

/-- The ordinary absolute-value distance embedded into `ENNReal`. -/
def real_abs_enn_dist (x y : ℝ) : ENNReal :=
  ENNReal.ofReal |x - y|

/--
Formalization boundary: this internally checked non-open-domain example is only
one clause of the corresponding textbook proposition and is not full coverage.
**命题（仿射局域算子的统一零化半径与阈值读出，非开域反例）**
线性部分为恒等的仿射函数限制到等值面单点后仍具有无穷精确常值半径。
-/
theorem affine_equality_slice_has_infinite_radius :
    (1 : ℝ) ≠ 0 ∧
      exact_constancy_radius real_abs_enn_dist (fun x : ℝ => x)
        ({0} : Set ℝ) 0 = ⊤ := by
  constructor
  · norm_num
  · apply exact_constancy_radius_eq_top_of_constant
    intro x hx
    simpa using hx


end

end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
