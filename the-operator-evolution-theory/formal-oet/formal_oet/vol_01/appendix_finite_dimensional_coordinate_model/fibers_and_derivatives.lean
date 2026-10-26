import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_and_calculus
import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix
import Mathlib.Tactic

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

open formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

variable {I X Y : Type} [Fintype I] [Nonempty I]

/-- A coordinate level-set fiber on a restricted domain. -/
def coordinate_level_fiber (f : X → I → ℝ) (U : Set X) (j : I)
    (value : ℝ) : Set X :=
  {x | x ∈ U ∧ f x j = value}

/-- The simultaneous coordinate level-set fiber. -/
def full_coordinate_level_fiber (f : X → I → ℝ) (U : Set X)
    (value : I → ℝ) : Set X :=
  {x | x ∈ U ∧ f x = value}

/-- Exact local constancy radius for an arbitrary input distance. -/
def exact_constancy_radius (d : X → X → ENNReal) (f : X → Y)
    (U : Set X) (y : X) : ENNReal :=
  ⨆ (r : ENNReal) (_ : FinitePositiveRadius r)
    (_ : ∀ x ∈ U, d x y < r → f x = f y), r

/-- Constant output on the restricted domain gives infinite exact radius. -/
theorem exact_constancy_radius_eq_top_of_constant
    (d : X → X → ENNReal) (f : X → Y) (U : Set X) (y : X)
    (hconst : ∀ x ∈ U, f x = f y) :
    exact_constancy_radius d f U y = ⊤ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  cases n with
  | zero => simp
  | succ n =>
      let r : ENNReal := (n + 1 : ℕ)
      have hr : FinitePositiveRadius r := by
        constructor
        · dsimp [r]
          exact Nat.cast_pos.mpr (Nat.succ_pos n)
        · exact ENNReal.natCast_ne_top (n + 1)
      apply le_iSup_of_le r
      apply le_iSup_of_le hr
      exact le_iSup_of_le (fun x hx _ => hconst x hx) le_rfl

/-- Arbitrarily close nonfiber points force the exact radius to be zero. -/
theorem exact_constancy_radius_eq_zero_of_close_nonfiber
    (d : X → X → ENNReal) (f : X → Y) (U : Set X) (y : X)
    (hclose : ∀ r, FinitePositiveRadius r →
      ∃ x ∈ U, d x y < r ∧ f x ≠ f y) :
    exact_constancy_radius d f U y = 0 := by
  apply le_antisymm
  · unfold exact_constancy_radius
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply iSup_le
    intro hgood
    rcases hclose r hr with ⟨x, hx, hxr, hne⟩
    exact False.elim (hne (hgood x hx hxr))
  · exact zero_le _

/--
Auxiliary level-set definitions. The original OET fiber and radius bridge is
proved in `coordinate_fiber_bridge.lean`.
-/
theorem coordinate_fibers_are_level_sets
    (f : X → I → ℝ) (U : Set X) (y : X)
    (d : I → X → X → ENNReal) :
    (∀ j,
      coordinate_level_fiber f U j (f y j) =
        {x | x ∈ U ∧ f x j = f y j}) ∧
    full_coordinate_level_fiber f U (f y) = {x | x ∈ U ∧ f x = f y} ∧
    (∀ i j,
      exact_constancy_radius (d i) (fun x => f x j) U y =
        ⨆ (r : ENNReal) (_ : FinitePositiveRadius r)
          (_ : ∀ x ∈ U, d i x y < r → f x j = f y j), r) := by
  exact ⟨fun _ => rfl, rfl, fun _ _ => rfl⟩



end

end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
