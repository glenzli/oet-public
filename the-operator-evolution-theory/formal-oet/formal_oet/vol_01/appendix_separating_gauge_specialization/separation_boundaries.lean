import formal_oet.vol_01.ch_01_foundations.gauge_space
import Mathlib.Tactic

namespace formal_oet.vol_01.appendix_separating_gauge_specialization

open formal_oet.vol_01.ch_01_foundations

/-- The three-point carrier of the separating-family counterexample. -/
inductive SeparationThreePoint where
  | bottom | a | b
deriving DecidableEq, Fintype

/-- The two gauge labels of the separating-family counterexample. -/
inductive SeparationGauge where
  | i | k
deriving DecidableEq, Fintype

/--
The first component identifies `a` and `b`; the second puts them at distance one.
Both components isolate `bottom` at infinite distance.
-/
def separation_three_point_distance :
    SeparationGauge → SeparationThreePoint → SeparationThreePoint → ENNReal
  | .i, .bottom, .bottom => 0
  | .i, .bottom, .a => ⊤
  | .i, .bottom, .b => ⊤
  | .i, .a, .bottom => ⊤
  | .i, .a, .a => 0
  | .i, .a, .b => 0
  | .i, .b, .bottom => ⊤
  | .i, .b, .a => 0
  | .i, .b, .b => 0
  | .k, .bottom, .bottom => 0
  | .k, .bottom, .a => ⊤
  | .k, .bottom, .b => ⊤
  | .k, .a, .bottom => ⊤
  | .k, .a, .a => 0
  | .k, .a, .b => 1
  | .k, .b, .bottom => ⊤
  | .k, .b, .a => 1
  | .k, .b, .b => 0

/-- Each component of the explicit three-point model is an extended pseudometric. -/
theorem separation_three_point_distance_is_extended (g : SeparationGauge) :
    ExtendedPseudoMetric SeparationThreePoint SeparationThreePoint.bottom
      (separation_three_point_distance g) := by
  refine
    { nonabsorbing := ⟨.a, by decide⟩
      dist_self := ?_
      symm := ?_
      triangle := ?_
      isolate_bot := ?_ }
  · intro x
    cases g <;> cases x <;> rfl
  · intro x y
    cases g <;> cases x <;> cases y <;> rfl
  · intro x y z
    cases g <;> cases x <;> cases y <;> cases z <;>
      simp [separation_three_point_distance]
  · intro x hx
    cases g <;> cases x <;> simp_all [separation_three_point_distance]

/--
OET anchor: h-716837664ceee36d
**注（族分离不蕴含单分量分离）**
一个显式有限扩展规范空间，其中规范族分离，但第一分量不分离两个非吸收点。
-/
theorem family_separating_component_nonseparating_counterexample :
    (∀ g, ExtendedPseudoMetric SeparationThreePoint SeparationThreePoint.bottom
      (separation_three_point_distance g)) ∧
    IsSeparating separation_three_point_distance ∧
      SeparationThreePoint.a ≠ SeparationThreePoint.b ∧
      separation_three_point_distance SeparationGauge.i
        SeparationThreePoint.a SeparationThreePoint.b = 0 ∧
      separation_three_point_distance SeparationGauge.k
        SeparationThreePoint.a SeparationThreePoint.b = 1 := by
  constructor
  · exact separation_three_point_distance_is_extended
  constructor
  · intro x y hzero
    have hk := hzero SeparationGauge.k
    cases x <;> cases y <;> simp [separation_three_point_distance] at hk ⊢
  · constructor
    · decide
    · exact ⟨rfl, rfl⟩

end formal_oet.vol_01.appendix_separating_gauge_specialization
