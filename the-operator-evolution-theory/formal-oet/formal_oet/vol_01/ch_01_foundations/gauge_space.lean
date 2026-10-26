import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_01_foundations

universe u

/--
OET anchor: h-b4babd684de7c112
**定义（扩展规范空间）**
设 `X` 为带有指定吸收元 `bot` 的集合，并要求存在非吸收点。
`X` 上的一个规范结构是一族扩展伪度量 `d_i: X × X → ENNReal` (i ∈ I)。
每个分量包含四个伪度量公理：自距零、对称、三角不等式、吸收元隔离。
-/
class ExtendedPseudoMetric (X : Type u) (bot : X) (d : X → X → ENNReal) where
  nonabsorbing : ∃ x : X, x ≠ bot
  dist_self : ∀ x : X, d x x = 0
  symm : ∀ x y : X, d x y = d y x
  triangle : ∀ x y z : X, d x z ≤ d x y + d y z
  isolate_bot : ∀ x ≠ bot, d x bot = ⊤

/-- 开球的定义：B_i(x_0, r) -/
def ball {X : Type} (d : X → X → ENNReal) (x0 : X) (r : ENNReal) : Set X :=
  { x | d x x0 < r }

/-- 规范族的全分量零距关系。 -/
def GaugeZeroRelated {X I : Type} (d : I → X → X → ENNReal) (x y : X) : Prop :=
  ∀ i : I, d i x y = 0

/-- 规范族分离，当且仅当其全分量零距关系蕴含点相等。 -/
def IsSeparating {X I : Type} (d : I → X → X → ENNReal) : Prop :=
  ∀ x y : X, GaugeZeroRelated d x y → x = y

/-- 规范族非分离，当且仅当它不分离。 -/
def IsNonSeparating {X I : Type} (d : I → X → X → ENNReal) : Prop :=
  ¬ IsSeparating d

/--
OET anchor: h-ecdfb943b4fb8922
**引理（族零距关系的等价性）**
任意伪度量族的全分量零距关系都是等价关系。
-/
theorem gauge_zero_related_equivalence {X I : Type}
    (d : I → X → X → ENNReal)
    (dist_self : ∀ i x, d i x x = 0)
    (symm : ∀ i x y, d i x y = d i y x)
    (triangle : ∀ i x y z, d i x z ≤ d i x y + d i y z) :
    Equivalence (GaugeZeroRelated d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x i
    exact dist_self i x
  · intro x y hxy i
    rw [symm i]
    exact hxy i
  · intro x y z hxy hyz i
    apply le_antisymm
    · calc
        d i x z ≤ d i x y + d i y z := triangle i x y z
        _ = 0 := by rw [hxy i, hyz i, zero_add]
    · exact zero_le _

end formal_oet.vol_01.ch_01_foundations
