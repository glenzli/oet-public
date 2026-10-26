import formal_oet.vol_01.ch_01_foundations.gauge_space
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.EReal.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_01_foundations

set_option linter.style.longLine false

open Set

/--
OET anchor: h-65d0745eb743dfe2
**定义（有限内覆盖）**
A finite set of centers contained in `U` whose open `ε`-balls cover `U`.
-/
def InternalEpsilonNet {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) (centers : Finset X) : Prop :=
  (↑centers : Set X) ⊆ U ∧
    ∀ x ∈ U, ∃ c ∈ centers, d x c < ε

/--
OET anchor: h-65d0745eb743dfe2
**定义（覆盖数）**
`U` 在 `d` 下的 `ε`-内覆盖数。不存在有限内覆盖时，第二个下确界
对空证明类型取值为 `⊤`；空集由空中心集给出覆盖数 `0`。
-/
noncomputable def covering_number {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) : ENNReal :=
  ⨅ (centers : Finset X) (_ : InternalEpsilonNet d ε U centers),
    (centers.card : ENNReal)

/--
OET anchor: h-65d0745eb743dfe2
存在有限内覆盖时，覆盖数由某个有限内覆盖的中心数取得，且该中心数最小。
这将下确界实现与正文的最小值定义对应起来。
-/
theorem covering_number_attained {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X)
    (hfinite : ∃ centers : Finset X, InternalEpsilonNet d ε U centers) :
    ∃ centers : Finset X, InternalEpsilonNet d ε U centers ∧
      covering_number d ε U = (centers.card : ENNReal) ∧
      ∀ other : Finset X, InternalEpsilonNet d ε U other →
        centers.card ≤ other.card := by
  classical
  have hex : ∃ n : ℕ, ∃ centers : Finset X,
      InternalEpsilonNet d ε U centers ∧ centers.card = n := by
    obtain ⟨centers, hcenters⟩ := hfinite
    exact ⟨centers.card, centers, hcenters, rfl⟩
  obtain ⟨centers, hcenters, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ other : Finset X, InternalEpsilonNet d ε U other →
      centers.card ≤ other.card := by
    intro other hother
    rw [hcard]
    exact Nat.find_min' hex ⟨other, hother, rfl⟩
  refine ⟨centers, hcenters, ?_, hmin⟩
  apply le_antisymm
  · exact iInf_le_of_le centers (iInf_le_of_le hcenters le_rfl)
  · apply le_iInf
    intro other
    apply le_iInf
    intro hother
    exact_mod_cast hmin other hother

/--
OET anchor: h-65d0745eb743dfe2
覆盖数为无穷，当且仅当不存在有限内覆盖。
-/
theorem covering_number_eq_top_iff {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) :
    covering_number d ε U = ⊤ ↔
      ¬ ∃ centers : Finset X, InternalEpsilonNet d ε U centers := by
  constructor
  · intro htop hfinite
    obtain ⟨centers, _, hcard, _⟩ := covering_number_attained d ε U hfinite
    have hne : (centers.card : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    exact hne (hcard.symm.trans htop)
  · intro hnone
    apply top_unique
    apply le_iInf
    intro centers
    apply le_iInf
    intro hcenters
    exact False.elim (hnone ⟨centers, hcenters⟩)

/-- 非空集合的内覆盖数至少为一。 -/
theorem one_le_covering_number_of_nonempty {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) (hU : U.Nonempty) :
    (1 : ENNReal) ≤ covering_number d ε U := by
  apply le_iInf
  intro centers
  apply le_iInf
  intro hcenters
  obtain ⟨x, hx⟩ := hU
  obtain ⟨c, hc, _⟩ := hcenters.2 x hx
  exact_mod_cast (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨c, hc⟩))

/-- The empty set has internal covering number zero. -/
@[simp] theorem covering_number_empty {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) :
    covering_number d ε (∅ : Set X) = 0 := by
  apply le_antisymm
  · have hnet : InternalEpsilonNet d ε (∅ : Set X) ∅ := by
      simp [InternalEpsilonNet]
    exact iInf_le_of_le ∅ (iInf_le_of_le hnet (by simp))
  · exact bot_le

/-- Finite internal covers of two sets combine to an internal cover of their
union. -/
private theorem internal_epsilon_net_union {X : Type} [DecidableEq X]
    {d : X → X → ENNReal}
    {ε : ENNReal} {A B : Set X} {centers_a centers_b : Finset X}
    (h_a : InternalEpsilonNet d ε A centers_a)
    (h_b : InternalEpsilonNet d ε B centers_b) :
    InternalEpsilonNet d ε (A ∪ B) (centers_a ∪ centers_b) := by
  classical
  constructor
  · intro c hc
    rcases Finset.mem_union.mp hc with hc_a | hc_b
    · exact Set.mem_union_left B (h_a.1 hc_a)
    · exact Set.mem_union_right A (h_b.1 hc_b)
  · intro x hx
    rcases hx with hx_a | hx_b
    · rcases h_a.2 x hx_a with ⟨c, hc, hdist⟩
      exact ⟨c, Finset.mem_union_left centers_b hc, hdist⟩
    · rcases h_b.2 x hx_b with ⟨c, hc, hdist⟩
      exact ⟨c, Finset.mem_union_right centers_a hc, hdist⟩

/-- Internal covering number is subadditive under binary unions. -/
theorem covering_number_union_le {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (A B : Set X) :
    covering_number d ε (A ∪ B) ≤
      covering_number d ε A + covering_number d ε B := by
  classical
  unfold covering_number
  apply ENNReal.le_iInf₂_add_iInf₂
  intro centers_a h_a centers_b h_b
  calc
    (⨅ (centers : Finset X)
        (_ : InternalEpsilonNet d ε (A ∪ B) centers),
        (centers.card : ENNReal)) ≤
        (((centers_a ∪ centers_b).card : Nat) : ENNReal) := by
      exact iInf_le_of_le (centers_a ∪ centers_b)
        (iInf_le_of_le (internal_epsilon_net_union h_a h_b) le_rfl)
    _ ≤ (centers_a.card : ENNReal) + (centers_b.card : ENNReal) := by
      exact_mod_cast Finset.card_union_le centers_a centers_b

/-- Internal covering number is subadditive under a union indexed by a finite
set. -/
theorem covering_number_bi_union_finset_le {X A : Type}
    (d : X → X → ENNReal) (ε : ENNReal) (pieces : A → Set X)
    (s : Finset A) :
    covering_number d ε (⋃ a ∈ s, pieces a) ≤
      ∑ a ∈ s, covering_number d ε (pieces a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hunion :
          (⋃ b ∈ (insert a s : Finset A), pieces b) =
            pieces a ∪ ⋃ b ∈ s, pieces b := by
        ext x
        simp
      rw [hunion]
      exact (covering_number_union_le d ε (pieces a) (⋃ b ∈ s, pieces b)).trans
        (add_le_add_right ih _)

/-- Internal covering number is subadditive under a finite indexed union. -/
theorem covering_number_i_union_finite_le {X A : Type} [Fintype A]
    (d : X → X → ENNReal) (ε : ENNReal) (pieces : A → Set X) :
    covering_number d ε (⋃ a : A, pieces a) ≤
      ∑ a : A, covering_number d ε (pieces a) := by
  classical
  simpa using
    covering_number_bi_union_finset_le d ε pieces (Finset.univ : Finset A)

/-- 对 ENNReal 声明对数函数（约定 log2(⊤) = ⊤, log2(0) = ⊥ 即 -∞） -/
noncomputable def log2_ereal (x : ENNReal) : EReal :=
  if x = 0 then ⊥
  else if x = ⊤ then ⊤
  else ↑(Real.logb 2 x.toReal)

/--
OET anchor: h-65d0745eb743dfe2
**定义（度量熵）**
基于覆盖数定义度量熵。
-/
noncomputable def metric_entropy {X : Type} (d : X → X → ENNReal) (ε : ENNReal) (U : Set X) : EReal :=
  log2_ereal (covering_number d ε U)

/--
OET anchor: h-65d0745eb743dfe2
非空集合的度量熵非负，允许取正无穷。
-/
theorem metric_entropy_nonneg {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) (U : Set X) (hU : U.Nonempty) :
    (0 : EReal) ≤ metric_entropy d ε U := by
  have hcover := one_le_covering_number_of_nonempty d ε U hU
  have hzero : covering_number d ε U ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hcover)
  by_cases htop : covering_number d ε U = ⊤
  · simp [metric_entropy, log2_ereal, htop]
  · simp only [metric_entropy, log2_ereal, if_neg hzero, if_neg htop]
    apply EReal.coe_le_coe_iff.mpr
    apply Real.logb_nonneg one_lt_two
    simpa using ENNReal.toReal_mono htop hcover

/-- 空集熵遵循正文约定，等于负无穷。 -/
@[simp] theorem metric_entropy_empty {X : Type} (d : X → X → ENNReal)
    (ε : ENNReal) : metric_entropy d ε (∅ : Set X) = ⊥ := by
  simp [metric_entropy, log2_ereal]

/--
OET anchor: h-65d0745eb743dfe2
**定义（子族复合伪度量）**
The composite pseudometric associated to a gauge subfamily.
-/
noncomputable def subfamily_pseudometric
    {X I : Type} (d : I → X → X → ENNReal) (J : Set I) : X → X → ENNReal :=
  fun x y => ⨆ j : {j // j ∈ J}, d j.1 x y

/--
OET anchor: h-65d0745eb743dfe2
**定义（子族复合伪度量）**
A nonempty subfamily of component extended pseudometrics again defines an
extended pseudometric by pointwise supremum.
-/
theorem subfamily_pseudometric_is_extended
    {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (J : Set I) (hJ : J.Nonempty)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    ExtendedPseudoMetric X bot (subfamily_pseudometric d J) := by
  rcases hJ with ⟨j₀, hj₀⟩
  refine
    { nonabsorbing := (hd j₀).nonabsorbing
      dist_self := ?_
      symm := ?_
      triangle := ?_
      isolate_bot := ?_ }
  · intro x
    apply le_antisymm
    · dsimp [subfamily_pseudometric]
      apply iSup_le
      intro j
      rw [(hd j.1).dist_self]
    · exact zero_le _
  · intro x y
    dsimp [subfamily_pseudometric]
    congr with j
    exact (hd j.1).symm x y
  · intro x y z
    dsimp [subfamily_pseudometric]
    apply iSup_le
    intro j
    exact ((hd j.1).triangle x y z).trans <|
      add_le_add
        (le_iSup (fun k : {k // k ∈ J} => d k.1 x y) j)
        (le_iSup (fun k : {k // k ∈ J} => d k.1 y z) j)
  · intro x hx
    apply top_unique
    have hj : d j₀ x bot ≤ subfamily_pseudometric d J x bot :=
      le_iSup (fun k : {k // k ∈ J} => d k.1 x bot) ⟨j₀, hj₀⟩
    simpa [(hd j₀).isolate_bot x hx] using hj

/-- A singleton subfamily recovers its unique component pseudometric. -/
theorem subfamily_pseudometric_singleton
    {X I : Type} (d : I → X → X → ENNReal) (i : I) :
    subfamily_pseudometric d ({i} : Set I) = d i := by
  funext x y
  apply le_antisymm
  · dsimp [subfamily_pseudometric]
    apply iSup_le
    intro j
    rw [show j.1 = i from j.2]
  · exact le_iSup_of_le ⟨i, Set.mem_singleton i⟩ le_rfl

/--
OET anchor: h-65d0745eb743dfe2
**定义（子族度量熵）**
Metric entropy associated to a gauge subfamily.
-/
noncomputable def subfamily_metric_entropy
    {X I : Type} (d : I → X → X → ENNReal) (J : Set I) (ε : ENNReal) (U : Set X) :
    EReal :=
  log2_ereal (covering_number (subfamily_pseudometric d J) ε U)

/-- 子族度量熵直接沿用对应复合伪度量的度量熵。 -/
theorem subfamily_metric_entropy_eq_metric_entropy
    {X I : Type} (d : I → X → X → ENNReal) (J : Set I) (ε : ENNReal) (U : Set X) :
    subfamily_metric_entropy d J ε U = metric_entropy (subfamily_pseudometric d J) ε U := rfl

/-- 单元素子族的度量熵等于对应的单分量度量熵。 -/
theorem subfamily_metric_entropy_singleton
    {X I : Type} (d : I → X → X → ENNReal) (i : I) (ε : ENNReal) (U : Set X) :
    subfamily_metric_entropy d ({i} : Set I) ε U = metric_entropy (d i) ε U := by
  rw [subfamily_metric_entropy_eq_metric_entropy, subfamily_pseudometric_singleton]

end formal_oet.vol_01.ch_01_foundations
