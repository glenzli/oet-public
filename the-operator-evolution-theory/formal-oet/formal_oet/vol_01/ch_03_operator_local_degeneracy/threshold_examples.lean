import formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_classification
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_examples

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

/-- The real line with its absorbing point, used in
`vol-01-gauge-spaces-and-operators/03-operator-local-degeneracy.md`,
习题（输入域改变下的阈值分类）. -/
abbrev RealPoint := Option ℝ

def real_distance : RealPoint → RealPoint → ENNReal
  | some x, some y => ENNReal.ofReal |x - y|
  | none, none => 0
  | _, _ => ⊤

def gauges (_ : Unit) := real_distance

theorem real_distance_is_extended :
    ExtendedPseudoMetric RealPoint none real_distance := by
  refine
    { nonabsorbing := ⟨some 0, by simp⟩
      dist_self := ?_
      symm := ?_
      triangle := ?_
      isolate_bot := ?_ }
  · intro x
    cases x <;> simp [real_distance]
  · intro x y
    cases x <;> cases y <;> simp [real_distance, abs_sub_comm]
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp only [real_distance]
    all_goals try simp
    rename_i x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le x y z)
  · intro x hx
    cases x with
    | none => exact (hx rfl).elim
    | some x => rfl

/-- The same operator is used on all four domains; the absorbing point is fixed. -/
def floor_operator : Operator RealPoint none :=
  ⟨Option.map (fun x : ℝ => (⌊x⌋ : ℝ)), rfl⟩

def lifted_domain (D : Set ℝ) : Set RealPoint := some '' D

theorem lifted_domain_valid (D : Set ℝ) : lifted_domain D ⊆ dom floor_operator := by
  rintro _ ⟨x, hx, rfl⟩
  simp [dom, floor_operator]

/-- Diameter computed on the actual lifted domain, using the ordinary distance. -/
def input_diameter (D : Set ℝ) : ENNReal :=
  ⨆ x ∈ lifted_domain D, ⨆ y ∈ lifted_domain D, real_distance x y

/-- The existing CH3 uniform zeroing-radius definition, with a singleton gauge. -/
def uniform_radius (D : Set ℝ) : ENNReal :=
  min_annihilation_radius gauges floor_operator () (singleton_nonempty_finset ())
    (lifted_domain D)

/-- The general operator two-bit readout with both thresholds equal to one. -/
def threshold_bits (D : Set ℝ) : ThresholdBits :=
  operator_threshold_readout gauges floor_operator (lifted_domain D)
    (diameter_scale_family gauges) 1 1 () ()

/-- The exercise uses the general readout with its actual diameter scale. -/
theorem threshold_bits_eq_components (D : Set ℝ) :
    threshold_bits D =
      (decide (input_diameter D < 1), decide (1 ≤ uniform_radius D)) := rfl

theorem input_diameter_Icc (a b : ℝ) (hab : a ≤ b) :
    input_diameter (Set.Icc a b) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · apply iSup_le
    rintro _
    apply iSup_le
    rintro ⟨x, hx, rfl⟩
    apply iSup_le
    rintro _
    apply iSup_le
    rintro ⟨y, hy, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    exact abs_le.mpr ⟨by linarith [hx.1, hx.2, hy.1, hy.2],
      by linarith [hx.1, hx.2, hy.1, hy.2]⟩
  · have ha : some a ∈ lifted_domain (Set.Icc a b) := ⟨a, ⟨le_rfl, hab⟩, rfl⟩
    have hb : some b ∈ lifted_domain (Set.Icc a b) := ⟨b, ⟨hab, le_rfl⟩, rfl⟩
    apply le_iSup_of_le (some b)
    apply le_iSup_of_le hb
    apply le_iSup_of_le (some a)
    apply le_iSup_of_le ha
    simp [real_distance, abs_of_nonneg (sub_nonneg.mpr hab)]

theorem input_diameter_pair : input_diameter ({0, 2} : Set ℝ) = 2 := by
  apply le_antisymm
  · apply iSup_le
    rintro _
    apply iSup_le
    rintro ⟨x, hx, rfl⟩
    apply iSup_le
    rintro _
    apply iSup_le
    rintro ⟨y, hy, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [real_distance]
  · apply le_iSup_of_le (some 0)
    apply le_iSup_of_le (show some 0 ∈ lifted_domain ({0, 2} : Set ℝ) from
      ⟨0, by simp, rfl⟩)
    apply le_iSup_of_le (some 2)
    apply le_iSup_of_le (show some 2 ∈ lifted_domain ({0, 2} : Set ℝ) from
      ⟨2, by simp, rfl⟩)
    norm_num [real_distance]

theorem floor_eq_zero_on_small {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ⌊x⌋ = 0 :=
  Int.floor_eq_zero_iff.mpr ⟨hx.1, by linarith [hx.2]⟩

theorem uniform_radius_small : uniform_radius (Set.Icc (0 : ℝ) (1 / 2)) = ⊤ := by
  apply const_components_min_annihilation_radius_eq_top
  intro j hj x hx y hy
  rcases hx with ⟨x, hx, rfl⟩
  rcases hy with ⟨y, hy, rfl⟩
  simp [gauges, real_distance, floor_operator, floor_eq_zero_on_small hx,
    floor_eq_zero_on_small hy]

/-- At the jump point 1, every positive ball contains a point to its left with
different floor value. This proves radius zero from the radius definition. -/
theorem radius_at_one_eq_zero (D : Set ℝ)
    (hD : Set.Icc (9 / 10 : ℝ) 1 ⊆ D) :
    annihilation_radius gauges floor_operator () (singleton_nonempty_finset ())
      (lifted_domain D) (some 1) = 0 := by
  apply bot_unique
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  apply iSup_le
  intro hball
  have hrpos : 0 < r.toReal := ENNReal.toReal_pos hr.1.ne' hr.2
  let δ : ℝ := min (r.toReal / 2) (1 / 20)
  have hδpos : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδsmall : δ ≤ 1 / 20 := min_le_right _ _
  have hδr : δ < r.toReal := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hxD : 1 - δ ∈ D := hD ⟨by linarith, by linarith⟩
  have hfloor : ⌊1 - δ⌋ = 0 :=
    Int.floor_eq_zero_iff.mpr ⟨by linarith, by linarith⟩
  have hdist : gauges () (some (1 - δ)) (some 1) < r := by
    change ENNReal.ofReal |1 - δ - 1| < r
    have habs : |1 - δ - 1| = δ := by
      rw [show 1 - δ - 1 = -δ by ring, abs_neg, abs_of_pos hδpos]
    rw [habs, ← ENNReal.ofReal_toReal hr.2]
    exact (ENNReal.ofReal_lt_ofReal_iff hrpos).mpr hδr
  have hout := hball ⟨hdist, ⟨1 - δ, hxD, rfl⟩⟩
  rw [singleton_computational_fiber_eq] at hout
  norm_num [gauges, floor_operator, real_distance, hfloor] at hout

theorem uniform_radius_eq_zero (D : Set ℝ)
    (hD : Set.Icc (9 / 10 : ℝ) 1 ⊆ D) : uniform_radius D = 0 := by
  apply bot_unique
  have hbase : some 1 ∈ lifted_domain D := ⟨1, hD ⟨by norm_num, le_rfl⟩, rfl⟩
  calc
    uniform_radius D ≤
        annihilation_radius gauges floor_operator () (singleton_nonempty_finset ())
          (lifted_domain D) (some 1) := iInf₂_le (some 1) hbase
    _ = 0 := radius_at_one_eq_zero D hD

theorem uniform_radius_crossing :
    uniform_radius (Set.Icc (9 / 10 : ℝ) (11 / 10)) = 0 := by
  apply uniform_radius_eq_zero
  intro x hx
  exact ⟨hx.1, by linarith [hx.2]⟩

theorem uniform_radius_wide : uniform_radius (Set.Icc (0 : ℝ) 2) = 0 := by
  apply uniform_radius_eq_zero
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem uniform_radius_pair : uniform_radius ({0, 2} : Set ℝ) = 2 := by
  apply le_antisymm
  · calc
      uniform_radius ({0, 2} : Set ℝ) ≤
          annihilation_radius gauges floor_operator () (singleton_nonempty_finset ())
            (lifted_domain ({0, 2} : Set ℝ)) (some 0) :=
        iInf₂_le (some 0) ⟨0, by simp, rfl⟩
      _ ≤ 2 := by
        apply iSup_le
        intro r
        apply iSup_le
        intro hr
        apply iSup_le
        intro hball
        by_contra h
        have h2r : (2 : ENNReal) < r := lt_of_not_ge h
        have hdist : gauges () (some 2) (some 0) < r := by
          norm_num [gauges, real_distance]
          exact h2r
        have hout := hball ⟨hdist, ⟨2, by simp, rfl⟩⟩
        rw [singleton_computational_fiber_eq] at hout
        norm_num [gauges, floor_operator, real_distance] at hout
  · apply le_iInf
    intro y
    apply le_iInf
    rintro ⟨y, hy, rfl⟩
    apply finite_radius_le_annihilation_radius_of_fiber_ball
    · constructor <;> norm_num
    · rintro x ⟨hxball, hx⟩
      rw [singleton_computational_fiber_eq]
      refine ⟨hx, ?_⟩
      rcases hx with ⟨x, hx, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      all_goals norm_num [gauges, real_distance, floor_operator, OpenBall] at hxball
      all_goals norm_num [gauges, real_distance, floor_operator]

/-- OET anchor: h-7ade05e895653cab
习题（输入域改变下的阈值分类）(i)：四个实际输入域的直径与统一零化半径。 -/
theorem four_domains_exact_values :
    (input_diameter (Set.Icc (0 : ℝ) (1 / 2)) = 1 / 2 ∧
      uniform_radius (Set.Icc (0 : ℝ) (1 / 2)) = ⊤) ∧
    (input_diameter (Set.Icc (9 / 10 : ℝ) (11 / 10)) = 1 / 5 ∧
      uniform_radius (Set.Icc (9 / 10 : ℝ) (11 / 10)) = 0) ∧
    (input_diameter ({0, 2} : Set ℝ) = 2 ∧ uniform_radius ({0, 2} : Set ℝ) = 2) ∧
    (input_diameter (Set.Icc (0 : ℝ) 2) = 2 ∧
      uniform_radius (Set.Icc (0 : ℝ) 2) = 0) := by
  refine ⟨⟨?_, uniform_radius_small⟩, ⟨?_, uniform_radius_crossing⟩,
    ⟨input_diameter_pair, uniform_radius_pair⟩, ⟨?_, uniform_radius_wide⟩⟩
  all_goals
    rw [input_diameter_Icc _ _ (by norm_num)]
    norm_num
  all_goals
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num

theorem four_domains_nonempty :
    (Set.Icc (0 : ℝ) (1 / 2)).Nonempty ∧
    (Set.Icc (9 / 10 : ℝ) (11 / 10)).Nonempty ∧
    ({0, 2} : Set ℝ).Nonempty ∧ (Set.Icc (0 : ℝ) 2).Nonempty := by
  refine ⟨⟨0, by norm_num⟩, ⟨1, by norm_num⟩, ⟨0, by simp⟩, ⟨0, by norm_num⟩⟩

/-- OET anchor: h-7ade05e895653cab
习题（输入域改变下的阈值分类）(i)：同一取整算子在两阈值均为一时实现四种组合。 -/
theorem four_threshold_combinations :
    threshold_bits (Set.Icc (0 : ℝ) (1 / 2)) = (true, true) ∧
    threshold_bits (Set.Icc (9 / 10 : ℝ) (11 / 10)) = (true, false) ∧
    threshold_bits ({0, 2} : Set ℝ) = (false, true) ∧
    threshold_bits (Set.Icc (0 : ℝ) 2) = (false, false) := by
  rcases four_domains_exact_values with ⟨⟨h₁, r₁⟩, ⟨h₂, r₂⟩, ⟨h₃, r₃⟩, ⟨h₄, r₄⟩⟩
  norm_num [threshold_bits_eq_components, h₁, h₂, h₃, h₄, r₁, r₂, r₃, r₄]

/-- OET anchor: h-7ade05e895653cab
习题（输入域改变下的阈值分类）(ii)：在实际输入域 `{0, 2}` 上，统一零化半径
达到阈值一，但域内两个点的输出距离恰为二，因而严格为正。 -/
theorem radius_threshold_not_total_zero_counterexample :
    some (0 : ℝ) ∈ lifted_domain ({0, 2} : Set ℝ) ∧
    some (2 : ℝ) ∈ lifted_domain ({0, 2} : Set ℝ) ∧
    (1 : ENNReal) ≤ uniform_radius ({0, 2} : Set ℝ) ∧
    real_distance (floor_operator.func (some 0)) (floor_operator.func (some 2)) = 2 ∧
    0 < real_distance (floor_operator.func (some 0)) (floor_operator.func (some 2)) := by
  norm_num [lifted_domain, uniform_radius_pair, real_distance, floor_operator]

/-- OET anchor: h-7ade05e895653cab
习题（输入域改变下的阈值分类）(ii)：否定题面关于所有非空实数输入域的蕴含式。 -/
theorem uniform_radius_threshold_does_not_imply_total_zero :
    ¬ ∀ D : Set ℝ, D.Nonempty → 1 ≤ uniform_radius D →
      ∀ x ∈ D, ∀ y ∈ D,
        real_distance (floor_operator.func (some x)) (floor_operator.func (some y)) = 0 := by
  intro h
  have hcounter := radius_threshold_not_total_zero_counterexample
  have hzero := h ({0, 2} : Set ℝ) ⟨0, by simp⟩ hcounter.2.2.1
    0 (by simp) 2 (by simp)
  exact (ne_of_gt hcounter.2.2.2.2) hzero

/-- OET anchor: h-451ca2134cd62db4
域缩小下尺度判断的反向失败：正文的带吸收元实直线、恒等算子、
默认直径尺度及实际非空有效域 `B = {0} ⊆ A = {0, 1}`。 -/
theorem identity_domain_refinement_counterexample :
    let A := lifted_domain ({0, 1} : Set ℝ)
    let B := lifted_domain ({0} : Set ℝ)
    ExtendedPseudoMetric RealPoint none real_distance ∧
      B.Nonempty ∧ B ⊆ A ∧
      A ⊆ dom (operator_identity : Operator RealPoint none) ∧
      diameter_scale_family gauges () B = 0 ∧
      diameter_scale_family gauges () A = 1 ∧
      diameter_scale_family gauges () B < (1 / 2 : ENNReal) ∧
      ¬ diameter_scale_family gauges () A < (1 / 2 : ENNReal) := by
  have hB : input_diameter ({0} : Set ℝ) = 0 := by
    simp [input_diameter, lifted_domain, real_distance]
  have hA : input_diameter ({0, 1} : Set ℝ) = 1 := by
    apply le_antisymm
    · apply iSup_le
      rintro _
      apply iSup_le
      rintro ⟨x, hx, rfl⟩
      apply iSup_le
      rintro _
      apply iSup_le
      rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        norm_num [real_distance]
    · apply le_iSup_of_le (some 0)
      apply le_iSup_of_le (show some 0 ∈ lifted_domain ({0, 1} : Set ℝ) from
        ⟨0, by simp, rfl⟩)
      apply le_iSup_of_le (some 1)
      apply le_iSup_of_le (show some 1 ∈ lifted_domain ({0, 1} : Set ℝ) from
        ⟨1, by simp, rfl⟩)
      norm_num [real_distance]
  refine ⟨real_distance_is_extended, ⟨some 0, 0, by simp, rfl⟩, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, Set.mem_insert_iff.mpr (Or.inl (Set.mem_singleton_iff.mp hx)), rfl⟩
  · rintro _ ⟨x, _hx, rfl⟩
    simp [dom, operator_identity]
  · change input_diameter ({0} : Set ℝ) = 0 ∧
      input_diameter ({0, 1} : Set ℝ) = 1 ∧
      input_diameter ({0} : Set ℝ) < (1 / 2 : ENNReal) ∧
      ¬ input_diameter ({0, 1} : Set ℝ) < (1 / 2 : ENNReal)
    rw [hB, hA]
    norm_num

end

end formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_examples
