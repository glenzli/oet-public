import formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_examples
import formal_oet.vol_01.ch_01_foundations.metric_entropy

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy.pointwise_uniform_radius_example

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_examples
  (RealPoint real_distance real_distance_is_extended)

noncomputable section

/-- The real step map, extended by the absorbing point. -/
def step_operator : Operator RealPoint none :=
  ⟨Option.map (fun x : ℝ => if x < 0 then 0 else 1), rfl⟩

/-- The punctured interval in the example in CH3, lifted into the absorbing space. -/
def sample_domain : Set RealPoint :=
  some '' (Set.Ico (-1 : ℝ) 0 ∪ Set.Ioc (0 : ℝ) 1)

private theorem mem_domain (y : ℝ) : some y ∈ sample_domain ↔
    (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1) := by
  simp [sample_domain]

/--
OET anchor: h-ae07c4b78c2b63cd
**反例（处处正的零化半径未必有正的统一下界，模型合法性）**
The ordinary real-line metric is extended by an absorbing point; the punctured
evaluation domain is nonempty and lies in the actual step operator's domain.
-/
theorem example_valid :
    ExtendedPseudoMetric RealPoint none real_distance ∧
      sample_domain.Nonempty ∧ sample_domain ⊆ dom step_operator := by
  refine ⟨real_distance_is_extended, ⟨some 1, ?_⟩, ?_⟩
  · exact (mem_domain 1).mpr (Or.inr ⟨by norm_num, le_rfl⟩)
  · rintro _ ⟨y, hy, rfl⟩
    simp [dom, step_operator]

private theorem abs_pos_of_mem {y : ℝ} (hy : some y ∈ sample_domain) : 0 < |y| := by
  rcases (mem_domain y).mp hy with hy | hy
  · rw [abs_of_neg hy.2]; linarith
  · exact lt_of_lt_of_le hy.1 (le_abs_self y)

private theorem same_output_of_close {y z : ℝ} (hy : some y ∈ sample_domain)
    (hclose : |z - y| < |y|) :
    step_operator.func (some z) = step_operator.func (some y) := by
  rcases (mem_domain y).mp hy with hy | hy
  · have hz : z < 0 := by
      rw [abs_of_neg hy.2] at hclose
      have h := (abs_lt.mp hclose).2
      linarith
    simp [step_operator, hy.2, hz]
  · have hy0 : ¬ y < 0 := not_lt.mpr hy.1.le
    have hz0 : ¬ z < 0 := by
      rw [abs_of_pos hy.1] at hclose
      have h := (abs_lt.mp hclose).1
      linarith
    simp [step_operator, hy0, hz0]

/--
OET anchor: h-ae07c4b78c2b63cd
**反例（处处正的零化半径未必有正的统一下界，精确点态半径）**
The radius in the existing OET definition is exactly the distance to the missing jump point.
-/
theorem pointwise_radius_eq (y : ℝ) (hy : some y ∈ sample_domain) :
    metric_annihilation_radius real_distance real_distance step_operator
      sample_domain (some y) = ENNReal.ofReal |y| := by
  have hyabs : 0 < |y| := abs_pos_of_mem hy
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply iSup_le
    intro hball
    by_contra hle
    have hrlarge : |y| < r.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg y) hr.2).mp (lt_of_not_ge hle)
    let δ : ℝ := min ((r.toReal - |y|) / 2) (1 / 2)
    have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδone : δ ≤ 1 / 2 := min_le_right _ _
    have hδr : δ + |y| < r.toReal := by
      have hδ := min_le_left ((r.toReal - |y|) / 2) (1 / 2)
      dsimp [δ]
      linarith
    rcases (mem_domain y).mp hy with hy | hy
    · have hz : some δ ∈ sample_domain :=
        (mem_domain δ).mpr (Or.inr ⟨hδpos, by linarith⟩)
      have hdist : real_distance (some δ) (some y) < r := by
        change ENNReal.ofReal |δ - y| < r
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2).mpr
        rw [abs_of_pos (by linarith : 0 < δ - y)]
        rw [abs_of_neg hy.2] at hδr
        linarith
      have hout := (hball ⟨hdist, hz⟩).2
      norm_num [step_operator, real_distance, hy.2, not_lt.mpr hδpos.le] at hout
    · have hz : some (-δ) ∈ sample_domain :=
        (mem_domain (-δ)).mpr (Or.inl ⟨by linarith, by linarith⟩)
      have hdist : real_distance (some (-δ)) (some y) < r := by
        change ENNReal.ofReal |-δ - y| < r
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2).mpr
        rw [abs_of_neg (by linarith : -δ - y < 0)]
        rw [abs_of_pos hy.1] at hδr
        linarith
      have hout := (hball ⟨hdist, hz⟩).2
      norm_num [step_operator, real_distance, show -δ < 0 by linarith,
        not_lt.mpr hy.1.le] at hout
  · apply le_iSup_of_le (ENNReal.ofReal |y|)
    apply le_iSup_of_le (show FinitePositiveRadius (ENNReal.ofReal |y|) from
      ⟨ENNReal.ofReal_pos.mpr hyabs, ENNReal.ofReal_ne_top⟩)
    have hball : {x | real_distance x (some y) < ENNReal.ofReal |y|} ∩ sample_domain ⊆
        {x ∈ sample_domain |
          real_distance (step_operator.func x) (step_operator.func (some y)) = 0} := by
      rintro x ⟨hclose, hx⟩
      rcases hx with ⟨z, hz, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      have hreal : |z - y| < |y| :=
        (ENNReal.ofReal_lt_ofReal_iff hyabs).mp hclose
      rw [same_output_of_close hy hreal]
      exact real_distance_is_extended.dist_self _
    exact le_iSup_of_le hball le_rfl

/--
OET anchor: h-ae07c4b78c2b63cd
**反例（处处正的零化半径未必有正的统一下界，处处正性）**
Every point of the fixed punctured domain has a strictly positive zeroing radius.
-/
theorem pointwise_radius_pos :
    ∀ x ∈ sample_domain,
      0 < metric_annihilation_radius real_distance real_distance step_operator sample_domain x := by
  rintro _ ⟨y, hy, rfl⟩
  have hymem : some y ∈ sample_domain := ⟨y, hy, rfl⟩
  rw [pointwise_radius_eq y hymem]
  exact ENNReal.ofReal_pos.mpr (abs_pos_of_mem hymem)

/--
OET anchor: h-ae07c4b78c2b63cd
**反例（处处正的零化半径未必有正的统一下界，统一半径）**
The infimum of these strictly positive pointwise radii is nevertheless zero.
-/
theorem uniform_radius_eq_zero :
    metric_min_annihilation_radius real_distance real_distance step_operator sample_domain = 0 := by
  apply bot_unique
  apply ENNReal.le_of_forall_pos_le_add (b := 0)
  intro ε hε _
  simp only [zero_add]
  have hεreal : (0 : ℝ) < ε := by exact_mod_cast hε
  let a : ℝ := min ((ε : ℝ) / 2) (1 / 2)
  have hapos : 0 < a := lt_min (by positivity) (by norm_num)
  have haone : a ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hamem : some a ∈ sample_domain := (mem_domain a).mpr (Or.inr ⟨hapos, haone⟩)
  calc
    metric_min_annihilation_radius real_distance real_distance step_operator sample_domain ≤
        metric_annihilation_radius real_distance real_distance step_operator sample_domain
          (some a) := iInf₂_le (some a) hamem
    _ = ENNReal.ofReal a := by rw [pointwise_radius_eq a hamem, abs_of_pos hapos]
    _ ≤ (ε : ENNReal) := by
      have haε : a ≤ (ε : ℝ) := le_trans (min_le_left _ _) (by linarith)
      simpa using ENNReal.ofReal_le_ofReal haε

/-- Two nonzero points on opposite sides of the jump. -/
def crossing_pair (a : ℝ) : Set RealPoint := {some (-a), some a}

theorem crossing_pair_subset (a : ℝ) (ha : 0 < a) (haone : a ≤ 1) :
    crossing_pair a ⊆ sample_domain := by
  intro x hx
  simp only [crossing_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact (mem_domain (-a)).mpr (Or.inl ⟨by linarith, by linarith⟩)
  · exact (mem_domain a).mpr (Or.inr ⟨ha, haone⟩)

theorem crossing_pair_image (a : ℝ) (ha : 0 < a) :
    step_operator.func '' crossing_pair a = {some 0, some 1} := by
  simp [crossing_pair, Set.image_insert_eq, step_operator,
    show -a < 0 by linarith, not_lt.mpr ha.le]

theorem crossing_pair_input_covering (a : ℝ) (ha : 0 < a) (τ : ENNReal)
    (hτ : ENNReal.ofReal (2 * a) < τ) :
    covering_number real_distance τ (crossing_pair a) = 1 := by
  classical
  have hτpos : 0 < τ := lt_of_le_of_lt (zero_le _) hτ
  have hnet : InternalEpsilonNet real_distance τ (crossing_pair a) {some a} := by
    constructor
    · intro x hx
      have hx' : x = some a := Finset.mem_singleton.mp hx
      subst x
      simp [crossing_pair]
    · intro x hx
      refine ⟨some a, by simp, ?_⟩
      simp only [crossing_pair, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simpa [real_distance, show -a - a = -(2 * a) by ring,
          abs_neg, abs_of_nonneg (by positivity : 0 ≤ 2 * a)] using hτ
      · simpa [real_distance] using hτpos
  apply le_antisymm
  · exact iInf_le_of_le {some a} (iInf_le_of_le hnet (by simp))
  · exact one_le_covering_number_of_nonempty _ _ _ ⟨some a, by simp [crossing_pair]⟩

private theorem output_covering :
    covering_number real_distance (1 / 2) ({some 0, some 1} : Set RealPoint) = 2 := by
  classical
  let C : Finset RealPoint := {some 0, some 1}
  have hnet : InternalEpsilonNet real_distance (1 / 2) ({some 0, some 1} : Set RealPoint) C := by
    constructor
    · simp [C]
    · intro x hx
      refine ⟨x, by simpa [C] using hx, ?_⟩
      rw [real_distance_is_extended.dist_self]
      norm_num
  apply le_antisymm
  · exact iInf_le_of_le C (iInf_le_of_le hnet (by norm_num [C]))
  · apply le_iInf
    intro centers
    apply le_iInf
    intro hcenters
    have hsub : C ⊆ centers := by
      intro x hx
      have hxU : x ∈ ({some 0, some 1} : Set RealPoint) := by simpa [C] using hx
      obtain ⟨c, hc, hxc⟩ := hcenters.2 x hxU
      have hcU := hcenters.1 hc
      have heq : x = c := by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxU hcU
        rcases hxU with rfl | rfl <;> rcases hcU with rfl | rfl <;>
          first | rfl | norm_num [real_distance] at hxc
      simpa [heq] using hc
    have hcard := Finset.card_le_card hsub
    norm_num [C] at hcard
    exact_mod_cast hcard

theorem crossing_pair_output_covering (a : ℝ) (ha : 0 < a) :
    covering_number real_distance (1 / 2) (step_operator.func '' crossing_pair a) = 2 := by
  rw [crossing_pair_image a ha]
  exact output_covering

/-- Continued calculation for the same CH3 example, in the explanatory paragraph
after the proof of the uniform-radius covering proposition: at every fixed finite
positive input scale, an actual two-point subset has input covering number one
and output covering number two. This is an auxiliary calculation, not a new
independently numbered object. -/
theorem every_scale_has_covering_counterexample (τ : ENNReal)
    (hτpos : 0 < τ) (hτfinite : τ ≠ ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < τ ∧
      crossing_pair a ⊆ sample_domain ∧
      covering_number real_distance τ (crossing_pair a) = 1 ∧
      covering_number real_distance (1 / 2) (step_operator.func '' crossing_pair a) = 2 := by
  have hτreal : 0 < τ.toReal := ENNReal.toReal_pos hτpos.ne' hτfinite
  let a : ℝ := min (τ.toReal / 4) (1 / 2)
  have hapos : 0 < a := lt_min (by positivity) (by norm_num)
  have haone : a ≤ 1 := le_trans (min_le_right _ _) (by norm_num)
  have hsmall : ENNReal.ofReal (2 * a) < τ := by
    apply (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hτfinite).mpr
    have ha := min_le_left (τ.toReal / 4) (1 / 2)
    dsimp [a]
    linarith
  exact ⟨a, hapos, haone, hsmall, crossing_pair_subset a hapos haone,
    crossing_pair_input_covering a hapos τ hsmall, crossing_pair_output_covering a hapos⟩

end

end formal_oet.vol_01.ch_03_operator_local_degeneracy.pointwise_uniform_radius_example
