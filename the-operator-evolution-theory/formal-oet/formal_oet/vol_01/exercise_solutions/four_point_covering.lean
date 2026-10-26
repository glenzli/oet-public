import formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_examples
import formal_oet.vol_01.ch_03_operator_local_degeneracy.mapping_entropy
import Mathlib.Tactic

namespace formal_oet.vol_01.exercise_solutions.four_point_covering

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open threshold_examples (RealPoint real_distance real_distance_is_extended)

noncomputable section

def sample_domain : Set RealPoint := {some 0, some 1, some 2, some 3}

def gauges (_ : Unit) := real_distance

def ordered_operator : Operator RealPoint none := by
  classical
  exact ⟨fun x => if x ∈ sample_domain then x else none, by simp [sample_domain]⟩

def reordered_operator : Operator RealPoint none := by
  classical
  exact ⟨fun x => if x = some 0 then some 0 else if x = some 1 then some 3
    else if x = some 2 then some 1 else if x = some 3 then some 2 else none,
    by simp⟩

private theorem domain_nonempty : sample_domain.Nonempty :=
  ⟨some 0, by simp [sample_domain]⟩

private theorem domain_finite : sample_domain.Finite := by
  simp [sample_domain]

private theorem mem_domain (x : RealPoint) : x ∈ sample_domain ↔
    x = some 0 ∨ x = some 1 ∨ x = some 2 ∨ x = some 3 := by
  simp [sample_domain]

private theorem distance_ge_one {x y : RealPoint}
    (hx : x ∈ sample_domain) (hy : y ∈ sample_domain) (hne : x ≠ y) :
    (1 : ENNReal) ≤ real_distance x y := by
  rcases (mem_domain x).mp hx with rfl | rfl | rfl | rfl <;>
    rcases (mem_domain y).mp hy with rfl | rfl | rfl | rfl <;>
    norm_num [real_distance] at *

private theorem all_points_cover (ε : ENNReal) (hε : 0 < ε) :
    InternalEpsilonNet real_distance ε sample_domain {some 0, some 1, some 2, some 3} := by
  constructor
  · intro x hx
    simpa [sample_domain] using hx
  · intro x hx
    refine ⟨x, by simpa [sample_domain] using hx, ?_⟩
    simpa [real_distance_is_extended.dist_self] using hε

/-- OET anchor: h-aba6bee391edd367
Exercise: four distinct points require four internal centers up to radius one. -/
theorem covering_small (ε : ENNReal) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    covering_number real_distance ε sample_domain = 4 := by
  classical
  apply le_antisymm
  · exact iInf_le_of_le {some 0, some 1, some 2, some 3}
      (iInf_le_of_le (all_points_cover ε hε) (by norm_num))
  · apply le_iInf
    intro centers
    apply le_iInf
    intro hnet
    have hsub : ({some 0, some 1, some 2, some 3} : Finset RealPoint) ⊆ centers := by
      intro x hx
      have hxU : x ∈ sample_domain := by simpa [sample_domain] using hx
      obtain ⟨c, hc, hxc⟩ := hnet.2 x hxU
      have hxc_eq : x = c := by
        by_contra hne
        exact (not_lt_of_ge ((distance_ge_one hxU (hnet.1 hc) hne).trans' hε1)) hxc
      simpa [hxc_eq] using hc
    have hcard := Finset.card_le_card hsub
    norm_num at hcard
    exact_mod_cast hcard

private theorem two_centers_cover (ε : ENNReal) (hε : 1 < ε) :
    InternalEpsilonNet real_distance ε sample_domain {some 0, some 2} := by
  constructor
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [sample_domain]
  · intro x hx
    rcases (mem_domain x).mp hx with rfl | rfl | rfl | rfl
    · exact ⟨some 0, by simp, by simpa [real_distance] using (lt_trans (by norm_num) hε)⟩
    · exact ⟨some 0, by simp, by norm_num [real_distance]; exact hε⟩
    · exact ⟨some 2, by simp, by simpa [real_distance] using (lt_trans (by norm_num) hε)⟩
    · exact ⟨some 2, by simp, by norm_num [real_distance]; exact hε⟩

private theorem endpoints_need_distinct_centers (ε : ENNReal) (hε : ε ≤ 2)
    {c : RealPoint} (hc : c ∈ sample_domain)
    (h0 : real_distance (some 0) c < ε)
    (h3 : real_distance (some 3) c < ε) : False := by
  have h0' := lt_of_lt_of_le h0 hε
  have h3' := lt_of_lt_of_le h3 hε
  rcases (mem_domain c).mp hc with rfl | rfl | rfl | rfl <;>
    norm_num [real_distance] at *

/-- OET anchor: h-aba6bee391edd367
Exercise: the middle radius range needs exactly two internal centers. -/
theorem covering_middle (ε : ENNReal) (hε1 : 1 < ε) (hε2 : ε ≤ 2) :
    covering_number real_distance ε sample_domain = 2 := by
  classical
  apply le_antisymm
  · exact iInf_le_of_le {some 0, some 2}
      (iInf_le_of_le (two_centers_cover ε hε1) (by norm_num))
  · apply le_iInf
    intro centers
    apply le_iInf
    intro hnet
    obtain ⟨c, hc, h0⟩ := hnet.2 (some 0) (by simp [sample_domain])
    obtain ⟨c', hc', h3⟩ := hnet.2 (some 3) (by simp [sample_domain])
    have hne : c ≠ c' := by
      intro heq
      subst c'
      exact endpoints_need_distinct_centers ε hε2 (hnet.1 hc) h0 h3
    have hsub : ({c, c'} : Finset RealPoint) ⊆ centers := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hcard := Finset.card_le_card hsub
    simp [hne] at hcard
    exact_mod_cast hcard

/-- OET anchor: h-aba6bee391edd367
Exercise: after radius two, one internal center suffices. -/
theorem covering_large (ε : ENNReal) (hε : 2 < ε) :
    covering_number real_distance ε sample_domain = 1 := by
  classical
  have hnet : InternalEpsilonNet real_distance ε sample_domain {some 1} := by
    constructor
    · intro x hx
      have hx' := Finset.mem_singleton.mp hx
      subst x
      simp [sample_domain]
    · intro x hx
      refine ⟨some 1, by simp, ?_⟩
      apply lt_of_le_of_lt _ hε
      rcases (mem_domain x).mp hx with rfl | rfl | rfl | rfl <;>
        norm_num [real_distance]
  exact le_antisymm
    (iInf_le_of_le {some 1} (iInf_le_of_le hnet (by simp)))
    (one_le_covering_number_of_nonempty _ _ _ domain_nonempty)

/-- OET anchor: h-aba6bee391edd367
Exercise: the complete three-case formula includes the open-ball endpoints. -/
theorem covering_formula (ε : ENNReal) (hε : 0 < ε) :
    covering_number real_distance ε sample_domain =
      if ε ≤ 1 then 4 else if ε ≤ 2 then 2 else 1 := by
  by_cases h1 : ε ≤ 1
  · simp [h1, covering_small ε hε h1]
  · by_cases h2 : ε ≤ 2
    · simp [h1, h2, covering_middle ε (lt_of_not_ge h1) h2]
    · simp [h1, h2, covering_large ε (lt_of_not_ge h2)]

/-- OET anchor: h-aba6bee391edd367
Exercise: an exterior center covers the set but is not an internal net. -/
theorem exterior_center_comparison :
    (∀ x ∈ sample_domain, real_distance x (some (3 / 2)) < 7 / 4) ∧
      some (3 / 2) ∉ sample_domain ∧
      ¬ InternalEpsilonNet real_distance (7 / 4) sample_domain {some (3 / 2)} := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases (mem_domain x).mp hx with rfl | rfl | rfl | rfl <;>
      norm_num [real_distance]
    all_goals
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]
  · norm_num [sample_domain]
  · intro h
    have hc := h.1 (by simp : some (3 / 2) ∈ ({some (3 / 2)} : Finset RealPoint))
    norm_num [sample_domain] at hc

/-- OET anchor: h-aba6bee391edd367
Exercise: both concrete operators are defined on the four-point domain. -/
theorem example_valid :
    ExtendedPseudoMetric RealPoint none real_distance ∧
      sample_domain ⊆ dom ordered_operator ∧ sample_domain ⊆ dom reordered_operator := by
  refine ⟨real_distance_is_extended, ?_, ?_⟩ <;>
    intro x hx <;>
    rcases (mem_domain x).mp hx with rfl | rfl | rfl | rfl <;>
    norm_num [dom, ordered_operator, reordered_operator, sample_domain] <;> exact Option.some_ne_none _

/-- OET anchor: h-aba6bee391edd367
Exercise: output reordering leaves the image set exactly unchanged. -/
theorem images_equal :
    ordered_operator.func '' sample_domain = sample_domain ∧
      reordered_operator.func '' sample_domain = sample_domain := by
  constructor <;> ext x <;>
    simp [sample_domain, Set.image_insert_eq, ordered_operator, reordered_operator]
  tauto

/-- OET anchor: h-aba6bee391edd367
Exercise: both images have the same covering number at every radius. -/
theorem image_coverings (ε : ENNReal) :
    covering_number real_distance ε (ordered_operator.func '' sample_domain) =
      covering_number real_distance ε sample_domain ∧
    covering_number real_distance ε (reordered_operator.func '' sample_domain) =
      covering_number real_distance ε sample_domain := by
  rw [images_equal.1, images_equal.2]
  exact ⟨rfl, rfl⟩

/-- OET anchor: h-aba6bee391edd367
Exercise: both entropy differences are well-defined on every finite positive scale. -/
theorem entropy_well_defined (ε : ENNReal) (hε : 0 < ε) (hfin : ε ≠ ⊤) :
    EntropyDiffWellDefined gauges ordered_operator sample_domain () () ε ∧
      EntropyDiffWellDefined gauges reordered_operator sample_domain () () ε := by
  constructor <;>
    exact (finite_set_mapping_entropy_diff_well_defined gauges _ _ () () ε
      domain_nonempty domain_finite hε hfin (fun _ => real_distance_is_extended.dist_self)).2.2

private theorem entropy_diff_zero_of_image (φ : Operator RealPoint none)
    (himage : φ.func '' sample_domain = sample_domain)
    (ε : ENNReal) (hε : 0 < ε)
    (hwd : EntropyDiffWellDefined gauges φ sample_domain () () ε) :
    mapping_entropy_diff gauges φ sample_domain () () ε hwd = 0 := by
  unfold mapping_entropy_diff
  rw [himage]
  change log2_ereal (covering_number real_distance ε sample_domain) -
    log2_ereal (covering_number real_distance ε sample_domain) = 0
  rw [covering_formula ε hε]
  split_ifs <;> simp [log2_ereal]
  exact EReal.sub_self (EReal.coe_ne_top 1) (EReal.coe_ne_bot 1)

/-- OET anchor: h-aba6bee391edd367
Exercise: the image entropy difference is zero for both input-output assignments. -/
theorem entropy_differences (ε : ENNReal) (hε : 0 < ε) (hfin : ε ≠ ⊤) :
    mapping_entropy_diff gauges ordered_operator sample_domain () () ε
      (entropy_well_defined ε hε hfin).1 = 0 ∧
    mapping_entropy_diff gauges reordered_operator sample_domain () () ε
      (entropy_well_defined ε hε hfin).2 = 0 :=
  ⟨entropy_diff_zero_of_image _ images_equal.1 ε hε _,
    entropy_diff_zero_of_image _ images_equal.2 ε hε _⟩

/-- OET anchor: h-aba6bee391edd367
Exercise: the ordered and reordered assignments admit scalar Lip bounds one and three. -/
theorem scalar_lip_bounds :
    HasScalarLipBound gauges ordered_operator sample_domain () () 1 ∧
      HasScalarLipBound gauges reordered_operator sample_domain () () 3 := by
  constructor
  · refine ⟨example_valid.2.1, ?_⟩
    intro x hx y hy
    simp [gauges, ordered_operator, hx, hy]
  · refine ⟨example_valid.2.2, ?_⟩
    intro x hx y hy
    rcases (mem_domain x).mp hx with rfl | rfl | rfl | rfl <;>
      rcases (mem_domain y).mp hy with rfl | rfl | rfl | rfl <;>
      norm_num [gauges, real_distance, reordered_operator]

/-- OET anchor: h-aba6bee391edd367
Exercise: the pair zero-one forces the two constants to be optimal. -/
theorem scalar_lip_optimal (L : ENNReal) :
    (HasScalarLipBound gauges ordered_operator sample_domain () () L → 1 ≤ L) ∧
      (HasScalarLipBound gauges reordered_operator sample_domain () () L → 3 ≤ L) := by
  constructor <;> intro h
  · have hb := h.2 (some 0) (by simp [sample_domain]) (some 1) (by simp [sample_domain])
    simpa [gauges, real_distance, ordered_operator, sample_domain] using hb
  · have hb := h.2 (some 0) (by simp [sample_domain]) (some 1) (by simp [sample_domain])
    simpa [gauges, real_distance, reordered_operator] using hb

/-- OET anchor: h-aba6bee391edd367
Exercise: applying the scalar transport theorem gives bounds two and four. -/
theorem transported_cover_bounds :
    covering_number real_distance (7 / 4) (ordered_operator.func '' sample_domain) ≤
      covering_number real_distance (7 / 4) sample_domain ∧
    covering_number real_distance (7 / 4) (reordered_operator.func '' sample_domain) ≤
      covering_number real_distance (7 / 12) sample_domain := by
  constructor
  · simpa [gauges, cov_num] using
      lip_cov_num_bound_aux gauges ordered_operator sample_domain () () 1 (7 / 4)
        scalar_lip_bounds.1 (by norm_num) (by norm_num)
  · have h := lip_cov_num_bound_aux gauges reordered_operator sample_domain () () 3 (7 / 12)
      scalar_lip_bounds.2 (by norm_num) (by norm_num)
    have heq : (3 : ENNReal) * (7 / 12) = 7 / 4 := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_mul, ENNReal.toReal_div]
    simpa [gauges, cov_num, heq] using h

/-- OET anchor: h-aba6bee391edd367
Exercise: the true image covering numbers are two, while the second input bound is four. -/
theorem numerical_comparison :
    covering_number real_distance (7 / 4) sample_domain = 2 ∧
    covering_number real_distance (7 / 12) sample_domain = 4 ∧
    covering_number real_distance (7 / 4) (ordered_operator.func '' sample_domain) = 2 ∧
    covering_number real_distance (7 / 4) (reordered_operator.func '' sample_domain) = 2 := by
  have hmiddle := covering_middle (7 / 4) (by norm_num [ENNReal.lt_div_iff_mul_lt])
    (by norm_num [ENNReal.div_le_iff])
  have hsmall := covering_small (7 / 12) (by norm_num) (by norm_num [ENNReal.div_le_iff])
  rw [images_equal.1, images_equal.2]
  exact ⟨hmiddle, hsmall, hmiddle, hmiddle⟩

end

end formal_oet.vol_01.exercise_solutions.four_point_covering
