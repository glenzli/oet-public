import formal_oet.vol_01.exercise_solutions.foundation_examples
import formal_oet.vol_01.ch_03_operator_local_degeneracy.mapping_entropy
import formal_oet.vol_01.ch_03_operator_local_degeneracy.pseudometric_composition

namespace formal_oet.vol_01.exercise_solutions.translation_entropy

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open pseudometric_composition (RealPoint absolute_distance absolute_distance_is_extended)
open foundation_examples (covering_number_eq_card_of_labels)

noncomputable section

def translation : Operator RealPoint none :=
  ⟨Option.map (fun x => x + 1), rfl⟩

def sample_domain : Set RealPoint := {some (-3), some (-2), some 0, some 2}

def fiber_at (φ : Operator RealPoint none) (x : RealPoint) : Set RealPoint :=
  ComputationalFiber absolute_distance φ (singleton_nonempty_finset ())
    sample_domain (φ.func x)

def fiber_partition (φ : Operator RealPoint none) : Set (Set RealPoint) :=
  fiber_at φ '' sample_domain

private theorem mem_fiber_at (φ : Operator RealPoint none) (b x : RealPoint) :
    x ∈ fiber_at φ b ↔
      (x = some (-3) ∧ absolute_distance () (φ.func (some (-3))) (φ.func b) = 0) ∨
      (x = some (-2) ∧ absolute_distance () (φ.func (some (-2))) (φ.func b) = 0) ∨
      (x = some 0 ∧ absolute_distance () (φ.func (some 0)) (φ.func b) = 0) ∨
      (x = some 2 ∧ absolute_distance () (φ.func (some 2)) (φ.func b) = 0) := by
  rw [fiber_at, singleton_computational_fiber_eq]
  simp only [Set.mem_setOf_eq, sample_domain, Set.mem_insert_iff, Set.mem_singleton_iff]
  aesop

/-- OET anchor: h-fc424fbae1afcbdc
The example uses an extended pseudometric and a valid nonabsorbing evaluation domain. -/
theorem example_valid :
    ExtendedPseudoMetric RealPoint none (absolute_distance ()) ∧
      sample_domain ⊆ dom translation := by
  refine ⟨absolute_distance_is_extended, ?_⟩
  intro x hx
  simp only [sample_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [dom, translation]

/-- OET anchor: h-fc424fbae1afcbdc
All identity fibers, as subsets of the input domain. -/
theorem identity_fibers :
    fiber_at operator_identity (some (-3)) = {some (-3)} ∧
    fiber_at operator_identity (some (-2)) = {some (-2), some 2} ∧
    fiber_at operator_identity (some 0) = {some 0} ∧
    fiber_at operator_identity (some 2) = {some (-2), some 2} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x <;>
    norm_num [mem_fiber_at, operator_identity, absolute_distance]

/-- OET anchor: h-fc424fbae1afcbdc
All translation fibers, still as subsets of the input domain. -/
theorem translation_fibers :
    fiber_at translation (some (-3)) = {some (-3)} ∧
    fiber_at translation (some (-2)) = {some (-2), some 0} ∧
    fiber_at translation (some 0) = {some (-2), some 0} ∧
    fiber_at translation (some 2) = {some 2} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext x <;>
    norm_num [mem_fiber_at, translation, absolute_distance]

/-- OET anchor: h-fc424fbae1afcbdc
The two full fiber partitions have the three classes displayed in the solution. -/
theorem exact_fiber_partitions :
    fiber_partition operator_identity =
      {{some (-3)}, {some (-2), some 2}, {some 0}} ∧
    fiber_partition translation =
      {{some (-3)}, {some (-2), some 0}, {some 2}} := by
  constructor
  · simp only [fiber_partition, sample_domain, Set.image_insert_eq, Set.image_singleton,
      identity_fibers.1, identity_fibers.2.1, identity_fibers.2.2.1, identity_fibers.2.2.2]
    ext s
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  · simp [fiber_partition, sample_domain, Set.image_insert_eq, translation_fibers.1,
      translation_fibers.2.1, translation_fibers.2.2.1, translation_fibers.2.2.2]

/-- OET anchor: h-fc424fbae1afcbdc
One pair merges while a formerly zero-distance pair separates. -/
theorem merging_and_separating_pairs :
    absolute_distance () (some (-2)) (some 0) = 2 ∧
    absolute_distance () (translation.func (some (-2))) (translation.func (some 0)) = 0 ∧
    absolute_distance () (some (-2)) (some 2) = 0 ∧
    absolute_distance () (translation.func (some (-2))) (translation.func (some 2)) = 2 := by
  norm_num [absolute_distance, translation]

/-- OET anchor: h-fc424fbae1afcbdc
Neither zero-distance equivalence relation refines the other on the domain. -/
theorem fiber_relations_incomparable :
    ¬ (∀ x ∈ sample_domain, ∀ y ∈ sample_domain,
      absolute_distance () x y = 0 →
        absolute_distance () (translation.func x) (translation.func y) = 0) ∧
    ¬ (∀ x ∈ sample_domain, ∀ y ∈ sample_domain,
      absolute_distance () (translation.func x) (translation.func y) = 0 →
        absolute_distance () x y = 0) := by
  constructor
  · intro h
    have hz := h (some (-2)) (by simp [sample_domain])
      (some 2) (by simp [sample_domain]) merging_and_separating_pairs.2.2.1
    rw [merging_and_separating_pairs.2.2.2] at hz
    norm_num at hz
  · intro h
    have hz := h (some (-2)) (by simp [sample_domain])
      (some 0) (by simp [sample_domain]) merging_and_separating_pairs.2.1
    rw [merging_and_separating_pairs.1] at hz
    norm_num at hz

/-- OET anchor: h-fc424fbae1afcbdc
The image consists of the four translated points. -/
theorem image_domain :
    translation.func '' sample_domain = {some (-2), some (-1), some 1, some 3} := by
  norm_num [sample_domain, translation, Set.image_insert_eq]

/-- OET anchor: h-fc424fbae1afcbdc
Two internal balls are necessary and sufficient for the input at precision 3/2. -/
theorem input_covering :
    covering_number (absolute_distance ()) (3 / 2) sample_domain = 2 := by
  classical
  let q : RealPoint → Bool := fun x => decide (x = some 0)
  let rep : Bool → RealPoint := fun b => if b then some 0 else some (-2)
  have hr : ∀ b, rep b ∈ sample_domain := by
    intro b; cases b <;> simp [rep, sample_domain]
  have hq : ∀ b, q (rep b) = b := by
    intro b; cases b <;> norm_num [q, rep]
  have hb : ∀ x ∈ sample_domain, ∀ c ∈ sample_domain,
      absolute_distance () x c < 3 / 2 ↔ q x = q c := by
    intro x hx c hc
    simp only [sample_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hc
    rcases hx with rfl | rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl | rfl <;>
      norm_num [q, absolute_distance, ENNReal.lt_div_iff_mul_lt, ENNReal.div_le_iff]
  simpa using covering_number_eq_card_of_labels
    (absolute_distance ()) (3 / 2) sample_domain q rep hr hq hb

/-- OET anchor: h-fc424fbae1afcbdc
A single internal ball centered at -2 covers the nonempty image. -/
theorem output_covering :
    covering_number (absolute_distance ()) (3 / 2) (translation.func '' sample_domain) = 1 := by
  classical
  rw [image_domain]
  let V : Set RealPoint := {some (-2), some (-1), some 1, some 3}
  have hnet : InternalEpsilonNet (absolute_distance ()) (3 / 2) V {some (-2)} := by
    constructor
    · intro c hc
      have hc' : c = some (-2) := Finset.mem_singleton.mp hc
      subst c
      simp [V]
    · intro x hx
      refine ⟨some (-2), by simp, ?_⟩
      simp only [V, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        norm_num [absolute_distance, ENNReal.lt_div_iff_mul_lt]
  apply le_antisymm
  · exact iInf_le_of_le {some (-2)} (iInf_le_of_le hnet (by simp))
  · exact one_le_covering_number_of_nonempty _ _ V ⟨some (-2), by simp [V]⟩

/-- OET anchor: h-fc424fbae1afcbdc
The entropy difference is well-defined because the input is nonempty with finite covering. -/
theorem entropy_diff_well_defined :
    EntropyDiffWellDefined absolute_distance translation sample_domain () () (3 / 2) := by
  refine ⟨⟨some 0, by simp [sample_domain]⟩, Or.inl ?_⟩
  change covering_number (absolute_distance ()) (3 / 2) sample_domain < ⊤
  rw [input_covering]
  norm_num

/-- OET anchor: h-fc424fbae1afcbdc
The input entropy is one and the output entropy is zero. -/
theorem entropy_values :
    metric_entropy (absolute_distance ()) (3 / 2) sample_domain = 1 ∧
    metric_entropy (absolute_distance ()) (3 / 2) (translation.func '' sample_domain) = 0 := by
  simp [metric_entropy, input_covering, output_covering, log2_ereal, Real.logb_self_eq_one]

/-- OET anchor: h-fc424fbae1afcbdc
The chapter's input-minus-output entropy difference equals one despite incomparable fibers. -/
theorem translation_entropy_diff :
    mapping_entropy_diff absolute_distance translation sample_domain () () (3 / 2)
      entropy_diff_well_defined = 1 := by
  change metric_entropy (absolute_distance ()) (3 / 2) sample_domain -
    metric_entropy (absolute_distance ()) (3 / 2) (translation.func '' sample_domain) = 1
  rw [entropy_values.1, entropy_values.2, sub_zero]

end

end formal_oet.vol_01.exercise_solutions.translation_entropy
