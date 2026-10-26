import formal_oet.vol_01.exercise_solutions.foundation_examples
import Mathlib.Data.ENNReal.BigOperators

namespace formal_oet.vol_01.exercise_solutions.operator_average

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.exercise_solutions.foundation_examples
open scoped BigOperators

def discrete_distance {n : ℕ} (x y : Fin n) : ENNReal := if x = y then 0 else 1
def point_distance {n : ℕ} := extend_distance (@discrete_distance n)

theorem point_distance_is_extended {n : ℕ} [NeZero n] :
    ExtendedPseudoMetric (Option (Fin n)) none (@point_distance n) := by
  apply extend_distance_is_extended
  · intro x; simp [discrete_distance]
  · intro x y; simp [discrete_distance, eq_comm]
  · intro x y z
    unfold discrete_distance
    split_ifs <;> simp_all

noncomputable def average_distance {n : ℕ}
    (φ ψ : Operator (Option (Fin n)) none) : ENNReal :=
  (n : ENNReal)⁻¹ * ∑ x : Fin n, point_distance (φ.func (some x)) (ψ.func (some x))

/-- OET anchor: h-92cd0a940e038231
The default supremum equals the finite supremum over all nonabsorbing inputs. -/
theorem op_dist_eq_nonabsorbing_sup {n : ℕ}
    (φ ψ : Operator (Option (Fin n)) none) :
    op_dist point_distance φ ψ =
      ⨆ x : Fin n, point_distance (φ.func (some x)) (ψ.func (some x)) := by
  simp [op_dist, iSup_option, φ.preserves_bot, ψ.preserves_bot,
    point_distance, extend_distance]

/-- OET anchor: h-92cd0a940e038231
A positive equal-weight average on all nonabsorbing inputs also gives an
extended operator gauge, including operators with partial domains. -/
theorem average_is_extended {n : ℕ} [NeZero n] :
    ExtendedPseudoMetric (Operator (Option (Fin n)) none) bot_operator
      (@average_distance n) := by
  have hd := @point_distance_is_extended n _
  refine ⟨operator_space_nonabsorbing hd.nonabsorbing, ?_, ?_, ?_, ?_⟩
  · intro φ
    simp [average_distance, hd.dist_self]
  · intro φ ψ
    simp only [average_distance]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    exact hd.symm _ _
  · intro φ ψ χ
    unfold average_distance
    calc
      _ ≤ (n : ENNReal)⁻¹ * ∑ x : Fin n,
          (point_distance (φ.func (some x)) (ψ.func (some x)) +
          point_distance (ψ.func (some x)) (χ.func (some x))) := by
        apply mul_le_mul_right
        apply Finset.sum_le_sum
        intro x _
        exact hd.triangle _ _ _
      _ = _ := by rw [Finset.sum_add_distrib, mul_add]
  · intro φ hφ
    have hex : ∃ x : Fin n, φ.func (some x) ≠ none := by
      by_contra h
      push Not at h
      apply hφ
      apply Operator.ext
      funext x
      cases x with
      | none => exact φ.preserves_bot
      | some x => exact h x
    obtain ⟨x, hx⟩ := hex
    have hsum : (∑ y : Fin n,
        point_distance (φ.func (some y)) none) = ⊤ := by
      apply ENNReal.sum_eq_top.mpr
      exact ⟨x, Finset.mem_univ _, hd.isolate_bot _ hx⟩
    simp [average_distance, bot_operator, hsum]

def constant_operator {n : ℕ} (a : Fin n) : Operator (Option (Fin n)) none :=
  ⟨Option.map (fun _ => a), rfl⟩

def spike_operator {n : ℕ} [NeZero n] (a b : Fin n) :
    Operator (Option (Fin n)) none :=
  ⟨Option.map (fun x => if x = 0 then b else a), rfl⟩

/-- OET anchor: h-92cd0a940e038231
A discrepancy at one input has supremum one and average 1/n. -/
theorem single_discrepancy {n : ℕ} [NeZero n] (a b : Fin n) (hab : a ≠ b) :
    op_dist point_distance (constant_operator a) (spike_operator a b) = 1 ∧
      average_distance (constant_operator a) (spike_operator a b) = (n : ENNReal)⁻¹ := by
  have hp (x : Fin n) :
      point_distance ((constant_operator a).func (some x))
        ((spike_operator a b).func (some x)) = if x = 0 then 1 else 0 := by
    by_cases hx : x = 0 <;>
      simp [point_distance, extend_distance, discrete_distance,
        constant_operator, spike_operator, hx, hab]
  constructor
  · rw [op_dist_eq_nonabsorbing_sup]
    simp only [hp]
    apply le_antisymm
    · apply iSup_le; intro x; split_ifs <;> simp
    · exact (by simpa using (le_iSup (fun x : Fin n =>
        if x = 0 then (1 : ENNReal) else 0) 0))
  · simp [average_distance, hp]

/-- OET anchor: h-92cd0a940e038231
A discrepancy at every input has both supremum and average one. -/
theorem everywhere_discrepancy {n : ℕ} [NeZero n] (a b : Fin n) (hab : a ≠ b) :
    op_dist point_distance (constant_operator a) (constant_operator b) = 1 ∧
      average_distance (constant_operator a) (constant_operator b) = 1 := by
  have hp (x : Fin n) :
      point_distance ((constant_operator a).func (some x))
        ((constant_operator b).func (some x)) = 1 := by
    simp [point_distance, extend_distance, discrete_distance, constant_operator, hab]
  constructor
  · rw [op_dist_eq_nonabsorbing_sup]; simp [hp]
  · simp [average_distance, hp, ENNReal.inv_mul_cancel, NeZero.ne n]

/-- OET anchor: h-92cd0a940e038231
For total operators the average is exactly the fraction of differing outputs. -/
theorem average_eq_discrepancy_fraction {n : ℕ}
    (φ ψ : Operator (Option (Fin n)) none)
    (hφ : ∀ x : Fin n, φ.func (some x) ≠ none)
    (hψ : ∀ x : Fin n, ψ.func (some x) ≠ none) :
    average_distance φ ψ = (n : ENNReal)⁻¹ *
      ((Finset.univ.filter (fun x : Fin n => φ.func (some x) ≠ ψ.func (some x))).card :
        ENNReal) := by
  have hp (x : Fin n) : point_distance (φ.func (some x)) (ψ.func (some x)) =
      if φ.func (some x) ≠ ψ.func (some x) then 1 else 0 := by
    cases heφ : φ.func (some x) with
    | none => exact False.elim (hφ x heφ)
    | some a =>
      cases heψ : ψ.func (some x) with
      | none => exact False.elim (hψ x heψ)
      | some b =>
        simp [point_distance, extend_distance, discrete_distance, ite_not]
  simp only [average_distance, hp]
  congr 1
  rw [← Finset.sum_filter]
  simp

end formal_oet.vol_01.exercise_solutions.operator_average
