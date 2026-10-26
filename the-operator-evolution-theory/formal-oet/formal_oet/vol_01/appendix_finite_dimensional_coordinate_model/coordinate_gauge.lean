import formal_oet.vol_01.appendix_separating_gauge_specialization.full_gauge
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Tactic

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.appendix_separating_gauge_specialization

noncomputable section

/-- A finite real coordinate vector. -/
abbrev CoordinateVector (n : ℕ) := Fin n → ℝ

/-- The coordinate model on `A`, with `none` as the absorbing point. -/
abbrev CoordinatePoint (n : ℕ) (A : Set (CoordinateVector n)) := Option A

/-- The distinguished absorbing point of the coordinate model. -/
def coordinate_bot {n : ℕ} {A : Set (CoordinateVector n)} : CoordinatePoint n A := none

/-- The extended pseudometric read by one coordinate. -/
def coordinate_dist {n : ℕ} {A : Set (CoordinateVector n)} (i : Fin n) :
    CoordinatePoint n A → CoordinatePoint n A → ENNReal
  | some x, some y => ENNReal.ofReal |x.1 i - y.1 i|
  | none, none => 0
  | _, _ => ⊤

/-- The finite maximum of all coordinate distances. -/
def coordinate_full_dist {n : ℕ} [NeZero n] {A : Set (CoordinateVector n)} :
    CoordinatePoint n A → CoordinatePoint n A → ENNReal :=
  full_gauge_dist (fun i : Fin n => coordinate_dist i)

/-- The coordinate supremum distance on the nonabsorbing part. -/
def coordinate_sup_distance {n : ℕ} (x y : CoordinateVector n) : ENNReal :=
  Finset.univ.sup fun i : Fin n => ENNReal.ofReal |x i - y i|

private theorem of_real_abs_sub_triangle (a b c : ℝ) :
    ENNReal.ofReal |a - c| ≤
      ENNReal.ofReal |a - b| + ENNReal.ofReal |b - c| := by
  rw [← ENNReal.ofReal_add (abs_nonneg (a - b)) (abs_nonneg (b - c))]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le a b c)

/-- Each coordinate distance is an extended pseudometric. -/
theorem coordinate_dist_is_extended_pseudo_metric {n : ℕ}
    {A : Set (CoordinateVector n)} (hA : A.Nonempty) (i : Fin n) :
    ExtendedPseudoMetric (CoordinatePoint n A) coordinate_bot (coordinate_dist i) := by
  refine
    { nonabsorbing := ⟨some ⟨hA.choose, hA.choose_spec⟩, by simp [coordinate_bot]⟩
      dist_self := ?_
      symm := ?_
      triangle := ?_
      isolate_bot := ?_ }
  · intro x
    cases x <;> simp [coordinate_dist]
  · intro x y
    cases x <;> cases y <;> simp [coordinate_dist, abs_sub_comm]
  · intro x y z
    cases x with
    | none =>
        cases y <;> cases z <;> simp [coordinate_dist]
    | some x =>
        cases y with
        | none => cases z <;> simp [coordinate_dist]
        | some y =>
            cases z with
            | none => simp [coordinate_dist]
            | some z =>
                simpa [coordinate_dist] using
                  of_real_abs_sub_triangle (x.1 i) (y.1 i) (z.1 i)
  · intro x hx
    cases x with
    | none => exact False.elim (hx rfl)
    | some x => rfl

/-- The coordinate family separates points when the coordinate set is nonempty. -/
theorem coordinate_family_is_separating {n : ℕ} [NeZero n]
    {A : Set (CoordinateVector n)} :
    IsSeparating (fun i : Fin n => coordinate_dist (A := A) i) := by
  intro x y hxy
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some y =>
          have h := hxy (0 : Fin n)
          simp [coordinate_dist] at h
  | some x =>
      cases y with
      | none =>
          have h := hxy (0 : Fin n)
          simp [coordinate_dist] at h
      | some y =>
          congr 1
          apply Subtype.ext
          funext i
          have hi := hxy i
          simp only [coordinate_dist, ENNReal.ofReal_eq_zero] at hi
          exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hi (abs_nonneg _)))

/-- A single extended pseudometric separates points. -/
def SeparatesPoints {X : Type} (d : X → X → ENNReal) : Prop :=
  ∀ x y, d x y = 0 → x = y

/--
OET anchor: h-98bad2ee358bf00b
**命题（坐标规范的分离性）**
坐标规范族是分离扩展规范族，其全族距离是坐标最大值；
单一坐标分离当且仅当该坐标投影在 `A` 上单射。
-/
theorem coordinate_gauge_separation {n : ℕ} [NeZero n]
    (A : Set (CoordinateVector n)) (hA : A.Nonempty) :
    (∀ i : Fin n,
      ExtendedPseudoMetric (CoordinatePoint n A) coordinate_bot (coordinate_dist i)) ∧
    IsSeparating (fun i : Fin n => coordinate_dist (A := A) i) ∧
    (∀ x y : A,
      coordinate_full_dist (some x) (some y) = coordinate_sup_distance x.1 y.1) ∧
    (∀ i : Fin n,
      SeparatesPoints (coordinate_dist (A := A) i) ↔
        Function.Injective (fun x : A => x.1 i)) := by
  refine ⟨coordinate_dist_is_extended_pseudo_metric hA, coordinate_family_is_separating, ?_, ?_⟩
  · intro x y
    simp [coordinate_full_dist, coordinate_sup_distance, full_gauge_dist,
      comp_pseudo_metric, full_nonempty_finset, coordinate_dist]
  · intro i
    constructor
    · intro hsep x y hxy
      apply Subtype.ext
      have hpoint : (some x : CoordinatePoint n A) = some y := by
        apply hsep
        simp [coordinate_dist, hxy]
      exact congrArg Subtype.val (Option.some.inj hpoint)
    · intro hinj x y hzero
      cases x with
      | none =>
          cases y with
          | none => rfl
          | some y => simp [coordinate_dist] at hzero
      | some x =>
          cases y with
          | none => simp [coordinate_dist] at hzero
          | some y =>
              congr 1
              apply hinj
              change ENNReal.ofReal |x.1 i - y.1 i| = 0 at hzero
              have hle : |x.1 i - y.1 i| ≤ 0 := by
                simpa only [ENNReal.ofReal_eq_zero] using hzero
              exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))

end

end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
