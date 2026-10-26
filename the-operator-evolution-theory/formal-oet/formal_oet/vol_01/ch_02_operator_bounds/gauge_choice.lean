import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Mathlib.Data.Real.ENatENNReal

namespace formal_oet.vol_01.ch_02_operator_bounds.gauge_choice

open formal_oet.vol_01.ch_01_foundations

noncomputable section

/-- The real plane with `none` as its absorbing point. -/
abbrev PlanePoint := Option (ℝ × ℝ)

/-- The two ordinary coordinate readings; Lean indices `0, 1` represent `1, 2`. -/
def read_coordinate (i : Fin 2) (x : ℝ × ℝ) : ℝ :=
  if i = 0 then x.1 else x.2

/-- Coordinate pseudometrics, extended by absorbing-point isolation. -/
def coordinate_dist (i : Fin 2) : PlanePoint → PlanePoint → ENNReal
  | some x, some y => ENNReal.ofReal |read_coordinate i x - read_coordinate i y|
  | none, none => 0
  | _, _ => ⊤

/-- The first gauge reads the first coordinate; the second reads both coordinates. -/
def overlapping_dist (i : Fin 2) (x y : PlanePoint) : ENNReal :=
  if i = 0 then coordinate_dist 0 x y else coordinate_dist 0 x y + coordinate_dist 1 x y

/-- The same shear operator is used with both gauges. -/
def shear_operator : Operator PlanePoint none :=
  ⟨Option.map (fun x => (x.1, x.1 + x.2)), rfl⟩

/-- The nonabsorbing real plane, on which every bound is evaluated. -/
def finite_part : Set PlanePoint := Set.range some

theorem finite_part_eq_dom : finite_part = dom shear_operator := by
  ext x
  cases x <;> simp [finite_part, dom, shear_operator]

theorem coordinate_dist_is_extended (i : Fin 2) :
    ExtendedPseudoMetric PlanePoint none (coordinate_dist i) := by
  refine
    { nonabsorbing := ⟨some (0, 0), by simp⟩
      dist_self := ?_
      symm := ?_
      triangle := ?_
      isolate_bot := ?_ }
  · intro x
    cases x <;> simp [coordinate_dist]
  · intro x y
    cases x <;> cases y <;> simp [coordinate_dist, abs_sub_comm]
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp only [coordinate_dist]
    all_goals try simp
    rename_i x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)
  · intro x hx
    cases x with
    | none => exact (hx rfl).elim
    | some x => rfl

/--
OET anchor: h-b2cea3f1af318f29
同一算子的两组规范：两组距离均满足扩展伪度量公理。
-/
theorem gauge_families_are_extended :
    (∀ i, ExtendedPseudoMetric PlanePoint none (overlapping_dist i)) ∧
      (∀ i, ExtendedPseudoMetric PlanePoint none (coordinate_dist i)) := by
  refine ⟨?_, coordinate_dist_is_extended⟩
  intro i
  by_cases hi : i = 0
  · simpa [overlapping_dist, hi] using coordinate_dist_is_extended 0
  · have h0 := coordinate_dist_is_extended 0
    have h1 := coordinate_dist_is_extended 1
    refine
      { nonabsorbing := h0.nonabsorbing
        dist_self := ?_
        symm := ?_
        triangle := ?_
        isolate_bot := ?_ }
    · intro x
      simp [overlapping_dist, hi, h0.dist_self, h1.dist_self]
    · intro x y
      simp only [overlapping_dist, hi, if_false]
      rw [h0.symm x y, h1.symm x y]
    · intro x y z
      simp only [overlapping_dist, hi, if_false]
      calc
        _ ≤ (coordinate_dist 0 x y + coordinate_dist 0 y z) +
            (coordinate_dist 1 x y + coordinate_dist 1 y z) :=
          add_le_add (h0.triangle x y z) (h1.triangle x y z)
        _ = _ := by simp only [add_assoc, add_left_comm]
    · intro x hx
      simp [overlapping_dist, hi, h0.isolate_bot x hx, h1.isolate_bot x hx]

/-- Entries are input-first, so this represents the displayed diagonal matrix. -/
def diagonal_matrix : Fin 2 → Fin 2 → ENNReal := ![![1, 0], ![0, 2]]

/-- Input-first entries of the displayed matrix with rows `(1,0)` and `(1,1)`. -/
def triangular_matrix : Fin 2 → Fin 2 → ENNReal := ![![1, 1], ![0, 1]]

private theorem shear_second_bound (x y : ℝ × ℝ) :
    |(x.1 + x.2) - (y.1 + y.2)| ≤ |x.1 - y.1| + |x.2 - y.2| := by
  calc
    _ = |(x.1 - y.1) + (x.2 - y.2)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _

/--
OET anchor: h-b2cea3f1af318f29
同一算子的两组规范 (i)：重叠规范下，对角矩阵 `diag(1,2)` 是 Lip 证书。
-/
theorem overlapping_diagonal_lip :
    IsLipMatrix overlapping_dist shear_operator finite_part diagonal_matrix := by
  refine ⟨by rw [finite_part_eq_dom], ?_⟩
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ j
  fin_cases j
  · simp [overlapping_dist, coordinate_dist, read_coordinate, shear_operator,
      diagonal_matrix, Fin.sum_univ_two]
  · simp [overlapping_dist, coordinate_dist, read_coordinate, shear_operator,
      diagonal_matrix, Fin.sum_univ_two]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
      ← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    apply ENNReal.ofReal_le_ofReal
    have hab := shear_second_bound x y
    have hb := abs_nonneg (x.2 - y.2)
    linarith

/--
OET anchor: h-b2cea3f1af318f29
同一算子的两组规范 (ii)：坐标规范下，题解给出的三角矩阵是 Lip 证书。
-/
theorem coordinate_triangular_lip :
    IsLipMatrix coordinate_dist shear_operator finite_part triangular_matrix := by
  refine ⟨by rw [finite_part_eq_dom], ?_⟩
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ j
  fin_cases j
  · simp [coordinate_dist, read_coordinate, shear_operator, triangular_matrix,
      Fin.sum_univ_two]
  · simp [coordinate_dist, read_coordinate, shear_operator, triangular_matrix,
      Fin.sum_univ_two]
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (shear_second_bound x y)

/--
OET anchor: h-b2cea3f1af318f29
同一算子的两组规范 (ii)：任意扩展非负实数 Lip 证书的交叉条目至少为一。
点对为 `(1,0)` 与 `(0,0)`；不要求矩阵条目有限。
-/
theorem coordinate_cross_entry_lower_bound (M : Fin 2 → Fin 2 → ENNReal)
    (hM : IsLipMatrix coordinate_dist shear_operator finite_part M) :
    1 ≤ M 0 1 := by
  have h := hM.2 (some (1, 0)) ⟨(1, 0), rfl⟩ (some (0, 0)) ⟨(0, 0), rfl⟩ 1
  norm_num [coordinate_dist, read_coordinate, shear_operator, Fin.sum_univ_two] at h
  exact h

end

end formal_oet.vol_01.ch_02_operator_bounds.gauge_choice
