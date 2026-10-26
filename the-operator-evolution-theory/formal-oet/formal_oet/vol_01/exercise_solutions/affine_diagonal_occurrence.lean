import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.restricted_affine_geometry
import formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_classification

namespace formal_oet.vol_01.exercise_solutions.affine_diagonal_occurrence

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Plane := CoordinateVector 2
abbrev ModelPoint := CoordinatePoint 2 Set.univ

def diagonal (t : ℝ) : Plane := ![t, t]
def domain : Set Plane := diagonal '' Set.Icc (-1 : ℝ) 1
def model_domain : Set ModelPoint := coordinate_model_set Set.univ domain

def linear_part : Plane →ₗ[ℝ] Plane where
  toFun x := ![x 0 - x 1, x 0 + x 1]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp <;> ring

lemma diagonal_sub (t s : ℝ) : diagonal t - diagonal s = (t - s) • diagonal 1 := by
  ext i
  fin_cases i <;> simp [diagonal]

lemma diagonal_mem {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : diagonal t ∈ domain :=
  ⟨t, ht, rfl⟩

lemma domain_nonempty : domain.Nonempty := ⟨diagonal 0, diagonal_mem (by norm_num)⟩

lemma domain_convex : Convex ℝ domain := by
  rintro x ⟨t, ht, rfl⟩ y ⟨s, hs, rfl⟩ a b ha hb hab
  refine ⟨a * t + b * s, ?_, ?_⟩
  · exact (convex_Icc (-1 : ℝ) 1) ht hs ha hb hab
  · ext i
    fin_cases i <;> simp [diagonal]

lemma model_diagonal_mem {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    full_coordinate_point (diagonal t) ∈ model_domain :=
  ⟨⟨diagonal t, Set.mem_univ _⟩, diagonal_mem ht, rfl⟩

lemma model_domain_eq :
    model_domain = (fun t => full_coordinate_point (diagonal t)) '' Set.Icc (-1 : ℝ) 1 := by
  ext z
  constructor
  · rintro ⟨a, ⟨t, ht, heq⟩, rfl⟩
    refine ⟨t, ht, ?_⟩
    change some ⟨diagonal t, Set.mem_univ _⟩ = some a
    congr 1
    exact Subtype.ext heq
  · rintro ⟨t, ht, rfl⟩
    exact model_diagonal_mem ht

lemma linear_diagonal (t : ℝ) : linear_part (diagonal t) = ![0, 2 * t] := by
  ext i
  fin_cases i
  · simp [linear_part, diagonal]
  · simp [linear_part, diagonal]
    ring

/-- OET anchor: h-b3af1b7e2f078cb4
The actual segment has the diagonal line as its direction space. -/
theorem actual_direction : direction_span domain = Submodule.span ℝ {diagonal 1} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨x, ⟨t, ht, rfl⟩, y, ⟨s, hs, rfl⟩, rfl⟩
    rw [diagonal_sub]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    rintro v (rfl : v = diagonal 1)
    have h := sub_mem_direction_span (diagonal_mem (by norm_num : (1 : ℝ) ∈ Set.Icc (-1) 1))
      (diagonal_mem (by norm_num : (0 : ℝ) ∈ Set.Icc (-1) 1))
    simpa [diagonal] using h

/-- OET anchor: h-b3af1b7e2f078cb4
The first ambient row is nonzero despite vanishing on the actual direction. -/
theorem first_row_nonzero : coordinate_linear_row linear_part 0 ≠ 0 := by
  intro h
  have hh := LinearMap.congr_fun h (![1, 0] : Plane)
  norm_num [coordinate_linear_row, linear_part] at hh

theorem first_row_restriction_zero :
    (coordinate_linear_row linear_part 0).domRestrict (direction_span domain) = 0 := by
  apply (affine_row_constant_iff linear_part 0 domain 0).mp
  rintro x ⟨t, ht, rfl⟩ y ⟨s, hs, rfl⟩
  simp [coordinate_affine_map, linear_diagonal]

theorem second_row_restriction_nonzero :
    (coordinate_linear_row linear_part 1).domRestrict (direction_span domain) ≠ 0 := by
  intro h
  have hv : diagonal 1 ∈ direction_span domain := by
    rw [actual_direction]
    exact Submodule.subset_span (Set.mem_singleton _)
  have hh := LinearMap.congr_fun h ⟨diagonal 1, hv⟩
  norm_num [coordinate_linear_row, linear_part, diagonal, LinearMap.domRestrict] at hh

/-- OET anchor: h-b3af1b7e2f078cb4
The ambient-open row test cannot be used on this occurrence domain. -/
theorem domain_not_open : ¬ IsOpen domain := by
  intro h
  exact first_row_nonzero ((linear_restriction_zero_iff_of_isOpen
    (coordinate_linear_row linear_part 0) domain domain_nonempty h).mp
      first_row_restriction_zero)

/-- OET anchor: h-b3af1b7e2f078cb4
Both input diameters are computed from the actual OET coordinate domain. -/
theorem coordinate_diameter (i : Fin 2) :
    input_diameter coordinate_dist i model_domain = 2 := by
  apply le_antisymm
  · unfold input_diameter
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    rw [model_domain_eq] at hx
    rcases hx with ⟨t, ht, rfl⟩
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    rw [model_domain_eq] at hy
    rcases hy with ⟨s, hs, rfl⟩
    have habs : |t - s| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1, hs.2], by linarith [ht.2, hs.1]⟩
    have h := ENNReal.ofReal_le_ofReal habs
    fin_cases i <;> simpa [coordinate_dist, full_coordinate_point, diagonal] using h
  · have h := component_distance_le_input_diameter coordinate_dist i model_domain
      (full_coordinate_point (diagonal (-1))) (full_coordinate_point (diagonal 1))
      (model_diagonal_mem (by norm_num)) (model_diagonal_mem (by norm_num))
    fin_cases i <;> (norm_num [coordinate_dist, full_coordinate_point, diagonal] at h; exact h)

variable (φ : Operator ModelPoint none)
variable (hF : ∀ x ∈ domain, φ.func (full_coordinate_point x) = full_coordinate_point (linear_part x))
include hF

/-- OET anchor: h-b3af1b7e2f078cb4
The constant component set is exactly the first coordinate, for any actual
local operator realizing the exercise map on the specified occurrence domain. -/
theorem actual_constant_components : ConstComponent coordinate_dist φ model_domain = {0} := by
  ext j
  fin_cases j
  · rw [Set.mem_singleton_iff]
    constructor
    · intro _
      rfl
    · intro _ x hx y hy
      rw [model_domain_eq] at hx hy
      rcases hx with ⟨t, ht, rfl⟩
      rcases hy with ⟨s, hs, rfl⟩
      rw [hF _ (diagonal_mem ht), hF _ (diagonal_mem hs), linear_diagonal, linear_diagonal]
      simp [coordinate_dist, full_coordinate_point]
  · rw [Set.mem_singleton_iff]
    constructor
    · intro h
      have hh := h (full_coordinate_point (diagonal 0)) (model_diagonal_mem (by norm_num))
        (full_coordinate_point (diagonal 1)) (model_diagonal_mem (by norm_num))
      rw [hF _ (diagonal_mem (by norm_num)), hF _ (diagonal_mem (by norm_num)),
        linear_diagonal, linear_diagonal] at hh
      norm_num [coordinate_dist, full_coordinate_point] at hh
    · intro h
      norm_num at h

/-- OET anchor: h-b3af1b7e2f078cb4
The original uniform radii are derived from the actual convex domain. -/
theorem actual_radii (i : Fin 2) :
    min_annihilation_radius coordinate_dist φ i (singleton_nonempty_finset 0) model_domain = ⊤ ∧
    min_annihilation_radius coordinate_dist φ i (singleton_nonempty_finset 1) model_domain = 0 := by
  have hφ : ∀ x ∈ domain, φ.func (full_coordinate_point x) =
      full_coordinate_point (coordinate_affine_map linear_part 0 x) := by
    intro x hx
    simpa [coordinate_affine_map] using hF x hx
  have hr (j : Fin 2) := affine_min_radius_on_convex_set φ linear_part 0 domain
    domain_nonempty domain_convex hφ i j
  constructor
  · simpa [first_row_restriction_zero, model_domain] using hr 0
  · simpa [second_row_restriction_nonzero, model_domain] using hr 1

/-- OET anchor: h-b3af1b7e2f078cb4
At both thresholds equal to one, the two output labels are
(false,true) and (false,false), independently of the input coordinate. -/
theorem actual_thresholds (i : Fin 2) :
    operator_threshold_readout coordinate_dist φ model_domain
      (diameter_scale_family coordinate_dist) 1 1 i 0 = (false, true) ∧
    operator_threshold_readout coordinate_dist φ model_domain
      (diameter_scale_family coordinate_dist) 1 1 i 1 = (false, false) := by
  have hr := actual_radii φ hF i
  norm_num [operator_threshold_readout, diameter_scale_family, coordinate_diameter, hr.1, hr.2]

end
end formal_oet.vol_01.exercise_solutions.affine_diagonal_occurrence
