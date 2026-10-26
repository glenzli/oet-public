import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.model_radius
import formal_oet.vol_01.ch_04_operator_chain_calculus.local_equivalence_chain

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_04_operator_chain_calculus
noncomputable section
attribute [local instance] Classical.propDecidable

theorem linear_small_nonfiber {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup G] [Module ℝ G] (T : E →ₗ[ℝ] G) (hT : T ≠ 0)
    (y : E) (r : ℝ) (hr : 0 < r) : ∃ x, ‖x - y‖ < r ∧ T x ≠ T y := by
  have hv : ∃ v, T v ≠ 0 := by
    by_contra! h
    exact hT (LinearMap.ext h)
  obtain ⟨v, hv⟩ := hv
  let t := r / (2 * (‖v‖ + 1))
  have ht : 0 < t := div_pos hr (by positivity)
  have heq : t * (‖v‖ + 1) = r / 2 := by
    dsimp [t]
    field_simp
  have hnorm : ‖t • v‖ < r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    nlinarith [norm_nonneg v]
  refine ⟨y + t • v, by simpa using hnorm, ?_⟩
  intro h
  have hz : t • T v = 0 := by
    simpa only [map_add, map_smul, add_eq_left] using h
  exact hv ((smul_eq_zero.mp hz).resolve_left ht.ne')

variable {n : ℕ} [NeZero n]

def coordinate_affine_map (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n)
    (b : CoordinateVector n) (x : CoordinateVector n) := T x + b

def coordinate_linear_row (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n) (j : Fin n) :
    CoordinateVector n →ₗ[ℝ] ℝ := (LinearMap.proj j).comp T

/--
OET anchor: h-055e3702cf9c3930
On any open input set, the full-output affine radius is determined by the
linear part. A nonzero part admits arbitrarily small nonfiber displacements
that remain inside the input set.
-/
theorem affine_full_model_radius_on_open_set
    (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n) (b : CoordinateVector n)
    (Q : Set (CoordinateVector n)) (hQ : IsOpen Q)
    (y : CoordinateVector n) (hy : y ∈ Q) :
    full_model_radius (coordinate_affine_map T b) Q y = if T = 0 then ⊤ else 0 := by
  classical
  rw [full_model_radius_eq _ _ _ hy]
  split_ifs with hT
  · apply exact_constancy_radius_eq_top_of_constant
    intro x _
    simp [coordinate_affine_map, hT]
  · apply exact_constancy_radius_eq_zero_of_close_nonfiber
    intro r hr
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hQ y hy
    obtain ⟨x, hx, hne⟩ := linear_small_nonfiber T hT y
      (min δ r.toReal) (lt_min hδ (ENNReal.toReal_pos hr.1.ne' hr.2))
    refine ⟨x, hball (by simpa only [Metric.mem_ball, dist_eq_norm] using hx.trans_le (min_le_left _ _)),
      ?_, ?_⟩
    · rw [coordinate_sup_distance_eq_norm]
      exact (ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) hr.2).mpr
        (hx.trans_le (min_le_right _ _))
    · exact fun h => hne (add_right_cancel h)

/--
OET anchor: h-055e3702cf9c3930
On any open input set, each coordinate-strip radius is determined by the
entire output row, independently of the chosen input coordinate.
-/
theorem affine_coordinate_radius_on_open_set
    (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n) (b : CoordinateVector n)
    (Q : Set (CoordinateVector n)) (hQ : IsOpen Q)
    (y : CoordinateVector n) (hy : y ∈ Q) (i j : Fin n) :
    coordinate_model_radius (coordinate_affine_map T b) Q i j y =
      if coordinate_linear_row T j = 0 then ⊤ else 0 := by
  classical
  rw [coordinate_model_radius_eq _ _ _ _ _ hy]
  split_ifs with hT
  · apply exact_constancy_radius_eq_top_of_constant
    intro x _
    have hx := LinearMap.congr_fun hT x
    have hy := LinearMap.congr_fun hT y
    simp only [coordinate_linear_row, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.zero_apply] at hx hy
    simp [coordinate_affine_map, hx, hy]
  · apply exact_constancy_radius_eq_zero_of_close_nonfiber
    intro r hr
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hQ y hy
    obtain ⟨x, hx, hne⟩ := linear_small_nonfiber (coordinate_linear_row T j) hT y
      (min δ r.toReal) (lt_min hδ (ENNReal.toReal_pos hr.1.ne' hr.2))
    refine ⟨x, hball (by simpa only [Metric.mem_ball, dist_eq_norm] using hx.trans_le (min_le_left _ _)),
      ?_, ?_⟩
    · apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2).mpr
      exact (norm_le_pi_norm (x - y) i).trans_lt (hx.trans_le (min_le_right _ _))
    · intro h
      exact hne (add_right_cancel h)

/-- Whole-space specialization retained for existing callers. -/
theorem affine_full_model_radius (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n)
    (b y : CoordinateVector n) :
    full_model_radius (coordinate_affine_map T b) Set.univ y = if T = 0 then ⊤ else 0 :=
  affine_full_model_radius_on_open_set T b Set.univ isOpen_univ y (Set.mem_univ y)

/-- Whole-space coordinate specialization retained for existing callers. -/
theorem affine_coordinate_model_radius (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n)
    (b y : CoordinateVector n) (i j : Fin n) :
    coordinate_model_radius (coordinate_affine_map T b) Set.univ i j y =
      if coordinate_linear_row T j = 0 then ⊤ else 0 :=
  affine_coordinate_radius_on_open_set T b Set.univ isOpen_univ y (Set.mem_univ y) i j

/--
OET anchor: h-055e3702cf9c3930
The same open-domain classification for an actual operator that agrees with
an affine map on its nonempty comparison set, after taking the infimum over
basepoints. No network structure is used. -/
theorem affine_min_radius_on_open_set
    (φ : Operator (CoordinatePoint n Set.univ) none)
    (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n) (b : CoordinateVector n)
    (Q : Set (CoordinateVector n)) (hne : Q.Nonempty) (hQ : IsOpen Q)
    (hF : ∀ x ∈ Q, φ.func (full_coordinate_point x) = full_coordinate_point (coordinate_affine_map T b x))
    (i j : Fin n) :
    min_annihilation_radius coordinate_dist φ i (singleton_nonempty_finset j)
      (coordinate_model_set Set.univ Q) = if coordinate_linear_row T j = 0 then ⊤ else 0 := by
  classical
  have he : LocalEquivalent φ (full_model_operator (coordinate_affine_map T b) Q)
      (coordinate_model_set Set.univ Q) := by
    rintro z ⟨a, ha, rfl⟩
    have hh := hF a.val ha
    simpa [full_coordinate_point, full_model_operator, coordinate_model_operator, ha] using hh
  have hr (y : CoordinateVector n) (hy : y ∈ Q) :
      annihilation_radius coordinate_dist φ i (singleton_nonempty_finset j)
        (coordinate_model_set Set.univ Q) (full_coordinate_point y) =
          if coordinate_linear_row T j = 0 then ⊤ else 0 := by
    rw [local_equiv_annihilation_radius_eq coordinate_dist φ _ _ i _ _
      (by exact ⟨⟨y, Set.mem_univ y⟩, hy, rfl⟩) he]
    exact affine_coordinate_radius_on_open_set T b Q hQ y hy i j
  unfold min_annihilation_radius
  apply le_antisymm
  · obtain ⟨y, hy⟩ := hne
    exact (iInf₂_le (full_coordinate_point y) ⟨⟨y, Set.mem_univ y⟩, hy, rfl⟩).trans (hr y hy).le
  · apply le_iInf
    intro y
    apply le_iInf
    rintro ⟨a, ha, rfl⟩
    exact (hr a.val ha).ge

/--
OET anchor: h-055e3702cf9c3930
An affine level set has infinite coordinate radius at each of its basepoints.
This conclusion does not require openness or a zero output row.
-/
theorem affine_coordinate_radius_on_level_set
    (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n) (b : CoordinateVector n)
    (Q : Set (CoordinateVector n)) (j : Fin n) (c : ℝ)
    (hlevel : ∀ x ∈ Q, coordinate_linear_row T j x = c)
    (y : CoordinateVector n) (hy : y ∈ Q) (i : Fin n) :
    coordinate_model_radius (coordinate_affine_map T b) Q i j y = ⊤ := by
  rw [coordinate_model_radius_eq _ _ _ _ _ hy]
  apply exact_constancy_radius_eq_top_of_constant
  intro x hx
  change coordinate_linear_row T j x + b j = coordinate_linear_row T j y + b j
  rw [hlevel x hx, hlevel y hy]

/--
OET anchor: h-055e3702cf9c3930
The affine level-set boundary for an actual operator, after taking the
infimum over basepoints. It also holds for the empty set by the infimum convention. -/
theorem affine_level_set_min_radius
    (φ : Operator (CoordinatePoint n Set.univ) none)
    (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n) (b : CoordinateVector n)
    (Q : Set (CoordinateVector n))
    (hF : ∀ x ∈ Q, φ.func (full_coordinate_point x) = full_coordinate_point (coordinate_affine_map T b x))
    (j : Fin n) (c : ℝ) (hlevel : ∀ x ∈ Q, coordinate_linear_row T j x = c) (i : Fin n) :
    min_annihilation_radius coordinate_dist φ i (singleton_nonempty_finset j)
      (coordinate_model_set Set.univ Q) = ⊤ := by
  have he : LocalEquivalent φ (full_model_operator (coordinate_affine_map T b) Q)
      (coordinate_model_set Set.univ Q) := by
    rintro z ⟨a, ha, rfl⟩
    simpa [full_coordinate_point, full_model_operator, coordinate_model_operator, ha] using hF a.val ha
  apply top_unique
  apply le_iInf
  intro y
  apply le_iInf
  rintro ⟨a, ha, rfl⟩
  rw [local_equiv_annihilation_radius_eq coordinate_dist φ
    (full_model_operator (coordinate_affine_map T b) Q) (coordinate_model_set Set.univ Q)
    i (singleton_nonempty_finset j) (some a) ⟨a, ha, rfl⟩ he]
  change ⊤ ≤ coordinate_model_radius (coordinate_affine_map T b) Q i j a.val
  exact le_of_eq (affine_coordinate_radius_on_level_set T b Q j c hlevel a.val ha i).symm

/-- The coordinate projection `(s,t) ↦ (s,0)` as a linear map. -/
def coordinate_plane_projection : CoordinateVector 2 →ₗ[ℝ] CoordinateVector 2 where
  toFun x := ![x 0, 0]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp

/--
OET anchor: h-291a10c8f6ac11cb
The map `(s,t) ↦ (s,0)` has a vertical line as each full-output fiber,
while its original full-output OET annihilation radius is zero.
-/
theorem coordinate_projection_fiber_and_radius (y : CoordinateVector 2) :
    {x | coordinate_plane_projection x = coordinate_plane_projection y} =
      Set.range (fun t : ℝ => ![y 0, t]) ∧
    full_model_radius coordinate_plane_projection Set.univ y = 0 := by
  constructor
  · ext x
    constructor
    · intro hx
      have hzero : x 0 = y 0 := congrFun hx 0
      refine ⟨x 1, ?_⟩
      ext i
      fin_cases i <;> simp [hzero]
    · rintro ⟨t, rfl⟩
      simp [coordinate_plane_projection]
  · have hne : coordinate_plane_projection ≠ 0 := by
      intro h
      have hz := congrArg (fun T : CoordinateVector 2 →ₗ[ℝ] CoordinateVector 2 =>
        T ![1, 0] 0) h
      norm_num [coordinate_plane_projection] at hz
    have heq : coordinate_affine_map coordinate_plane_projection 0 =
        coordinate_plane_projection := by
      funext x
      simp [coordinate_affine_map]
    rw [← heq, affine_full_model_radius, if_neg hne]


end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
