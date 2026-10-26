import formal_oet.vol_01.appendix_separating_gauge_specialization.finite_image
import formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_examples
import Mathlib.Tactic

namespace formal_oet.vol_01.exercise_solutions.finite_image_boundaries

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.appendix_separating_gauge_specialization

noncomputable section

abbrev distance := threshold_examples.real_distance
def gauges (_ : Unit) := distance
def identity_operator : Operator (Option ℝ) none := ⟨id, rfl⟩

theorem distance_is_extended : ExtendedPseudoMetric (Option ℝ) none distance :=
  threshold_examples.real_distance_is_extended

theorem gauges_separating : IsSeparating gauges := by
  intro x y h
  have hz := h ()
  cases x <;> cases y <;> simp only [gauges, threshold_examples.real_distance] at hz
  · rfl
  · simp at hz
  · simp at hz
  · congr 1
    exact sub_eq_zero.mp (abs_eq_zero.mp
      (le_antisymm (ENNReal.ofReal_eq_zero.mp hz) (abs_nonneg _)))

theorem full_distance (x y : Option ℝ) : full_gauge_dist gauges x y = distance x y := by
  simp [full_gauge_dist, comp_pseudo_metric, full_nonempty_finset, gauges]

theorem full_distance_eq : full_gauge_dist gauges = distance :=
  funext (fun x => funext (full_distance x))

def reciprocal (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)
def reciprocal_gap (n : ℕ) : ℝ := 1 / ((n + 1 : ℝ) * (n + 2 : ℝ))
def reciprocal_domain : Set (Option ℝ) := Set.range (fun n => some (reciprocal n))
def integer_domain : Set (Option ℝ) := Set.range (fun n : ℕ => some (n + 1 : ℝ))

theorem reciprocal_pos (n : ℕ) : 0 < reciprocal n := by unfold reciprocal; positivity
theorem reciprocal_gap_pos (n : ℕ) : 0 < reciprocal_gap n := by
  unfold reciprocal_gap
  positivity

theorem reciprocal_antitone : Antitone reciprocal := by
  intro m n hmn
  exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hmn 1)

theorem reciprocal_gap_antitone : Antitone reciprocal_gap := by
  intro m n hmn
  apply one_div_le_one_div_of_le (by positivity)
  have h : (m : ℝ) ≤ n := by exact_mod_cast hmn
  nlinarith

theorem reciprocal_succ_difference (n : ℕ) :
    reciprocal n - reciprocal (n + 1) = reciprocal_gap n := by
  unfold reciprocal reciprocal_gap
  push_cast
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem reciprocal_nearest_gap {m n : ℕ} (hmn : m ≠ n) :
    reciprocal_gap n ≤ |reciprocal m - reciprocal n| := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hle : reciprocal n ≤ reciprocal (m + 1) :=
      reciprocal_antitone (Nat.succ_le_of_lt hlt)
    have hgap := reciprocal_gap_antitone (Nat.le_of_lt hlt)
    rw [← reciprocal_succ_difference m] at hgap
    exact hgap.trans ((sub_le_sub_left hle _).trans (le_abs_self _))
  · have hle : reciprocal m ≤ reciprocal (n + 1) :=
      reciprocal_antitone (Nat.succ_le_of_lt hgt)
    rw [abs_sub_comm, ← reciprocal_succ_difference n]
    exact (sub_le_sub_left hle _).trans (le_abs_self _)

theorem reciprocal_injective : Function.Injective reciprocal := by
  intro m n heq
  by_contra hmn
  have hgap := reciprocal_nearest_gap hmn
  rw [heq, sub_self, abs_zero] at hgap
  exact (not_le_of_gt (reciprocal_gap_pos n)) hgap

private theorem identity_radius_eq_nearest
    (U : Set (Option ℝ)) (y : Option ℝ) (a : ENNReal)
    (ha : FinitePositiveRadius a)
    (hlower : ∀ x ∈ U, x ≠ y → a ≤ distance x y)
    (hwitness : ∃ x ∈ U, distance x y = a) :
    metric_annihilation_radius distance distance identity_operator U y = a := by
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro _hr
    apply iSup_le
    intro hball
    by_contra hnot
    have har : a < r := lt_of_not_ge hnot
    obtain ⟨x, hx, hxy⟩ := hwitness
    have hz := (hball ⟨by simpa [hxy] using har, hx⟩).2
    change distance x y = 0 at hz
    rw [hxy] at hz
    exact (ne_of_gt ha.1) hz
  · apply le_iSup_of_le a
    apply le_iSup_of_le ha
    have hball : {x | distance x y < a} ∩ U ⊆
        {x ∈ U | distance (identity_operator.func x) (identity_operator.func y) = 0} := by
      intro x hx
      refine ⟨hx.2, ?_⟩
      have hxy : x = y := by
        by_contra hne
        exact (not_lt_of_ge (hlower x hx.2 hne)) hx.1
      subst x
      exact distance_is_extended.dist_self y
    exact le_iSup_of_le hball le_rfl

/-- OET anchor: h-93e134ff76be8bc0
倒数点的零化半径恰好等于其与最近邻的距离。 -/
theorem reciprocal_point_radius (n : ℕ) :
    metric_annihilation_radius distance distance identity_operator reciprocal_domain
      (some (reciprocal n)) = ENNReal.ofReal (reciprocal_gap n) := by
  apply identity_radius_eq_nearest
  · exact ⟨ENNReal.ofReal_pos.mpr (reciprocal_gap_pos n), ENNReal.ofReal_ne_top⟩
  · rintro x ⟨m, rfl⟩ hne
    apply ENNReal.ofReal_le_ofReal
    apply reciprocal_nearest_gap
    intro hmn
    subst m
    exact hne rfl
  · refine ⟨some (reciprocal (n + 1)), ⟨n + 1, rfl⟩, ?_⟩
    change ENNReal.ofReal |reciprocal (n + 1) - reciprocal n| = _
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (reciprocal_antitone (by omega))),
      reciprocal_succ_difference]


/-- OET anchor: h-93e134ff76be8bc0
倒数点域中的逐点半径为正，但统一半径为零。 -/
theorem reciprocal_uniform_radius :
    metric_min_annihilation_radius distance distance identity_operator reciprocal_domain = 0 := by
  by_contra hne
  have hpos := bot_lt_iff_ne_bot.mpr hne
  obtain ⟨ε, _, hε, hεmin⟩ := ENNReal.lt_iff_exists_real_btwn.mp hpos
  have hεpos : 0 < ε := ENNReal.ofReal_pos.mp hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hεpos
  have hgap : reciprocal_gap n ≤ reciprocal n := by
    rw [← reciprocal_succ_difference]
    linarith [reciprocal_pos (n + 1)]
  have hmin : metric_min_annihilation_radius distance distance identity_operator
      reciprocal_domain ≤ metric_annihilation_radius distance distance identity_operator
        reciprocal_domain (some (reciprocal n)) :=
    iInf_le_of_le _ (iInf_le_of_le (show some (reciprocal n) ∈ reciprocal_domain from ⟨n, rfl⟩)
      le_rfl)
  rw [reciprocal_point_radius] at hmin
  have hsmall : ENNReal.ofReal (reciprocal_gap n) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hεpos).mpr (lt_of_le_of_lt hgap hn)
  exact (not_lt_of_ge hmin) (hsmall.trans hεmin)

/-- OET anchor: h-93e134ff76be8bc0
对每个有限正半径，以有限个倒数点为内部中心即可覆盖整个倒数点域。 -/
theorem reciprocal_finite_internal_net (r : ENNReal) (hr : FinitePositiveRadius r) :
    ∃ S : Finset (Option ℝ), InternalEpsilonNet distance r reciprocal_domain S := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (ENNReal.toReal_pos hr.1.ne' hr.2)
  let S := (Finset.range (N + 1)).image (fun n => some (reciprocal n))
  refine ⟨S, ?_, ?_⟩
  · intro x hx
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨n, rfl⟩
  · rintro x ⟨n, rfl⟩
    by_cases hn : n ≤ N
    · refine ⟨some (reciprocal n), Finset.mem_image.mpr ⟨n, ?_, rfl⟩, ?_⟩
      · exact Finset.mem_range.mpr (by omega)
      · simpa only [distance_is_extended.dist_self] using hr.1
    · refine ⟨some (reciprocal N), Finset.mem_image.mpr ⟨N, ?_, rfl⟩, ?_⟩
      · exact Finset.mem_range.mpr (by omega)
      · change ENNReal.ofReal |reciprocal n - reciprocal N| < r
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2).mpr
        rw [abs_sub_comm, abs_of_nonneg
          (sub_nonneg.mpr (reciprocal_antitone (by omega)))]
        have hN' : reciprocal N < r.toReal := hN
        linarith [reciprocal_pos n]

/-- OET anchor: h-93e134ff76be8bc0
原定义中的内部覆盖数在倒数点域的每个有限正尺度上均有限。 -/
theorem reciprocal_covering_number_finite (r : ENNReal) (hr : FinitePositiveRadius r) :
    covering_number (full_gauge_dist gauges) r reciprocal_domain < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hnone := (covering_number_eq_top_iff (full_gauge_dist gauges) r reciprocal_domain).mp htop
  apply hnone
  simpa only [full_distance_eq] using reciprocal_finite_internal_net r hr

/-- OET anchor: h-93e134ff76be8bc0 倒数点域上的恒等映射具有无限像。 -/
theorem reciprocal_image_infinite : (identity_operator.func '' reciprocal_domain).Infinite := by
  have hU : reciprocal_domain.Infinite :=
    Set.infinite_range_of_injective (fun _ _ h => reciprocal_injective (Option.some.inj h))
  simpa only [identity_operator, Set.image_id] using hU

private theorem integer_nearest_gap {m n : ℕ} (hmn : m ≠ n) :
    (1 : ℝ) ≤ |(m + 1 : ℝ) - (n + 1 : ℝ)| := by
  rcases lt_or_gt_of_ne hmn with hlt | hgt
  · have hle : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hlt
    have habs := neg_le_abs ((m + 1 : ℝ) - (n + 1 : ℝ))
    linarith
  · have hle : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hgt
    have habs := le_abs_self ((m + 1 : ℝ) - (n + 1 : ℝ))
    linarith

/-- OET anchor: h-93e134ff76be8bc0 正整数域中的每个点恰有零化半径 1。 -/
theorem integer_point_radius (n : ℕ) :
    metric_annihilation_radius distance distance identity_operator integer_domain
      (some (n + 1 : ℝ)) = 1 := by
  apply identity_radius_eq_nearest
  · exact ⟨by norm_num, by norm_num⟩
  · rintro x ⟨m, rfl⟩ hne
    change (1 : ENNReal) ≤ ENNReal.ofReal |(m + 1 : ℝ) - (n + 1 : ℝ)|
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply integer_nearest_gap
    intro hmn
    subst m
    exact hne rfl
  · refine ⟨some ((n + 1 : ℕ) + 1 : ℝ), ⟨n + 1, rfl⟩, ?_⟩
    change ENNReal.ofReal |((n + 1 : ℕ) + 1 : ℝ) - (n + 1 : ℝ)| = 1
    push_cast
    ring_nf
    norm_num

/-- OET anchor: h-93e134ff76be8bc0 正整数域上的统一零化半径为 1。 -/
theorem integer_uniform_radius :
    metric_min_annihilation_radius distance distance identity_operator integer_domain = 1 := by
  apply le_antisymm
  · have hmin : metric_min_annihilation_radius distance distance identity_operator
        integer_domain ≤ metric_annihilation_radius distance distance identity_operator
          integer_domain (some (0 + 1 : ℝ)) :=
      iInf_le_of_le _ (iInf_le_of_le (show some (0 + 1 : ℝ) ∈ integer_domain from ⟨0, by norm_num⟩)
        le_rfl)
    have hpoint : metric_annihilation_radius distance distance identity_operator
        integer_domain (some (0 + 1 : ℝ)) = 1 := by
      simpa using integer_point_radius 0
    exact hmin.trans (le_of_eq hpoint)
  · apply le_iInf
    rintro x
    apply le_iInf
    rintro ⟨n, rfl⟩
    exact le_of_eq (integer_point_radius n).symm

/-- OET anchor: h-93e134ff76be8bc0 正整数域上的恒等映射具有无限像。 -/
theorem integer_image_infinite : (identity_operator.func '' integer_domain).Infinite := by
  have hinj : Function.Injective (fun n : ℕ => some (n + 1 : ℝ)) := by
    intro m n h
    have heq : (m : ℝ) = n := by linarith [Option.some.inj h]
    exact_mod_cast heq
  have hU : integer_domain.Infinite := Set.infinite_range_of_injective hinj
  simpa only [identity_operator, Set.image_id] using hU

private theorem integer_domain_nonempty : integer_domain.Nonempty :=
  ⟨some (0 + 1 : ℝ), ⟨0, by norm_num⟩⟩

private theorem integer_domain_subset_dom : integer_domain ⊆ dom identity_operator := by
  rintro x ⟨n, rfl⟩
  simp [dom, identity_operator]

/-- OET anchor: h-93e134ff76be8bc0
正整数域在半径 1 处没有有限内覆盖，故按原定义其覆盖数为无穷。 -/
theorem integer_covering_number_top :
    covering_number (full_gauge_dist gauges) 1 integer_domain = ⊤ := by
  apply (covering_number_eq_top_iff _ _ _).mpr
  rintro ⟨S, hS⟩
  have hradius : (1 : ENNReal) ≤ metric_min_annihilation_radius
      (full_gauge_dist gauges) (full_gauge_dist gauges) identity_operator integer_domain := by
    simpa only [full_distance_eq] using (le_of_eq integer_uniform_radius.symm)
  obtain ⟨_, hfinite, _⟩ := finite_image_of_uniform_full_output_radius gauges gauges_separating
    identity_operator integer_domain integer_domain_nonempty integer_domain_subset_dom 1
    ⟨by norm_num, by norm_num⟩ hradius S hS
  exact integer_image_infinite hfinite


/-- OET anchor: h-93e134ff76be8bc0
两个反例共同使用真实的分离扩展规范，且各自输入域非空并包含于恒等算子的定义域。 -/
theorem boundary_models_valid :
    (∀ i, ExtendedPseudoMetric (Option ℝ) none (gauges i)) ∧ IsSeparating gauges ∧
    reciprocal_domain.Nonempty ∧ reciprocal_domain ⊆ dom identity_operator ∧
    integer_domain.Nonempty ∧ integer_domain ⊆ dom identity_operator := by
  refine ⟨fun _ => distance_is_extended, gauges_separating,
    ⟨some (reciprocal 0), ⟨0, rfl⟩⟩, ?_, integer_domain_nonempty, integer_domain_subset_dom⟩
  rintro x ⟨n, rfl⟩
  simp [dom, identity_operator]

/-- OET anchor: h-93e134ff76be8bc0
单分量输入、全输出子族的原始零化半径与计算所得逐点半径精确一致且为正。 -/
theorem reciprocal_full_output_point_radius (n : ℕ) :
    annihilation_radius gauges identity_operator () full_nonempty_finset reciprocal_domain
      (some (reciprocal n)) = ENNReal.ofReal (reciprocal_gap n) ∧
    0 < annihilation_radius gauges identity_operator () full_nonempty_finset reciprocal_domain
      (some (reciprocal n)) := by
  have heq : annihilation_radius gauges identity_operator () full_nonempty_finset
      reciprocal_domain (some (reciprocal n)) = ENNReal.ofReal (reciprocal_gap n) := by
    rw [annihilation_radius_eq_metric]
    change metric_annihilation_radius distance (full_gauge_dist gauges) identity_operator
      reciprocal_domain (some (reciprocal n)) = _
    rw [full_distance_eq]
    exact reciprocal_point_radius n
  exact ⟨heq, heq ▸ ENNReal.ofReal_pos.mpr (reciprocal_gap_pos n)⟩


/-- OET anchor: h-93e134ff76be8bc0
两个实际域上的统一半径使用正文单输入分量、全输出子族的原始定义。 -/
theorem full_output_uniform_radii :
    min_annihilation_radius gauges identity_operator () full_nonempty_finset
      reciprocal_domain = 0 ∧
    min_annihilation_radius gauges identity_operator () full_nonempty_finset
      integer_domain = 1 := by
  constructor
  · rw [min_annihilation_radius_eq_metric]
    change metric_min_annihilation_radius distance (full_gauge_dist gauges) identity_operator
      reciprocal_domain = 0
    rw [full_distance_eq]
    exact reciprocal_uniform_radius
  · rw [min_annihilation_radius_eq_metric]
    change metric_min_annihilation_radius distance (full_gauge_dist gauges) identity_operator
      integer_domain = 1
    rw [full_distance_eq]
    exact integer_uniform_radius

end

end formal_oet.vol_01.exercise_solutions.finite_image_boundaries
