import formal_oet.vol_01.appendix_separating_gauge_specialization.finite_image
import formal_oet.vol_01.ch_03_operator_local_degeneracy.finite_counterexamples

namespace formal_oet.vol_01.exercise_solutions.infinite_radius

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.appendix_separating_gauge_specialization

noncomputable section

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

/--
OET anchor: h-38e12b6f9364127f
习题解答见 h-7e21c861157c9002。
统一全输出零化半径为无穷，当且仅当有限距离的输入点对具有相同像值。
半径定义只取有限正数；反向证明以任意大的自然数半径逼近无穷。
-/
theorem uniform_full_radius_eq_top_iff_finite_distance_outputs_equal
    (d : I → X → X → ENNReal) (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X)
    (hU : U.Nonempty) (hdom : U ⊆ dom φ) :
    metric_min_annihilation_radius (full_gauge_dist d) (full_gauge_dist d) φ U = ⊤ ↔
      ∀ x ∈ U, ∀ y ∈ U, full_gauge_dist d x y < ⊤ → φ.func x = φ.func y := by
  -- Retain the exercise's nonempty effective-domain convention.
  have _ := hU
  have _ := hdom
  constructor
  · intro htop x hx y hy hfinite
    exact equal_of_lt_uniform_full_output_radius d hsep φ U ⊤
      (by rw [htop]) hx hy hfinite
  · intro hfinite_equal
    apply top_unique
    unfold metric_min_annihilation_radius metric_min_annihilation_radius_on
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    rw [← ENNReal.iSup_natCast]
    apply iSup_le
    intro n
    cases n with
    | zero => simp
    | succ n =>
        have hr : FinitePositiveRadius ((n + 1 : ℕ) : ENNReal) :=
          ⟨Nat.cast_pos.mpr (Nat.succ_pos n), ENNReal.natCast_ne_top (n + 1)⟩
        apply le_iSup_of_le ((n + 1 : ℕ) : ENNReal)
        apply le_iSup_of_le hr
        have hball : {x | full_gauge_dist d x y < ((n + 1 : ℕ) : ENNReal)} ∩ U ⊆
            {x ∈ U | full_gauge_dist d (φ.func x) (φ.func y) = 0} := by
          intro x hx
          refine ⟨hx.2, ?_⟩
          apply (full_gauge_dist_eq_zero_iff d hd_self hsep _ _).mpr
          exact hfinite_equal x hx.2 y hy (lt_of_lt_of_le hx.1 le_top)
        exact le_iSup_of_le hball le_rfl

/--
OET anchor: h-38e12b6f9364127f
习题解答见 h-7e21c861157c9002。
若域内每一对点的全族距离均有限，无穷统一全输出零化半径推出点值常值。
不要求所有点对距离具有共同的有限上界。
-/
theorem constant_of_infinite_uniform_full_radius_of_pairwise_finite
    (d : I → X → X → ENNReal) (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X)
    (hU : U.Nonempty) (hdom : U ⊆ dom φ)
    (hfinite : ∀ x ∈ U, ∀ y ∈ U, full_gauge_dist d x y < ⊤)
    (hradius : metric_min_annihilation_radius
      (full_gauge_dist d) (full_gauge_dist d) φ U = ⊤) :
    ∃ z, ∀ x ∈ U, φ.func x = z := by
  obtain ⟨y, hy⟩ := hU
  refine ⟨φ.func y, ?_⟩
  intro x hx
  exact (uniform_full_radius_eq_top_iff_finite_distance_outputs_equal
    d hd_self hsep φ U ⟨y, hy⟩ hdom).mp hradius x hx y hy (hfinite x hx y hy)

/-- The Chapter 3 infinite-distance example is a valid gauge on the whole carrier. -/
theorem infinite_counter_gauge_is_extended (i : Unit) :
    ExtendedPseudoMetric ThreePoint ThreePoint.bottom (infinite_counter_distance i) := by
  cases i
  obtain ⟨hself, hsymm, htriangle, hbot, _⟩ := infinite_counter_distance_is_extended
  exact
    { nonabsorbing := ⟨ThreePoint.a, by decide⟩
      dist_self := hself
      symm := hsymm
      triangle := htriangle
      isolate_bot := hbot }

/--
OET anchor: h-38e12b6f9364127f
习题解答见 h-7e21c861157c9002。
CH3 的无穷离散距离反例满足族分离性。
-/
theorem infinite_counter_gauge_is_separating : IsSeparating infinite_counter_distance := by
  intro x y hzero
  have h := hzero ()
  cases x <;> cases y <;>
    simp_all [infinite_counter_distance, top_pullback_distance, three_point_code]

private theorem infinite_full_distance_eq_component (x y : ThreePoint) :
    full_gauge_dist infinite_counter_distance x y = infinite_counter_distance () x y := by
  simp [full_gauge_dist, comp_pseudo_metric, full_nonempty_finset]

/--
OET anchor: h-38e12b6f9364127f
习题解答见 h-7e21c861157c9002。
族分离并不消除无穷距离点对：两非吸收点间距离为无穷的恒等算子，
在合法非空域上具有无穷统一全输出零化半径，却不是常值。
-/
theorem separating_infinite_radius_nonconstant_counterexample :
    (∀ i, ExtendedPseudoMetric ThreePoint ThreePoint.bottom (infinite_counter_distance i)) ∧
      IsSeparating infinite_counter_distance ∧
      three_point_domain.Nonempty ∧
      three_point_domain ⊆ dom identity_counter_operator ∧
      full_gauge_dist infinite_counter_distance ThreePoint.a ThreePoint.b = ⊤ ∧
      metric_min_annihilation_radius
        (full_gauge_dist infinite_counter_distance) (full_gauge_dist infinite_counter_distance)
        identity_counter_operator three_point_domain = ⊤ ∧
      ¬ ∃ z, ∀ x ∈ three_point_domain, identity_counter_operator.func x = z := by
  obtain ⟨hU, hdom⟩ := identity_counter_domain
  refine ⟨infinite_counter_gauge_is_extended, infinite_counter_gauge_is_separating,
    hU, hdom, ?_, ?_, ?_⟩
  · rw [infinite_full_distance_eq_component]
    exact infinite_counter_distance_is_extended.2.2.2.2
  · apply (uniform_full_radius_eq_top_iff_finite_distance_outputs_equal
      infinite_counter_distance (fun i x => (infinite_counter_gauge_is_extended i).dist_self x)
      infinite_counter_gauge_is_separating identity_counter_operator three_point_domain
      hU hdom).mpr
    intro x _ y _ hfinite
    rw [infinite_full_distance_eq_component] at hfinite
    cases x <;> cases y <;>
      simp_all [infinite_counter_distance, top_pullback_distance, three_point_code,
        identity_counter_operator]
  · rintro ⟨z, hz⟩
    have ha := hz ThreePoint.a (by simp [three_point_domain])
    have hb := hz ThreePoint.b (by simp [three_point_domain])
    have hab := ha.trans hb.symm
    simp [identity_counter_operator] at hab

end

end formal_oet.vol_01.exercise_solutions.infinite_radius
