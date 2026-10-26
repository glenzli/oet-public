import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.coordinate_gauge
import formal_oet.vol_01.ch_01_foundations.metric_entropy

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model

open formal_oet.vol_01.ch_01_foundations

noncomputable section

/-- Ball containment sufficient to compare two internal covering numbers. -/
theorem covering_number_le_of_ball_containment {X : Type}
    (d_small d_large : X → X → ENNReal)
    (r_small r_large : ENNReal) (S : Set X)
    (hball : ∀ x y, d_small x y < r_small → d_large x y < r_large) :
    covering_number d_large r_large S ≤ covering_number d_small r_small S := by
  unfold covering_number
  apply le_iInf
  intro centers
  apply le_iInf
  intro hnet
  have hnet' : InternalEpsilonNet d_large r_large S centers := by
    exact ⟨hnet.1, fun x hx ↦ by
      rcases hnet.2 x hx with ⟨c, hc, hxc⟩
      exact ⟨c, hc, hball x c hxc⟩⟩
  exact iInf_le_of_le centers (iInf_le_of_le hnet' le_rfl)

/--
The standard norm-equivalence ball inclusions used by the quantitative
comparison. The radii are named explicitly so the certificate does not hide
any OET conclusion.
-/
structure NormBallComparisonCertificate (X : Type)
    (d_full d_star : X → X → ENNReal)
    (radius_over_b radius radius_over_a : ENNReal) where
  full_small_to_star :
    ∀ x y, d_full x y < radius_over_b → d_star x y < radius
  star_to_full_large :
    ∀ x y, d_star x y < radius → d_full x y < radius_over_a

/--
Auxiliary covering transfer. The actual norm-bound instance is proved in norm_ball_bridge.lean.
**命题（范数球与覆盖数的比较）**
由范数等价的两个球包含推出同一集合的两侧内覆盖数界。
-/
theorem norm_ball_and_covering_number_comparison {X : Type}
    (d_full d_star : X → X → ENNReal)
    (radius_over_b radius radius_over_a : ENNReal) (S : Set X)
    (h : NormBallComparisonCertificate X d_full d_star
      radius_over_b radius radius_over_a) :
    (∀ x, ball d_full x radius_over_b ⊆ ball d_star x radius) ∧
    (∀ x, ball d_star x radius ⊆ ball d_full x radius_over_a) ∧
    covering_number d_full radius_over_a S ≤
      covering_number d_star radius S ∧
    covering_number d_star radius S ≤
      covering_number d_full radius_over_b S := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hy
    exact h.full_small_to_star y x hy
  · intro x y hy
    exact h.star_to_full_large y x hy
  · exact covering_number_le_of_ball_containment d_star d_full
      radius radius_over_a S h.star_to_full_large
  · exact covering_number_le_of_ball_containment d_full d_star
      radius_over_b radius S h.full_small_to_star


end

end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
