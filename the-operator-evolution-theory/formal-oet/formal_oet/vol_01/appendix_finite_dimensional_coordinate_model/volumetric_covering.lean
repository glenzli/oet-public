import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Data.Nat.Lattice

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open MeasureTheory Module Set
open scoped BigOperators Function
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Volume packing with separation ≥ ε, so maximality gives OPEN ε-balls.
This also applies to dimension zero and to nonclosed bounded sets. -/
theorem separated_card_volume_bound (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ R)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → ε ≤ dist c d) :
    (s.card : ℝ) ≤ (1 + 2 * R / ε) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ := ε / 2
  let ρ := R + ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let U := ⋃ c ∈ s, Metric.ball c δ
  have hdisj : Set.Pairwise (s : Set E) (Disjoint on fun c => Metric.ball c δ) := by
    intro c hc d hd hcd
    apply Metric.ball_disjoint_ball
    have h := hsep c hc d hd hcd
    dsimp [δ]
    linarith
  have hU : U ⊆ Metric.ball (0 : E) ρ := by
    refine iUnion₂_subset fun c hc => ?_
    apply Metric.ball_subset_ball'
    rw [dist_zero_right]
    dsimp [δ, ρ]
    linarith [hs c hc]
  have hvol : (s.card : ENNReal) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (Metric.ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (Metric.ball 0 1) := by
    calc
      _ = μ U := by
        rw [show U = ⋃ c ∈ s, Metric.ball c δ from rfl,
          measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (Metric.ball (0 : E) ρ) := measure_mono hU
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hcancel := (ENNReal.mul_le_mul_iff_left
    (Metric.measure_ball_pos μ (0 : E) zero_lt_one).ne' measure_ball_lt_top.ne).mp hvol
  have hreal : (s.card : ℝ) * δ ^ finrank ℝ E ≤ ρ ^ finrank ℝ E := by
    simpa [ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] using
      ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hcancel
  have hquot := (le_div_iff₀ (pow_pos hδ (finrank ℝ E))).mpr hreal
  rw [← div_pow] at hquot
  have hratio : ρ / δ = 1 + 2 * R / ε := by dsimp [ρ, δ]; field_simp; ring
  simpa [hratio] using hquot

/-- A maximum-cardinality separated subset exists by the volume bound, without
compactness of S. Its own points provide an internal open-ball net. -/
theorem exists_internal_net_volume_bound (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    (S : Set E) (hS : ∀ x ∈ S, ‖x‖ ≤ R) :
    ∃ s : Finset E, InternalEpsilonNet edist (ENNReal.ofReal ε) S s ∧
      (s.card : ℝ) ≤ (1 + 2 * R / ε) ^ finrank ℝ E := by
  classical
  let good (s : Finset E) := (↑s : Set E) ⊆ S ∧
    ∀ c ∈ s, ∀ d ∈ s, c ≠ d → ε ≤ dist c d
  let K : Set ℕ := {k | ∃ s : Finset E, s.card = k ∧ good s}
  have hKne : K.Nonempty := ⟨0, ∅, by simp [good]⟩
  have hKbd : BddAbove K := by
    refine ⟨⌊(1 + 2 * R / ε) ^ finrank ℝ E⌋₊, ?_⟩
    rintro k ⟨s, rfl, hs⟩
    exact Nat.le_floor (separated_card_volume_bound R ε hR hε s
      (fun c hc => hS c (hs.1 hc)) hs.2)
  obtain ⟨s, hcard, hs⟩ := Nat.sSup_mem hKne hKbd
  have hcover : ∀ x ∈ S, ∃ c ∈ s, dist x c < ε := by
    intro x hx
    by_contra hnot
    push_neg at hnot
    have hxs : x ∉ s := by
      intro hxs
      have h := hnot x hxs
      simp only [dist_self] at h
      exact hε.not_ge h
    have hgood : good (insert x s) := by
      refine ⟨?_, ?_⟩
      · intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hx
        · exact hs.1 hy
      · intro c hc d hd hcd
        simp only [Finset.mem_insert] at hc hd
        rcases hc with rfl | hc <;> rcases hd with rfl | hd
        · exact (hcd rfl).elim
        · exact hnot d hd
        · simpa [dist_comm] using hnot c hc
        · exact hs.2 c hc d hd hcd
    have hle : (insert x s).card ≤ sSup K := le_csSup hKbd ⟨insert x s, rfl, hgood⟩
    rw [Finset.card_insert_of_notMem hxs, hcard] at hle
    omega
  refine ⟨s, ⟨hs.1, ?_⟩, separated_card_volume_bound R ε hR hε s
    (fun c hc => hS c (hs.1 hc)) hs.2⟩
  intro x hx
  obtain ⟨c, hc, hxc⟩ := hcover x hx
  exact ⟨c, hc, by simpa [edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] using hxc⟩

theorem internal_cover_volume_upper (R ε : ℝ) (hR : 0 ≤ R) (hε : 0 < ε)
    (S : Set E) (hS : ∀ x ∈ S, ‖x‖ ≤ R) :
    covering_number edist (ENNReal.ofReal ε) S ≤
      ENNReal.ofReal ((1 + 2 * R / ε) ^ finrank ℝ E) := by
  obtain ⟨s, hnet, hcard⟩ := exists_internal_net_volume_bound R ε hR hε S hS
  exact (iInf_le_of_le s (iInf_le_of_le hnet le_rfl)).trans
    (by simpa using ENNReal.ofReal_le_ofReal hcard)

/-- Lower bound for the same open-ball convention; no measurability of the
finite union beyond its actual balls is assumed. -/
theorem internal_closed_ball_volume_lower (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε) :
    ENNReal.ofReal ((R / ε) ^ finrank ℝ E) ≤
      covering_number edist (ENNReal.ofReal ε) (Metric.closedBall (0 : E) R) := by
  classical
  borelize E
  let μ : Measure E := Measure.addHaar
  apply le_iInf
  intro s
  apply le_iInf
  intro hnet
  have hsub : Metric.closedBall (0 : E) R ⊆ ⋃ c ∈ s, Metric.ball c ε := by
    intro x hx
    obtain ⟨c, hc, hxc⟩ := hnet.2 x hx
    refine mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    simpa [Metric.mem_ball, edist_dist, ENNReal.ofReal_lt_ofReal_iff hε] using hxc
  have hvol : ENNReal.ofReal (R ^ finrank ℝ E) * μ (Metric.ball 0 1) ≤
      ((s.card : ENNReal) * ENNReal.ofReal (ε ^ finrank ℝ E)) * μ (Metric.ball 0 1) := by
    calc
      _ = μ (Metric.closedBall (0 : E) R) := (μ.addHaar_closedBall _ hR.le).symm
      _ ≤ μ (⋃ c ∈ s, Metric.ball c ε) := measure_mono hsub
      _ ≤ ∑ c ∈ s, μ (Metric.ball c ε) := measure_biUnion_finset_le _ _
      _ = _ := by simp [μ.addHaar_ball_of_pos _ hε, mul_assoc]
  have hcancel := (ENNReal.mul_le_mul_iff_left
    (Metric.measure_ball_pos μ (0 : E) zero_lt_one).ne' measure_ball_lt_top.ne).mp hvol
  have hreal : R ^ finrank ℝ E ≤ (s.card : ℝ) * ε ^ finrank ℝ E := by
    have h := ENNReal.toReal_mono (by finiteness) hcancel
    simpa [ENNReal.toReal_ofReal (pow_nonneg hε.le _),
      ENNReal.toReal_ofReal (pow_nonneg hR.le _)] using h
  have hdiv := (div_le_iff₀ (pow_pos hε (finrank ℝ E))).mpr hreal
  rw [← div_pow] at hdiv
  simpa using ENNReal.ofReal_le_ofReal hdiv

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
