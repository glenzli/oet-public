import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.coordinate_topology
import Mathlib.Topology.Order.Compact

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open scoped BigOperators
noncomputable section
variable {n : ℕ} [NeZero n]

/-- Finite-dimensional norm equivalence for the actual selected norm, proved
from the coordinate basis and compactness of the ordinary unit sphere. -/
theorem definite_seminorm_equivalence_constants (p : Seminorm ℝ (CoordinateVector n))
    (hp : ∀ v, p v = 0 → v = 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ (∀ v, a * ‖v‖ ≤ p v) ∧ (∀ v, p v ≤ b * ‖v‖) := by
  classical
  let b := (∑ i : Fin n, p (Pi.single i 1)) + 1
  have hb : 0 < b := by dsimp [b]; positivity
  have hsum (s : Finset (Fin n)) (f : Fin n → CoordinateVector n) :
      p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
    induction s using Finset.induction with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)
  have hupper (v : CoordinateVector n) : p v ≤ b * ‖v‖ := by
    have hdecomp : v = ∑ i : Fin n, v i • (Pi.single i 1 : CoordinateVector n) := by
      ext j
      simp [Pi.single_apply]
    calc
      p v = p (∑ i : Fin n, v i • (Pi.single i 1 : CoordinateVector n)) := congrArg p hdecomp
      _ ≤ ∑ i : Fin n, p (v i • (Pi.single i 1 : CoordinateVector n)) := hsum _ _
      _ = ∑ i : Fin n, ‖v i‖ * p (Pi.single i 1) := by simp_rw [map_smul_eq_mul]
      _ ≤ ∑ i : Fin n, ‖v‖ * p (Pi.single i 1) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v i) (apply_nonneg p _)
      _ = (∑ i : Fin n, p (Pi.single i 1)) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]
      _ ≤ b * ‖v‖ := by dsimp [b]; nlinarith [norm_nonneg v]
  have hcont : Continuous p := by
    have hlip : LipschitzWith ⟨b, hb.le⟩ p := LipschitzWith.of_dist_le_mul fun x y => by
      simpa [dist_eq_norm] using (p.norm_sub_map_le_sub x y).trans (hupper (x - y))
    exact hlip.continuous
  have hsne : (Metric.sphere (0 : CoordinateVector n) 1).Nonempty := by
    refine ⟨Pi.single (0 : Fin n) 1, ?_⟩
    simp [Metric.mem_sphere, dist_zero_right, Pi.norm_single]
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : CoordinateVector n) 1).exists_isMinOn hsne hcont.continuousOn
  have hunorm : ‖u‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hu
  have ha : 0 < p u := by
    apply lt_of_le_of_ne (apply_nonneg p _)
    intro hz
    have huz := hp u hz.symm
    rw [huz, norm_zero] at hunorm
    norm_num at hunorm
  refine ⟨p u, b, ha, hb, ?_, hupper⟩
  intro v
  by_cases hv : v = 0
  · simp [hv]
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hwnorm : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm), inv_mul_cancel₀ hvnorm.ne']
  have hminv := hmin (show ‖v‖⁻¹ • v ∈ Metric.sphere (0 : CoordinateVector n) 1 by
    simpa [Metric.mem_sphere, dist_zero_right] using hwnorm)
  change p u ≤ p (‖v‖⁻¹ • v) at hminv
  rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvnorm)] at hminv
  have h := mul_le_mul_of_nonneg_right hminv hvnorm.le
  simpa [mul_assoc, mul_comm, mul_left_comm, hvnorm.ne'] using h

/--
OET anchor: h-5cd365cd756cb93e
The topology/completeness/compactness conclusions apply to every actual norm:
norm-equivalence constants are derived, not required from the caller.
-/
theorem arbitrary_norm_topology_and_completeness {A : Set (CoordinateVector n)}
    (hA : A.Nonempty) (p : Seminorm ℝ (CoordinateVector n)) (hp : ∀ v, p v = 0 → v = 0) :
    coordinate_gauge_topology hA = (coordinate_full_space hA).toUniformSpace.toTopologicalSpace ∧
    (coordinate_full_space hA).toUniformSpace.toTopologicalSpace =
      (coordinate_norm_space (A := A) p).toUniformSpace.toTopologicalSpace ∧
    (@IsComplete _ (seminorm_uniformity p) A ↔ IsClosed A) ∧
    (@IsCompact _ (seminorm_uniformity p).toTopologicalSpace A ↔
      IsClosed A ∧ Bornology.IsBounded A) := by
  obtain ⟨a, b, ha, hb, hlower, hupper⟩ := definite_seminorm_equivalence_constants p hp
  have htop := coordinate_and_actual_norm_topologies hA p a b ha hb hlower hupper
  have hgeom := actual_norm_complete_compact_criteria p a b ha hb hlower hupper A
  exact ⟨htop.1, htop.2, hgeom.1, hgeom.2⟩

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
