import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.model_radius

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open Filter Topology
noncomputable section

theorem exact_radius_pos_gives_locally_constant
    {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → G) (Q : Set E) (hQ : IsOpen Q) (y : E) (hy : y ∈ Q)
    (hpos : 0 < exact_constancy_radius (fun x y => ENNReal.ofReal ‖x - y‖) F Q y) :
    F =ᶠ[𝓝 y] fun _ => F y := by
  obtain ⟨r, hr⟩ := lt_iSup_iff.mp hpos
  obtain ⟨hrpos, hr⟩ := lt_iSup_iff.mp hr
  obtain ⟨hgood, _⟩ := lt_iSup_iff.mp hr
  have hreal : 0 < r.toReal := ENNReal.toReal_pos hrpos.1.ne' hrpos.2
  filter_upwards [hQ.mem_nhds hy, Metric.ball_mem_nhds y hreal] with x hx hxy
  apply hgood x hx
  apply (ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) hrpos.2).mpr
  simpa only [Metric.mem_ball, dist_eq_norm] using hxy

variable {n : ℕ} [NeZero n]

/--
OET anchor: h-055e3702cf9c3930
A positive original OET full-output radius gives actual neighborhood constancy,
so uniqueness of the Frechet derivative forces the actual derivative to vanish.
-/
theorem full_model_radius_pos_derivative_zero
    (F : CoordinateVector n → CoordinateVector n) (Q : Set (CoordinateVector n))
    (hQ : IsOpen Q) (y : CoordinateVector n) (hy : y ∈ Q)
    (D : CoordinateVector n →L[ℝ] CoordinateVector n) (hD : HasFDerivAt F D y)
    (hpos : 0 < full_model_radius F Q y) : D = 0 := by
  rw [full_model_radius_eq F Q y hy] at hpos
  have hd : coordinate_sup_distance (n := n) = fun x y => ENNReal.ofReal ‖x - y‖ := by
    funext x y; exact coordinate_sup_distance_eq_norm x y
  rw [hd] at hpos
  have heq := exact_radius_pos_gives_locally_constant F Q hQ y hy hpos
  rw [← hD.fderiv, heq.fderiv_eq]
  simp

def coordinate_quadratic (x : CoordinateVector 1) : CoordinateVector 1 := fun _ => x 0 ^ 2

/--
OET anchor: h-055e3702cf9c3930
The literal one-dimensional quadratic has derivative zero at the origin.
-/
theorem coordinate_quadratic_derivative_zero :
    HasFDerivAt (𝕜 := ℝ) coordinate_quadratic 0 0 := by
  let p : CoordinateVector 1 →L[ℝ] ℝ := ContinuousLinearMap.proj 0
  have hp := (p.hasFDerivAt (x := (0 : CoordinateVector 1))).pow 2
  have hz : HasFDerivAt (𝕜 := ℝ) (fun x : CoordinateVector 1 => x 0 ^ 2) 0 0 := by
    simpa [p] using hp
  simpa only [coordinate_quadratic, ContinuousLinearMap.pi_zero] using
    (hasFDerivAt_pi.mpr (fun _ : Fin 1 => hz))

/--
OET anchor: h-055e3702cf9c3930
The same quadratic has zero original OET full-output radius, despite that derivative.
-/
theorem coordinate_quadratic_radius_zero :
    full_model_radius coordinate_quadratic Set.univ 0 = 0 := by
  rw [full_model_radius_eq _ _ _ (Set.mem_univ _)]
  apply exact_constancy_radius_eq_zero_of_close_nonfiber
  intro r hr
  have hpos : 0 < r.toReal := ENNReal.toReal_pos hr.1.ne' hr.2
  let x : CoordinateVector 1 := fun _ => r.toReal / 2
  refine ⟨x, Set.mem_univ x, ?_, ?_⟩
  · rw [coordinate_sup_distance_eq_norm]
    apply (ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) hr.2).mpr
    simp only [sub_zero, x, CoordinateVector, pi_norm_const, Real.norm_eq_abs,
      abs_of_pos (half_pos hpos)]
    linarith
  · intro heq
    have hh := congrFun heq 0
    have hhalf := half_pos hpos
    simp only [coordinate_quadratic, x, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow] at hh
    nlinarith

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
