import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.constant_rank_linear
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open Filter Topology Module
noncomputable section
variable {E F K : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]

/-- In submersion coordinates for P ∘ g, the constant-rank bound forces the
actual derivative of g along each vertical slice to vanish. -/
theorem slice_derivative_zero (g : E → E) (P : E →L[ℝ] F)
    (H : OpenPartialHomeomorph E (F × K))
    (hfst : ∀ z ∈ H.source, (H z).1 = P (g z))
    (q : F × K) (hq : q ∈ H.target)
    (hg : DifferentiableAt ℝ g (H.symm q)) (hi : DifferentiableAt ℝ H.symm q)
    (hrank : finrank ℝ (fderiv ℝ g (H.symm q)).toLinearMap.range ≤ finrank ℝ F) :
    HasFDerivAt (fun k => g (H.symm (q.1, k))) (0 : K →L[ℝ] E) q.2 := by
  let D := (fderiv ℝ g (H.symm q)).comp (fderiv ℝ H.symm q)
  have hd : HasFDerivAt (fun w => g (H.symm w)) D q :=
    hg.hasFDerivAt.comp q hi.hasFDerivAt
  have hpd : P.comp D = ContinuousLinearMap.fst ℝ F K := by
    have heq : (fun w => P (g (H.symm w))) =ᶠ[𝓝 q] Prod.fst := by
      filter_upwards [H.open_target.mem_nhds hq] with w hw
      rw [← hfst (H.symm w) (H.map_target hw), H.right_inv hw]
    have h := (P.hasFDerivAt.comp q hd).congr_of_eventuallyEq heq.symm
    exact h.unique hasFDerivAt_fst
  have hsurj : Function.Surjective (P.toLinearMap.comp D.toLinearMap) := by
    intro y
    refine ⟨(y, 0), ?_⟩
    exact congrArg (fun L : (F × K) →L[ℝ] F => L (y, 0)) hpd
  have hdim : finrank ℝ D.toLinearMap.range ≤ finrank ℝ F := by
    apply (Submodule.finrank_mono (LinearMap.range_comp_le_range
      (fderiv ℝ H.symm q).toLinearMap (fderiv ℝ g (H.symm q)).toLinearMap)).trans hrank
  have hz : D.comp (ContinuousLinearMap.inr ℝ F K) = 0 := by
    ext k
    apply zero_of_projected_zero_of_rank_bound D.toLinearMap P.toLinearMap hdim hsurj
    have h := congrArg (fun L : (F × K) →L[ℝ] F => L (0, k)) hpd
    exact h
  have hp : HasFDerivAt (fun k : K => (q.1, k)) (ContinuousLinearMap.inr ℝ F K) q.2 :=
    hasFDerivAt_prodMk_right q.1 q.2
  have h : HasFDerivAt (fun k => g (H.symm (q.1, k)))
      (D.comp (ContinuousLinearMap.inr ℝ F K)) q.2 := by
    convert HasFDerivAt.comp q.2 hd hp using 1
  simpa only [hz] using h

/-- A genuine local flattening of the level fiber. The chart and its inverse
are already actual maps; the equality of fibers is proved from the rank bound.
This lemma is later instantiated by the implicit-function theorem. -/
theorem local_fiber_slice (g : E → E) (P : E →L[ℝ] F)
    (W : Set E) (hW : IsOpen W) (hg : ContDiffOn ℝ 1 g W)
    (H : OpenPartialHomeomorph E (F × K))
    (hfst : ∀ z ∈ H.source, (H z).1 = P (g z))
    (x : E) (hx : x ∈ W) (hxH : x ∈ H.source)
    (hi : ContDiffAt ℝ 1 H.symm (H x))
    (hrank : ∀ z ∈ W, finrank ℝ (fderiv ℝ g z).toLinearMap.range ≤ finrank ℝ F) :
    ∃ W₀ : Set E, IsOpen W₀ ∧ x ∈ W₀ ∧ W₀ ⊆ W ∩ H.source ∧
      ContDiffOn ℝ 1 H.symm (H '' W₀) ∧
      (∀ z ∈ W₀, g z = g x ↔ (H z).1 = (H x).1) := by
  have hxT := H.map_source hxH
  have hnear : ∀ᶠ q in 𝓝 (H x), q ∈ H.target ∧ H.symm q ∈ W ∧
      ContDiffAt ℝ 1 H.symm q := by
    have hmap : ∀ᶠ q in 𝓝 (H x), H.symm q ∈ W := by
      have hx' : H.symm (H x) ∈ W := by rwa [H.left_inv hxH]
      exact (H.symm.continuousAt hxT).eventually (hW.mem_nhds hx')
    filter_upwards [H.open_target.mem_nhds hxT, hmap, hi.eventually (by norm_num)] with q h₁ h₂ h₃
    exact ⟨h₁, h₂, h₃⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let W₀ := H.source ∩ H ⁻¹' Metric.ball (H x) δ
  have hx₀ : x ∈ W₀ := ⟨hxH, Metric.mem_ball_self hδ⟩
  have hsub : W₀ ⊆ W ∩ H.source := by
    intro z hz
    have h := (hball hz.2).2.1
    rw [H.left_inv hz.1] at h
    exact ⟨h, hz.1⟩
  have hcInv : ContDiffOn ℝ 1 H.symm (H '' W₀) := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hball hz.2).2.2.contDiffWithinAt
  let a := (H x).1
  let k₀ := (H x).2
  let G (k : K) := g (H.symm (a, k))
  have hkb (k : K) (hk : k ∈ Metric.ball k₀ δ) : (a, k) ∈ Metric.ball (H x) δ := by
    simpa [Metric.mem_ball, Prod.dist_eq, a, k₀] using hk
  have hzero (k : K) (hk : k ∈ Metric.ball k₀ δ) : HasFDerivAt G (0 : K →L[ℝ] E) k := by
    have h := hball (hkb k hk)
    exact slice_derivative_zero g P H hfst (a, k) h.1
      ((hg _ h.2.1).contDiffAt (hW.mem_nhds h.2.1)).differentiableAt_one
      h.2.2.differentiableAt_one (hrank _ h.2.1)
  have hconst (k : K) (hk : k ∈ Metric.ball k₀ δ) : G k = G k₀ :=
    Metric.isOpen_ball.is_const_of_fderiv_eq_zero (convex_ball k₀ δ).isPreconnected
      (fun k hk => (hzero k hk).differentiableAt.differentiableWithinAt)
      (fun k hk => (hzero k hk).fderiv) hk (Metric.mem_ball_self hδ)
  refine ⟨W₀, H.isOpen_inter_preimage Metric.isOpen_ball, hx₀, hsub, hcInv, ?_⟩
  intro z hz
  constructor
  · intro heq
    rw [hfst z hz.1, hfst x hxH, heq]
  · intro heq
    have hk : (H z).2 ∈ Metric.ball k₀ δ := by
      have h := hz.2
      change dist (H z) (H x) < δ at h
      exact (le_max_right _ _).trans_lt h
    have he : (a, (H z).2) = H z := Prod.ext heq.symm rfl
    have h := hconst (H z).2 hk
    dsimp only [G] at h
    rw [he, H.left_inv hz.1] at h
    simpa only [a, k₀, Prod.mk.eta, H.left_inv hxH] using h

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
