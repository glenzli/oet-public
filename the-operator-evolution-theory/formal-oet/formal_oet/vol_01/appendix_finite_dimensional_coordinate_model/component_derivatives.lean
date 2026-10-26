import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.model_radius

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open Filter Topology
open scoped BigOperators
noncomputable section

theorem constant_on_open_convex_iff_derivative_zero
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (D : E → E →L[ℝ] ℝ) (Q : Set E)
    (hQ : IsOpen Q) (hc : Convex ℝ Q) (x₀ : E) (hx₀ : x₀ ∈ Q)
    (hD : ∀ x ∈ Q, HasFDerivAt f (D x) x) :
    (∃ c, ∀ x ∈ Q, f x = c) ↔ ∀ x ∈ Q, D x = 0 := by
  constructor
  · rintro ⟨c, h⟩ x hx
    have heq : f =ᶠ[𝓝 x] fun _ => c := Filter.mem_of_superset (hQ.mem_nhds hx) h
    rw [← (hD x hx).fderiv, heq.fderiv_eq]
    simp
  · intro h
    refine ⟨f x₀, fun x hx => ?_⟩
    apply hc.is_const_of_fderivWithin_eq_zero
      (fun x hx => (hD x hx).differentiableAt.differentiableWithinAt) ?_ hx hx₀
    intro z hz
    rw [(hD z hz).hasFDerivWithinAt.fderivWithin (hQ.uniqueDiffOn z hz), h z hz]

variable {n : ℕ} [NeZero n]

def coordinate_covector (T : CoordinateVector n →L[ℝ] ℝ) : CoordinateVector n :=
  fun i => T (Pi.single i 1)

theorem coordinate_covector_injective : Function.Injective (coordinate_covector (n := n)) := by
  intro T U h
  ext v
  have hs : (∑ i : Fin n, v i • (Pi.single i 1 : CoordinateVector n)) = v := by
    ext j; simp [Pi.single_apply]
  rw [← hs, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul, smul_eq_mul]
  exact congrArg (fun t => v i * t) (congrFun h i)

@[simp] theorem coordinate_covector_zero : coordinate_covector (0 : CoordinateVector n →L[ℝ] ℝ) = 0 := by
  rfl

@[simp] theorem coordinate_covector_proj (j : Fin n) :
    coordinate_covector (ContinuousLinearMap.proj j : CoordinateVector n →L[ℝ] ℝ) =
      Pi.single j 1 := by
  ext i; simp [coordinate_covector, Pi.single_apply, eq_comm]

def component_differential (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (j : Fin n) (x : CoordinateVector n) : CoordinateVector n →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j).comp (D x)

/-- The gradient is the vector of actual standard-coordinate partial derivatives. -/
def component_gradient (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (j : Fin n) (x : CoordinateVector n) : CoordinateVector n :=
  coordinate_covector (component_differential D j x)

theorem model_pointwise_zero_iff (F : CoordinateVector n → CoordinateVector n)
    (Q : Set (CoordinateVector n)) (j : Fin n) :
    (∀ z ∈ coordinate_model_set Set.univ Q,
      coordinate_dist j ((full_model_operator F Q).func z) z = 0) ↔
      ∀ x ∈ Q, F x j = x j := by
  constructor
  · intro h x hx
    have hh := h (full_coordinate_point x) ⟨⟨x, Set.mem_univ x⟩, hx, rfl⟩
    simpa [full_coordinate_point, full_model_operator, coordinate_model_operator,
      coordinate_dist, hx, ENNReal.ofReal_eq_zero, abs_nonpos_iff, sub_eq_zero] using hh
  · intro h z hz
    rcases hz with ⟨x, hx, rfl⟩
    simp [full_model_operator, coordinate_model_operator, coordinate_dist, hx, h x.val hx]

theorem model_constant_component_iff (F : CoordinateVector n → CoordinateVector n)
    (Q : Set (CoordinateVector n))
    (x₀ : CoordinateVector n) (hx₀ : x₀ ∈ Q) (j : Fin n) :
    j ∈ ConstComponent coordinate_dist (full_model_operator F Q) (coordinate_model_set Set.univ Q) ↔
      ∃ c : ℝ, ∀ x ∈ Q, F x j = c := by
  constructor
  · intro h
    refine ⟨F x₀ j, fun x hx => ?_⟩
    have hh := h (full_coordinate_point x) ⟨⟨x, Set.mem_univ x⟩, hx, rfl⟩
      (full_coordinate_point x₀) ⟨⟨x₀, Set.mem_univ x₀⟩, hx₀, rfl⟩
    simpa [full_coordinate_point, full_model_operator, coordinate_model_operator, coordinate_dist,
      hx, hx₀, ENNReal.ofReal_eq_zero, abs_nonpos_iff, sub_eq_zero] using hh
  · rintro ⟨c, h⟩ x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    simp [full_model_operator, coordinate_model_operator, coordinate_dist, ha, hb, h a.val ha, h b.val hb]

theorem model_identity_component_iff (F : CoordinateVector n → CoordinateVector n)
    (Q : Set (CoordinateVector n)) (hQ : IsOpen Q) (hc : Convex ℝ Q)
    (x₀ : CoordinateVector n) (hx₀ : x₀ ∈ Q) (j : Fin n) :
    j ∈ IdComponent coordinate_dist (full_model_operator F Q) (coordinate_model_set Set.univ Q) ↔
      ∀ x ∈ Q, F x j = x j := by
  constructor
  · intro h
    exact (model_pointwise_zero_iff F Q j).mp h.2
  · intro h
    refine ⟨?_, (model_pointwise_zero_iff F Q j).mpr h⟩
    intro hconst
    rcases (model_constant_component_iff F Q x₀ hx₀ j).mp hconst with ⟨c, hconstant⟩
    let p : CoordinateVector n →L[ℝ] ℝ := ContinuousLinearMap.proj j
    have hz := (constant_on_open_convex_iff_derivative_zero p (fun _ => p) Q hQ hc x₀ hx₀
      (fun x _ => p.hasFDerivAt)).mp ⟨c, fun x hx => (h x hx).symm.trans (hconstant x hx)⟩ x₀ hx₀
    have hh := congrArg (fun T : CoordinateVector n →L[ℝ] ℝ => T (Pi.single j 1)) hz
    simpa [p] using hh

/--
OET anchor: h-ac7cdc1d2ab36d93
**习题（恒等分量与常值分量的导数判据）**
The constant-coordinate criterion uses actual gradients and the original OET
constant component set defined by pairwise zero output distance. Only
pointwise derivatives are needed; the stated C1 hypothesis implies them.
-/
theorem constant_component_gradient_criterion
    (F : CoordinateVector n → CoordinateVector n)
    (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (Q : Set (CoordinateVector n)) (hQ : IsOpen Q) (hc : Convex ℝ Q)
    (x₀ : CoordinateVector n) (hx₀ : x₀ ∈ Q)
    (hD : ∀ x ∈ Q, HasFDerivAt F (D x) x) (j : Fin n) :
    ((∃ c : ℝ, ∀ x ∈ Q, F x j = c) ↔ ∀ x ∈ Q, component_gradient D j x = 0) ∧
    (j ∈ ConstComponent coordinate_dist (full_model_operator F Q) (coordinate_model_set Set.univ Q) ↔
      ∀ x ∈ Q, component_gradient D j x = 0) := by
  have hg (x : CoordinateVector n) (hx : x ∈ Q) :
      HasFDerivAt (fun x => F x j) (component_differential D j x) x :=
    (ContinuousLinearMap.proj j : CoordinateVector n →L[ℝ] ℝ).hasFDerivAt.comp x (hD x hx)
  have he : (∃ c, ∀ x ∈ Q, F x j = c) ↔ ∀ x ∈ Q, component_gradient D j x = 0 := by
    rw [constant_on_open_convex_iff_derivative_zero _ _ Q hQ hc x₀ hx₀ hg]
    apply forall_congr'
    intro x
    apply forall_congr'
    intro _
    constructor
    · intro hz; simp [component_gradient, hz]
    · intro hz
      apply coordinate_covector_injective
      simpa only [coordinate_covector_zero] using hz
  exact ⟨he, (model_constant_component_iff F Q x₀ hx₀ j).trans he⟩

/--
OET anchor: h-ac7cdc1d2ab36d93
**习题（恒等分量与常值分量的导数判据）**
The identity-coordinate criterion retains the indispensable base-point value,
and identifies it with the original OET identity component set.
-/
theorem identity_component_gradient_criterion
    (F : CoordinateVector n → CoordinateVector n)
    (D : CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (Q : Set (CoordinateVector n)) (hQ : IsOpen Q) (hc : Convex ℝ Q)
    (x₀ : CoordinateVector n) (hx₀ : x₀ ∈ Q)
    (hD : ∀ x ∈ Q, HasFDerivAt F (D x) x) (j : Fin n) :
    ((∀ x ∈ Q, F x j = x j) ↔
      (∀ x ∈ Q, component_gradient D j x = Pi.single j 1) ∧ F x₀ j = x₀ j) ∧
    (j ∈ IdComponent coordinate_dist (full_model_operator F Q) (coordinate_model_set Set.univ Q) ↔
      (∀ x ∈ Q, component_gradient D j x = Pi.single j 1) ∧ F x₀ j = x₀ j) := by
  let p : CoordinateVector n →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hg (x : CoordinateVector n) (hx : x ∈ Q) :
      HasFDerivAt (fun x => F x j) (component_differential D j x) x :=
    p.hasFDerivAt.comp x (hD x hx)
  have he : (∀ x ∈ Q, F x j = x j) ↔
      (∀ x ∈ Q, component_gradient D j x = Pi.single j 1) ∧ F x₀ j = x₀ j := by
    constructor
    · intro h
      refine ⟨fun x hx => ?_, h x₀ hx₀⟩
      have heq : (fun x => F x j) =ᶠ[𝓝 x] p := Filter.mem_of_superset (hQ.mem_nhds hx) h
      have hd : component_differential D j x = p := by
        rw [← (hg x hx).fderiv, heq.fderiv_eq, p.fderiv]
      simpa [component_gradient, hd, p] using coordinate_covector_proj j
    · rintro ⟨h, hb⟩
      have hd (x : CoordinateVector n) (hx : x ∈ Q) : component_differential D j x = p := by
        apply coordinate_covector_injective
        simpa only [p, coordinate_covector_proj] using h x hx
      apply hc.eqOn_of_fderivWithin_eq
        (fun x hx => (hg x hx).differentiableAt.differentiableWithinAt) p.differentiable.differentiableOn
        hQ.uniqueDiffOn ?_ hx₀ hb
      intro x hx
      rw [(hg x hx).hasFDerivWithinAt.fderivWithin (hQ.uniqueDiffOn x hx),
        p.hasFDerivAt.hasFDerivWithinAt.fderivWithin (hQ.uniqueDiffOn x hx), hd x hx]
  exact ⟨he, (model_identity_component_iff F Q hQ hc x₀ hx₀ j).trans he⟩

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
