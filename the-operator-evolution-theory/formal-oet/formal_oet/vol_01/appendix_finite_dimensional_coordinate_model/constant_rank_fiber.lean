import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.constant_rank_slice
import Mathlib.Analysis.Normed.Module.HahnBanach

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open Module Filter Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/--
Library background result for local fiber geometry.
The constant-rank branch in the explicit local-chart characterization of a
C¹ embedded submanifold: an actual C¹ coordinate homeomorphism, with C¹ inverse,
turns the actual level set on an open neighborhood into a vertical slice.
The slice factor has dimension dim(E)-r. No submanifold predicate or fiber
equality is supplied as a premise.
-/
theorem actual_constant_rank_fiber_chart (g : E → E) (W : Set E) (hW : IsOpen W)
    (hg : ContDiffOn ℝ 1 g W) (x : E) (hx : x ∈ W) (r : ℕ)
    (hrank : ∀ z ∈ W, finrank ℝ (fderiv ℝ g z).toLinearMap.range = r) :
    let T := fderiv ℝ g x
    ∃ (H : OpenPartialHomeomorph E (T.toLinearMap.range × T.rangeRestrict.ker)) (W₀ : Set E),
      IsOpen W₀ ∧ x ∈ W₀ ∧ W₀ ⊆ W ∩ H.source ∧
      ContDiffOn ℝ 1 H W₀ ∧ ContDiffOn ℝ 1 H.symm (H '' W₀) ∧
      finrank ℝ T.rangeRestrict.ker = finrank ℝ E - r ∧
      (∀ z ∈ W₀, g z = g x ↔ (H z).1 = (H x).1) := by
  let T := fderiv ℝ g x
  let C := T.toLinearMap.range
  letI : NormedAddCommGroup C := inferInstance
  letI : NormedSpace ℝ C := inferInstance
  letI : CompleteSpace C := inferInstance
  obtain ⟨P, hP⟩ := Submodule.ClosedComplemented.of_finiteDimensional C
  have hPT : P.comp T = T.rangeRestrict := by
    ext z
    exact congrArg Subtype.val (hP (⟨T z, ⟨z, rfl⟩⟩ : C))
  have hc : ContDiffAt ℝ 1 g x := (hg x hx).contDiffAt (hW.mem_nhds hx)
  have hleft : ContDiffAt ℝ 1 (fun z => P (g z)) x := P.contDiff.contDiffAt.comp x hc
  have hd : HasStrictFDerivAt (fun z => P (g z)) T.rangeRestrict x := by
    rw [← hPT]
    exact P.hasStrictFDerivAt.comp x (hc.hasStrictFDerivAt one_ne_zero)
  have hsurj : T.rangeRestrict.range = ⊤ := by
    apply LinearMap.range_eq_top.mpr
    rintro ⟨y, z, rfl⟩
    exact ⟨z, rfl⟩
  let hker := T.rangeRestrict.ker_closedComplemented_of_finiteDimensional_range
  let φ : ImplicitFunctionData ℝ E C T.rangeRestrict.ker :=
    HasStrictFDerivAt.implicitFunctionDataOfComplemented
      (fun z => P (g z)) T.rangeRestrict hd hsurj hker
  let H := φ.toOpenPartialHomeomorph
  have hright : ContDiffAt ℝ 1 φ.rightFun x := by
    dsimp [φ, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
    fun_prop
  have hi : ContDiffAt ℝ 1 H.symm (H x) := by
    have h := φ.contDiffAt_implicitFunction hleft hright one_ne_zero
    simpa only [ImplicitFunctionData.implicitFunction_def, Function.uncurry_curry,
      ← ImplicitFunctionData.toOpenPartialHomeomorph_apply] using h
  have hxH : x ∈ H.source := φ.pt_mem_toOpenPartialHomeomorph_source
  have hfst : ∀ z ∈ H.source, (H z).1 = P (g z) := by
    intro z _
    rw [show H z = φ.prodFun z from φ.toOpenPartialHomeomorph_apply z]
    rfl
  obtain ⟨W₀, ho, hx₀, hsub, hInv, hfiber⟩ := local_fiber_slice g P W hW hg H hfst x hx hxH hi
    (fun z hz => by rw [hrank z hz, ← hrank x hx])
  have hforward : ContDiffOn ℝ 1 H W₀ := by
    intro z hz
    have hgz := (hg z (hsub hz).1).contDiffAt (hW.mem_nhds (hsub hz).1)
    have h₁ : ContDiffAt ℝ 1 φ.leftFun z := P.contDiff.contDiffAt.comp z hgz
    have h₂ : ContDiffAt ℝ 1 φ.rightFun z := by
      dsimp [φ, HasStrictFDerivAt.implicitFunctionDataOfComplemented]
      fun_prop
    exact (h₁.prodMk h₂).contDiffWithinAt
  have hdim : finrank ℝ T.rangeRestrict.ker = finrank ℝ E - r := by
    have h := T.rangeRestrict.toLinearMap.finrank_range_add_finrank_ker
    rw [hsurj, finrank_top] at h
    have ht : finrank ℝ C = r := hrank x hx
    dsimp only [C] at ht
    omega
  exact ⟨H, W₀, ho, hx₀, hsub, hforward, hInv, hdim, hfiber⟩

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
