import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.differential_chain

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
noncomputable section
open Filter Topology
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact composition domain of maps with specified open domains. Totalized
function values outside their domains do not make the composition well-defined. -/
def extension_chain_domain : List (DifferentialFunction E × Set E) → Set E
  | [] => Set.univ
  | step :: steps => extension_chain_domain steps ∩
      (differential_function_chain (steps.map Prod.fst)) ⁻¹' step.2

/-- Local well-definedness and the actual chain derivative follow from the
individual open domains and derivatives at all their points. -/
theorem open_extension_chain_at
    (steps : List (DifferentialFunction E × Set E))
    (hsteps : ∀ step ∈ steps, IsOpen step.2 ∧
      ∀ x ∈ step.2, HasFDerivAt step.1.func (step.1.differential x) x)
    (x : E) (hx : x ∈ extension_chain_domain steps) :
    ChainDifferentiableAt (steps.map Prod.fst) x ∧
      extension_chain_domain steps ∈ 𝓝 x := by
  induction steps with
  | nil => exact ⟨trivial, Filter.univ_mem⟩
  | cons step steps ih =>
    have ht := ih (fun s hs => hsteps s (by simp [hs])) hx.1
    have hs := hsteps step (by simp)
    have hd := hs.2 _ hx.2
    refine ⟨⟨ht.1, hd⟩, ?_⟩
    have hc := (differential_chain_has_fderiv (steps.map Prod.fst) x ht.1).continuousAt
    exact Filter.inter_mem ht.2 (hc.preimage_mem_nhds (hs.1.mem_nhds hx.2))

theorem open_extension_chain_neighborhood
    (steps : List (DifferentialFunction E × Set E))
    (hsteps : ∀ step ∈ steps, IsOpen step.2 ∧
      ∀ x ∈ step.2, HasFDerivAt step.1.func (step.1.differential x) x)
    (x : E) (hx : x ∈ extension_chain_domain steps) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ extension_chain_domain steps := by
  rcases mem_nhds_iff.mp (open_extension_chain_at steps hsteps x hx).2 with ⟨W, hW, ho, hxW⟩
  exact ⟨W, ho, hxW, hW⟩

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
