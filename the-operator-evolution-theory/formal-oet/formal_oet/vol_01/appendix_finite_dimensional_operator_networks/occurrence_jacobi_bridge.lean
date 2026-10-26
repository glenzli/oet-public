import formal_oet.vol_01.ch_05_operator_networks.occurrence_matrix
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.jacobi_coordinate_bridge
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.jacobi_block_bridge

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
noncomputable section

/-- Totalization for the finite ordered product; values at and beyond `r` are
never used in `occurrence_matrix_product ... r`. -/
def extend_occurrence_matrices {I : Type} {r : ℕ}
    (M : Fin r → I → I → ENNReal) (k : ℕ) : I → I → ENNReal :=
  if hk : k < r then M ⟨k, hk⟩ else 0

/--
OET anchor: h-282a390854b22758
节点发生域上的坐标导数证书。Actual Jacobi suprema on convex covers
give the ordered product for the actual network path operator. Repeated
occurrences have separate covers; no local Lip matrix is supplied as input.
-/
theorem path_coordinate_jacobi_lip_matrix
    {n : ℕ} [NeZero n] {A : Set (CoordinateVector n)} {V : Type}
    (N : FiniteOperatorNetwork (CoordinatePoint n A) none V) (p : N.ReachablePath)
    (F : V → CoordinateVector n → CoordinateVector n)
    (D : V → CoordinateVector n → CoordinateVector n →L[ℝ] CoordinateVector n)
    (Q : Fin p.nodes.length → Set (CoordinateVector n))
    (hne : ∀ k, (Q k).Nonempty) (hQ : ∀ k, Convex ℝ (Q k))
    (hreal : ∀ k, ModelRealizationOn (N.node_op (p.nodes.get k)) (F (p.nodes.get k))
      (Q k) ((N.path_chain (p.nodes.take k.val)).func '' N.path_domain p.nodes))
    (hC1 : ∀ k, C1DerivativeOnOpenNeighborhood (F (p.nodes.get k)) (D (p.nodes.get k)) (Q k))
    (hfinite : ∀ k i j, BddAbove
      ((fun z => |jacobi_entry (D (p.nodes.get k)) z i j|) '' Q k)) :
    IsLipMatrix coordinate_dist (N.path_chain p.nodes) (N.path_domain p.nodes)
      (occurrence_matrix_product (extend_occurrence_matrices
        (fun k i j => ENNReal.ofReal (jacobi_entry_sup (D (p.nodes.get k)) (Q k) i j)))
        p.nodes.length) := by
  apply N.path_occurrence_lip_matrix coordinate_dist p
  intro k hk
  simp only [extend_occurrence_matrices, dif_pos hk]
  exact jacobi_coordinate_sup_on_realized_set _ _ _ (hne ⟨k, hk⟩) _ _
    (hreal ⟨k, hk⟩) (hC1 ⟨k, hk⟩) (hQ ⟨k, hk⟩) (hfinite ⟨k, hk⟩)

/--
OET anchor: h-282a390854b22758
节点发生域上的正交块导数证书。The actual projected Jacobi operators
and the original extended block pseudometrics yield the path Lip matrix.
Only realized node inputs must belong to the state space, not their convex covers.
-/
theorem path_block_jacobi_lip_matrix
    {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype H] {A : Set E} {V : Type}
    (N : FiniteOperatorNetwork (Option A) none V) (p : N.ReachablePath)
    (W : H → Submodule ℝ E)
    (hW : OrthogonalFamily ℝ (fun a => W a) (fun a => (W a).subtypeₗᵢ))
    (hspan : iSup W = ⊤) (F : V → E → E) (D : V → E → E →L[ℝ] E)
    (Q : Fin p.nodes.length → Set E)
    (hne : ∀ k, (Q k).Nonempty) (hQ : ∀ k, Convex ℝ (Q k))
    (hreal : ∀ k, ModelRealizationOn (N.node_op (p.nodes.get k)) (F (p.nodes.get k))
      (Q k) ((N.path_chain (p.nodes.take k.val)).func '' N.path_domain p.nodes))
    (hC1 : ∀ k, C1DerivativeOnOpenNeighborhood (F (p.nodes.get k)) (D (p.nodes.get k)) (Q k))
    (hfinite : ∀ k a b, BddAbove
      ((fun z => ‖jacobi_block_map W (D (p.nodes.get k)) z a b‖) '' Q k)) :
    IsLipMatrix (orthogonal_block_dist W) (N.path_chain p.nodes) (N.path_domain p.nodes)
      (occurrence_matrix_product (extend_occurrence_matrices
        (fun k a b => ENNReal.ofReal (jacobi_block_sup W (D (p.nodes.get k)) (Q k) a b)))
        p.nodes.length) := by
  apply N.path_occurrence_lip_matrix (orthogonal_block_dist W) p
  intro k hk
  simp only [extend_occurrence_matrices, dif_pos hk]
  exact jacobi_block_sup_is_lip_matrix W hW hspan _ _ _ _ (hne ⟨k, hk⟩) _
    (hreal ⟨k, hk⟩) (hC1 ⟨k, hk⟩) (hQ ⟨k, hk⟩) (hfinite ⟨k, hk⟩)

end
end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
