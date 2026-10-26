import formal_oet.vol_01.ch_05_operator_networks.path_matrix

namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
variable {X V I : Type} {bot : X} [Fintype I]

/-- Position-indexed matrices allow repeated visits to the same node to use
different comparison domains. Products follow the original composition order. -/
def occurrence_matrix_product (M : ℕ → I → I → ENNReal) (r : ℕ) : I → I → ENNReal :=
  matrix_list_mul (((List.range r).map M).reverse)

@[simp] theorem occurrence_matrix_product_succ (M : ℕ → I → I → ENNReal) (r : ℕ) :
    occurrence_matrix_product M (r + 1) = matrix_mul (M r) (occurrence_matrix_product M r) := by
  simp [occurrence_matrix_product, List.range_succ, matrix_list_mul]

namespace FiniteOperatorNetwork

/-- Compose bounds on the exact prefix images, without enlarging them to full
node domains or identifying different occurrences of the same label. -/
theorem path_occurrence_lip_bounded
    (N : FiniteOperatorNetwork X bot V) (d : I → X → X → ENNReal)
    (nodes : List V) (U : Set X) (M : ℕ → I → I → ENNReal)
    (hU : ∀ x ∈ U, x ≠ bot)
    (hM : ∀ k (hk : k < nodes.length),
      IsLipMatrix d (N.node_op (nodes.get ⟨k, hk⟩))
        ((N.path_chain (nodes.take k)).func '' U) (M k)) :
    RightChainLipBounded d ((nodes.map N.node_op).reverse) U
      (occurrence_matrix_product M nodes.length) := by
  induction nodes using List.reverseRecOn with
  | nil => exact RightChainLipBounded.nil U hU
  | append_singleton nodes v ih =>
    have hprefix : ∀ k (hk : k < nodes.length),
        IsLipMatrix d (N.node_op (nodes.get ⟨k, hk⟩))
          ((N.path_chain (nodes.take k)).func '' U) (M k) := by
      intro k hk
      have h := hM k (lt_trans hk (by simp))
      rw [List.take_append_of_le_length (Nat.le_of_lt hk)] at h
      simpa [List.get_eq_getElem, hk] using h
    have hlast : IsLipMatrix d (N.node_op v) ((N.path_chain nodes).func '' U)
        (M nodes.length) := by
      simpa using hM nodes.length (by simp)
    simpa [path_chain] using
      RightChainLipBounded.cons (d := d) (N.node_op v) ((nodes.map N.node_op).reverse)
        U (M nodes.length) (occurrence_matrix_product M nodes.length) (ih hprefix) hlast

theorem path_occurrence_lip_matrix
    (N : FiniteOperatorNetwork X bot V) (d : I → X → X → ENNReal)
    (p : N.ReachablePath) (M : ℕ → I → I → ENNReal)
    (hM : ∀ k (hk : k < p.nodes.length),
      IsLipMatrix d (N.node_op (p.nodes.get ⟨k, hk⟩))
        ((N.path_chain (p.nodes.take k)).func '' N.path_domain p.nodes) (M k)) :
    IsLipMatrix d (N.path_chain p.nodes) (N.path_domain p.nodes)
      (occurrence_matrix_product M p.nodes.length) := by
  apply N.path_chain_lip_matrix_of_right_chain d
  apply N.path_occurrence_lip_bounded d p.nodes (N.path_domain p.nodes) M ?_ hM
  intro x hx hxb
  subst x
  exact N.bot_not_mem (N.path_domain_subset_source hx)

end FiniteOperatorNetwork
end
end formal_oet.vol_01.ch_05_operator_networks
