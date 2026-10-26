import formal_oet.vol_01.ch_05_operator_networks.network_relabeling
import formal_oet.vol_01.ch_05_operator_networks.network_routing

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations

namespace FiniteOperatorNetwork

variable {X V : Type} {bot : X}

/-- The original network data on a fixed node type. Empty entry and edge domains
encode absent entries and edges. Termination bounds, selected terminal paths and
routing choices outside local output images are not part of these data. -/
structure PresentationData (X : Type) (bot : X) (V : Type) where
  U : Set X
  node_op : V → Operator X bot
  entry_domain : V → Set X
  edge_domain : V → V → Set X

/-- Forget implementation witnesses without identifying different node labels. -/
def presentation_data (N : FiniteOperatorNetwork X bot V) : PresentationData X bot V :=
  ⟨N.U, N.node_op, N.entry_domain, N.edge_domain⟩

variable {N M : FiniteOperatorNetwork X bot V}

theorem presentation_data_eq_source (h : N.presentation_data = M.presentation_data) :
    N.U = M.U := congrArg PresentationData.U h

theorem presentation_data_eq_node_op (h : N.presentation_data = M.presentation_data) :
    N.node_op = M.node_op := congrArg PresentationData.node_op h

theorem presentation_data_eq_entry_domain
    (h : N.presentation_data = M.presentation_data) :
    N.entry_domain = M.entry_domain := congrArg PresentationData.entry_domain h

theorem presentation_data_eq_edge_domain
    (h : N.presentation_data = M.presentation_data) :
    N.edge_domain = M.edge_domain := congrArg PresentationData.edge_domain h

/-- Original edge data determine routing on every local output image, including
outputs not reached from the network input domain. -/
theorem presentation_data_eq_choice
    (h : N.presentation_data = M.presentation_data) (v : V) (z : X)
    (hz : z ∈ N.node_image v) : N.choice v z = M.choice v z := by
  have hop := presentation_data_eq_node_op h
  have hzM : z ∈ M.node_image v := by
    change z ∈ (M.node_op v).func '' dom (M.node_op v)
    change z ∈ (N.node_op v).func '' dom (N.node_op v) at hz
    simpa only [hop] using hz
  have hnext (w : V) : N.choice v z = .next w ↔ M.choice v z = .next w := by
    have hed : (z ∈ N.edge_domain v w) ↔ z ∈ M.edge_domain v w := by
      rw [presentation_data_eq_edge_domain h]
    change (z ∈ N.node_image v ∧ N.choice v z = .next w) ↔
      (z ∈ M.node_image v ∧ M.choice v z = .next w) at hed
    simpa only [hz, hzM, true_and] using hed
  cases hn : N.choice v z with
  | stop =>
      cases hm : M.choice v z with
      | stop => rfl
      | next w =>
          have hc := (hnext w).mpr hm
          simp [hn] at hc
  | next w => exact ((hnext w).mp hn).symm

theorem presentation_data_eq_terminal_path
    (h : N.presentation_data = M.presentation_data) {v : V} {x : X} {p : List V}
    (hx : x ∈ dom (N.node_op v))
    (hp : TerminalPathFrom N.node_op N.choice v x p) :
    TerminalPathFrom M.node_op M.choice v x p := by
  have hop := presentation_data_eq_node_op h
  induction hp with
  | @stop v x hs =>
      apply TerminalPathFrom.stop
      rw [← hop, ← presentation_data_eq_choice h v ((N.node_op v).func x) ⟨x, hx, rfl⟩]
      exact hs
  | @next v w x rest hs ht ih =>
      apply TerminalPathFrom.next (γ := w)
      · rw [← hop, ← presentation_data_eq_choice h v ((N.node_op v).func x) ⟨x, hx, rfl⟩]
        exact hs
      · simpa only [← hop] using ih (N.choice_next_mem hx hs)

theorem presentation_data_eq_entry
    (h : N.presentation_data = M.presentation_data) (x : N.U) :
    N.entry x = M.entry ⟨x.val, (presentation_data_eq_source h) ▸ x.property⟩ := by
  have hx : x.val ∈ N.entry_domain (N.entry x) := ⟨x.property, rfl⟩
  rw [presentation_data_eq_entry_domain h] at hx
  rcases hx with ⟨hx, he⟩
  exact he.symm

/-- The complete path is determined by the original network data, not by the
stored termination witness. -/
theorem presentation_data_eq_path_of
    (h : N.presentation_data = M.presentation_data) (x : N.U) :
    N.path_of x = M.path_of ⟨x.val, (presentation_data_eq_source h) ▸ x.property⟩ := by
  have ht := presentation_data_eq_terminal_path h (N.entry_mem x) (N.path_terminal x)
  rw [presentation_data_eq_entry h x] at ht
  exact terminal_path_unique ht (M.path_terminal _)

theorem presentation_data_eq_path_domain
    (h : N.presentation_data = M.presentation_data) (p : List V) :
    N.path_domain p = M.path_domain p := by
  ext x
  constructor
  · rintro ⟨hx, hp⟩
    refine ⟨(presentation_data_eq_source h) ▸ hx, ?_⟩
    exact (presentation_data_eq_path_of h ⟨x, hx⟩).symm.trans hp
  · rintro ⟨hx, hp⟩
    refine ⟨(presentation_data_eq_source h.symm) ▸ hx, ?_⟩
    exact (presentation_data_eq_path_of h.symm ⟨x, hx⟩).symm.trans hp

theorem presentation_data_eq_extensional_operator
    (h : N.presentation_data = M.presentation_data) :
    N.extensional_operator = M.extensional_operator := by
  classical
  have hU := presentation_data_eq_source h
  have hop := presentation_data_eq_node_op h
  ext x
  by_cases hx : x ∈ N.U
  · have hxM : x ∈ M.U := hU ▸ hx
    simp only [extensional_operator, dif_pos hx, dif_pos hxM, eval]
    rw [presentation_data_eq_path_of h ⟨x, hx⟩, hop]
  · have hxM : x ∉ M.U := by simpa only [← hU] using hx
    simp [extensional_operator, hx, hxM]

end FiniteOperatorNetwork
end formal_oet.vol_01.ch_05_operator_networks
