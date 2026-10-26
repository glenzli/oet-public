import formal_oet.vol_01.ch_05_operator_networks.effective_equivalence

namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
variable {X V W : Type} {bot : X}
namespace FiniteOperatorNetwork
variable {N : FiniteOperatorNetwork X bot V} {M : FiniteOperatorNetwork X bot W}

namespace TaggedSegmentExpressionIsomorphism
variable (h : TaggedSegmentExpressionIsomorphism N M)

theorem node_at_position_eq (p : N.ReachablePath) (n : Nat)
    (hn : n < p.nodes.length) :
    (h.path_equiv p).nodes.get ⟨n, by rw [← h.path_length_eq p]; exact hn⟩ =
      h.node_equiv (p.nodes.get ⟨n, hn⟩) := by
  simp [h.path_nodes_eq p]

/-- Prefix images, not only final outputs, are determined by corresponding
ordered factors on their actual inputs. -/
theorem prefix_image_eq (p : N.ReachablePath) (n : Nat) (hn : n ≤ p.nodes.length) :
    N.chain_eval_nodes (p.nodes.take n) '' N.path_domain p.nodes =
      M.chain_eval_nodes ((h.path_equiv p).nodes.take n) ''
        M.path_domain (h.path_equiv p).nodes := by
  have heval (x : X) (hx : x ∈ N.path_domain p.nodes) :
      N.chain_eval_nodes (p.nodes.take n) x =
        M.chain_eval_nodes ((h.path_equiv p).nodes.take n) x := by
    simpa [h.path_nodes_eq p, List.map_take] using h.prefix_eval_eq p hx n hn
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, h.path_domain_eq p ▸ hx, (heval x hx).symm⟩
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ N.path_domain p.nodes := (h.path_domain_eq p).symm ▸ hx
    exact ⟨x, hx', heval x hx'⟩

/-- OET anchor: h-31fdfdb343da7ff2
Corresponding labels have the same actual input domain. This follows from
prefix images and the union over occurrences, rather than being assumed. -/
theorem actual_input_domain_eq (v : V) :
    N.node_actual_input_domain v = M.node_actual_input_domain (h.node_equiv v) := by
  rw [← N.tagged_recovered_node_input_domain_eq,
    ← M.tagged_recovered_node_input_domain_eq]
  ext y
  constructor
  · rintro ⟨p, n, hlabel, hy⟩
    refine ⟨h.path_equiv p, ⟨n.val, by rw [← h.path_length_eq p]; exact n.isLt⟩, ?_, ?_⟩
    · rw [h.node_at_position_eq p n.val n.isLt, hlabel]
    · change y ∈ M.chain_eval_nodes ((h.path_equiv p).nodes.take n.val) ''
        M.path_domain (h.path_equiv p).nodes
      rw [← h.prefix_image_eq p n.val (Nat.le_of_lt n.isLt)]
      exact hy
  · rintro ⟨q, n, hlabel, hy⟩
    obtain ⟨p, rfl⟩ := h.path_equiv.surjective q
    have hn : n.val < p.nodes.length := by rw [h.path_length_eq p]; exact n.isLt
    refine ⟨p, ⟨n.val, hn⟩, ?_, ?_⟩
    · apply h.node_equiv.injective
      exact (h.node_at_position_eq p n.val hn).symm.trans hlabel
    · change y ∈ N.chain_eval_nodes (p.nodes.take n.val) '' N.path_domain p.nodes
      rw [h.prefix_image_eq p n.val (Nat.le_of_lt hn)]
      exact hy

/-- Original factors agree on the entire reconstructed domain of a label. -/
theorem node_factor_local_equiv (v : V) :
    LocalEquivalent (N.node_op v) (M.node_op (h.node_equiv v))
      (N.node_actual_input_domain v) := by
  intro y hy
  rw [← N.tagged_recovered_node_input_domain_eq] at hy
  obtain ⟨p, n, hlabel, hy⟩ := hy
  have hf := h.factor_local_equiv p n y hy
  rw [hlabel] at hf
  exact hf

/-- OET anchor: h-31fdfdb343da7ff2
After restriction to actual inputs, the full local operators are equal. -/
theorem effective_node_operator_eq (v : V) :
    N.effective_reduction.node_op v = M.effective_reduction.node_op (h.node_equiv v) := by
  change N.effective_node_operator v = M.effective_node_operator (h.node_equiv v)
  ext y
  by_cases hy : y ∈ N.node_actual_input_domain v
  · rw [N.effective_node_operator_apply_eq v y hy,
      M.effective_node_operator_apply_eq _ y (h.actual_input_domain_eq v ▸ hy)]
    exact h.node_factor_local_equiv v y hy
  · have hy' : y ∉ M.node_actual_input_domain (h.node_equiv v) := by
      rwa [← h.actual_input_domain_eq v]
    simp only [effective_node_operator,
      restrict_operator_apply_of_not_mem _ _ hy,
      restrict_operator_apply_of_not_mem _ _ hy']

/-- First labels and path domains determine the same entrance blocks. -/
theorem entry_domain_eq (v : V) :
    N.effective_reduction.entry_domain v =
      M.effective_reduction.entry_domain (h.node_equiv v) := by
  rw [N.tagged_reconstruction_of_effective_reduction.2.1,
    M.tagged_reconstruction_of_effective_reduction.2.1]
  ext x
  constructor
  · rintro ⟨p, hx, hhead⟩
    refine ⟨h.path_equiv p, h.path_domain_eq p ▸ hx, ?_⟩
    rw [h.path_nodes_eq p, List.head?_map, hhead]
    rfl
  · rintro ⟨q, hx, hhead⟩
    obtain ⟨p, rfl⟩ := h.path_equiv.surjective q
    refine ⟨p, (h.path_domain_eq p).symm ▸ hx, ?_⟩
    rw [h.path_nodes_eq p, List.head?_map] at hhead
    cases he : p.nodes.head? with
    | none => simp [he] at hhead
    | some u =>
      simp only [he, Option.map_some, Option.some.injEq] at hhead
      exact congrArg some (h.node_equiv.injective hhead)

/-- Adjacent labelled occurrences and their prefix images determine all
transition domains of the effective network. -/
theorem edge_domain_eq (v w : V) :
    N.effective_reduction.edge_domain v w =
      M.effective_reduction.edge_domain (h.node_equiv v) (h.node_equiv w) := by
  rw [N.tagged_reconstruction_of_effective_reduction.2.2.1,
    M.tagged_reconstruction_of_effective_reduction.2.2.1]
  ext z
  constructor
  · rintro ⟨p, n, hn, hv, hw, hz⟩
    refine ⟨h.path_equiv p, n, ?_, ?_, ?_, ?_⟩
    · rwa [← h.path_length_eq p]
    · rw [h.node_at_position_eq p n (Nat.lt_of_succ_lt hn), hv]
    · rw [h.node_at_position_eq p (n + 1) hn, hw]
    · exact h.prefix_image_eq p (n + 1) (Nat.le_of_lt hn) ▸ hz
  · rintro ⟨q, n, hn, hv, hw, hz⟩
    obtain ⟨p, rfl⟩ := h.path_equiv.surjective q
    have hn' : n + 1 < p.nodes.length := by rwa [h.path_length_eq p]
    refine ⟨p, n, hn', ?_, ?_, ?_⟩
    · apply h.node_equiv.injective
      exact (h.node_at_position_eq p n (Nat.lt_of_succ_lt hn')).symm.trans hv
    · apply h.node_equiv.injective
      exact (h.node_at_position_eq p (n + 1) hn').symm.trans hw
    · exact (h.prefix_image_eq p (n + 1) (Nat.le_of_lt hn')).symm ▸ hz

/-- Last labelled factors and the full prefix image determine termination. -/
theorem terminal_domain_eq (v : V) :
    N.effective_reduction.terminal_domain v =
      M.effective_reduction.terminal_domain (h.node_equiv v) := by
  rw [N.tagged_reconstruction_of_effective_reduction.2.2.2,
    M.tagged_reconstruction_of_effective_reduction.2.2.2]
  ext z
  constructor
  · rintro ⟨p, pref, hnodes, hz⟩
    refine ⟨h.path_equiv p, pref.map h.node_equiv, ?_, ?_⟩
    · simp [h.path_nodes_eq p, hnodes]
    · have himage := h.prefix_image_eq p p.nodes.length le_rfl
      have htake : (h.path_equiv p).nodes.take p.nodes.length = (h.path_equiv p).nodes := by
        rw [h.path_length_eq p, List.take_length]
      simp only [List.take_length, htake] at himage
      exact himage ▸ hz
  · rintro ⟨q, pref, hnodes, hz⟩
    obtain ⟨p, rfl⟩ := h.path_equiv.surjective q
    refine ⟨p, pref.map h.node_equiv.symm, ?_, ?_⟩
    · have hp := congrArg (List.map h.node_equiv.symm) hnodes
      simpa [h.path_nodes_eq p, List.map_map, Function.comp_def] using hp
    · have himage := h.prefix_image_eq p p.nodes.length le_rfl
      have htake : (h.path_equiv p).nodes.take p.nodes.length = (h.path_equiv p).nodes := by
        rw [h.path_length_eq p, List.take_length]
      simp only [List.take_length, htake] at himage
      exact himage.symm ▸ hz
end TaggedSegmentExpressionIsomorphism

/-- Exact network data up to one global renaming of nodes. The arbitrary
routing values outside node output images and proof fields are not data of
the underlying transition graph. -/
structure NetworkDataIsomorphism
    (N : FiniteOperatorNetwork X bot V) (M : FiniteOperatorNetwork X bot W) where
  node_equiv : V ≃ W
  source_eq : N.U = M.U
  node_op_eq : ∀ v, N.node_op v = M.node_op (node_equiv v)
  entry_domain_eq : ∀ v, N.entry_domain v = M.entry_domain (node_equiv v)
  edge_domain_eq : ∀ v w, N.edge_domain v w = M.edge_domain (node_equiv v) (node_equiv w)
  terminal_domain_eq : ∀ v, N.terminal_domain v = M.terminal_domain (node_equiv v)

/-- Equality of entrance blocks gives pointwise equality of the entry map
under the common source-domain identification. -/
theorem NetworkDataIsomorphism.entry_eq (h : NetworkDataIsomorphism N M)
    (x : {x // x ∈ N.U}) :
    h.node_equiv (N.entry x) = M.entry ⟨x.val, h.source_eq ▸ x.property⟩ := by
  have hx : x.val ∈ N.entry_domain (N.entry x) := ⟨x.property, rfl⟩
  rw [h.entry_domain_eq] at hx
  obtain ⟨hxM, heq⟩ := hx
  exact heq.symm

/-- Local-operator equality also identifies the node domains. -/
theorem NetworkDataIsomorphism.node_dom_eq (h : NetworkDataIsomorphism N M) (v : V) :
    N.node_dom v = M.node_dom (h.node_equiv v) := by
  change dom (N.node_op v) = dom (M.node_op (h.node_equiv v))
  rw [h.node_op_eq]

/-- OET anchor: h-31fdfdb343da7ff2
Isomorphic tagged segment expressions reconstruct isomorphic effective
networks. Every local-data equality is proved from the tagged factors. -/
noncomputable def TaggedSegmentExpressionIsomorphism.effective_network_isomorphism
    (h : TaggedSegmentExpressionIsomorphism N M) :
    NetworkDataIsomorphism N.effective_reduction M.effective_reduction where
  node_equiv := h.node_equiv
  source_eq := h.source_eq
  node_op_eq := h.effective_node_operator_eq
  entry_domain_eq := h.entry_domain_eq
  edge_domain_eq := h.edge_domain_eq
  terminal_domain_eq := h.terminal_domain_eq

/-- OET anchor: h-31fdfdb343da7ff2
Effective equivalence determines the effective network up to node renaming. -/
theorem effective_equivalent_implies_effective_network_isomorphic
    (h : EffectiveEquivalent N M) :
    Nonempty (NetworkDataIsomorphism N.effective_reduction M.effective_reduction) := by
  obtain ⟨h⟩ := h
  exact ⟨h.effective_network_isomorphism⟩

end FiniteOperatorNetwork
end formal_oet.vol_01.ch_05_operator_networks
