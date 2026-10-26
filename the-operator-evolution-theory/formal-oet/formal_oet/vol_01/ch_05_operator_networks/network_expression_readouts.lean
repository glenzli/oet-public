import formal_oet.vol_01.ch_05_operator_networks.effective_equivalence
import formal_oet.vol_01.ch_05_operator_networks.network_profiles

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus

variable {X V : Type} {bot : X}

/--
OET anchor: h-374f884cd4d69e88
A finite unindexed family of nonempty, disjoint input pieces and payloads.
Only pieces and payloads are data; no originating network or path labels are
retained as an index. The source is the union of the pieces.
-/
@[ext] structure FiniteSegmentExpression (X : Type) (bot : X) (F : Type) where
  pieces : Set (Set X × F)
  finite : pieces.Finite
  nonempty : ∀ s ∈ pieces, s.1.Nonempty
  disjoint : ∀ s ∈ pieces, ∀ t ∈ pieces, s ≠ t → Disjoint s.1 t.1
  bot_not_mem : ∀ s ∈ pieces, bot ∉ s.1

namespace FiniteSegmentExpression

variable {F G : Type}

/-- An empty expression has empty source and no payload. -/
def empty : FiniteSegmentExpression X bot F where
  pieces := ∅
  finite := Set.finite_empty
  nonempty := by simp
  disjoint := by simp
  bot_not_mem := by simp

/-- Forget or transform payload data without retaining its former indices. -/
def map (f : F → G) (E : FiniteSegmentExpression X bot F) :
    FiniteSegmentExpression X bot G where
  pieces := (fun s : Set X × F => (s.1, f s.2)) '' E.pieces
  finite := E.finite.image _
  nonempty := by rintro _ ⟨s, hs, rfl⟩; exact E.nonempty s hs
  disjoint := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩ hne
    exact E.disjoint s hs t ht (fun h => hne (by dsimp; rw [h]))
  bot_not_mem := by rintro _ ⟨s, hs, rfl⟩; exact E.bot_not_mem s hs

/-- A point belongs to at most one complete piece, including its payload. -/
theorem piece_unique (E : FiniteSegmentExpression X bot F)
    {s t : Set X × F} (hs : s ∈ E.pieces) (ht : t ∈ E.pieces)
    {x : X} (hxs : x ∈ s.1) (hxt : x ∈ t.1) : s = t := by
  by_contra hne
  exact Set.disjoint_left.mp (E.disjoint s hs t ht hne) hxs hxt

end FiniteSegmentExpression

/-- OET anchor: h-374f884cd4d69e88
The common value space of untagged path readouts. -/
abbrev PathReadout (X : Type) (bot : X) :=
  FiniteSegmentExpression X bot (Operator X bot)

/-- OET anchor: h-adb38f8458662a70
The common value space of tagged readouts. Natural-number labels record one
shared numbering across all pieces; the source network is not part of the value.
-/
abbrev TaggedReadout (X : Type) (bot : X) :=
  FiniteSegmentExpression X bot (List (Nat × Operator X bot))

namespace PathReadout

/-- OET anchor: h-374f884cd4d69e88
Glue the recorded operators on their pieces and use the absorbing point outside.
-/
noncomputable def evaluate (E : PathReadout X bot) : Operator X bot := by
  classical
  refine ⟨fun x => if h : ∃ s ∈ E.pieces, x ∈ s.1 then
    (Classical.choose h).2.func x else bot, ?_⟩
  have hnone : ¬ ∃ s ∈ E.pieces, bot ∈ s.1 := by
    rintro ⟨s, hs, hx⟩
    exact E.bot_not_mem s hs hx
  simp [hnone]

theorem evaluate_of_mem (E : PathReadout X bot)
    {s : Set X × Operator X bot} (hs : s ∈ E.pieces)
    {x : X} (hx : x ∈ s.1) : E.evaluate.func x = s.2.func x := by
  classical
  have h : ∃ t ∈ E.pieces, x ∈ t.1 := ⟨s, hs, hx⟩
  have hc := Classical.choose_spec h
  have heq : Classical.choose h = s := E.piece_unique hc.1 hs hc.2 hx
  simp only [evaluate, dif_pos h]
  rw [heq]

theorem evaluate_of_not_mem (E : PathReadout X bot) {x : X}
    (hx : ¬ ∃ s ∈ E.pieces, x ∈ s.1) : E.evaluate.func x = bot := by
  classical
  simp only [evaluate, dif_neg hx]

end PathReadout

namespace TaggedReadout

/-- OET anchor: h-adb38f8458662a70
Compose each ordered factor list, discarding all labels and factor boundaries.
-/
noncomputable def forget (E : TaggedReadout X bot) : PathReadout X bot :=
  E.map fun factors => OperatorChain (factors.map Prod.snd).reverse

end TaggedReadout

namespace FiniteOperatorNetwork

variable (N : FiniteOperatorNetwork X bot V)

/-- OET anchor: h-374f884cd4d69e88
The raw-network path readout retains input pieces and complete composites only.
-/
noncomputable def path_readout : PathReadout X bot where
  pieces := Set.range fun p : N.ReachablePath => (N.path_domain p.nodes, N.path_chain p.nodes)
  finite := Set.finite_range _
  nonempty := by rintro _ ⟨p, rfl⟩; exact p.nonempty_domain
  disjoint := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hne
    exact N.disjoint_path_domain_of_ne (fun h => hne (by dsimp; rw [h]))
  bot_not_mem := by
    rintro _ ⟨p, rfl⟩ hx
    exact N.bot_not_mem (N.path_domain_subset_source hx)

/-- OET anchor: h-adb38f8458662a70
A single injective label map preserves node identity and sharing across every
factor and every piece of the raw-network tagged readout.
-/
noncomputable def tagged_readout (label : V ↪ Nat) : TaggedReadout X bot where
  pieces := Set.range fun p : N.ReachablePath =>
    (N.path_domain p.nodes, p.nodes.map fun β => (label β, N.node_op β))
  finite := Set.finite_range _
  nonempty := by rintro _ ⟨p, rfl⟩; exact p.nonempty_domain
  disjoint := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ hne
    exact N.disjoint_path_domain_of_ne (fun h => hne (by dsimp; rw [h]))
  bot_not_mem := by
    rintro _ ⟨p, rfl⟩ hx
    exact N.bot_not_mem (N.path_domain_subset_source hx)

/-- OET anchor: h-adb38f8458662a70
The first forgetting map gives exactly the untagged raw-network readout.
-/
theorem tagged_readout_forget (label : V ↪ Nat) :
    (N.tagged_readout label).forget = N.path_readout := by
  apply FiniteSegmentExpression.ext
  ext s
  constructor
  · rintro ⟨_, ⟨p, rfl⟩, rfl⟩
    refine ⟨p, ?_⟩
    simp [path_chain, Function.comp_def]
  · rintro ⟨p, rfl⟩
    refine ⟨(N.path_domain p.nodes,
      p.nodes.map fun β => (label β, N.node_op β)), ⟨p, rfl⟩, ?_⟩
    simp [path_chain, Function.comp_def]

/-- OET anchor: h-374f884cd4d69e88
Gluing path pieces recovers the complete operator, including its value outside U.
-/
theorem path_readout_evaluate : N.path_readout.evaluate = N.extensional_operator := by
  ext x
  by_cases hx : x ∈ N.U
  · let p : N.ReachablePath := ⟨N.path_of ⟨x, hx⟩, ⟨x, hx, rfl⟩⟩
    have heval := N.path_readout.evaluate_of_mem
      (s := (N.path_domain p.nodes, N.path_chain p.nodes))
      (show (N.path_domain p.nodes, N.path_chain p.nodes) ∈ N.path_readout.pieces from ⟨p, rfl⟩)
      (show x ∈ N.path_domain p.nodes from ⟨hx, rfl⟩)
    exact heval.trans ((N.local_equivalent_extensional_path_chain p) x ⟨hx, rfl⟩).symm
  · rw [N.path_readout.evaluate_of_not_mem]
    · simp [extensional_operator, hx]
    · rintro ⟨_, ⟨p, rfl⟩, hxp⟩
      exact hx (N.path_domain_subset_source hxp)

/-- Changing node labels changes no complete path-chain operator. -/
theorem path_chain_relabel {W : Type} (e : V ≃ W) (p : List V) :
    (N.relabel e).path_chain (p.map e) = N.path_chain p := by
  ext x
  rw [(N.relabel e).path_chain_apply_eq_chain_eval_nodes,
    N.path_chain_apply_eq_chain_eval_nodes]
  exact N.chain_eval_nodes_relabel e p x

/-- OET anchor: h-374f884cd4d69e88
The untagged readout is invariant under a global node renaming. The original
path indices have actually been discarded, rather than hidden in its value type.
-/
theorem path_readout_relabel {W : Type} (e : V ≃ W) :
    (N.relabel e).path_readout = N.path_readout := by
  apply FiniteSegmentExpression.ext
  ext s
  constructor
  · rintro ⟨q, rfl⟩
    rcases q.nonempty_domain with ⟨x, hx, hq⟩
    let p : N.ReachablePath := ⟨N.path_of ⟨x, hx⟩, ⟨x, hx, rfl⟩⟩
    have hnodes : q.nodes = p.nodes.map e := hq.symm
    refine ⟨p, ?_⟩
    dsimp
    rw [hnodes, N.relabel_path_domain e, N.path_chain_relabel e]
  · rintro ⟨p, rfl⟩
    let q : (N.relabel e).ReachablePath := ⟨p.nodes.map e, by
      rw [N.relabel_path_domain e]
      exact p.nonempty_domain⟩
    refine ⟨q, ?_⟩
    change ((N.relabel e).path_domain (p.nodes.map e),
      (N.relabel e).path_chain (p.nodes.map e)) = _
    rw [N.relabel_path_domain e, N.path_chain_relabel e]

/-- The untagged expression depends only on its actual path domains and factors. -/
theorem path_readout_eq_of_domains_node_ops (M : FiniteOperatorNetwork X bot V)
    (hdom : ∀ p, N.path_domain p = M.path_domain p) (hop : N.node_op = M.node_op) :
    N.path_readout = M.path_readout := by
  apply FiniteSegmentExpression.ext
  ext s
  constructor
  · rintro ⟨p, rfl⟩
    let q : M.ReachablePath := ⟨p.nodes, by rw [← hdom]; exact p.nonempty_domain⟩
    refine ⟨q, ?_⟩
    change (M.path_domain p.nodes, M.path_chain p.nodes) = _
    rw [← hdom]
    simp only [path_chain, hop]
  · rintro ⟨p, rfl⟩
    let q : N.ReachablePath := ⟨p.nodes, by rw [hdom]; exact p.nonempty_domain⟩
    refine ⟨q, ?_⟩
    change (N.path_domain p.nodes, N.path_chain p.nodes) = _
    rw [hdom]
    simp only [path_chain, hop]

/-- The tagged expression depends on actual domains and one shared factor family. -/
theorem tagged_readout_eq_of_domains_node_ops (M : FiniteOperatorNetwork X bot V)
    (label : V ↪ Nat) (hdom : ∀ p, N.path_domain p = M.path_domain p)
    (hop : N.node_op = M.node_op) :
    N.tagged_readout label = M.tagged_readout label := by
  apply FiniteSegmentExpression.ext
  ext s
  constructor
  · rintro ⟨p, rfl⟩
    let q : M.ReachablePath := ⟨p.nodes, by rw [← hdom]; exact p.nonempty_domain⟩
    refine ⟨q, ?_⟩
    change (M.path_domain p.nodes, p.nodes.map fun β => (label β, M.node_op β)) = _
    rw [← hdom]
    simp only [hop]
  · rintro ⟨p, rfl⟩
    let q : N.ReachablePath := ⟨p.nodes, by rw [hdom]; exact p.nonempty_domain⟩
    refine ⟨q, ?_⟩
    change (N.path_domain p.nodes, p.nodes.map fun β => (label β, N.node_op β)) = _
    rw [hdom]
    simp only [hop]

/-- Readouts respect equality of the original, certificate-free network data. -/
theorem path_readout_eq_of_presentation_data {M : FiniteOperatorNetwork X bot V}
    (h : N.presentation_data = M.presentation_data) : N.path_readout = M.path_readout :=
  N.path_readout_eq_of_domains_node_ops M (presentation_data_eq_path_domain h)
    (presentation_data_eq_node_op h)

/-- Tagged readouts also respect the original numbered data. -/
theorem tagged_readout_eq_of_presentation_data {M : FiniteOperatorNetwork X bot V}
    (label : V ↪ Nat) (h : N.presentation_data = M.presentation_data) :
    N.tagged_readout label = M.tagged_readout label :=
  N.tagged_readout_eq_of_domains_node_ops M label (presentation_data_eq_path_domain h)
    (presentation_data_eq_node_op h)

end FiniteOperatorNetwork

namespace NonemptyOperatorNetwork

/-- Numbered labels are recorded by their natural-number values. -/
def numbered_label (n : Nat) : Fin n ↪ Nat := ⟨Fin.val, Fin.val_injective⟩

/-- The path value does not depend on the chosen implementation witness. -/
theorem presentation_data_eq_path_readout
    {N M : NonemptyOperatorNetwork X bot} (h : N.presentation_data = M.presentation_data) :
    N.network.path_readout = M.network.path_readout := by
  apply presentation_data_eq_elim (P := fun N M =>
    N.network.path_readout = M.network.path_readout) ?_ h
  intro n N M hN hM hd
  exact N.path_readout_eq_of_presentation_data hd

/-- The one global numbering is retained, while implementation witnesses are forgotten. -/
theorem presentation_data_eq_tagged_readout
    {N M : NonemptyOperatorNetwork X bot} (h : N.presentation_data = M.presentation_data) :
    N.network.tagged_readout (numbered_label N.node_count) =
      M.network.tagged_readout (numbered_label M.node_count) := by
  apply presentation_data_eq_elim (P := fun N M =>
    N.network.tagged_readout (numbered_label N.node_count) =
      M.network.tagged_readout (numbered_label M.node_count)) ?_ h
  intro n N M hN hM hd
  exact N.tagged_readout_eq_of_presentation_data (numbered_label n) hd

end NonemptyOperatorNetwork

namespace NetworkObject

/-- OET anchor: h-374f884cd4d69e88
The path readout on the faithful numbered object space is well defined.
Its value retains neither the original object nor the original path indices.
-/
noncomputable def path_readout : NetworkObject X bot → PathReadout X bot :=
  lift FiniteSegmentExpression.empty (fun N => N.network.path_readout)
    (fun _ _ h => NonemptyOperatorNetwork.presentation_data_eq_path_readout h)

/-- OET anchor: h-adb38f8458662a70
The tagged readout is well defined on the same faithful object space.
-/
noncomputable def tagged_readout : NetworkObject X bot → TaggedReadout X bot :=
  lift FiniteSegmentExpression.empty
    (fun N => N.network.tagged_readout (NonemptyOperatorNetwork.numbered_label N.node_count))
    (fun _ _ h => NonemptyOperatorNetwork.presentation_data_eq_tagged_readout h)

@[simp] theorem path_readout_empty :
    (empty : NetworkObject X bot).path_readout = FiniteSegmentExpression.empty := rfl

@[simp] theorem path_readout_nonempty (N : NonemptyOperatorNetwork X bot) :
    (nonempty N).path_readout = N.network.path_readout := rfl

@[simp] theorem tagged_readout_empty :
    (empty : NetworkObject X bot).tagged_readout = FiniteSegmentExpression.empty := rfl

@[simp] theorem tagged_readout_nonempty (N : NonemptyOperatorNetwork X bot) :
    (nonempty N).tagged_readout =
      N.network.tagged_readout (NonemptyOperatorNetwork.numbered_label N.node_count) := rfl

/-- OET anchor: h-adb38f8458662a70
The tagged-to-path forgetting diagram commutes for every network object,
including the empty network.
-/
theorem tagged_readout_forget (N : NetworkObject X bot) :
    N.tagged_readout.forget = N.path_readout := by
  cases N with
  | empty =>
      apply FiniteSegmentExpression.ext
      simp [TaggedReadout.forget, FiniteSegmentExpression.map, FiniteSegmentExpression.empty]
  | present q =>
      induction q using Quotient.inductionOn with
      | h N => exact N.network.tagged_readout_forget _

/-- OET anchor: h-374f884cd4d69e88
The path-to-operator forgetting diagram commutes on the entire base space.
-/
theorem path_readout_evaluate (N : NetworkObject X bot) :
    N.path_readout.evaluate = N.extensional_operator := by
  cases N with
  | empty =>
      ext x
      exact PathReadout.evaluate_of_not_mem FiniteSegmentExpression.empty (by
        simp [FiniteSegmentExpression.empty])
  | present q =>
      induction q using Quotient.inductionOn with
      | h N => exact N.network.path_readout_evaluate

/-- Encoding arbitrary finite labels does not change the untagged readout. -/
theorem path_readout_encode (N : FiniteOperatorNetwork X bot V) (hU : N.U.Nonempty) :
    (nonempty (NonemptyOperatorNetwork.encode N hU)).path_readout = N.path_readout := by
  change N.standard_relabel.path_readout = N.path_readout
  exact N.path_readout_relabel _

end NetworkObject

/-- OET anchor: h-374f884cd4d69e88
The path readout value space consists of network-induced expressions. The
existence of an inducing network is a proposition, not retained readout data.
-/
abbrev NetworkPathReadout (X : Type) (bot : X) :=
  {E : PathReadout X bot // E ∈ Set.range (NetworkObject.path_readout (X := X) (bot := bot))}

/-- OET anchor: h-adb38f8458662a70
The tagged readout value space consists of network-induced tagged expressions.
Only the expression is retained as data; its realizability witness is a proof.
-/
abbrev NetworkTaggedReadout (X : Type) (bot : X) :=
  {E : TaggedReadout X bot // E ∈ Set.range (NetworkObject.tagged_readout (X := X) (bot := bot))}

/-- OET anchor: h-adb38f8458662a70
Forgetting tags is a map between the exact common value spaces.
-/
noncomputable def NetworkTaggedReadout.forget (E : NetworkTaggedReadout X bot) :
    NetworkPathReadout X bot :=
  ⟨E.val.forget, by
    rcases E.property with ⟨N, hN⟩
    exact ⟨N, (NetworkObject.tagged_readout_forget N).symm.trans
      (congrArg TaggedReadout.forget hN)⟩⟩

/-- OET anchor: h-374f884cd4d69e88
The second forgetting map produces the complete absorbing-point extension.
-/
noncomputable def NetworkPathReadout.evaluate (E : NetworkPathReadout X bot) :
    Operator X bot := E.val.evaluate

/-- OET anchor: h-374f884cd4d69e88
The common-value-space path profile corresponding to the chapter's Γ_path.
-/
noncomputable def path_profile :
    NetworkProfile (NetworkObject X bot) (NetworkPathReadout X bot) where
  read := fun N => ⟨N.path_readout, ⟨N, rfl⟩⟩

/-- OET anchor: h-adb38f8458662a70
The common-value-space tagged profile corresponding to Γ_tag.
-/
noncomputable def tagged_profile :
    NetworkProfile (NetworkObject X bot) (NetworkTaggedReadout X bot) where
  read := fun N => ⟨N.tagged_readout, ⟨N, rfl⟩⟩

/-- OET anchor: h-adb38f8458662a70
The tagged-to-path diagram also commutes in the exact realizable value spaces.
-/
theorem tagged_profile_forget (N : NetworkObject X bot) :
    NetworkTaggedReadout.forget ((tagged_profile (X := X) (bot := bot)).read N) =
      (path_profile (X := X) (bot := bot)).read N := by
  apply Subtype.ext
  exact N.tagged_readout_forget

/-- OET anchor: h-374f884cd4d69e88
The path-to-operator diagram commutes on every network object.
-/
theorem path_profile_evaluate (N : NetworkObject X bot) :
    NetworkPathReadout.evaluate ((path_profile (X := X) (bot := bot)).read N) =
      (operator_profile (X := X) (bot := bot)).read N :=
  N.path_readout_evaluate

end formal_oet.vol_01.ch_05_operator_networks
