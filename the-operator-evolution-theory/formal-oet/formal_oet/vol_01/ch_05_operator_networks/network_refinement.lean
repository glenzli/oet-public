import formal_oet.vol_01.ch_05_operator_networks.network_routing
import formal_oet.vol_01.ch_05_operator_networks.effective_equivalence
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open scoped BigOperators

variable {X V V' : Type} {bot : X}

namespace FiniteOperatorNetwork

/-- Evaluation of a list of operators in the order in which its factors are
encountered along a network path. -/
def operator_list_eval : List (Operator X bot) → X → X
  | [], x => x
  | φ :: rest, x => operator_list_eval rest (φ.func x)

/-- Ordered-list evaluation respects concatenation. -/
theorem operator_list_eval_append (left right : List (Operator X bot)) (x : X) :
    operator_list_eval (left ++ right) x =
      operator_list_eval right (operator_list_eval left x) := by
  induction left generalizing x with
  | nil => rfl
  | cons φ rest ih =>
      simp only [List.cons_append, operator_list_eval]
      exact ih (φ.func x)

/-- Evaluating the local-operator list attached to a node path agrees with
the network's path evaluator. -/
theorem operator_list_eval_map_node_op
    (N : FiniteOperatorNetwork X bot V) (nodes : List V) (x : X) :
    operator_list_eval (nodes.map N.node_op) x = N.chain_eval_nodes nodes x := by
  induction nodes generalizing x with
  | nil => rfl
  | cons β rest ih =>
      simp only [List.map_cons, operator_list_eval,
        FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core]
      exact ih ((N.node_op β).func x)

/-- Transport the same point between two propositionally equal network input
domains. -/
def transport_network_input {U U' : Set X} (hU : U' = U) :
    {x : X // x ∈ U'} → {x : X // x ∈ U} :=
  fun x => ⟨x.val, hU ▸ x.property⟩

/-- A partition piece is retained after redundant-node deletion exactly when
some realised occurrence of the split node receives an input in that piece. -/
def NodePieceReached (N : FiniteOperatorNetwork X bot V) (target : V)
    {A : Type} (piece : A → Set X) (a : A) : Prop :=
  ∃ x : {x : X // x ∈ N.U},
    ∃ n : Fin (N.path_of x).length,
      (N.path_of x).get n = target ∧
        N.chain_eval_nodes ((N.path_of x).take n.val) x.val ∈ piece a

/-- Project a split-node label back to its original node. -/
def node_domain_projection (target : V) {A : Type}
    (source : V' → ({v : V // v ≠ target} ⊕ A)) (v : V') : V :=
  match source v with
  | .inl w => w.val
  | .inr _ => target

/-- An auxiliary relation preserving realised routing. It is deliberately weaker
than textbook domain refinement: unused edges are not constrained here.
`NodeDomainRefinement` below adds their exact full-domain intersection laws. -/
structure OperationalNodeDomainRefinement
    (N : FiniteOperatorNetwork X bot V)
    (N' : FiniteOperatorNetwork X bot V') where
  target : V
  part_count : Nat
  part_count_pos : 0 < part_count
  piece : Fin part_count → Set X
  piece_nonempty : ∀ a : Fin part_count, (piece a).Nonempty
  piece_disjoint :
    ∀ {a b : Fin part_count}, a ≠ b → Disjoint (piece a) (piece b)
  piece_cover : (⋃ a : Fin part_count, piece a) = N.node_dom target
  local_factor : Fin part_count → Operator X bot
  local_domain :
    ∀ a : Fin part_count, dom (local_factor a) = piece a
  local_equiv :
    ∀ a : Fin part_count,
      LocalEquivalent (local_factor a) (N.node_op target) (piece a)
  source : V' → ({β : V // β ≠ target} ⊕ Fin part_count)
  source_injective : Function.Injective source
  old_node_present :
    ∀ β : {β : V // β ≠ target}, ∃ β' : V', source β' = Sum.inl β
  piece_node_present_iff_reached :
    ∀ a : Fin part_count,
      (∃ β' : V', source β' = Sum.inr a) ↔ NodePieceReached N target piece a
  old_node_op_compat :
    ∀ (β' : V') (β : {β : V // β ≠ target}),
      source β' = Sum.inl β → N'.node_op β' = N.node_op β.val
  piece_node_op_compat :
    ∀ (β' : V') (a : Fin part_count),
      source β' = Sum.inr a → N'.node_op β' = local_factor a
  same_input_domain : N'.U = N.U
  entry_projection :
    ∀ x : N'.U, node_domain_projection target source (N'.entry x) =
      N.entry (transport_network_input same_input_domain x)
  -- Pruning may change choices at outputs never reached from the source.
  choice_projection :
    ∀ (v : V') (z : X), z ∈ (N'.node_op v).func '' N'.node_actual_input_domain v →
      map_output_choice (node_domain_projection target source) (N'.choice v z) =
        N.choice (node_domain_projection target source v) z


/--
OET anchor: h-eddd1f2d0a9d3528
**定义（网络加细，节点域加细）**
The exact relation after unreachable-piece deletion. Every retained edge is
prescribed on the full local output image, including edges never used by an
entry trajectory. Intersecting with the source image and destination domain
simultaneously covers old edges, incoming/outgoing edges and split self-loops.
The actual construction satisfies all fields in `domain_refinement_construction`.
-/
structure NodeDomainRefinement
    (N : FiniteOperatorNetwork X bot V)
    (N' : FiniteOperatorNetwork X bot V')
    extends OperationalNodeDomainRefinement N N' where
  edge_domain_eq : ∀ v w : V',
    N'.edge_domain v w =
      (N.edge_domain (node_domain_projection target source v)
        (node_domain_projection target source w) ∩ N'.node_image v) ∩ N'.node_dom w


/-- A successor entering a replaced node must enter its first factor.
The second factor is an internal node and cannot be an external entry. -/
def algebraic_entry_projection (target : V)
    (source : V' → ({v : V // v ≠ target} ⊕ Bool)) (v : V') : Option V :=
  match source v with
  | .inl w => some w.val
  | .inr false => some target
  | .inr true => none

/-- The same local stop/next decision, with a valid lifted destination. -/
def ChoiceLift (f : V' → Option V) : OutputChoice V' → OutputChoice V → Prop
  | .stop, .stop => True
  | .next v, .next w => f v = some w
  | _, _ => False

/--
OET anchor: h-eddd1f2d0a9d3528
**定义（网络加细，代数加细）**
Local entry, internal-factor edge and inherited successor laws from the text.
This relation proves equivalence for given finite networks. The standalone
construction from factor data is in `algebraic_refinement_construction`,
where equivalence is proved directly for the constructed network. -/
structure AlgebraicRefinement
    (N : FiniteOperatorNetwork X bot V)
    (N' : FiniteOperatorNetwork X bot V') where
  target : V
  first_factor : Operator X bot
  second_factor : Operator X bot
  first_domain : N.node_dom target ⊆ dom first_factor
  second_domain :
    first_factor.func '' N.node_dom target ⊆ dom second_factor
  factorization :
    ∀ x ∈ N.node_dom target,
      (N.node_op target).func x =
        second_factor.func (first_factor.func x)
  source : V' → ({β : V // β ≠ target} ⊕ Bool)
  source_bijective : Function.Bijective source
  old_node_op_compat :
    ∀ (β' : V') (β : {β : V // β ≠ target}),
      source β' = Sum.inl β → N'.node_op β' = N.node_op β.val
  first_node_op_compat :
    ∀ β' : V', source β' = Sum.inr false →
      N'.node_op β' = restrict_operator first_factor (N.node_dom target)
  second_node_op_compat :
    ∀ β' : V', source β' = Sum.inr true →
      N'.node_op β' = restrict_operator second_factor
        (first_factor.func '' N.node_dom target)
  same_input_domain : N'.U = N.U
  entry_projection :
    ∀ x : N'.U, algebraic_entry_projection target source (N'.entry x) =
      some (N.entry (transport_network_input same_input_domain x))
  old_choice :
    ∀ (v : V') (w : {v : V // v ≠ target}), source v = .inl w →
      ∀ z ∈ N'.node_image v,
        ChoiceLift (algebraic_entry_projection target source) (N'.choice v z) (N.choice w.val z)
  first_choice :
    ∀ (v : V'), source v = .inr false → ∀ z ∈ N'.node_image v,
      ∃ w, source w = .inr true ∧ N'.choice v z = .next w
  second_choice :
    ∀ (v : V'), source v = .inr true → ∀ z ∈ N'.node_image v,
      ChoiceLift (algebraic_entry_projection target source) (N'.choice v z) (N.choice target z)


namespace NodeDomainRefinement

variable {N : FiniteOperatorNetwork X bot V} {N' : FiniteOperatorNetwork X bot V'}
variable (h : NodeDomainRefinement N N')

def projection (v : V') : V := node_domain_projection h.target h.source v

theorem node_eval_eq (v : V') (x : X) (hx : x ∈ N'.node_dom v) :
    (N'.node_op v).func x = (N.node_op (h.projection v)).func x := by
  cases hs : h.source v with
  | inl w => simp [projection, node_domain_projection, hs, h.old_node_op_compat v w hs]
  | inr a =>
    have hxpiece : x ∈ h.piece a := by
      rw [← h.local_domain a, ← h.piece_node_op_compat v a hs]
      exact hx
    simpa [projection, node_domain_projection, hs, h.piece_node_op_compat v a hs] using
      h.local_equiv a x hxpiece

theorem terminal_projection {v x p}
    (ht : TerminalPathFrom N'.node_op N'.choice v x p) (hx : x ∈ N'.node_actual_input_domain v) :
    TerminalPathFrom N.node_op N.choice (h.projection v) x (p.map h.projection) := by
  induction ht with
  | @stop v x hs =>
    have hdom := N'.node_actual_input_domain_subset_node_dom v hx
    apply TerminalPathFrom.stop
    have hc := h.choice_projection v ((N'.node_op v).func x) ⟨x, hx, rfl⟩
    rw [hs, map_output_choice] at hc
    simpa only [← h.node_eval_eq v x hdom] using hc.symm
  | @next v w x rest hs ht ih =>
    have hdom := N'.node_actual_input_domain_subset_node_dom v hx
    have hy := N'.next_output_mem_node_actual_input_domain hx hs
    have hc := h.choice_projection v ((N'.node_op v).func x) ⟨x, hx, rfl⟩
    rw [hs, map_output_choice] at hc
    apply TerminalPathFrom.next (γ := h.projection w)
    · simpa only [← h.node_eval_eq v x hdom] using hc.symm
    · simpa only [← h.node_eval_eq v x hdom] using ih hy

theorem path_projection (x : N'.U) :
    (N'.path_of x).map h.projection =
      N.path_of (transport_network_input h.same_input_domain x) := by
  apply terminal_path_unique
  · simpa only [projection, h.entry_projection x] using
      h.terminal_projection (N'.path_terminal x) (N'.entry_mem_node_actual_input_domain x)
  · exact N.path_terminal _

theorem eval_projected {v x p}
    (ht : TerminalPathFrom N'.node_op N'.choice v x p) (hx : x ∈ N'.node_dom v) :
    chain_eval_nodes_core N'.node_op p x =
      chain_eval_nodes_core N.node_op (p.map h.projection) x := by
  induction ht with
  | @stop v x hs =>
    simp only [List.map_cons, List.map_nil, chain_eval_nodes_core, h.node_eval_eq v x hx]
  | @next v w x rest hs ht ih =>
    simp only [List.map_cons, chain_eval_nodes_core]
    rw [← h.node_eval_eq v x hx]
    exact ih (N'.choice_next_mem hx hs)

/-- Two surviving copies of the same original node cannot share a local input. -/
theorem label_eq_of_projection_eq_of_mem {v w : V'} (hp : h.projection v = h.projection w)
    {x : X} (hv : x ∈ N'.node_dom v) (hw : x ∈ N'.node_dom w) : v = w := by
  apply h.source_injective
  cases hs : h.source v with
  | inl a =>
    cases ht : h.source w with
    | inl b =>
      have hab : a.val = b.val := by simpa [projection, node_domain_projection, hs, ht] using hp
      rw [← Subtype.ext hab]
    | inr b =>
      have ha : a.val = h.target := by simpa [projection, node_domain_projection, hs, ht] using hp
      exact False.elim (a.property ha)
  | inr a =>
    cases ht : h.source w with
    | inl b =>
      have hb : h.target = b.val := by simpa [projection, node_domain_projection, hs, ht] using hp
      exact False.elim (b.property hb.symm)
    | inr b =>
      have ha : x ∈ h.piece a := by
        rw [← h.local_domain a, ← h.piece_node_op_compat v a hs]
        exact hv
      have hb : x ∈ h.piece b := by
        rw [← h.local_domain b, ← h.piece_node_op_compat w b ht]
        exact hw
      have hab : a = b := by
        by_contra hab
        exact Set.disjoint_left.mp (h.piece_disjoint hab) ha hb
      rw [hab]

/--
OET anchor: h-eddd1f2d0a9d3528
Entry projection and disjoint piece domains give the exact entry intersections.
Thus unchanged old entry pieces and split-node entry pieces are both recovered.
-/
theorem entry_domain_eq (v : V') :
    N'.entry_domain v = N.entry_domain (h.projection v) ∩ N'.node_dom v := by
  ext x
  constructor
  · rintro ⟨hx, he⟩
    have hp := h.entry_projection ⟨x, hx⟩
    rw [he] at hp
    refine ⟨⟨h.same_input_domain ▸ hx, hp.symm⟩, ?_⟩
    simpa only [he] using N'.entry_mem ⟨x, hx⟩
  · rintro ⟨⟨hx, he⟩, hdom⟩
    have hx' : x ∈ N'.U := h.same_input_domain.symm ▸ hx
    refine ⟨hx', ?_⟩
    apply h.label_eq_of_projection_eq_of_mem _ (N'.entry_mem ⟨x, hx'⟩) hdom
    exact (h.entry_projection ⟨x, hx'⟩).trans he

/-- A retained edge cannot be removed at a point in its full source image and
full destination domain, whether or not that point is actually encountered. -/
theorem retained_edge_mem {v w : V'} {z : X}
    (hz : z ∈ N.edge_domain (h.projection v) (h.projection w))
    (hv : z ∈ N'.node_image v) (hw : z ∈ N'.node_dom w) :
    z ∈ N'.edge_domain v w := by
  rw [h.edge_domain_eq]
  exact ⟨⟨hz, hv⟩, hw⟩

end NodeDomainRefinement

namespace AlgebraicRefinement
variable {N : FiniteOperatorNetwork X bot V} {N' : FiniteOperatorNetwork X bot V'}
variable (h : AlgebraicRefinement N N')

/-- Complete exactly one original node, using one unchanged node or the two
prescribed factors. This is derived from local routing and factorization. -/
theorem finish_step {v : V} {v' : V'} {x : X} {p : List V'}
    (hs : algebraic_entry_projection h.target h.source v' = some v)
    (ht : TerminalPathFrom N'.node_op N'.choice v' x p)
    (hx : x ∈ N'.node_dom v') :
    ∃ (w : V') (z : X) (q : List V'),
      z ∈ N'.node_dom w ∧
      TerminalPathFrom N'.node_op N'.choice w z q ∧
      chain_eval_nodes_core N'.node_op p x = chain_eval_nodes_core N'.node_op q z ∧
      (N'.node_op w).func z = (N.node_op v).func x ∧
      ChoiceLift (algebraic_entry_projection h.target h.source)
        (N'.choice w ((N'.node_op w).func z))
        (N.choice v ((N.node_op v).func x)) := by
  cases hv : h.source v' with
  | inl old =>
    have hvv : old.val = v := by simpa [algebraic_entry_projection, hv] using hs
    subst v
    have hop := h.old_node_op_compat v' old hv
    refine ⟨v', x, p, hx, ht, rfl, congrArg (fun f : Operator X bot => f.func x) hop, ?_⟩
    have hc := h.old_choice v' old hv ((N'.node_op v').func x) ⟨x, hx, rfl⟩
    simpa only [hop] using hc
  | inr b =>
    cases b with
    | true => simp [algebraic_entry_projection, hv] at hs
    | false =>
      have hvv : h.target = v := by simpa [algebraic_entry_projection, hv] using hs
      subst v
      have hf := h.first_node_op_compat v' hv
      have hdomain : x ∈ N.node_dom h.target := by
        have hd : dom (N'.node_op v') = N.node_dom h.target := by
          rw [hf, dom_restrict_operator_eq _ _ h.first_domain]
        exact hd ▸ hx
      rcases h.first_choice v' hv ((N'.node_op v').func x) ⟨x, hx, rfl⟩ with ⟨w, hw, hc⟩
      cases ht with
      | stop hstop => simp [hstop] at hc
      | @next _ u _ rest hnext hrest =>
        have huw : u = w := OutputChoice.next.inj (hnext.symm.trans hc)
        subst u
        have hz := N'.choice_next_mem hx hc
        have hout : (N'.node_op w).func ((N'.node_op v').func x) =
            (N.node_op h.target).func x := by
          rw [h.second_node_op_compat w hw, hf,
            restrict_operator_apply_of_mem _ _ hdomain,
            restrict_operator_apply_of_mem h.second_factor
              (h.first_factor.func '' N.node_dom h.target)
              (Set.mem_image_of_mem h.first_factor.func hdomain)]
          exact (h.factorization x hdomain).symm
        refine ⟨w, (N'.node_op v').func x, rest, hz, hrest, rfl, hout, ?_⟩
        have hl := h.second_choice w hw ((N'.node_op w).func ((N'.node_op v').func x))
          ⟨(N'.node_op v').func x, hz, rfl⟩
        simpa only [hout] using hl

/-- Local entry and successor rules imply equality of complete evaluations.
The induction follows the original terminal path; factor nodes consume one
original step together. No complete path correspondence is an input. -/
theorem eval_from {v x p}
    (ht : TerminalPathFrom N.node_op N.choice v x p) :
    ∀ {v' q}, algebraic_entry_projection h.target h.source v' = some v →
      TerminalPathFrom N'.node_op N'.choice v' x q → x ∈ N'.node_dom v' →
      chain_eval_nodes_core N'.node_op q x = chain_eval_nodes_core N.node_op p x := by
  induction ht with
  | @stop v x hs =>
    intro v' q hentry hnew hx
    rcases h.finish_step hentry hnew hx with ⟨w, z, rest, hz, hr, heval, hout, hl⟩
    cases hr with
    | stop hstop =>
      simpa only [chain_eval_nodes_core] using heval.trans hout
    | next hnext hrest =>
      simp only [ChoiceLift, hnext, hs] at hl
  | @next v u x tail hs ht ih =>
    intro v' q hentry hnew hx
    rcases h.finish_step hentry hnew hx with ⟨w, z, rest, hz, hr, heval, hout, hl⟩
    cases hr with
    | stop hstop => simp only [ChoiceLift, hstop, hs] at hl
    | @next _ w' _ rest' hnext hrest =>
      simp only [ChoiceLift, hnext, hs] at hl
      have hz' := N'.choice_next_mem hz hnext
      rw [hout] at hrest hz'
      have hi := ih hl hrest hz'
      calc
        chain_eval_nodes_core N'.node_op q x =
            chain_eval_nodes_core N'.node_op rest' ((N'.node_op w).func z) := heval
        _ = chain_eval_nodes_core N'.node_op rest' ((N.node_op v).func x) := by rw [hout]
        _ = chain_eval_nodes_core N.node_op tail ((N.node_op v).func x) := hi
        _ = chain_eval_nodes_core N.node_op (v :: tail) x := rfl

end AlgebraicRefinement

/--
OET anchor: h-eddd1f2d0a9d3528
**定义（网络加细）**
The two one-step refinements admitted by the text, kept disjoint at the
formal boundary instead of being hidden in a broad certificate. -/
inductive NetworkRefinement
    (N : FiniteOperatorNetwork X bot V)
    (N' : FiniteOperatorNetwork X bot V') : Type where
  | node_domain : NodeDomainRefinement N N' → NetworkRefinement N N'
  | algebraic : AlgebraicRefinement N N' → NetworkRefinement N N'

def NetworkRefinement.same_input_domain
    {N : FiniteOperatorNetwork X bot V}
    {N' : FiniteOperatorNetwork X bot V'}
    (h : NetworkRefinement N N') : N'.U = N.U :=
  match h with
  | .node_domain href => href.same_input_domain
  | .algebraic href => href.same_input_domain

def NetworkRefinement.old_input
    {N : FiniteOperatorNetwork X bot V}
    {N' : FiniteOperatorNetwork X bot V'}
    (h : NetworkRefinement N N') :
    {x : X // x ∈ N'.U} → {x : X // x ∈ N.U} :=
  transport_network_input h.same_input_domain

theorem NetworkRefinement.path_eval_eq
    {N : FiniteOperatorNetwork X bot V}
    {N' : FiniteOperatorNetwork X bot V'}
    (h : NetworkRefinement N N') (x : {x : X // x ∈ N'.U}) :
    operator_list_eval ((N'.path_of x).map N'.node_op) x.val =
      operator_list_eval ((N.path_of (h.old_input x)).map N.node_op) x.val := by
  cases h with
  | node_domain href =>
      rw [operator_list_eval_map_node_op, operator_list_eval_map_node_op]
      have he := href.eval_projected (N'.path_terminal x) (N'.entry_mem x)
      rw [href.path_projection x] at he
      exact he
  | algebraic href =>
      rw [operator_list_eval_map_node_op, operator_list_eval_map_node_op]
      exact href.eval_from
        (N.path_terminal (transport_network_input href.same_input_domain x))
        (href.entry_projection x)
        (N'.path_terminal x) (N'.entry_mem x)


/--
OET anchor: h-012f4ba72aeb3f20
**命题（加细保持等价）**
若 `N'` 是 `N` 的一步加细，则二者外延算子在 `U` 上局部等价。
-/
theorem refinement_preserves_local_equivalence
    {N : FiniteOperatorNetwork X bot V} {N' : FiniteOperatorNetwork X bot V'}
    (h : NetworkRefinement N N') :
    LocalEquivalent N'.extensional_operator N.extensional_operator N.U := by
  intro x hxU
  let x' : {x : X // x ∈ N'.U} := ⟨x, by
    rw [h.same_input_domain]
    exact hxU⟩
  have hrefined := h.path_eval_eq x'
  calc
    N'.extensional_operator.func x =
        N'.chain_eval_nodes (N'.path_of x') x :=
      N'.extensional_apply_eq_chain_eval_path x'
    _ = operator_list_eval ((N'.path_of x').map N'.node_op) x := by
      exact (operator_list_eval_map_node_op N' (N'.path_of x') x).symm
    _ = operator_list_eval
        ((N.path_of (h.old_input x')).map N.node_op) x := hrefined
    _ = N.chain_eval_nodes (N.path_of (h.old_input x')) x :=
      operator_list_eval_map_node_op N (N.path_of (h.old_input x')) x
    _ = N.extensional_operator.func x :=
      (N.extensional_apply_eq_chain_eval_path (h.old_input x')).symm

/--
OET anchor: h-012f4ba72aeb3f20
**命题（加细保持网络表示）**
若 `N` 表示 `φ`，且 `N'` 是 `N` 的一步加细，则 `N'` 也表示 `φ`。
-/
theorem refinement_preserves_representation
    {N : FiniteOperatorNetwork X bot V} {N' : FiniteOperatorNetwork X bot V'}
    {φ : Operator X bot}
    (hrep : N.represents φ)
    (href : NetworkRefinement N N') :
    N'.represents φ := by
  refine ⟨?_, ?_⟩
  · rw [href.same_input_domain]
    exact hrep.1
  intro x hx
  have hxN : x ∈ N.U := by
    rw [← href.same_input_domain]
    exact hx
  exact
    (refinement_preserves_local_equivalence href x hxN).trans
      (hrep.2 x hxN)

/--
OET anchor: h-eddd1f2d0a9d3528 **定义（允许加细规则）** 允许的一步加细关系。 -/
abbrev RefinementRule (α : Type) := α → α → Prop

/--
OET anchor: h-eddd1f2d0a9d3528 **定义（不可约性）** 对给定规则不存在可继续加细的后继。 -/
def Irreducible {α : Type} (R : RefinementRule α) (N : α) : Prop :=
  ¬ ∃ N' : α, R N N'

/--
OET anchor: h-eddd1f2d0a9d3528
**定义（不可约网络表示）**
具有指定非空输入域、表示给定算子且关于允许规则不可再加细的网络对象。
结构记录这些条件，不声明这样的网络表示存在或唯一。
-/
structure IrreducibleRepresentative (φ : Operator X bot) (U : Set X)
    (R : RefinementRule (NetworkObject X bot)) where
  network : NetworkObject X bot
  source_nonempty : U.Nonempty
  input_domain_eq : dom network.extensional_operator = U
  represents : LocalEquivalent network.extensional_operator φ U
  irreducible : Irreducible R network

/-- The represented source lies in the target operator's domain, as required
by the definition of a network representation. -/
theorem IrreducibleRepresentative.source_subset_dom
    {φ : Operator X bot} {U : Set X}
    {R : RefinementRule (NetworkObject X bot)}
    (N : IrreducibleRepresentative φ U R) : U ⊆ dom φ := by
  intro x hx
  have hx_dom : x ∈ dom N.network.extensional_operator := by
    rw [N.input_domain_eq]
    exact hx
  change φ.func x ≠ bot
  rw [← N.represents x hx]
  exact hx_dom

end FiniteOperatorNetwork

end formal_oet.vol_01.ch_05_operator_networks
