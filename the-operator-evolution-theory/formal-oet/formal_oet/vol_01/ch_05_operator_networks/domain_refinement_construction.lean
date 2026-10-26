import formal_oet.vol_01.ch_05_operator_networks.network_presentation
import formal_oet.vol_01.ch_05_operator_networks.network_refinement

namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open FiniteOperatorNetwork
noncomputable section
variable {X V : Type} {bot : X}

/-- The finite partition and local operators in the node-domain refinement definition. -/
structure NodePartitionData (N : FiniteOperatorNetwork X bot V) (target : V) where
  count : ℕ
  count_pos : 0 < count
  piece : Fin count → Set X
  nonempty : ∀ a, (piece a).Nonempty
  disjoint : ∀ {a b}, a ≠ b → Disjoint (piece a) (piece b)
  cover : (⋃ a, piece a) = N.node_dom target
  local_op : Fin count → Operator X bot
  local_domain : ∀ a, dom (local_op a) = piece a
  local_eq : ∀ a x, x ∈ piece a → (local_op a).func x = (N.node_op target).func x

namespace NodePartitionData
variable {N : FiniteOperatorNetwork X bot V} {target : V}
variable (P : NodePartitionData N target)

/--
OET anchor: h-eddd1f2d0a9d3528
The prescribed domain and local equality determine the whole subnode operator.
-/
theorem local_op_eq_restrict (a : Fin P.count) :
    P.local_op a = restrict_operator (N.node_op target) (P.piece a) := by
  apply Operator.ext
  funext x
  by_cases hx : x ∈ P.piece a
  · rw [restrict_operator_apply_of_mem _ _ hx]
    exact P.local_eq a x hx
  · rw [restrict_operator_apply_of_not_mem _ _ hx]
    by_contra hne
    exact hx ((P.local_domain a) ▸ hne)

abbrev Label := {v : V // v ≠ target} ⊕ Fin P.count

/-- On the target domain the unique partition member is chosen. Outside it the
choice is an irrelevant totalization used only to define the routing function. -/
def piece_at (x : X) : Fin P.count := by
  classical
  exact if h : ∃ a, x ∈ P.piece a then h.choose else ⟨0, P.count_pos⟩

theorem mem_piece_at (x : X) (hx : x ∈ N.node_dom target) : x ∈ P.piece (P.piece_at x) := by
  classical
  have h : ∃ a, x ∈ P.piece a := by rw [← P.cover] at hx; exact Set.mem_iUnion.mp hx
  simpa [piece_at, h] using h.choose_spec

theorem piece_at_unique (x : X) (a : Fin P.count) (hx : x ∈ P.piece a) : P.piece_at x = a := by
  have hxdom : x ∈ N.node_dom target := by rw [← P.cover]; exact Set.mem_iUnion.mpr ⟨a, hx⟩
  by_contra h
  exact Set.disjoint_left.mp (P.disjoint h) (P.mem_piece_at x hxdom) hx

def projection : P.Label → V
  | .inl v => v.val
  | .inr _ => target

def lift_label (v : V) (x : X) : P.Label := by
  classical
  exact if hv : v = target then .inr (P.piece_at x) else .inl ⟨v, hv⟩

@[simp] theorem projection_lift (v : V) (x : X) : P.projection (P.lift_label v x) = v := by
  classical
  by_cases hv : v = target <;> simp [lift_label, projection, hv]

def node_op : P.Label → Operator X bot
  | .inl v => N.node_op v.val
  | .inr a => P.local_op a

theorem lift_mem_dom (v : V) (x : X) (hx : x ∈ N.node_dom v) :
    x ∈ dom (P.node_op (P.lift_label v x)) := by
  classical
  by_cases hv : v = target
  · subst v
    simp only [lift_label, ↓reduceDIte, node_op, P.local_domain]
    exact P.mem_piece_at x hx
  · simpa [lift_label, hv, node_op] using hx

theorem lift_apply (v : V) (x : X) (hx : x ∈ N.node_dom v) :
    (P.node_op (P.lift_label v x)).func x = (N.node_op v).func x := by
  classical
  by_cases hv : v = target
  · subst v
    simp only [lift_label, ↓reduceDIte, node_op]
    exact P.local_eq _ x (P.mem_piece_at x hx)
  · simp [lift_label, hv, node_op]

theorem node_domain_subset_original (v : P.Label) :
    dom (P.node_op v) ⊆ N.node_dom (P.projection v) := by
  cases v with
  | inl v => exact Set.Subset.rfl
  | inr a =>
    intro x hx
    rw [node_op, P.local_domain a] at hx
    change x ∈ N.node_dom target
    rw [← P.cover]
    exact Set.mem_iUnion.mpr ⟨a, hx⟩

theorem node_apply_eq_original (v : P.Label) (x : X) (hx : x ∈ dom (P.node_op v)) :
    (P.node_op v).func x = (N.node_op (P.projection v)).func x := by
  cases v with
  | inl v => rfl
  | inr a => exact P.local_eq a x ((P.local_domain a) ▸ hx)

def choice (v : P.Label) (z : X) : OutputChoice P.Label :=
  map_output_choice (fun w => P.lift_label w z) (N.choice (P.projection v) z)

/--
OET anchor: h-eddd1f2d0a9d3528
A split self-loop must select both the source piece and the destination piece.
This is the routing part of the double-intersection edge formula.
-/
theorem self_loop_choice_iff (a b : Fin P.count) (z : X)
    (hz : z ∈ (P.local_op a).func '' P.piece a) :
    P.choice (.inr a) z = .next (.inr b) ↔
      z ∈ N.edge_domain target target ∧ z ∈ P.piece b := by
  classical
  have himage : z ∈ N.node_image target := by
    rcases hz with ⟨x, hx, rfl⟩
    refine ⟨x, ?_, (P.local_eq a x hx).symm⟩
    change x ∈ N.node_dom target
    rw [← P.cover]
    exact Set.mem_iUnion.mpr ⟨a, hx⟩
  constructor
  · intro h
    unfold choice map_output_choice at h
    split at h
    · contradiction
    · rename_i v hv
      have hlift : P.lift_label v z = .inr b := OutputChoice.next.inj h
      have hvtarget : v = target := by
        have hproj := congrArg P.projection hlift
        change P.projection (P.lift_label v z) = target at hproj
        rw [P.projection_lift] at hproj
        exact hproj
      subst v
      have hpiece : P.piece_at z = b := by
        simpa [lift_label] using hlift
      have hedge : z ∈ N.edge_domain target target := ⟨himage, hv⟩
      refine ⟨hedge, ?_⟩
      rw [← hpiece]
      exact P.mem_piece_at z (N.edge_domain_subset_node_dom hedge)
  · rintro ⟨hedge, hpiece⟩
    have hchoice : N.choice target z = .next target := hedge.2
    simp [choice, projection, map_output_choice, hchoice, lift_label,
      P.piece_at_unique z b hpiece]

theorem choice_next_mem {v w : P.Label} {x : X}
    (hx : x ∈ dom (P.node_op v)) (hc : P.choice v ((P.node_op v).func x) = .next w) :
    (P.node_op v).func x ∈ dom (P.node_op w) := by
  unfold choice map_output_choice at hc
  split at hc
  · contradiction
  · rename_i u hu
    cases hc
    apply P.lift_mem_dom
    have hdom := P.node_domain_subset_original v hx
    rw [P.node_apply_eq_original v x hx] at hu ⊢
    exact N.choice_next_mem hdom hu

/-- Recolour each target occurrence using its actual current input. -/
def colour_path (P : NodePartitionData N target) : List V → X → List P.Label
  | [], _ => []
  | v :: rest, x => P.lift_label v x :: P.colour_path rest ((N.node_op v).func x)

@[simp] theorem colour_path_length (p : List V) (x : X) :
    (P.colour_path p x).length = p.length := by
  induction p generalizing x with
  | nil => rfl
  | cons v rest ih => simp [colour_path, ih]

@[simp] theorem colour_path_projection (p : List V) (x : X) :
    (P.colour_path p x).map P.projection = p := by
  induction p generalizing x with
  | nil => rfl
  | cons v rest ih => simp [colour_path, ih]

theorem coloured_terminal {v x p}
    (ht : TerminalPathFrom N.node_op N.choice v x p) (hx : x ∈ N.node_dom v) :
    TerminalPathFrom P.node_op P.choice (P.lift_label v x) x (P.colour_path p x) := by
  induction ht with
  | @stop v x hs =>
    apply TerminalPathFrom.stop
    simp [choice, P.lift_apply v x hx, hs, map_output_choice]
  | @next v w x rest hs ht ih =>
    apply TerminalPathFrom.next (γ := P.lift_label w ((N.node_op v).func x))
    · simp [choice, P.lift_apply v x hx, hs, map_output_choice]
    · rw [P.lift_apply v x hx]
      exact ih (N.choice_next_mem hx hs)

theorem coloured_eval {v x p}
    (ht : TerminalPathFrom N.node_op N.choice v x p) (hx : x ∈ N.node_dom v) :
    chain_eval_nodes_core P.node_op (P.colour_path p x) x =
      chain_eval_nodes_core N.node_op p x := by
  induction ht with
  | @stop v x hs => simp [colour_path, chain_eval_nodes_core, P.lift_apply v x hx]
  | @next v w x rest hs ht ih =>
    simp only [colour_path, chain_eval_nodes_core, P.lift_apply v x hx]
    exact ih (N.choice_next_mem hx hs)

/-- Every finite-network obligation is derived before unreachable-piece deletion. -/
def presentation : FiniteNetworkPresentation X bot P.Label := by
  classical
  letI := N.node_fintype
  exact {
    U := N.U
    bot_not_mem := N.bot_not_mem
    node_fintype := inferInstance
    node_op := P.node_op
    node_dom_nonempty := by
      intro v
      cases v with
      | inl v => exact N.node_dom_nonempty v.val
      | inr a => simpa only [node_op, P.local_domain] using P.nonempty a
    entry := fun x => P.lift_label (N.entry x) x.val
    entry_mem := fun x => P.lift_mem_dom (N.entry x) x.val (N.entry_mem x)
    choice := P.choice
    choice_next_mem := P.choice_next_mem
    depth_bound := N.depth_bound
    path_of := fun x => P.colour_path (N.path_of x) x.val
    path_terminal := fun x => P.coloured_terminal (N.path_terminal x) (N.entry_mem x)
    path_length_le_depth := by intro x; simpa using N.path_length_le_depth x
  }

/--
OET anchor: h-eddd1f2d0a9d3528
Actual node-domain refinement, including deletion of all unreachable pieces.
-/
def network := P.presentation.prune

/--
OET anchor: h-012f4ba72aeb3f20
The constructed refinement has exactly the recoloured original paths.
-/
theorem network_path_labels (x : N.U) :
    (P.network.path_of x).map Subtype.val = P.colour_path (N.path_of x) x.val :=
  P.presentation.prune_path_labels x

/--
OET anchor: h-012f4ba72aeb3f20
Forgetting split labels recovers the actual original path, so its length is unchanged.
-/
theorem network_path_projection (x : N.U) :
    (P.network.path_of x).map (fun v => P.projection v.val) = N.path_of x := by
  change List.map (P.projection ∘ Subtype.val) (P.network.path_of x) = _
  rw [← List.map_map, P.network_path_labels, P.colour_path_projection]

/--
OET anchor: h-012f4ba72aeb3f20
The actual constructed and pruned domain refinement has the same global operator.
-/
theorem network_extensional_eq : P.network.extensional_operator = N.extensional_operator := by
  classical
  apply Operator.ext
  funext x
  by_cases hx : x ∈ N.U
  · change (if h : x ∈ N.U then P.network.eval ⟨x, h⟩ else bot) = _
    rw [dif_pos hx]
    change P.presentation.prune.eval ⟨x, hx⟩ = _
    rw [FiniteNetworkPresentation.prune_eval]
    exact (P.coloured_eval (N.path_terminal ⟨x, hx⟩) (N.entry_mem _)).trans
      (N.extensional_apply_eq_chain_eval_path ⟨x, hx⟩).symm
  · simp [extensional_operator, network, presentation, FiniteNetworkPresentation.prune, hx]

/-- The recoloured occurrence uses the original current input at that position. -/
theorem colour_path_get (p : List V) (x : X) (n : Fin p.length) :
    (P.colour_path p x).get ⟨n.val, by simp [n.isLt]⟩ =
      P.lift_label (p.get n) (N.chain_eval_nodes (p.take n.val) x) := by
  induction p generalizing x with
  | nil => exact Fin.elim0 n
  | cons v rest ih =>
    rcases n with ⟨n, hn⟩
    cases n with
    | zero => rfl
    | succ n =>
      simpa [colour_path, FiniteOperatorNetwork.chain_eval_nodes,
        chain_eval_nodes_core] using ih ((N.node_op v).func x) ⟨n, by simpa using hn⟩

/-- A local input uniquely identifies its full split label. -/
theorem lift_projection_of_mem (v : P.Label) (x : X) (hx : x ∈ dom (P.node_op v)) :
    P.lift_label (P.projection v) x = v := by
  classical
  cases v with
  | inl v => simp [projection, lift_label, v.property]
  | inr a =>
    have ha : x ∈ P.piece a := (P.local_domain a) ▸ hx
    simp [projection, lift_label, P.piece_at_unique x a ha]

/-- Every unaffected old node is retained after refinement. -/
theorem old_label_reached (v : {v : V // v ≠ target}) :
    P.presentation.Reached (.inl v) := by
  rcases N.node_reachable v.val with ⟨x, hx⟩
  have hm : v.val ∈ (P.colour_path (N.path_of x) x.val).map P.projection := by
    rw [P.colour_path_projection]
    exact hx
  rcases List.mem_map.mp hm with ⟨w, hw, hp⟩
  have hwv : w = .inl v := by
    cases w with
    | inl u => exact congrArg Sum.inl (Subtype.ext hp)
    | inr a => exact False.elim (v.property hp.symm)
  exact ⟨x, hwv ▸ hw⟩

/-- A split piece survives exactly when an original occurrence enters it. -/
theorem piece_label_reached_iff (a : Fin P.count) :
    P.presentation.Reached (.inr a) ↔ NodePieceReached N target P.piece a := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨n, hn⟩ := List.get_of_mem hx
    have hlen : n.val < (N.path_of x).length := by
      simpa only [presentation, colour_path_length] using n.isLt
    let k : Fin (N.path_of x).length := ⟨n.val, hlen⟩
    have hget : P.lift_label ((N.path_of x).get k)
        (N.chain_eval_nodes ((N.path_of x).take k.val) x.val) = .inr a := by
      exact (P.colour_path_get (N.path_of x) x.val k).symm.trans hn
    have htarget : (N.path_of x).get k = target := by
      have hp := congrArg P.projection hget
      change P.projection (P.lift_label ((N.path_of x).get k)
        (N.chain_eval_nodes ((N.path_of x).take k.val) x.val)) = target at hp
      rwa [P.projection_lift] at hp
    have hdom : N.chain_eval_nodes ((N.path_of x).take k.val) x.val ∈
        N.node_dom ((N.path_of x).get k) :=
      terminal_path_prefix_input_mem N.choice_next_mem (N.entry_mem x) (N.path_terminal x) k
    refine ⟨x, k, htarget, ?_⟩
    have hlocal := P.lift_mem_dom ((N.path_of x).get k) _ hdom
    rw [hget] at hlocal
    exact (P.local_domain a) ▸ hlocal
  · rintro ⟨x, n, hn, hp⟩
    refine ⟨x, ?_⟩
    have hget := P.colour_path_get (N.path_of x) x.val n
    rw [hn] at hget
    have hlift : P.lift_label target
        (N.chain_eval_nodes ((N.path_of x).take n.val) x.val) = .inr a := by
      classical
      simp [lift_label, P.piece_at_unique _ a hp]
    rw [hlift] at hget
    exact hget ▸ List.get_mem _ _

/-- On complete local images, refinement has precisely the textbook edge
intersection formula. Unreachable destinations have already been removed. -/
theorem network_edge_domain_eq (v w : {v // P.presentation.Reached v}) :
    P.network.edge_domain v w =
      (N.edge_domain (P.projection v.val) (P.projection w.val) ∩
        P.network.node_image v) ∩ P.network.node_dom w := by
  classical
  ext z
  change (z ∈ P.network.node_image v ∧
    prune_choice P.presentation.Reached P.choice v z = .next w) ↔ _
  constructor
  · rintro ⟨hz, hc⟩
    have hchoice : P.choice v.val z = .next w.val := by
      unfold prune_choice at hc
      split at hc
      · contradiction
      · rename_i u hu
        split at hc
        · cases hc
          exact hu
        · contradiction
    have hproj : N.choice (P.projection v.val) z = .next (P.projection w.val) := by
      unfold choice map_output_choice at hchoice
      split at hchoice
      · contradiction
      · rename_i u hu
        have heq := congrArg P.projection (OutputChoice.next.inj hchoice)
        rw [P.projection_lift] at heq
        exact heq ▸ hu
    have himage : z ∈ N.node_image (P.projection v.val) := by
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, P.node_domain_subset_original v.val hx,
        (P.node_apply_eq_original v.val x hx).symm⟩
    have hw := P.network.edge_domain_subset_node_dom
      (show z ∈ P.network.edge_domain v w from ⟨hz, hc⟩)
    exact ⟨⟨⟨himage, hproj⟩, hz⟩, hw⟩
  · rintro ⟨⟨hz, hv⟩, hw⟩
    refine ⟨hv, ?_⟩
    have hchoice : P.choice v.val z = .next w.val := by
      rw [choice, hz.2, map_output_choice, P.lift_projection_of_mem w.val z hw]
    simp [prune_choice, hchoice, w.property]

/-- Pruning keeps the route at every actually encountered local output. -/
theorem network_choice_projection (v : {v // P.presentation.Reached v}) (z : X)
    (hz : z ∈ (P.network.node_op v).func '' P.network.node_actual_input_domain v) :
    map_output_choice (fun w => P.projection w.val) (P.network.choice v z) =
      N.choice (P.projection v.val) z := by
  classical
  rcases hz with ⟨y, ⟨x, pref, suffix, hpath, hy, hydom⟩, rfl⟩
  have heval : ∀ (p : List {v // P.presentation.Reached v}) (x : X),
      chain_eval_nodes_core P.node_op (p.map Subtype.val) x = P.network.chain_eval_nodes p x := by
    intro p x
    induction p generalizing x with
    | nil => rfl
    | cons v rest ih => exact ih _
  have hpath' : P.presentation.path_of x =
      pref.map Subtype.val ++ v.val :: suffix.map Subtype.val := by
    change P.colour_path (N.path_of x) x.val = _
    rw [← P.network_path_labels x, hpath]
    simp
  have hp : ∀ u, P.choice v.val ((P.node_op v.val).func y) = .next u →
      P.presentation.Reached u := by
    intro u hu
    have hu' : P.choice v.val
        ((P.node_op v.val).func (chain_eval_nodes_core P.node_op (pref.map Subtype.val) x.val)) =
          .next u := by
      rw [heval, ← hy]
      exact hu
    obtain ⟨tail, htail⟩ := terminal_path_suffix_of_next_at_prefix
      (P.presentation.path_terminal x) hpath' hu'
    refine ⟨x, ?_⟩
    rw [hpath', htail]
    simp
  change map_output_choice (fun w => P.projection w.val)
    (prune_choice P.presentation.Reached P.choice v ((P.node_op v.val).func y)) =
      N.choice (P.projection v.val) ((P.node_op v.val).func y)
  cases hc : P.choice v.val ((P.node_op v.val).func y) with
  | stop =>
    have ho : N.choice (P.projection v.val) ((P.node_op v.val).func y) = .stop := by
      unfold choice map_output_choice at hc
      split at hc
      · assumption
      · contradiction
    simp [prune_choice, hc, map_output_choice, ho]
  | next u =>
    have ho : N.choice (P.projection v.val) ((P.node_op v.val).func y) =
        .next (P.projection u) := by
      unfold choice map_output_choice at hc
      split at hc
      · contradiction
      · rename_i w hw
        have heq := congrArg P.projection (OutputChoice.next.inj hc)
        rw [P.projection_lift] at heq
        exact heq ▸ hw
    simp [prune_choice, hc, hp u hc, map_output_choice, ho]

theorem network_label_projection (v : {v // P.presentation.Reached v}) :
    node_domain_projection target Subtype.val v = P.projection v.val := by
  cases hv : v.val <;> simp only [node_domain_projection, projection, hv]

/--
OET anchor: h-eddd1f2d0a9d3528
The exact constructive refinement inhabits the textbook relation, including
nonredundancy, entry data, all unused retained edges and split self-loops.
-/
def network_refinement : NodeDomainRefinement N P.network where
  target := target
  part_count := P.count
  part_count_pos := P.count_pos
  piece := P.piece
  piece_nonempty := P.nonempty
  piece_disjoint := P.disjoint
  piece_cover := P.cover
  local_factor := P.local_op
  local_domain := P.local_domain
  local_equiv := P.local_eq
  source := Subtype.val
  source_injective := Subtype.val_injective
  old_node_present := fun v => ⟨⟨.inl v, P.old_label_reached v⟩, rfl⟩
  piece_node_present_iff_reached := by
    intro a
    constructor
    · rintro ⟨v, hv⟩
      exact (P.piece_label_reached_iff a).mp (hv ▸ v.property)
    · intro h
      exact ⟨⟨.inr a, (P.piece_label_reached_iff a).mpr h⟩, rfl⟩
  old_node_op_compat := by
    intro v w h
    change P.node_op v.val = N.node_op w.val
    rw [h]
    rfl
  piece_node_op_compat := by
    intro v a h
    change P.node_op v.val = P.local_op a
    rw [h]
    rfl
  same_input_domain := rfl
  entry_projection := by
    intro x
    rw [P.network_label_projection]
    exact P.projection_lift (N.entry x) x.val
  choice_projection := by
    intro v z hz
    have hproj : node_domain_projection target Subtype.val =
        fun w : {v // P.presentation.Reached v} => P.projection w.val :=
      funext P.network_label_projection
    simpa only [hproj] using P.network_choice_projection v z hz
  edge_domain_eq := by
    intro v w
    simpa only [P.network_label_projection] using P.network_edge_domain_eq v w

/-- The constructed exact refinement is an allowed one-step network refinement. -/
def allowed_network_refinement : NetworkRefinement N P.network :=
  .node_domain P.network_refinement

end NodePartitionData
end
end formal_oet.vol_01.ch_05_operator_networks
