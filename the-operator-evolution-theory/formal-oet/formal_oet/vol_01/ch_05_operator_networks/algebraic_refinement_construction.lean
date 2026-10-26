import formal_oet.vol_01.ch_05_operator_networks.network_presentation
import formal_oet.vol_01.ch_05_operator_networks.network_routing
import formal_oet.vol_01.ch_05_operator_networks.network_refinement

namespace formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open FiniteOperatorNetwork
noncomputable section
variable {X V : Type} {bot : X}

/-- Exactly the local factor data allowed by algebraic refinement. -/
structure NodeFactorizationData (N : FiniteOperatorNetwork X bot V) (target : V) where
  first : Operator X bot
  second : Operator X bot
  first_domain : N.node_dom target ⊆ dom first
  second_domain : first.func '' N.node_dom target ⊆ dom second
  factorization : ∀ x ∈ N.node_dom target,
    (N.node_op target).func x = second.func (first.func x)

namespace NodeFactorizationData
variable {N : FiniteOperatorNetwork X bot V} {target : V}
variable (F : NodeFactorizationData N target)
local instance : DecidableEq V := Classical.decEq V

/-- The target's old label becomes the first factor; the extra label is the second. -/
def node_op : V ⊕ Unit → Operator X bot := by
  classical
  exact fun v => match v with
    | .inl v => if v = target then restrict_operator F.first (N.node_dom target) else N.node_op v
    | .inr _ => restrict_operator F.second (F.first.func '' N.node_dom target)

def choice (_F : NodeFactorizationData N target) : (V ⊕ Unit) → X → OutputChoice (V ⊕ Unit) := by
  classical
  exact fun v z => match v with
    | .inl v => if v = target then .next (.inr ()) else
        map_output_choice Sum.inl (N.choice v z)
    | .inr _ => map_output_choice Sum.inl (N.choice target z)

/--
OET anchor: h-eddd1f2d0a9d3528
An old self-loop returns from the second factor to the first, with its old domain.
-/
theorem self_loop_choice_iff (z : X) :
    F.choice (.inr ()) z = .next (.inl target) ↔
      N.choice target z = .next target := by
  cases h : N.choice target z <;> simp [choice, map_output_choice, h]

@[simp] theorem node_dom_inl (v : V) : dom (F.node_op (.inl v)) = N.node_dom v := by
  classical
  by_cases hv : v = target
  · subst v
    simp only [node_op, ↓reduceIte]
    exact dom_restrict_operator_eq F.first _ F.first_domain
  · simp [node_op, hv, node_dom_eq_dom]

@[simp] theorem node_dom_inr : dom (F.node_op (.inr ())) =
    F.first.func '' N.node_dom target :=
  dom_restrict_operator_eq F.second _ F.second_domain

theorem first_apply (x : X) (hx : x ∈ N.node_dom target) :
    (F.node_op (.inl target)).func x = F.first.func x := by
  classical
  simp only [node_op, ↓reduceIte]
  exact restrict_operator_apply_of_mem _ _ hx

theorem pair_apply (x : X) (hx : x ∈ N.node_dom target) :
    (F.node_op (.inr ())).func ((F.node_op (.inl target)).func x) =
      (N.node_op target).func x := by
  rw [F.first_apply x hx]
  change (restrict_operator F.second _).func _ = _
  rw [restrict_operator_apply_of_mem F.second (F.first.func '' N.node_dom target)
    (show F.first.func x ∈ F.first.func '' N.node_dom target from ⟨x, hx, rfl⟩)]
  exact (F.factorization x hx).symm

theorem choice_next_mem {v w : V ⊕ Unit} {x : X}
    (hx : x ∈ dom (F.node_op v))
    (hc : F.choice v ((F.node_op v).func x) = .next w) :
    (F.node_op v).func x ∈ dom (F.node_op w) := by
  classical
  cases v with
  | inl v =>
    by_cases hv : v = target
    · subst v
      simp only [choice, ↓reduceIte, OutputChoice.next.injEq] at hc
      subst w
      rw [F.node_dom_inl] at hx
      rw [F.node_dom_inr, F.first_apply x hx]
      exact ⟨x, hx, rfl⟩
    · simp only [choice, hv, if_false, map_output_choice] at hc
      split at hc
      · contradiction
      · rename_i u hu
        cases hc
        rw [F.node_dom_inl]
        have hxold : x ∈ N.node_dom v := (F.node_dom_inl v) ▸ hx
        have hop : F.node_op (.inl v) = N.node_op v := by simp [node_op, hv]
        rw [hop] at hu ⊢
        exact N.choice_next_mem hxold hu
  | inr u =>
    cases u
    rw [F.node_dom_inr] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hout : (F.node_op (.inr ())).func (F.first.func y) =
        (N.node_op target).func y := by
      simpa only [F.first_apply y hy] using F.pair_apply y hy
    simp only [choice, map_output_choice] at hc
    split at hc
    · contradiction
    · rename_i w hw
      cases hc
      rw [F.node_dom_inl, hout]
      rw [hout] at hw
      exact N.choice_next_mem hy hw

def expand_path (F : NodeFactorizationData N target) : List V → List (V ⊕ Unit)
  | [] => []
  | v :: rest => if v = target then .inl v :: .inr () :: F.expand_path rest
      else .inl v :: F.expand_path rest

theorem expand_path_length (p : List V) : (F.expand_path p).length ≤ 2 * p.length := by
  classical
  induction p with
  | nil => simp [expand_path]
  | cons v rest ih =>
    by_cases hv : v = target <;> simp only [expand_path, hv, if_true, if_false, List.length_cons]
    all_goals omega

theorem expanded_terminal {v x p}
    (ht : TerminalPathFrom N.node_op N.choice v x p) (hx : x ∈ N.node_dom v) :
    TerminalPathFrom F.node_op F.choice (.inl v) x (F.expand_path p) := by
  classical
  induction ht with
  | @stop v x hs =>
    by_cases hv : v = target
    · subst v
      simp only [expand_path, ↓reduceIte]
      apply TerminalPathFrom.next (γ := .inr ()) (by simp [choice])
      apply TerminalPathFrom.stop
      simp [choice, F.pair_apply x hx, hs, map_output_choice]
    · simp only [expand_path, if_neg hv]
      apply TerminalPathFrom.stop
      simp [choice, node_op, hv, hs, map_output_choice]
  | @next v w x rest hs ht ih =>
    have hy := N.choice_next_mem hx hs
    by_cases hv : v = target
    · subst v
      simp only [expand_path, ↓reduceIte]
      apply TerminalPathFrom.next (γ := .inr ()) (by simp [choice])
      apply TerminalPathFrom.next (γ := .inl w)
      · simp [choice, F.pair_apply x hx, hs, map_output_choice]
      · rw [F.pair_apply x hx]
        exact ih hy
    · simp only [expand_path, if_neg hv]
      apply TerminalPathFrom.next (γ := .inl w)
      · simp [choice, node_op, hv, hs, map_output_choice]
      · simpa [node_op, hv] using ih hy

theorem expanded_eval {v x p}
    (ht : TerminalPathFrom N.node_op N.choice v x p) (hx : x ∈ N.node_dom v) :
    chain_eval_nodes_core F.node_op (F.expand_path p) x =
      chain_eval_nodes_core N.node_op p x := by
  classical
  induction ht with
  | @stop v x hs =>
    by_cases hv : v = target
    · subst v
      simpa only [expand_path, ↓reduceIte, chain_eval_nodes_core] using F.pair_apply x hx
    · simp [expand_path, hv, chain_eval_nodes_core, node_op]
  | @next v w x rest hs ht ih =>
    have hy := N.choice_next_mem hx hs
    by_cases hv : v = target
    · subst v
      simp only [expand_path, ↓reduceIte, chain_eval_nodes_core]
      rw [F.pair_apply x hx]
      exact ih hy
    · simpa [expand_path, hv, chain_eval_nodes_core, node_op] using ih hy

/-- Build all finite-network obligations, prior to reachability pruning. -/
def presentation : FiniteNetworkPresentation X bot (V ⊕ Unit) := by
  classical
  letI := N.node_fintype
  exact {
    U := N.U
    bot_not_mem := N.bot_not_mem
    node_fintype := inferInstance
    node_op := F.node_op
    node_dom_nonempty := by
      intro v
      cases v with
      | inl v => simpa using N.node_dom_nonempty v
      | inr u =>
        cases u
        rw [F.node_dom_inr]
        exact (N.node_dom_nonempty target).image F.first.func
    entry := fun x => .inl (N.entry x)
    entry_mem := by intro x; rw [F.node_dom_inl]; exact N.entry_mem x
    choice := F.choice
    choice_next_mem := F.choice_next_mem
    depth_bound := 2 * N.depth_bound
    path_of := fun x => F.expand_path (N.path_of x)
    path_terminal := fun x => F.expanded_terminal (N.path_terminal x) (N.entry_mem x)
    path_length_le_depth := fun x => (F.expand_path_length _).trans
      (Nat.mul_le_mul_left 2 (N.path_length_le_depth x))
  }

/--
OET anchor: h-eddd1f2d0a9d3528
Actual algebraic refinement from the two factors in the definition.
-/
def network := F.presentation.prune

/--
OET anchor: h-012f4ba72aeb3f20
The constructed network replaces every target occurrence by two consecutive nodes.
-/
theorem network_path_labels (x : N.U) :
    (F.network.path_of x).map Subtype.val = F.expand_path (N.path_of x) :=
  F.presentation.prune_path_labels x

/--
OET anchor: h-012f4ba72aeb3f20
The actual constructed and pruned algebraic refinement has the same global operator.
-/
theorem network_extensional_eq : F.network.extensional_operator = N.extensional_operator := by
  classical
  apply Operator.ext
  funext x
  by_cases hx : x ∈ N.U
  · change (if h : x ∈ N.U then F.network.eval ⟨x, h⟩ else bot) = _
    rw [dif_pos hx]
    change F.presentation.prune.eval ⟨x, hx⟩ = _
    rw [FiniteNetworkPresentation.prune_eval]
    exact (F.expanded_eval (N.path_terminal ⟨x, hx⟩) (N.entry_mem _)).trans
      (N.extensional_apply_eq_chain_eval_path ⟨x, hx⟩).symm
  · simp [extensional_operator, network, presentation, FiniteNetworkPresentation.prune, hx]

private theorem inl_mem_expand_path (v : V) (p : List V) (hv : v ∈ p) :
    Sum.inl v ∈ F.expand_path p := by
  induction p with
  | nil => simp at hv
  | cons w p ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · by_cases hw : v = target <;> simp [expand_path, hw]
    · by_cases hw : w = target <;> simp [expand_path, hw, ih hv]

private theorem inr_mem_expand_path (p : List V) (ht : target ∈ p) :
    Sum.inr () ∈ F.expand_path p := by
  induction p with
  | nil => simp at ht
  | cons v p ih =>
    rcases List.mem_cons.mp ht with h | ht
    · subst v; simp [expand_path]
    · by_cases hv : v = target <;> simp [expand_path, hv, ih ht]

/-- Every old node and both factors occur. Algebraic splitting therefore
deletes no node during the general reachability-pruning construction. -/
theorem label_reached (v : V ⊕ Unit) : F.presentation.Reached v := by
  cases v with
  | inl v =>
    obtain ⟨x, hx⟩ := N.node_reachable v
    exact ⟨x, F.inl_mem_expand_path v _ hx⟩
  | inr u =>
    cases u
    obtain ⟨x, hx⟩ := N.node_reachable target
    exact ⟨x, F.inr_mem_expand_path _ hx⟩

/-- The labels used by the refinement relation: retained old nodes, first
factor, and second factor. -/
def source (v : {v // F.presentation.Reached v}) : {v : V // v ≠ target} ⊕ Bool :=
  match v.val with
  | .inl v => if h : v = target then .inr false else .inl ⟨v, h⟩
  | .inr _ => .inr true

private def lift_label (v : V ⊕ Unit) : {v // F.presentation.Reached v} :=
  ⟨v, F.label_reached v⟩

theorem source_bijective : Function.Bijective F.source := by
  classical
  constructor
  · rintro ⟨v, hv⟩ ⟨w, hw⟩ h
    apply Subtype.ext
    cases v with
    | inl v =>
      cases w with
      | inl w =>
        by_cases hv : v = target <;> by_cases hw : w = target
        all_goals simp_all [source]
      | inr u => by_cases ht : v = target <;> simp [source, ht] at h
    | inr u =>
      cases w with
      | inl w => by_cases ht : w = target <;> simp [source, ht] at h
      | inr t => cases u; cases t; rfl
  · intro w
    cases w with
    | inl w => exact ⟨F.lift_label (.inl w.val), by simp [source, lift_label, w.property]⟩
    | inr b =>
      cases b
      · exact ⟨F.lift_label (.inl target), by simp [source, lift_label]⟩
      · exact ⟨F.lift_label (.inr ()), rfl⟩

private theorem entry_projection_inl (v : V) (hv : F.presentation.Reached (.inl v)) :
    algebraic_entry_projection target F.source ⟨.inl v, hv⟩ = some v := by
  by_cases h : v = target <;> simp [algebraic_entry_projection, source, h]

private theorem network_choice_eq (v : {v // F.presentation.Reached v}) (z : X) :
    F.network.choice v z =
      map_output_choice F.lift_label (F.choice v.val z) := by
  change prune_choice F.presentation.Reached F.choice v z = _
  cases hc : F.choice v.val z with
  | stop => simp [prune_choice, hc, map_output_choice]
  | next w => simp [prune_choice, hc, F.label_reached, map_output_choice, lift_label]

private theorem mapped_choice_lift (c : OutputChoice V) :
    ChoiceLift (algebraic_entry_projection target F.source)
      (map_output_choice F.lift_label (map_output_choice Sum.inl c)) c := by
  cases c with
  | stop => trivial
  | next v => exact F.entry_projection_inl v _

/--
OET anchor: h-eddd1f2d0a9d3528
The actual two-factor construction satisfies the allowed refinement relation.
In particular, its full local routing data, not only its terminal outputs,
can be used by the algebraic-rank termination theorem.
-/
def network_refinement : AlgebraicRefinement N F.network where
  target := target
  first_factor := F.first
  second_factor := F.second
  first_domain := F.first_domain
  second_domain := F.second_domain
  factorization := F.factorization
  source := F.source
  source_bijective := F.source_bijective
  old_node_op_compat := by
    rintro ⟨v, hv⟩ w h
    cases v with
    | inl v =>
      by_cases ht : v = target
      · simp [source, ht] at h
      · have hs : (⟨v, ht⟩ : {v : V // v ≠ target}) = w := by simpa [source, ht] using h
        have heq : v = w.val := congrArg Subtype.val hs
        subst v
        simp [network, FiniteNetworkPresentation.prune, presentation, node_op, w.property]
    | inr u => simp [source] at h
  first_node_op_compat := by
    rintro ⟨v, hv⟩ h
    cases v with
    | inl v =>
      by_cases ht : v = target
      · subst v; simp [network, FiniteNetworkPresentation.prune, presentation, node_op]
      · simp [source, ht] at h
    | inr u => simp [source] at h
  second_node_op_compat := by
    rintro ⟨v, hv⟩ h
    cases v with
    | inl v => by_cases ht : v = target <;> simp [source, ht] at h
    | inr u => cases u; rfl
  same_input_domain := rfl
  entry_projection := fun x => F.entry_projection_inl (N.entry x) _
  old_choice := by
    rintro ⟨v, hv⟩ w h z hz
    rw [F.network_choice_eq]
    cases v with
    | inl v =>
      by_cases ht : v = target
      · simp [source, ht] at h
      · have hs : (⟨v, ht⟩ : {v : V // v ≠ target}) = w := by simpa [source, ht] using h
        have heq : v = w.val := congrArg Subtype.val hs
        subst v
        simpa only [choice, if_neg w.property] using F.mapped_choice_lift (N.choice w.val z)
    | inr u => simp [source] at h
  first_choice := by
    rintro ⟨v, hv⟩ h z hz
    cases v with
    | inl v =>
      by_cases ht : v = target
      · subst v
        refine ⟨F.lift_label (.inr ()), rfl, ?_⟩
        rw [F.network_choice_eq]
        simp [choice, map_output_choice]
      · simp [source, ht] at h
    | inr u => simp [source] at h
  second_choice := by
    rintro ⟨v, hv⟩ h z hz
    rw [F.network_choice_eq]
    cases v with
    | inl v => by_cases ht : v = target <;> simp [source, ht] at h
    | inr u => cases u; exact F.mapped_choice_lift (N.choice target z)

/-- The construction is an allowed one-step refinement, so the general
finite-chain and termination results apply without an extra interface premise. -/
def allowed_network_refinement : NetworkRefinement N F.network :=
  .algebraic F.network_refinement

end NodeFactorizationData
end
end formal_oet.vol_01.ch_05_operator_networks
