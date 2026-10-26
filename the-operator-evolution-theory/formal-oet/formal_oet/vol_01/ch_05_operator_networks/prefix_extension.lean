import formal_oet.vol_01.ch_05_operator_networks.network_presentation
import formal_oet.vol_01.ch_05_operator_networks.path_matrix

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_02_operator_bounds

noncomputable section
variable {X V : Type} {bot : X}
namespace FiniteOperatorNetwork
variable (N : FiniteOperatorNetwork X bot V) (φ : Operator X bot) (D : Set X)

/-- `none` labels the new entry; `some v` retains an old node label. -/
def prefix_node_op : Option V → Operator X bot
  | none => restrict_operator φ D
  | some v => N.node_op v

/-- The new entry routes its output through the old entry partition. -/
def prefix_choice : Option V → X → OutputChoice (Option V) := by
  classical
  exact fun v z => match v with
    | none => if hz : z ∈ N.U then .next (some (N.entry ⟨z, hz⟩)) else .stop
    | some v => match N.choice v z with
      | .stop => .stop
      | .next w => .next (some w)

private theorem prefix_terminal_some {v y p}
    (h : TerminalPathFrom N.node_op N.choice v y p) :
    TerminalPathFrom (N.prefix_node_op φ D) N.prefix_choice (some v) y (p.map some) := by
  classical
  induction h with
  | stop hs =>
    apply TerminalPathFrom.stop
    simp [prefix_node_op, prefix_choice, hs]
  | @next v w y rest hs ht ih =>
    apply TerminalPathFrom.next (γ := some w)
    · simp [prefix_node_op, prefix_choice, hs]
    · exact ih

/-- Add an entry node before pruning. No path correspondence is assumed: the
new terminal paths are constructed from the original terminal paths. -/
def prefix_presentation (hD : D ⊆ dom φ) (hne : D.Nonempty)
    (himage : φ.func '' D ⊆ N.U) : FiniteNetworkPresentation X bot (Option V) := by
  classical
  letI := N.node_fintype
  exact {
    U := D
    bot_not_mem := fun hb => (hD hb) φ.preserves_bot
    node_fintype := inferInstance
    node_op := N.prefix_node_op φ D
    node_dom_nonempty := by
      intro v
      cases v with
      | none => simpa only [prefix_node_op, dom_restrict_operator_eq φ D hD] using hne
      | some v => exact N.node_dom_nonempty v
    entry := fun _ => none
    entry_mem := by
      intro x
      change x.val ∈ dom (restrict_operator φ D)
      rw [dom_restrict_operator_eq φ D hD]
      exact x.prop
    choice := N.prefix_choice
    choice_next_mem := by
      intro v w y hy hc
      cases v with
      | none =>
        dsimp [prefix_choice] at hc
        split at hc
        · cases hc
          exact N.entry_mem _
        · contradiction
      | some v =>
        dsimp [prefix_choice] at hc
        split at hc
        · contradiction
        · rename_i u heq
          cases hc
          exact N.choice_next_mem hy heq
    depth_bound := N.depth_bound + 1
    path_of := fun x => none :: (N.path_of ⟨φ.func x.val, himage ⟨x.val, x.prop, rfl⟩⟩).map some
    path_terminal := by
      intro x
      have hxU := himage ⟨x.val, x.prop, rfl⟩
      have hφ : (N.prefix_node_op φ D none).func x.val = φ.func x.val :=
        restrict_operator_apply_of_mem φ D x.prop
      apply TerminalPathFrom.next (γ := some (N.entry ⟨φ.func x.val, hxU⟩))
      · simp [hφ, prefix_choice, hxU]
      · rw [hφ]
        exact N.prefix_terminal_some φ D (N.path_terminal _)
    path_length_le_depth := by
      intro x
      simp only [List.length_cons, List.length_map]
      exact Nat.add_le_add_right (N.path_length_le_depth _) 1
  }

/--
OET anchor: h-8893f19c84720522
前缀扩展网络：增加入口节点并删除对 `D` 不可达的旧节点。
-/
def prefix_extension (hD : D ⊆ dom φ) (hne : D.Nonempty)
    (himage : φ.func '' D ⊆ N.U) :=
  (N.prefix_presentation φ D hD hne himage).prune

private theorem prefix_eval_some (p : List V) (x : X) :
    chain_eval_nodes_core (N.prefix_node_op φ D) (p.map some) x =
      chain_eval_nodes_core N.node_op p x := by
  induction p generalizing x with
  | nil => rfl
  | cons v rest ih => exact ih _

/--
OET anchor: h-8893f19c84720522
扩展网络的每条实际路径先经过新入口，然后逐节点对应原网络的实际路径。
-/
theorem prefix_extension_path_labels (hD : D ⊆ dom φ) (hne : D.Nonempty)
    (himage : φ.func '' D ⊆ N.U) (x : D) :
    ((N.prefix_extension φ D hD hne himage).path_of x).map Subtype.val =
      none :: (N.path_of ⟨φ.func x.val, himage ⟨x.val, x.prop, rfl⟩⟩).map some := by
  exact (N.prefix_presentation φ D hD hne himage).prune_path_labels x

/--
OET anchor: h-8893f19c84720522
前缀扩展的全域算子等式，包括 `D` 外的吸收元值。
-/
theorem prefix_extension_extensional_eq (hD : D ⊆ dom φ) (hne : D.Nonempty)
    (himage : φ.func '' D ⊆ N.U) :
    (N.prefix_extension φ D hD hne himage).extensional_operator =
      restrict_operator (OperatorChain [N.extensional_operator, φ]) D := by
  classical
  apply Operator.ext
  funext x
  by_cases hx : x ∈ D
  · rw [restrict_operator_apply_of_mem _ D hx]
    change (N.prefix_extension φ D hD hne himage).extensional_operator.func x =
      N.extensional_operator.func (φ.func x)
    rw [(N.prefix_extension φ D hD hne himage).extensional_apply_eq_chain_eval_path ⟨x, hx⟩]
    change (N.prefix_presentation φ D hD hne himage).prune.eval ⟨x, hx⟩ = _
    rw [FiniteNetworkPresentation.prune_eval]
    change chain_eval_nodes_core (N.prefix_node_op φ D)
      (none :: (N.path_of ⟨φ.func x, himage ⟨x, hx, rfl⟩⟩).map some) x = _
    rw [chain_eval_nodes_core, prefix_node_op, restrict_operator_apply_of_mem φ D hx,
      N.prefix_eval_some]
    exact (N.extensional_apply_eq_chain_eval_path _).symm
  · rw [restrict_operator_apply_of_not_mem _ D hx]
    simp [extensional_operator, prefix_extension, FiniteNetworkPresentation.prune,
      prefix_presentation, hx]

/--
OET anchor: h-8893f19c84720522
按保留的节点标签读取扩展路径，其实际初始输入域 `U_p^φ` 正是 `D ∩ φ⁻¹(U_p)`。
-/
theorem prefix_extension_path_domain (hD : D ⊆ dom φ) (hne : D.Nonempty)
    (himage : φ.func '' D ⊆ N.U) (p : List V) :
    {x | ∃ hx : x ∈ D,
      ((N.prefix_extension φ D hD hne himage).path_of ⟨x, hx⟩).map Subtype.val =
        none :: p.map some} = D ∩ φ.func ⁻¹' N.path_domain p := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hx, hp⟩
    rw [N.prefix_extension_path_labels φ D hD hne himage] at hp
    have heq : N.path_of ⟨φ.func x, himage ⟨x, hx, rfl⟩⟩ = p := by
      exact (List.map_inj_right (fun _ _ h => Option.some.inj h)).mp (List.cons.inj hp).2
    exact ⟨hx, ⟨himage ⟨x, hx, rfl⟩, heq⟩⟩
  · rintro ⟨hx, hpath⟩
    refine ⟨hx, ?_⟩
    rw [N.prefix_extension_path_labels φ D hD hne himage]
    exact congrArg (fun q : List V => none :: q.map some) hpath.2


/-- On an actual extended path domain, the extension agrees with the old path
composed after the prefix. The domain is derived from routing, not assumed. -/
theorem prefix_extension_local_path_comp (hD : D ⊆ dom φ) (hne : D.Nonempty)
    (himage : φ.func '' D ⊆ N.U) (p : List V) :
    LocalEquivalent (N.prefix_extension φ D hD hne himage).extensional_operator
      (OperatorChain [N.path_chain p, φ]) (D ∩ φ.func ⁻¹' N.path_domain p) := by
  intro x hx
  rw [N.prefix_extension_extensional_eq φ D hD hne himage,
    restrict_operator_apply_of_mem _ D hx.1]
  change N.extensional_operator.func (φ.func x) = (N.path_chain p).func (φ.func x)
  exact N.local_equivalent_extensional_path_chain
    ⟨p, ⟨φ.func x, hx.2⟩⟩ (φ.func x) hx.2

/--
OET anchor: h-8893f19c84720522
前缀扩展在实际路径域上的 Lip 乘积证书；由原有复合律和已证网络求值等式得到。
-/
theorem prefix_extension_lip_matrix {I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (hD : D ⊆ dom φ) (hne : D.Nonempty)
    (himage : φ.func '' D ⊆ N.U) (p : List V) (Lφ Lp : I → I → ENNReal)
    (hLφ : IsLipMatrix d φ (D ∩ φ.func ⁻¹' N.path_domain p) Lφ)
    (hLp : IsLipMatrix d (N.path_chain p) (N.path_domain p) Lp) :
    IsLipMatrix d (N.prefix_extension φ D hD hne himage).extensional_operator
      (D ∩ φ.func ⁻¹' N.path_domain p) (matrix_mul Lp Lφ) := by
  apply (local_equiv_lip_matrix_iff d _ _ _ _
    (N.prefix_extension_local_path_comp φ D hD hne himage p)).mpr
  exact lip_matrix_comp d φ (N.path_chain p) _ _ Lφ Lp (fun _ hx => hx.2) hLφ hLp

/--
OET anchor: h-8893f19c84720522
前缀扩展在同一实际非空路径域上的 co-Lip 乘积证书；非空性来自合法的前缀证书。
-/
theorem prefix_extension_colip_matrix {I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (hD : D ⊆ dom φ) (hne : D.Nonempty)
    (himage : φ.func '' D ⊆ N.U) (p : List V) (Kφ Kp : I → I → ENNReal)
    (hKφ : IsCoLipMatrix d φ (D ∩ φ.func ⁻¹' N.path_domain p) Kφ)
    (hKp : IsCoLipMatrix d (N.path_chain p) (N.path_domain p) Kp) :
    IsCoLipMatrix d (N.prefix_extension φ D hD hne himage).extensional_operator
      (D ∩ φ.func ⁻¹' N.path_domain p) (matrix_mul Kp Kφ) := by
  apply (local_equiv_colip_matrix_iff d _ _ _ _
    (N.prefix_extension_local_path_comp φ D hD hne himage p)).mpr
  exact colip_matrix_comp d φ (N.path_chain p) _ _ Kφ Kp (fun _ hx => hx.2) hKφ hKp

end FiniteOperatorNetwork
end
end formal_oet.vol_01.ch_05_operator_networks
