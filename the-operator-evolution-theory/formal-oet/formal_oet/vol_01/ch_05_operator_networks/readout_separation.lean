import formal_oet.vol_01.ch_05_operator_networks.network_expression_readouts

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus

namespace ReadoutSeparation

theorem fin3_id_ne_bot : (id_operator : Operator (Fin 3) 0) ≠ bot_operator := by
  intro h
  have hf := congrArg (fun f : Operator (Fin 3) 0 => f.func 1) h
  norm_num [id_operator, bot_operator] at hf

noncomputable def single : FiniteOperatorNetwork (Fin 3) 0 Unit :=
  NetworkObject.single_node_network id_operator fin3_id_ne_bot

def split : FiniteOperatorNetwork (Fin 3) 0 (Fin 2) where
  U := {x | x ≠ 0}
  bot_not_mem := by simp
  node_fintype := inferInstance
  node_op := fun _ => id_operator
  node_dom_nonempty := fun _ => ⟨1, by norm_num [dom, id_operator]⟩
  entry := fun x => if x.val = 1 then 0 else 1
  entry_mem := fun x => x.property
  choice := fun _ _ => .stop
  choice_next_mem := by intros; contradiction
  depth_bound := 1
  path_of := fun x => [if x.val = 1 then 0 else 1]
  path_terminal := fun _ => .stop rfl
  path_length_le_depth := by intro x; rfl
  node_reachable := by
    intro v
    fin_cases v
    · exact ⟨⟨1, by decide⟩, by simp⟩
    · exact ⟨⟨2, by decide⟩, by simp⟩

theorem single_extensional_operator : single.extensional_operator = id_operator :=
  NetworkObject.single_node_network_extensional_operator_eq _ _

theorem split_extensional_operator : split.extensional_operator = id_operator := by
  ext x
  fin_cases x <;>
    simp [FiniteOperatorNetwork.extensional_operator, FiniteOperatorNetwork.eval,
      chain_eval_nodes_core, split, id_operator]

/-- The single network has a piece containing both nonabsorbing inputs. No
piece of the two-entry network can contain both, since their node lists differ. -/
theorem raw_path_readouts_differ : single.path_readout ≠ split.path_readout := by
  have h1 : (1 : Fin 3) ∈ single.path_domain [()] :=
    ⟨by simp [single, NetworkObject.single_node_network, dom, id_operator], rfl⟩
  have h2 : (2 : Fin 3) ∈ single.path_domain [()] :=
    ⟨by simp [single, NetworkObject.single_node_network, dom, id_operator], rfl⟩
  have hpiece : (single.path_domain [()], single.path_chain [()]) ∈
      single.path_readout.pieces :=
    ⟨⟨[()], ⟨1, h1⟩⟩, rfl⟩
  intro heq
  rw [heq] at hpiece
  rcases hpiece with ⟨p, hp⟩
  have hdom : split.path_domain p.nodes = single.path_domain [()] := congrArg Prod.fst hp
  have h1' : (1 : Fin 3) ∈ split.path_domain p.nodes := by rw [hdom]; exact h1
  have h2' : (2 : Fin 3) ∈ split.path_domain p.nodes := by rw [hdom]; exact h2
  have hpaths := h1'.2.trans h2'.2.symm
  simp [split] at hpaths

theorem single_source_nonempty : single.U.Nonempty :=
  ⟨1, by simp [single, NetworkObject.single_node_network, dom, id_operator]⟩

theorem split_source_nonempty : split.U.Nonempty := ⟨1, by simp [split]⟩

noncomputable def single_object : NetworkObject (Fin 3) 0 :=
  NetworkObject.nonempty (NonemptyOperatorNetwork.encode single single_source_nonempty)

noncomputable def split_object : NetworkObject (Fin 3) 0 :=
  NetworkObject.nonempty (NonemptyOperatorNetwork.encode split split_source_nonempty)

theorem objects_same_operator :
    single_object.extensional_operator = split_object.extensional_operator := by
  simp only [single_object, split_object, NetworkObject.extensional_operator_nonempty,
    NonemptyOperatorNetwork.encode_extensional_operator,
    single_extensional_operator, split_extensional_operator]

theorem object_path_readouts_differ :
    single_object.path_readout ≠ split_object.path_readout := by
  simpa only [single_object, split_object, NetworkObject.path_readout_encode] using
    raw_path_readouts_differ

theorem object_path_profiles_differ :
    (path_profile (X := Fin 3) (bot := 0)).read single_object ≠
      (path_profile (X := Fin 3) (bot := 0)).read split_object := by
  intro h
  exact object_path_readouts_differ (congrArg Subtype.val h)

theorem object_tagged_profiles_differ :
    (tagged_profile (X := Fin 3) (bot := 0)).read single_object ≠
      (tagged_profile (X := Fin 3) (bot := 0)).read split_object := by
  intro h
  apply object_path_profiles_differ
  exact (tagged_profile_forget single_object).symm.trans
    ((congrArg NetworkTaggedReadout.forget h).trans (tagged_profile_forget split_object))

/--
OET anchor: h-e7bf88d54855ca9f
**注（路径分段不由外延决定）**
On the same two-point nonabsorbing input domain, a single identity node and
two identity entry nodes have the same operator but different path and tagged
profiles. Both witnesses are elements of the faithful public network space.
-/
theorem same_operator_different_readouts :
    ∃ N M : NetworkObject (Fin 3) 0,
      N.extensional_operator = M.extensional_operator ∧
      (path_profile (X := Fin 3) (bot := 0)).read N ≠ path_profile.read M ∧
      (tagged_profile (X := Fin 3) (bot := 0)).read N ≠ tagged_profile.read M :=
  ⟨single_object, split_object, objects_same_operator,
    object_path_profiles_differ, object_tagged_profiles_differ⟩

/-- OET anchor: h-e7bf88d54855ca9f
The path readout fails the chapter's extensional-invariance predicate. -/
theorem path_profile_not_extensional_invariant :
    ¬ ExtensionalInvariantProfile (path_profile (X := Fin 3) (bot := 0)) := by
  intro h
  exact object_path_profiles_differ (h single_object split_object objects_same_operator)

/-- OET anchor: h-e7bf88d54855ca9f
The tagged readout likewise fails extensional invariance. -/
theorem tagged_profile_not_extensional_invariant :
    ¬ ExtensionalInvariantProfile (tagged_profile (X := Fin 3) (bot := 0)) := by
  intro h
  exact object_tagged_profiles_differ (h single_object split_object objects_same_operator)

end ReadoutSeparation
end formal_oet.vol_01.ch_05_operator_networks
