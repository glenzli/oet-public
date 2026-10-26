import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_05_operator_networks.network_extensional_space
import formal_oet.vol_01.ch_03_operator_local_degeneracy.mapping_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_04_operator_chain_calculus

open scoped BigOperators

variable {X I : Type} {bot : X}

/--
OET anchor: h-cc601faacb6105b5
**注 #h-cc601faacb6105b5（节点数不是外延不变量）**
`Fin 2` 上的恒等算子不是全未定义算子。
-/
theorem fin2_id_operator_ne_bot :
    (id_operator : Operator (Fin 2) 0) ≠ bot_operator := by
  intro h
  have hfun := congrArg (fun φ : Operator (Fin 2) 0 => φ.func (1 : Fin 2)) h
  norm_num [id_operator, bot_operator] at hfun

/--
OET anchor: h-cc601faacb6105b5
**注 #h-cc601faacb6105b5（节点数不是外延不变量）**
`Fin 2` 上由两个串联恒等节点构成的网络。
-/
noncomputable def fin2_two_node_id_network : OperatorNetwork (Fin 2) 0 (Fin 2) := by
  classical
  let one : Fin 2 := 1
  refine
    { U := {one}
      bot_not_mem := ?_
      node_fintype := inferInstance
      node_op := fun _ => id_operator
      node_dom_nonempty := ?_
      entry := fun _ => 0
      entry_mem := ?_
      choice := fun β z =>
        if β = (0 : Fin 2) then
          if z = one then OutputChoice.next (1 : Fin 2) else OutputChoice.stop
        else OutputChoice.stop
      choice_next_mem := ?_
      rank := fun β => if β = (0 : Fin 2) then 1 else 0
      choice_next_rank := ?_
      node_reachable := ?_ }
  · intro hbot
    simp [one] at hbot
  · intro β
    exact ⟨one, by simp [dom, id_operator, one]⟩
  · intro x
    have hxone : x.val = one := by
      exact Set.mem_singleton_iff.mp x.property
    simp [dom, id_operator, hxone, one]
  · intro β γ y hy hchoice
    dsimp [id_operator, dom] at hy ⊢
    by_cases hβ : β = (0 : Fin 2)
    · by_cases hyone : y = one
      · simp [hβ, hyone, one] at hchoice
        simp [hyone, one]
      · simp [id_operator, hβ, hyone] at hchoice
    · simp [hβ] at hchoice
  · intro β γ y hy hchoice
    by_cases hβ : β = (0 : Fin 2)
    · by_cases hyone : y = one
      · simp [hβ, hyone, one] at hchoice
        fin_cases γ <;> simp [id_operator, hβ] at hchoice ⊢
      · simp [id_operator, hβ, hyone] at hchoice
    · simp [hβ] at hchoice
  · intro β
    refine ⟨⟨one, by simp [one]⟩, ?_⟩
    fin_cases β <;>
      simp [path_with_fuel_core, id_operator, one]

/--
OET anchor: h-cc601faacb6105b5
**注 #h-cc601faacb6105b5（节点数不是外延不变量）**
单节点恒等网络与二节点串联恒等网络外延相同，但节点数不同。
-/
theorem node_count_not_extensional_invariant :
    let N₁ : FiniteOperatorNetwork (Fin 2) 0 Unit := NetworkObject.single_node_network
      (X := Fin 2) (bot := 0) (id_operator : Operator (Fin 2) 0)
      fin2_id_operator_ne_bot
    let N₂ : FiniteOperatorNetwork (Fin 2) 0 (Fin 2) := fin2_two_node_id_network.to_finite
    N₁.extensional_operator = N₂.extensional_operator ∧
      N₁.node_count = 1 ∧ N₂.node_count = 2 ∧
        N₁.node_count ≠ N₂.node_count := by
  classical
  dsimp
  have hN₁ :
      (NetworkObject.single_node_network
        (X := Fin 2) (bot := 0) (id_operator : Operator (Fin 2) 0)
        fin2_id_operator_ne_bot).extensional_operator =
        (id_operator : Operator (Fin 2) 0) :=
    NetworkObject.single_node_network_extensional_operator_eq
      (X := Fin 2) (bot := 0) (id_operator : Operator (Fin 2) 0)
      fin2_id_operator_ne_bot
  have hN₂ :
      fin2_two_node_id_network.to_finite.extensional_operator =
        (id_operator : Operator (Fin 2) 0) := by
    exact fin2_two_node_id_network.to_finite_extensional_operator_eq.trans
      (by
        ext x
        fin_cases x <;>
          simp [OperatorNetwork.extensional_operator, OperatorNetwork.eval,
            OperatorNetwork.eval_from, OperatorNetwork.eval_with_fuel,
            eval_with_fuel_core, fin2_two_node_id_network, id_operator])
  have hN₁_count :
      (NetworkObject.single_node_network
        (X := Fin 2) (bot := 0) (id_operator : Operator (Fin 2) 0)
        fin2_id_operator_ne_bot).node_count = 1 := by
    norm_num [FiniteOperatorNetwork.node_count]
  have hN₂_count : fin2_two_node_id_network.to_finite.node_count = 2 := by
    exact Fintype.card_fin 2
  refine ⟨hN₁.trans hN₂.symm, hN₁_count, hN₂_count, ?_⟩
  rw [hN₁_count, hN₂_count]
  norm_num

end formal_oet.vol_01.ch_05_operator_networks
