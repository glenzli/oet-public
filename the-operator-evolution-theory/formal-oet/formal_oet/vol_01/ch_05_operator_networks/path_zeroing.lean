import formal_oet.vol_01.ch_05_operator_networks.prefix_thresholds


namespace formal_oet.vol_01.ch_05_operator_networks

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork

open scoped BigOperators

variable {X V I : Type} {bot : X}
local instance instDecidableEqIPathRecurrence : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

namespace FiniteOperatorNetwork

variable (N : FiniteOperatorNetwork X bot V)

/-- A zeroing-radius bound followed by a scalar Lip bound on a specified suffix domain. -/
theorem zero_radius_zeroing_then_suffix
    (τ_ν : ENNReal) (q : N.PrefixOccurrence) (i j l : I)
    (suffix : Operator X bot) (S : Set X) (a : ENNReal)
    (hLip : HasScalarLipBound d suffix S j l a)
    (hν : τ_ν ≤ prefix_zero_radius d N q i j)
    (x y : X) (hx : x ∈ prefix_occurrence_input_domain N q)
    (hy : y ∈ prefix_occurrence_input_domain N q)
    (hxS : (prefix_occurrence_local_operator N q).func x ∈ S)
    (hyS : (prefix_occurrence_local_operator N q).func y ∈ S)
    (hdist : d i y x < τ_ν) :
    d l (suffix.func ((prefix_occurrence_local_operator N q).func y))
      (suffix.func ((prefix_occurrence_local_operator N q).func x)) = 0 := by
  have hzero := zero_radius_zeroing_step d N τ_ν q i j hν x hx y hy hdist
  apply le_antisymm _ (zero_le _)
  simpa only [hzero, mul_zero] using hLip.2 _ hyS _ hxS

/--
OET anchor: h-98e73f2611c67c92
The actual prefix image lies in the actual suffix domain, without a new premise.
-/
theorem path_suffix_input_domain_subset_dom (p : N.ReachablePath) (k : Nat) :
    (N.chain_eval_nodes (p.nodes.take k)) '' N.path_domain p.nodes ⊆
      dom (N.path_chain (p.nodes.drop k)) := by
  rintro y ⟨x, hx, rfl⟩
  have h := N.path_domain_subset_path_chain_dom p hx
  dsimp [dom] at h ⊢
  rw [N.path_chain_apply_eq_chain_eval_nodes] at h ⊢
  rw [← N.chain_eval_nodes_append, List.take_append_drop]
  exact h

/--
OET anchor: h-98e73f2611c67c92
**命题 #h-98e73f2611c67c92（路径中的零距传播条件）**
在可达路径的第 `n + 1` 个前缀上，零化半径条件先使该步输出在分量 `j`
上零测距；真实后缀在整个路径前缀像域上的单通道 Lip 界
再推出终端分量零距。没有点对上的结论等价前提。
-/
theorem path_zero_radius_zeroing_then_suffix
    (τ_ν : ENNReal)
    (p : N.ReachablePath) (n : Nat) (hn : n < p.nodes.length)
    (q : N.PrefixOccurrence)
    (hq : q.nodes = p.nodes.take (n + 1))
    (i j l : I) (x y : X)
    (hx : x ∈ N.path_domain p.nodes) (hy : y ∈ N.path_domain p.nodes)
    (hν : τ_ν ≤ prefix_zero_radius d N q i j)
    (hdist :
      d i (N.chain_eval_nodes (p.nodes.take n) y)
          (N.chain_eval_nodes (p.nodes.take n) x) < τ_ν)
    (a : ENNReal)
    (hLip :
      ∀ u ∈ (N.chain_eval_nodes (p.nodes.take (n + 1))) '' N.path_domain p.nodes,
      ∀ v ∈ (N.chain_eval_nodes (p.nodes.take (n + 1))) '' N.path_domain p.nodes,
        d l ((N.path_chain (p.nodes.drop (n + 1))).func u)
            ((N.path_chain (p.nodes.drop (n + 1))).func v) ≤ a * d j u v) :
    d j (N.chain_eval_nodes (p.nodes.take (n + 1)) y)
        (N.chain_eval_nodes (p.nodes.take (n + 1)) x) = 0 ∧
      d l (N.chain_eval_nodes p.nodes y) (N.chain_eval_nodes p.nodes x) = 0 := by
  have htake :
      p.nodes.take (n + 1) =
        p.nodes.take n ++ [p.nodes.get ⟨n, hn⟩] :=
    (List.take_concat_get' p.nodes n hn).symm
  have hdrop : q.nodes.dropLast = p.nodes.take n := by
    rw [hq, htake, List.dropLast_concat]
  have hlast :
      prefix_occurrence_last N q = p.nodes.get ⟨n, hn⟩ := by
    unfold prefix_occurrence_last
    simpa only [hq, htake] using
      (List.getLast_concat
        (l := p.nodes.take n) (a := p.nodes.get ⟨n, hn⟩))
  have hx_prefix : x ∈ N.prefix_domain q.nodes := by
    rcases hx with ⟨hxU, hxpath⟩
    refine ⟨hxU, p.nodes.drop (n + 1), ?_⟩
    calc
      N.path_of ⟨x, hxU⟩ = p.nodes := hxpath
      _ = p.nodes.take (n + 1) ++ p.nodes.drop (n + 1) :=
        (List.take_append_drop (n + 1) p.nodes).symm
      _ = q.nodes ++ p.nodes.drop (n + 1) := by rw [hq]
  have hy_prefix : y ∈ N.prefix_domain q.nodes := by
    rcases hy with ⟨hyU, hypath⟩
    refine ⟨hyU, p.nodes.drop (n + 1), ?_⟩
    calc
      N.path_of ⟨y, hyU⟩ = p.nodes := hypath
      _ = p.nodes.take (n + 1) ++ p.nodes.drop (n + 1) :=
        (List.take_append_drop (n + 1) p.nodes).symm
      _ = q.nodes ++ p.nodes.drop (n + 1) := by rw [hq]
  have hx_current :
      N.chain_eval_nodes (p.nodes.take n) x ∈
        prefix_occurrence_input_domain N q := by
    refine ⟨x, hx_prefix, ?_⟩
    rw [hdrop]
  have hy_current :
      N.chain_eval_nodes (p.nodes.take n) y ∈
        prefix_occurrence_input_domain N q := by
    refine ⟨y, hy_prefix, ?_⟩
    rw [hdrop]
  have hzero_local :=
    zero_radius_zeroing_step d N τ_ν q i j hν
      (N.chain_eval_nodes (p.nodes.take n) x) hx_current
      (N.chain_eval_nodes (p.nodes.take n) y) hy_current hdist
  have hx_step := N.chain_eval_nodes_take_succ hn x
  have hy_step := N.chain_eval_nodes_take_succ hn y
  have hzero_step :
      d j (N.chain_eval_nodes (p.nodes.take (n + 1)) y)
          (N.chain_eval_nodes (p.nodes.take (n + 1)) x) = 0 := by
    rw [hy_step, hx_step]
    simpa [prefix_occurrence_local_operator, hlast] using hzero_local
  refine ⟨hzero_step, ?_⟩
  have hbound := hLip _ (Set.mem_image_of_mem _ hy) _ (Set.mem_image_of_mem _ hx)
  have hsuffix :
      d l
        (N.chain_eval_nodes (p.nodes.drop (n + 1))
          (N.chain_eval_nodes (p.nodes.take (n + 1)) y))
        (N.chain_eval_nodes (p.nodes.drop (n + 1))
          (N.chain_eval_nodes (p.nodes.take (n + 1)) x)) = 0 := by
    apply le_antisymm _ (zero_le _)
    simpa only [N.path_chain_apply_eq_chain_eval_nodes, hzero_step, mul_zero] using hbound
  rw [← List.take_append_drop (n + 1) p.nodes]
  simpa only [N.chain_eval_nodes_append] using hsuffix

/-- Actual intermediate inputs on a complete path belong to its selected prefix
occurrence's actual input domain. -/
theorem path_current_input_mem_prefix_domain
    (p : N.ReachablePath) (n : Nat) (hn : n < p.nodes.length)
    (q : N.PrefixOccurrence) (hq : q.nodes = p.nodes.take (n + 1))
    (x : X) (hx : x ∈ N.path_domain p.nodes) :
    N.chain_eval_nodes (p.nodes.take n) x ∈ prefix_occurrence_input_domain N q := by
  have hdrop : q.nodes.dropLast = p.nodes.take n := by
    rw [hq, ← List.take_concat_get' p.nodes n hn, List.dropLast_concat]
  have hx_prefix : x ∈ N.prefix_domain q.nodes := by
    rcases hx with ⟨hxU, hxpath⟩
    refine ⟨hxU, p.nodes.drop (n + 1), ?_⟩
    rw [hq, List.take_append_drop]
    exact hxpath
  exact ⟨x, hx_prefix, by rw [hdrop]⟩

/-- OET anchor: h-98e73f2611c67c92
路径中的零距传播条件，联合阈值的整路径块特例. The actual input-domain
diameter supplies the distance condition for every pair in the actual path domain. -/
theorem path_joint_zeroing_then_suffix
    (τ_σ τ_ν : ENNReal)
    (p : N.ReachablePath) (n : Nat) (hn : n < p.nodes.length)
    (q : N.PrefixOccurrence) (hq : q.nodes = p.nodes.take (n + 1))
    (i j l : I)
    (hdiam : input_diameter d i (prefix_occurrence_input_domain N q) < τ_σ)
    (hthreshold : τ_σ ≤ τ_ν)
    (hν : τ_ν ≤ prefix_zero_radius d N q i j)
    (a : ENNReal)
    (hLip :
      ∀ u ∈ (N.chain_eval_nodes (p.nodes.take (n + 1))) '' N.path_domain p.nodes,
      ∀ v ∈ (N.chain_eval_nodes (p.nodes.take (n + 1))) '' N.path_domain p.nodes,
        d l ((N.path_chain (p.nodes.drop (n + 1))).func u)
            ((N.path_chain (p.nodes.drop (n + 1))).func v) ≤ a * d j u v) :
    ∀ x ∈ N.path_domain p.nodes, ∀ y ∈ N.path_domain p.nodes,
      d j (N.chain_eval_nodes (p.nodes.take (n + 1)) y)
          (N.chain_eval_nodes (p.nodes.take (n + 1)) x) = 0 ∧
        d l (N.chain_eval_nodes p.nodes y) (N.chain_eval_nodes p.nodes x) = 0 := by
  intro x hx y hy
  apply path_zero_radius_zeroing_then_suffix d N τ_ν p n hn q hq i j l
    x y hx hy hν _ a hLip
  exact lt_of_le_of_lt (component_distance_le_input_diameter d i _ _ _
    (path_current_input_mem_prefix_domain N p n hn q hq y hy)
    (path_current_input_mem_prefix_domain N p n hn q hq x hx))
    (lt_of_lt_of_le hdiam hthreshold)

end FiniteOperatorNetwork

end

end formal_oet.vol_01.ch_05_operator_networks
