import formal_oet.vol_01.ch_05_operator_networks.path_matrix
import formal_oet.vol_01.ch_03_operator_local_degeneracy.mapping_entropy

namespace formal_oet.vol_01.ch_05_operator_networks
noncomputable section
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_04_operator_chain_calculus

variable {X V I : Type} {bot : X}
variable (d : I → X → X → ENNReal)
namespace FiniteOperatorNetwork
variable (N : FiniteOperatorNetwork X bot V)

/--
OET anchor: h-374f884cd4d69e88 **§ #h-374f884cd4d69e88（末节点）** 前缀发生 `q` 的末节点。 -/
def prefix_occurrence_last (q : N.PrefixOccurrence) : V :=
  q.nodes.getLast q.nonempty_nodes

/--
OET anchor: h-4b1389b158d2780e **定义（发生上的局部算子）** 前缀发生上的局部算子 `f_q`。 -/
def prefix_occurrence_local_operator (q : N.PrefixOccurrence) : Operator X bot :=
  N.node_op (prefix_occurrence_last N q)

/--
OET anchor: h-374f884cd4d69e88 **§ #h-374f884cd4d69e88（当前输入域）** 前缀发生上的当前输入域 `D_q^in`。 -/
def prefix_occurrence_input_domain (q : N.PrefixOccurrence) : Set X :=
  N.prefix_input_domain q.nodes

/--
OET anchor: h-374f884cd4d69e88 **§ #h-374f884cd4d69e88（当前输出域）** 前缀发生上的当前输出域 `D_q^out`。 -/
def prefix_occurrence_output_domain (q : N.PrefixOccurrence) : Set X :=
  N.prefix_output_domain q.nodes

/--
OET anchor: h-374f884cd4d69e88
**§ #h-374f884cd4d69e88（当前输出域）**
前缀当前输出域等于末节点局域算子作用于前缀当前输入域所得的像。
-/
theorem prefix_occurrence_output_domain_eq_local_image
    (q : N.PrefixOccurrence) :
    prefix_occurrence_output_domain N q =
      (prefix_occurrence_local_operator N q).func ''
        prefix_occurrence_input_domain N q := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    refine ⟨N.chain_eval_nodes q.nodes.dropLast x, ⟨x, hx, rfl⟩, ?_⟩
    unfold prefix_occurrence_local_operator prefix_occurrence_last
    calc
      (N.node_op (q.nodes.getLast q.nonempty_nodes)).func
          (N.chain_eval_nodes q.nodes.dropLast x) =
          N.chain_eval_nodes [q.nodes.getLast q.nonempty_nodes]
            (N.chain_eval_nodes q.nodes.dropLast x) := rfl
      _ = N.chain_eval_nodes
          (q.nodes.dropLast ++ [q.nodes.getLast q.nonempty_nodes]) x :=
        (N.chain_eval_nodes_append q.nodes.dropLast
          [q.nodes.getLast q.nonempty_nodes] x).symm
      _ = N.chain_eval_nodes q.nodes x :=
        congrArg (fun nodes => N.chain_eval_nodes nodes x)
          (List.dropLast_append_getLast q.nonempty_nodes)
  · rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨x, hx, ?_⟩
    unfold prefix_occurrence_local_operator prefix_occurrence_last
    calc
      N.chain_eval_nodes q.nodes x =
          N.chain_eval_nodes
            (q.nodes.dropLast ++ [q.nodes.getLast q.nonempty_nodes]) x :=
        congrArg (fun nodes => N.chain_eval_nodes nodes x)
          (List.dropLast_append_getLast q.nonempty_nodes).symm
      _ = N.chain_eval_nodes [q.nodes.getLast q.nonempty_nodes]
          (N.chain_eval_nodes q.nodes.dropLast x) :=
        N.chain_eval_nodes_append q.nodes.dropLast
          [q.nodes.getLast q.nonempty_nodes] x
      _ = (N.node_op (q.nodes.getLast q.nonempty_nodes)).func
          (N.chain_eval_nodes q.nodes.dropLast x) := rfl

/--
OET anchor: h-374f884cd4d69e88 **§ #h-374f884cd4d69e88（当前输入域非空）** 可达前缀发生的输入域非空。 -/
theorem prefix_occurrence_input_domain_nonempty (q : N.PrefixOccurrence) :
    (prefix_occurrence_input_domain N q).Nonempty := by
  exact N.prefix_input_domain_nonempty q

/--
OET anchor: h-374f884cd4d69e88 **§ #h-374f884cd4d69e88（当前输出域非空）** 可达前缀发生的输出域非空。 -/
theorem prefix_occurrence_output_domain_nonempty (q : N.PrefixOccurrence) :
    (prefix_occurrence_output_domain N q).Nonempty := by
  exact N.prefix_output_domain_nonempty q

/--
OET anchor: h-4b1389b158d2780e **定义（前缀统一零化半径）** `\underline{r}^{\mathrm N}_q(i,j)`。 -/
noncomputable def prefix_zero_radius (q : N.PrefixOccurrence) (i j : I) :
    ENNReal :=
  min_annihilation_radius d (prefix_occurrence_local_operator N q) i
    (singleton_nonempty_finset j) (prefix_occurrence_input_domain N q)

/--
OET anchor: h-4b1389b158d2780e **定义（阈值分类）** `\operatorname{Type}_q(i,j)`。
Both inequalities are tested independently; neither coordinate masks the other.
-/
noncomputable def prefix_threshold_readout (σ : ScaleFamily (X := X) (I := I))
    (τ_σ τ_ν : ENNReal) (q : N.PrefixOccurrence) (i j : I) : ThresholdBits :=
  operator_threshold_readout d (prefix_occurrence_local_operator N q)
    (prefix_occurrence_input_domain N q) σ τ_σ τ_ν i j

/-- The network readout is the general operator readout on its actual occurrence domain. -/
theorem prefix_threshold_readout_eq_operator
    (σ : ScaleFamily X I) (τ_σ τ_ν : ENNReal)
    (q : N.PrefixOccurrence) (i j : I) :
    prefix_threshold_readout d N σ τ_σ τ_ν q i j =
      operator_threshold_readout d (prefix_occurrence_local_operator N q)
        (prefix_occurrence_input_domain N q) σ τ_σ τ_ν i j := rfl

/-- OET anchor: h-98e73f2611c67c92
路径中的零距传播条件的单步实例，直接应用一般算子零化半径定理。 -/
theorem zero_radius_zeroing_step
    (τ_ν : ENNReal) (q : N.PrefixOccurrence) (i j : I)
    (hν : τ_ν ≤ prefix_zero_radius d N q i j) :
    ∀ x ∈ prefix_occurrence_input_domain N q, ∀ y ∈ prefix_occurrence_input_domain N q,
      d i y x < τ_ν →
        d j ((prefix_occurrence_local_operator N q).func y)
          ((prefix_occurrence_local_operator N q).func x) = 0 := by
  intro x hx y hy hdist
  exact zero_of_lt_min_annihilation_radius d (prefix_occurrence_local_operator N q)
    (prefix_occurrence_input_domain N q) i j x y τ_ν hν hx hy hdist

/-- The general covering bound specialized to a subset of an actual prefix input domain. -/
theorem zero_radius_cov_num_bound
    (τ_ν : ENNReal) (q : N.PrefixOccurrence) (i j : I)
    (A : Set X) (hA : A ⊆ prefix_occurrence_input_domain N q)
    (ε : ENNReal) (hε : FinitePositiveRadius ε)
    (hν : τ_ν ≤ prefix_zero_radius d N q i j) :
    cov_num d j ε ((prefix_occurrence_local_operator N q).func '' A) ≤
      cov_num d i τ_ν A :=
  operator_zero_radius_cov_num_bound d (prefix_occurrence_local_operator N q)
    (prefix_occurrence_input_domain N q) A hA i j τ_ν ε hε.1 hν

/-- The reachable prefix ending at a concrete position of a complete path. -/
def path_prefix_at (N : FiniteOperatorNetwork X bot V)
    (p : N.ReachablePath) (k : Fin p.nodes.length) : N.PrefixOccurrence where
  nodes := p.nodes.take (k.val + 1)
  nonempty_nodes := by
    apply List.ne_nil_iff_length_pos.mpr
    simp [List.length_take]
  reachable := ⟨p, p.nodes.drop (k.val + 1),
    (List.take_append_drop (k.val + 1) p.nodes).symm⟩

/-- OET anchor: h-4b1389b158d2780e
路径阈值序列 `(\operatorname{Type}_{q_1}, …, \operatorname{Type}_{q_r})`：
按完整路径的实际发生次序，记录每个前缀的通道分类表。 -/
noncomputable def path_threshold_sequence (σ : ScaleFamily X I) (τ_σ τ_ν : ENNReal)
    (p : N.ReachablePath) : List (I → I → ThresholdBits) :=
  List.ofFn fun k : Fin p.nodes.length =>
    prefix_threshold_readout d N σ τ_σ τ_ν (path_prefix_at N p k)

/-- The threshold sequence has one entry for each actual position on the path. -/
theorem path_threshold_sequence_length (σ : ScaleFamily X I) (τ_σ τ_ν : ENNReal)
    (p : N.ReachablePath) :
    (path_threshold_sequence d N σ τ_σ τ_ν p).length = p.nodes.length := by
  simp [path_threshold_sequence]

end FiniteOperatorNetwork
end
end formal_oet.vol_01.ch_05_operator_networks
