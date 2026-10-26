import formal_oet.vol_01.ch_05_operator_networks.operator_network
import formal_oet.vol_01.ch_02_operator_bounds.path_algebra


namespace formal_oet.vol_01.ch_05_operator_networks

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators

variable {X V I : Type} {bot : X}
variable [Fintype I]
local instance instDecidableEqIPathMatrix : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

namespace FiniteOperatorNetwork

variable (N : FiniteOperatorNetwork X bot V)

/-- The ordered matrix product attached to a path node sequence. -/
noncomputable def path_matrix_product
    (M : V → I → I → ENNReal) (nodes : List V) : I → I → ENNReal :=
  matrix_list_mul ((nodes.map M).reverse)

@[simp]
theorem path_matrix_product_nil (M : V → I → I → ENNReal) :
    path_matrix_product M [] = matrix_id := rfl

@[simp]
theorem path_matrix_product_append_singleton
    (M : V → I → I → ENNReal) (nodes : List V) (β : V) :
    path_matrix_product M (nodes ++ [β]) =
      matrix_mul (M β) (path_matrix_product M nodes) := by
  simp [path_matrix_product, matrix_list_mul]

/-- Restricting the set of inputs preserves a Lip matrix. -/
theorem is_lip_matrix_mono {A B : Set X} {φ : Operator X bot}
    {L : I → I → ENNReal} (hAB : A ⊆ B) (hL : IsLipMatrix d φ B L) :
    IsLipMatrix d φ A L := by
  exact ⟨fun x hx => hL.1 (hAB hx), fun x hx y hy j =>
    hL.2 x (hAB hx) y (hAB hy) j⟩

/-- Restricting to a nonempty subset preserves a co-Lip matrix. -/
theorem is_colip_matrix_mono {A B : Set X} {φ : Operator X bot}
    {K : I → I → ENNReal} (hA : A.Nonempty) (hAB : A ⊆ B)
    (hK : IsCoLipMatrix d φ B K) : IsCoLipMatrix d φ A K := by
  exact ⟨hA, fun x hx => hK.2.1 (hAB hx), fun x hx y hy j =>
    hK.2.2 x (hAB hx) y (hAB hy) j⟩

/-- Every path-prefix image lies in the domain of its next stored node. -/
theorem path_prefix_image_subset_node_dom (p : N.ReachablePath)
    (n : Fin p.nodes.length) :
    (N.path_chain (p.nodes.take n.val)).func '' N.path_domain p.nodes ⊆
      N.node_dom (p.nodes.get n) := by
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  have hpos := N.path_position_input_domain_subset_node_dom
    (⟨p, n⟩ : N.PathPosition)
  have hmem :
      N.chain_eval_nodes (p.nodes.take n.val) x ∈
        N.path_position_input_domain (⟨p, n⟩ : N.PathPosition) :=
    ⟨x, hx, rfl⟩
  have := hpos hmem
  simpa [FiniteOperatorNetwork.path_position_label,
    FiniteOperatorNetwork.node_dom,
    N.path_chain_apply_eq_chain_eval_nodes] using this

/-- Full-node Lip certificates generate the exact ordered path product. -/
theorem path_right_chain_lip_bounded
    (nodes : List V) (U : Set X) (L : V → I → I → ENNReal)
    (hU : ∀ x ∈ U, x ≠ bot)
    (hinput : ∀ (n : Nat) (hn : n < nodes.length),
      (N.path_chain (nodes.take n)).func '' U ⊆
        N.node_dom (nodes.get ⟨n, hn⟩))
    (hL : ∀ β ∈ nodes,
      IsLipMatrix d (N.node_op β) (N.node_dom β) (L β)) :
    RightChainLipBounded d ((nodes.map N.node_op).reverse) U
      (path_matrix_product L nodes) := by
  induction nodes using List.reverseRecOn with
  | nil =>
      exact RightChainLipBounded.nil U hU
  | append_singleton nodes β ih =>
      have hinput_prefix : ∀ (n : Nat) (hn : n < nodes.length),
          (N.path_chain (nodes.take n)).func '' U ⊆
            N.node_dom (nodes.get ⟨n, hn⟩) := by
        intro n hn
        have hn' : n < (nodes ++ [β]).length :=
          lt_trans hn (by simp)
        have h := hinput n hn'
        have htake : (nodes ++ [β]).take n = nodes.take n :=
          List.take_append_of_le_length (Nat.le_of_lt hn)
        rw [htake] at h
        simpa [List.get_eq_getElem, hn] using h
      have htail := ih hinput_prefix (by
        intro γ hγ
        exact hL γ (by simp [hγ]))
      have hlast :
          (N.path_chain nodes).func '' U ⊆ N.node_dom β := by
        have h := hinput nodes.length (by simp)
        simpa using h
      have hnode :
          IsLipMatrix d (N.node_op β) ((N.path_chain nodes).func '' U) (L β) :=
        is_lip_matrix_mono d hlast (hL β (by simp))
      simpa [FiniteOperatorNetwork.path_chain] using
        (RightChainLipBounded.cons (d := d) (N.node_op β)
          ((nodes.map N.node_op).reverse) U (L β)
          (path_matrix_product L nodes) htail hnode)

/-- Full-node co-Lip certificates generate the exact ordered path product. -/
theorem path_right_chain_colip_bounded
    (nodes : List V) (U : Set X) (K : V → I → I → ENNReal)
    (hU : ∀ x ∈ U, x ≠ bot) (hU_ne : U.Nonempty)
    (hinput : ∀ (n : Nat) (hn : n < nodes.length),
      (N.path_chain (nodes.take n)).func '' U ⊆
        N.node_dom (nodes.get ⟨n, hn⟩))
    (hK : ∀ β ∈ nodes,
      IsCoLipMatrix d (N.node_op β) (N.node_dom β) (K β)) :
    RightChainCoLipBounded d ((nodes.map N.node_op).reverse) U
      (path_matrix_product K nodes) := by
  induction nodes using List.reverseRecOn with
  | nil =>
      exact RightChainCoLipBounded.nil U hU hU_ne
  | append_singleton nodes β ih =>
      have hinput_prefix : ∀ (n : Nat) (hn : n < nodes.length),
          (N.path_chain (nodes.take n)).func '' U ⊆
            N.node_dom (nodes.get ⟨n, hn⟩) := by
        intro n hn
        have hn' : n < (nodes ++ [β]).length :=
          lt_trans hn (by simp)
        have h := hinput n hn'
        have htake : (nodes ++ [β]).take n = nodes.take n :=
          List.take_append_of_le_length (Nat.le_of_lt hn)
        rw [htake] at h
        simpa [List.get_eq_getElem, hn] using h
      have htail := ih hinput_prefix (by
        intro γ hγ
        exact hK γ (by simp [hγ]))
      have hlast :
          (N.path_chain nodes).func '' U ⊆ N.node_dom β := by
        have h := hinput nodes.length (by simp)
        simpa using h
      have himage : ((N.path_chain nodes).func '' U).Nonempty :=
        hU_ne.image (N.path_chain nodes).func
      have hnode :
          IsCoLipMatrix d (N.node_op β) ((N.path_chain nodes).func '' U) (K β) :=
        is_colip_matrix_mono d himage hlast (hK β (by simp))
      simpa [FiniteOperatorNetwork.path_chain] using
        (RightChainCoLipBounded.cons (d := d) (N.node_op β)
          ((nodes.map N.node_op).reverse) U (K β)
          (path_matrix_product K nodes) htail hnode)

/--
OET anchor: h-d64105c6ec192365
**命题 #h-d64105c6ec192365（路径级矩阵证书继承，Lip）**
Node-level Lip matrices on the node domains of one reachable path compose to
the ordered path product on that path domain.
-/
theorem path_chain_lip_matrix (p : N.ReachablePath)
    (L : V → I → I → ENNReal)
    (hL : ∀ β ∈ p.nodes,
      IsLipMatrix d (N.node_op β) (N.node_dom β) (L β)) :
    IsLipMatrix d (N.path_chain p.nodes) (N.path_domain p.nodes)
      (path_matrix_product L p.nodes) := by
  have hU : ∀ x ∈ N.path_domain p.nodes, x ≠ bot := by
    intro x hx hxb
    subst x
    exact N.bot_not_mem (N.path_domain_subset_source hx)
  have hinput : ∀ (n : Nat) (hn : n < p.nodes.length),
      (N.path_chain (p.nodes.take n)).func '' N.path_domain p.nodes ⊆
        N.node_dom (p.nodes.get ⟨n, hn⟩) := by
    intro n hn
    exact N.path_prefix_image_subset_node_dom p ⟨n, hn⟩
  simpa [FiniteOperatorNetwork.path_chain] using
    right_chain_lip_matrix d ((p.nodes.map N.node_op).reverse)
      (N.path_domain p.nodes) (path_matrix_product L p.nodes)
      (N.path_right_chain_lip_bounded d p.nodes (N.path_domain p.nodes)
        L hU hinput hL)

/--
OET anchor: h-d64105c6ec192365
**命题 #h-d64105c6ec192365（路径级矩阵证书继承，co-Lip）**
Node-level co-Lip matrices on the node domains of one reachable path compose
to the ordered path product on that nonempty path domain.
-/
theorem path_chain_colip_matrix (p : N.ReachablePath)
    (K : V → I → I → ENNReal)
    (hK : ∀ β ∈ p.nodes,
      IsCoLipMatrix d (N.node_op β) (N.node_dom β) (K β)) :
    IsCoLipMatrix d (N.path_chain p.nodes) (N.path_domain p.nodes)
      (path_matrix_product K p.nodes) := by
  have hU : ∀ x ∈ N.path_domain p.nodes, x ≠ bot := by
    intro x hx hxb
    subst x
    exact N.bot_not_mem (N.path_domain_subset_source hx)
  have hinput : ∀ (n : Nat) (hn : n < p.nodes.length),
      (N.path_chain (p.nodes.take n)).func '' N.path_domain p.nodes ⊆
        N.node_dom (p.nodes.get ⟨n, hn⟩) := by
    intro n hn
    exact N.path_prefix_image_subset_node_dom p ⟨n, hn⟩
  simpa [FiniteOperatorNetwork.path_chain] using
    right_chain_colip_matrix d ((p.nodes.map N.node_op).reverse)
      (N.path_domain p.nodes) (path_matrix_product K p.nodes)
      (N.path_right_chain_colip_bounded d p.nodes (N.path_domain p.nodes)
        K hU p.nonempty_domain hinput hK)

/--
OET anchor: h-d64105c6ec192365
**命题 #h-d64105c6ec192365（路径级矩阵证书继承，Lip）**
若 《算子界》 的右链 Lip 递推条件在路径域上成立，则路径链具有对应矩阵上界。
-/
theorem path_chain_lip_matrix_of_right_chain (nodes : List V) (U : Set X)
    (L : I → I → ENNReal)
    (hL :
      RightChainLipBounded d ((nodes.map N.node_op).reverse) U L) :
    IsLipMatrix d (N.path_chain nodes) U L := by
  simpa [path_chain] using
    right_chain_lip_matrix d ((nodes.map N.node_op).reverse) U L hL

/--
OET anchor: h-d64105c6ec192365
**命题 #h-d64105c6ec192365（路径级矩阵证书继承，co-Lip）**
若 《算子界》 的右链 co-Lip 递推条件在路径域上成立，则路径链具有对应矩阵下界。
-/
theorem path_chain_colip_matrix_of_right_chain (nodes : List V) (U : Set X)
    (K : I → I → ENNReal)
    (hK :
      RightChainCoLipBounded d ((nodes.map N.node_op).reverse) U K) :
    IsCoLipMatrix d (N.path_chain nodes) U K := by
  simpa [path_chain] using
    right_chain_colip_matrix d ((nodes.map N.node_op).reverse) U K hK

/--
OET anchor: h-d64105c6ec192365
**命题 #h-d64105c6ec192365（路径级矩阵证书继承，Lip 逐点形式）**
合法路径 Lip 矩阵给出路径终点距离的逐分量上界。
-/
theorem path_chain_lip_pointwise (nodes : List V) (U : Set X)
    (L : I → I → ENNReal)
    (hL : IsLipMatrix d (N.path_chain nodes) U L) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j ((N.path_chain nodes).func x) ((N.path_chain nodes).func y) ≤
        ∑ i : I, L i j * d i x y := by
  intro x hx y hy j
  exact hL.2 x hx y hy j

/--
OET anchor: h-d64105c6ec192365
**命题 #h-d64105c6ec192365（路径级矩阵证书继承，co-Lip 逐点形式）**
合法路径 co-Lip 矩阵给出路径终点距离的逐分量下界。
-/
theorem path_chain_colip_pointwise (nodes : List V) (U : Set X)
    (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d (N.path_chain nodes) U K) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i : I, K i j * d i x y ≤
        d j ((N.path_chain nodes).func x) ((N.path_chain nodes).func y) := by
  intro x hx y hy j
  exact hK.2.2 x hx y hy j

/--
**命题 #h-8893f19c84720522（前缀扩展的复合等式，算子链形式）**
Auxiliary chain unfolding. The actual network extension, path domains and
matrix inheritance are proved in `prefix_extension.lean`.
-/
theorem prefix_extension_path_chain_apply (φ : Operator X bot)
    (nodes : List V) (x : X) :
    (OperatorChain [N.path_chain nodes, φ]).func x =
      (N.path_chain nodes).func (φ.func x) := by
  simp [OperatorChain]

end FiniteOperatorNetwork

end

end formal_oet.vol_01.ch_05_operator_networks
