import formal_oet.vol_01.ch_05_operator_networks.network_identity

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus

variable {X I : Type} {bot : X}

/--
OET anchor: h-4a79b2e15dc90f1a
**定义（非空编号网络表示）**
`FiniteOperatorNetwork` 的非空输入域版本，保留构造时使用的辅助证书。
进入 `NetworkObject` 时只按原始编号数据判断相等；唯一空对象由
`NetworkObject.empty` 表示。
-/
structure NonemptyOperatorNetwork (X : Type) (bot : X) where
  node_count : Nat
  network : FiniteOperatorNetwork X bot (Fin node_count)
  source_nonempty : network.U.Nonempty

namespace NonemptyOperatorNetwork

/-- Original data retain the actual finite numbering. Equal data forget only
implementation witnesses, not graph isomorphisms or extensional differences. -/
def presentation_data (N : NonemptyOperatorNetwork X bot) :
    Σ n : Nat, FiniteOperatorNetwork.PresentationData X bot (Fin n) :=
  ⟨N.node_count, N.network.presentation_data⟩

def data_setoid : Setoid (NonemptyOperatorNetwork X bot) where
  r := fun N M => N.presentation_data = M.presentation_data
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Eliminate equality of numbered data into equality on one fixed node type. -/
theorem presentation_data_eq_elim
    {P : NonemptyOperatorNetwork X bot → NonemptyOperatorNetwork X bot → Prop}
    (step : ∀ (n : Nat) (N M : FiniteOperatorNetwork X bot (Fin n))
      (hN : N.U.Nonempty) (hM : M.U.Nonempty),
      N.presentation_data = M.presentation_data → P ⟨n, N, hN⟩ ⟨n, M, hM⟩)
    {N M : NonemptyOperatorNetwork X bot}
    (h : N.presentation_data = M.presentation_data) : P N M := by
  rcases N with ⟨n, N, hN⟩
  rcases M with ⟨m, M, hM⟩
  have hn : n = m := congrArg Sigma.fst h
  subst m
  have hd : N.presentation_data = M.presentation_data := by
    simpa only [presentation_data, Sigma.mk.inj_iff, heq_iff_eq, true_and] using h
  exact step n N M hN hM hd

theorem presentation_data_eq_extensional_operator
    {N M : NonemptyOperatorNetwork X bot}
    (h : N.presentation_data = M.presentation_data) :
    N.network.extensional_operator = M.network.extensional_operator := by
  apply presentation_data_eq_elim (P := fun N M =>
    N.network.extensional_operator = M.network.extensional_operator) ?_ h
  intro n N M hN hM hd
  exact FiniteOperatorNetwork.presentation_data_eq_extensional_operator hd

/--
OET anchor: h-b2fb8267687c8372
Encode an arbitrary finite-label representation without identifying its nodes.
-/
noncomputable def encode {V : Type} (N : FiniteOperatorNetwork X bot V)
    (hU : N.U.Nonempty) : NonemptyOperatorNetwork X bot :=
  { node_count := N.node_count
    network := N.standard_relabel
    source_nonempty := hU }

theorem encode_extensional_operator {V : Type} (N : FiniteOperatorNetwork X bot V)
    (hU : N.U.Nonempty) :
    (encode N hU).network.extensional_operator = N.extensional_operator :=
  N.standard_relabel_preserves.2.1

/--
OET anchor: h-4a79b2e15dc90f1a
**命题（非空网络外延非空）**
非空网络对象的外延算子不是全未定义算子。
-/
theorem extensional_operator_ne_bot (N : NonemptyOperatorNetwork X bot) :
    N.network.extensional_operator ≠ bot_operator := by
  intro h
  rcases N.source_nonempty with ⟨x, hx⟩
  have hxdom : x ∈ dom N.network.extensional_operator := by
    rw [N.network.dom_extensional_operator_eq]
    exact hx
  have hbot : N.network.extensional_operator.func x = bot := by
    have hfun := congrArg (fun op : Operator X bot => op.func x) h
    simpa [bot_operator] using hfun
  exact hxdom hbot

end NonemptyOperatorNetwork

/--
OET anchor: h-038163ee6fa2eddc
**定义（有限编号网络的对象集合）**
The nonempty component identifies precisely equal original numbered data.
Termination witnesses and choices outside node output images are discarded;
different numbered data remain distinct. The empty network is one constructor.
-/
inductive NetworkObject (X : Type) (bot : X) where
  | empty : NetworkObject X bot
  | present : Quotient (NonemptyOperatorNetwork.data_setoid (X := X) (bot := bot)) →
      NetworkObject X bot

namespace NetworkObject

/-- Enter a certified nonempty numbered representation into the object space. -/
def nonempty (N : NonemptyOperatorNetwork X bot) : NetworkObject X bot :=
  present (Quotient.mk _ N)

@[simp] theorem nonempty_ne_empty (N : NonemptyOperatorNetwork X bot) :
    nonempty N ≠ empty := by intro h; cases h

theorem nonempty_eq_iff {N M : NonemptyOperatorNetwork X bot} :
    nonempty N = nonempty M ↔ N.presentation_data = M.presentation_data := by
  constructor
  · intro h
    exact Quotient.exact (NetworkObject.present.inj h)
  · intro h
    exact congrArg present (Quotient.sound h)

/-- Lift a readout that depends only on the original numbered data. -/
def lift {P : Type} (empty_value : P) (f : NonemptyOperatorNetwork X bot → P)
    (compatible : ∀ N M, N.presentation_data = M.presentation_data → f N = f M) :
    NetworkObject X bot → P
  | empty => empty_value
  | present q => Quotient.lift f compatible q

@[simp] theorem lift_empty {P : Type} (empty_value : P)
    (f : NonemptyOperatorNetwork X bot → P)
    (compatible : ∀ N M, N.presentation_data = M.presentation_data → f N = f M) :
    lift empty_value f compatible empty = empty_value := rfl

@[simp] theorem lift_nonempty {P : Type} (empty_value : P)
    (f : NonemptyOperatorNetwork X bot → P)
    (compatible : ∀ N M, N.presentation_data = M.presentation_data → f N = f M)
    (N : NonemptyOperatorNetwork X bot) :
    lift empty_value f compatible (nonempty N) = f N := rfl

/--
OET anchor: h-4a79b2e15dc90f1a
**定义（算子读出映射）**
空网络读出为 `⊥_op`，非空网络读出为其外延算子。
-/
noncomputable def extensional_operator : NetworkObject X bot → Operator X bot :=
  lift bot_operator (fun N => N.network.extensional_operator)
    (fun _ _ h => NonemptyOperatorNetwork.presentation_data_eq_extensional_operator h)

@[simp] theorem extensional_operator_nonempty (N : NonemptyOperatorNetwork X bot) :
    (nonempty N).extensional_operator = N.network.extensional_operator := rfl

/--
OET anchor: h-4a79b2e15dc90f1a
**命题（空网络外延）**
唯一空网络的外延算子为全未定义算子。
-/
theorem extensional_operator_empty :
    extensional_operator (X := X) (bot := bot) empty = bot_operator :=
  rfl

/--
OET anchor: h-4a79b2e15dc90f1a
**命题（非空网络外延隔离）**
非空网络对象的外延算子不是 `⊥_op`。
-/
theorem extensional_operator_ne_bot_of_ne_empty {N : NetworkObject X bot}
    (hN : N ≠ empty) : N.extensional_operator ≠ bot_operator := by
  cases N with
  | empty =>
      exact (hN rfl).elim
  | present q =>
      induction q using Quotient.inductionOn with
      | h N => exact N.extensional_operator_ne_bot

/--
OET anchor: h-4a79b2e15dc90f1a
**定义（外延网络伪度量）**
网络对象上的伪度量由算子空间伪度量沿算子读出拉回。
-/
noncomputable def extensional_dist (d : X → X → ENNReal)
    (N M : NetworkObject X bot) : ENNReal :=
  op_dist d N.extensional_operator M.extensional_operator

/--
OET anchor: h-4a79b2e15dc90f1a
The componentwise pseudometric and absorbing-point axioms pulled back from
the operator space.  Nonabsorption is supplied separately when constructing
the full extended pseudometric structure. -/
theorem extensional_dist_axioms (d : X → X → ENNReal)
    (dist_self : ∀ x : X, d x x = 0)
    (symm : ∀ x y : X, d x y = d y x)
    (triangle : ∀ x y z : X, d x z ≤ d x y + d y z)
    (dist_bot : ∀ x ≠ bot, d x bot = ⊤) :
    (∀ N : NetworkObject X bot, extensional_dist d N N = 0) ∧
    (∀ N M : NetworkObject X bot,
      extensional_dist d N M = extensional_dist d M N) ∧
    (∀ N M K : NetworkObject X bot,
      extensional_dist d N K ≤ extensional_dist d N M + extensional_dist d M K) ∧
    (∀ N : NetworkObject X bot, N ≠ empty →
      extensional_dist d N empty = ⊤) := by
  rcases op_dist_is_pseudo_metric d dist_self symm triangle dist_bot with
    ⟨hself, hsymm, htri, hbot⟩
  constructor
  · intro N
    exact hself N.extensional_operator
  constructor
  · intro N M
    exact hsymm N.extensional_operator M.extensional_operator
  constructor
  · intro N M K
    exact htri N.extensional_operator M.extensional_operator K.extensional_operator
  · intro N hN
    exact hbot N.extensional_operator (N.extensional_operator_ne_bot_of_ne_empty hN)

/--
OET anchor: h-1fb1b80c5f14f459
**定义（外延等价关系）**
两个网络对象外延等价当且仅当外延算子相等。
-/
def ExtensionalEquivalent (N M : NetworkObject X bot) : Prop :=
  N.extensional_operator = M.extensional_operator

/--
OET anchor: h-1fb1b80c5f14f459
**命题（外延等价关系）**
外延等价是等价关系。
-/
theorem extensional_equivalent_equivalence :
    Equivalence (ExtensionalEquivalent (X := X) (bot := bot)) := by
  constructor
  · intro N
    rfl
  · intro N M h
    exact h.symm
  · intro N M K hNM hMK
    exact hNM.trans hMK

/--
OET anchor: h-1fb1b80c5f14f459
**定义（外延商）**
外延等价给出的商关系。
-/
def extensional_setoid : Setoid (NetworkObject X bot) where
  r := ExtensionalEquivalent
  iseqv := extensional_equivalent_equivalence

/--
OET anchor: h-1fb1b80c5f14f459
**定义（外延商算子读出）**
算子读出在外延商上良定义。
-/
noncomputable def quotient_extensional_operator :
    Quotient (extensional_setoid (X := X) (bot := bot)) → Operator X bot :=
  Quotient.lift extensional_operator (by
    intro N M h
    exact h)

/--
OET anchor: h-1fb1b80c5f14f459
**命题（非空算子定义域）**
非全未定义算子的定义域非空。
-/
theorem dom_nonempty_of_operator_ne_bot (φ : Operator X bot)
    (hφ : φ ≠ bot_operator) : (dom φ).Nonempty := by
  by_contra h
  apply hφ
  ext x
  by_cases hx : φ.func x = bot
  · exact hx
  · exact False.elim (h ⟨x, hx⟩)

/--
OET anchor: h-1fb1b80c5f14f459
**定义（单节点实现）**
任意非全未定义算子先由单节点有限算子网络实现。
-/
noncomputable def single_node_network (φ : Operator X bot)
    (hφ : φ ≠ bot_operator) : FiniteOperatorNetwork X bot Unit := by
  classical
  have hdom : (dom φ).Nonempty := dom_nonempty_of_operator_ne_bot φ hφ
  refine
    { U := dom φ
      bot_not_mem := ?_
      node_fintype := inferInstance
      node_op := fun _ => φ
      node_dom_nonempty := fun _ => hdom
      entry := fun _ => ()
      entry_mem := fun x => x.property
      choice := fun _ _ => OutputChoice.stop
      choice_next_mem := ?_
      depth_bound := 1
      path_of := fun _ => [()]
      path_terminal := ?_
      path_length_le_depth := ?_
      node_reachable := ?_ }
  · intro hbot_dom
    exact hbot_dom φ.preserves_bot
  · intro β γ y hy hchoice
    cases hchoice
  · intro x
    exact TerminalPathFrom.stop rfl
  · intro x
    simp
  · intro β
    rcases hdom with ⟨x, hx⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    cases β
    simp

/--
OET anchor: h-1fb1b80c5f14f459
**定义（单节点非空网络对象）**
任意非全未定义算子由单节点非空网络对象实现。
-/
noncomputable def single_node_nonempty_network (φ : Operator X bot)
    (hφ : φ ≠ bot_operator) : NonemptyOperatorNetwork X bot :=
  { node_count := (single_node_network φ hφ).node_count
    network := (single_node_network φ hφ).standard_relabel
    source_nonempty := by
      simpa [single_node_network] using dom_nonempty_of_operator_ne_bot φ hφ }

/--
OET anchor: h-1fb1b80c5f14f459
**命题（单节点实现外延）**
单节点网络的外延算子等于原算子。
-/
theorem single_node_network_extensional_operator_eq
    (φ : Operator X bot) (hφ : φ ≠ bot_operator) :
    (single_node_network φ hφ).extensional_operator = φ := by
  classical
  ext x
  by_cases hx : x ∈ dom φ
  · simp [single_node_network, FiniteOperatorNetwork.extensional_operator,
      FiniteOperatorNetwork.eval, chain_eval_nodes_core, hx]
  · have hfx : φ.func x = bot := by
      by_contra hne
      exact hx hne
    simp [single_node_network, FiniteOperatorNetwork.extensional_operator,
      FiniteOperatorNetwork.eval, chain_eval_nodes_core, hx, hfx]

/--
OET anchor: h-1fb1b80c5f14f459
**命题（单节点非空网络对象外延）**
单节点非空网络对象的外延算子等于原算子。
-/
theorem single_node_nonempty_network_extensional_operator_eq
    (φ : Operator X bot) (hφ : φ ≠ bot_operator) :
    (single_node_nonempty_network φ hφ).network.extensional_operator = φ := by
  exact (single_node_network φ hφ).standard_relabel_preserves.2.1.trans
    (single_node_network_extensional_operator_eq φ hφ)

/--
OET anchor: h-4a79b2e15dc90f1a
**命题 #h-4a79b2e15dc90f1a（有限算子网络的外延规范空间）**
Each component pseudometric on the base space pulls back along the extensional
readout to an extended pseudometric on finite network objects.  A one-node
restriction of the identity at a nonabsorbing point supplies the required
nonabsorbing network object.
-/
theorem extensional_pseudo_metric (d : X → X → ENNReal)
    (hd : ExtendedPseudoMetric X bot d) :
    ExtendedPseudoMetric (NetworkObject X bot) NetworkObject.empty
      (extensional_dist d) := by
  classical
  rcases hd.nonabsorbing with ⟨z, hz⟩
  let φ : Operator X bot :=
    restrict_operator (id_operator : Operator X bot) ({z} : Set X)
  have hφ : φ ≠ bot_operator := by
    intro h
    have hfun := congrArg (fun op : Operator X bot => op.func z) h
    apply hz
    simpa [φ, restrict_operator, id_operator, bot_operator] using hfun
  let N : NetworkObject X bot :=
    NetworkObject.nonempty (single_node_nonempty_network φ hφ)
  have hN : N ≠ NetworkObject.empty := by
    simp [N]
  rcases extensional_dist_axioms d hd.dist_self hd.symm hd.triangle hd.isolate_bot with
    ⟨hself, hsymm, htriangle, hisolate⟩
  exact
    { nonabsorbing := ⟨N, hN⟩
      dist_self := hself
      symm := hsymm
      triangle := htriangle
      isolate_bot := hisolate }

/--
OET anchor: h-038163ee6fa2eddc
The small coded object space can actually be used again as a network base.
-/
theorem iterated_extensional_pseudo_metric (d : X → X → ENNReal)
    (hd : ExtendedPseudoMetric X bot d) :
    ExtendedPseudoMetric
      (NetworkObject (NetworkObject X bot) NetworkObject.empty) NetworkObject.empty
      (extensional_dist (extensional_dist d)) :=
  extensional_pseudo_metric (extensional_dist d) (extensional_pseudo_metric d hd)

/--
OET anchor: h-1fb1b80c5f14f459
**命题（算子读出满射）**
每个算子都是某个网络对象的算子读出。
-/
theorem extensional_operator_surjective :
    Function.Surjective (extensional_operator (X := X) (bot := bot)) := by
  intro φ
  by_cases hφ : φ = bot_operator
  · refine ⟨empty, ?_⟩
    simp [extensional_operator, hφ]
  · refine ⟨nonempty (single_node_nonempty_network φ hφ), ?_⟩
    simpa [extensional_operator] using
      single_node_nonempty_network_extensional_operator_eq φ hφ

/--
OET anchor: h-1fb1b80c5f14f459
**命题 #h-1fb1b80c5f14f459（外延商与算子空间）**
算子读出诱导从外延商到算子空间的双射。
-/
theorem quotient_extensional_operator_bijective :
    Function.Bijective
      (quotient_extensional_operator (X := X) (bot := bot)) := by
  constructor
  · intro Q R hQR
    refine Quotient.inductionOn₂ Q R ?_ hQR
    intro N M hNM
    exact Quotient.sound hNM
  · intro φ
    rcases extensional_operator_surjective (X := X) (bot := bot) φ with
      ⟨N, hN⟩
    exact ⟨Quotient.mk _ N, hN⟩

/--
OET anchor: h-1fb1b80c5f14f459
**命题 #h-1fb1b80c5f14f459（商读出下的距离等式）**
外延网络伪度量等于商读出后在算子空间中的伪度量。
-/
theorem extensional_dist_eq_quotient_operator_dist
    (d : X → X → ENNReal) (N M : NetworkObject X bot) :
    extensional_dist d N M =
      op_dist d
        (quotient_extensional_operator
          (Quotient.mk (extensional_setoid (X := X) (bot := bot)) N))
        (quotient_extensional_operator
          (Quotient.mk (extensional_setoid (X := X) (bot := bot)) M)) := by
  rfl

end NetworkObject

end formal_oet.vol_01.ch_05_operator_networks
