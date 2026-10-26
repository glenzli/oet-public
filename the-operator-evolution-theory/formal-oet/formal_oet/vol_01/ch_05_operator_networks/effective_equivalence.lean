import formal_oet.vol_01.ch_05_operator_networks.path_matrix
import formal_oet.vol_01.ch_05_operator_networks.network_readouts

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus

variable {X V W : Type} {bot : X}

namespace FiniteOperatorNetwork

variable (N : FiniteOperatorNetwork X bot V)

/--
OET anchor: h-374f884cd4d69e88
**§ #h-374f884cd4d69e88（路径分段算子表达）**
A network-indexed accessor view records each reachable path domain and chain.
The common untagged value space in `network_expression_readouts` discards these
indices and retains only the input pieces and complete composites.
-/
structure PathSegmentExpression where
  domain : N.ReachablePath → Set X
  chain : N.ReachablePath → Operator X bot

/--
OET anchor: h-374f884cd4d69e88
**§ #h-374f884cd4d69e88（路径分段算子表达）**
The concrete path segment expression induced by a network.
-/
noncomputable def path_segment_expression : PathSegmentExpression N where
  domain := fun p => N.path_domain p.nodes
  chain := fun p => N.path_chain p.nodes

/--
OET anchor: h-56edb9917107efcd
**命题 #h-56edb9917107efcd（路径分解与可达路径有限性，路径分段表达）**
On every path segment, the network extensional operator is locally equivalent
to the path-chain operator selected by the segment expression.
-/
theorem path_segment_expression_local_equivalent
    (p : N.ReachablePath) :
    LocalEquivalent N.extensional_operator
      ((N.path_segment_expression).chain p)
      ((N.path_segment_expression).domain p) := by
  simpa [path_segment_expression] using
    N.local_equivalent_extensional_path_chain p

/--
OET anchor: h-adb38f8458662a70
**§ #h-adb38f8458662a70（节点实际输入域）**
The actual input domain of a node consists of current inputs obtained
before occurrences of that node along reachable paths, restricted to the
node's local operator domain.
-/
def node_actual_input_domain (β : V) : Set X :=
  {y | ∃ (x : {x : X // x ∈ N.U}) (pref suffix : List V),
    N.path_of x = pref ++ β :: suffix ∧
      y = N.chain_eval_nodes pref x.val ∧ y ∈ N.node_dom β}

/--
OET anchor: h-adb38f8458662a70
**§ #h-adb38f8458662a70（节点实际输入域）**
The actual input domain is a subdomain of the corresponding local
operator domain.
-/
theorem node_actual_input_domain_subset_node_dom (β : V) :
    N.node_actual_input_domain β ⊆ N.node_dom β := by
  intro y hy
  rcases hy with ⟨_x, _prefix, _suffix, _hpath, _hy, hydom⟩
  exact hydom

/--
OET anchor: h-adb38f8458662a70
**§ #h-adb38f8458662a70（有效约化网络）**
The local operator used by the effective reduction at a node is the original
local operator restricted to the actual input domain.
-/
noncomputable def effective_node_operator (β : V) : Operator X bot :=
  restrict_operator (N.node_op β) (N.node_actual_input_domain β)

/--
OET anchor: h-adb38f8458662a70
**§ #h-adb38f8458662a70（有效约化网络）**
The domain of an effective node operator is exactly the actual input domain.
-/
theorem dom_effective_node_operator_eq (β : V) :
    dom (N.effective_node_operator β) =
      N.node_actual_input_domain β := by
  exact dom_restrict_operator_eq (N.node_op β)
    (N.node_actual_input_domain β)
    (N.node_actual_input_domain_subset_node_dom β)

/--
OET anchor: h-e84d11a2bc70b939
**命题 #h-e84d11a2bc70b939（有效约化保持外延，局域算子逐点一致）**
On the actual input domain of a node, the effective local operator agrees
pointwise with the original local operator.
-/
theorem effective_node_operator_apply_eq (β : V) :
    ∀ x ∈ N.node_actual_input_domain β,
      (N.effective_node_operator β).func x = (N.node_op β).func x := by
  intro x hx
  exact restrict_operator_apply_of_mem (N.node_op β)
    (N.node_actual_input_domain β) hx

/--
OET anchor: h-e84d11a2bc70b939
**命题 #h-e84d11a2bc70b939（有效约化保持外延，局域算子局部等价）**
The effective local operator and the original local operator are locally
equivalent on the actual input domain.
-/
theorem effective_node_operator_local_equivalent (β : V) :
    LocalEquivalent (N.effective_node_operator β) (N.node_op β)
      (N.node_actual_input_domain β) := by
  intro x hx
  exact N.effective_node_operator_apply_eq β x hx

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络）**
This network-indexed accessor view records each path domain and ordered
node-label/operator factors. The common value space is implemented separately
in `network_expression_readouts`; only its expression data survive there.
The chain and label list below are derived from one factor list.
-/
structure TaggedPathSegmentExpression where
  domain : N.ReachablePath → Set X
  factors : N.ReachablePath → List (V × Operator X bot)

/-- The ordered node labels derived from a tagged path segment expression. -/
def TaggedPathSegmentExpression.tags
    {N : FiniteOperatorNetwork X bot V}
    (E : TaggedPathSegmentExpression N) (p : N.ReachablePath) : List V :=
  (E.factors p).map Prod.fst

/-- The ordered local operators derived from a tagged path segment expression. -/
def TaggedPathSegmentExpression.operators
    {N : FiniteOperatorNetwork X bot V}
    (E : TaggedPathSegmentExpression N) (p : N.ReachablePath) :
    List (Operator X bot) :=
  (E.factors p).map Prod.snd

/-- The path-chain operator obtained by composing the ordered factors. -/
noncomputable def TaggedPathSegmentExpression.chain
    {N : FiniteOperatorNetwork X bot V}
    (E : TaggedPathSegmentExpression N) (p : N.ReachablePath) : Operator X bot :=
  OperatorChain (E.operators p).reverse

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络）**
The concrete tagged segment expression induced by a network.
-/
noncomputable def tagged_path_segment_expression :
    TaggedPathSegmentExpression N where
  domain := fun p => N.path_domain p.nodes
  factors := fun p => p.nodes.map fun β => (β, N.node_op β)

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，路径域读出）**
The tagged segment expression reads out the original path domain on every
reachable path.
-/
theorem tagged_path_segment_expression_domain_eq (p : N.ReachablePath) :
    N.tagged_path_segment_expression.domain p = N.path_domain p.nodes := rfl

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，有序因子读出）**
The tagged segment expression reads out the ordered node-label/operator
factor list on every reachable path.
-/
theorem tagged_path_segment_expression_factors_eq (p : N.ReachablePath) :
    N.tagged_path_segment_expression.factors p =
      p.nodes.map fun β => (β, N.node_op β) := rfl

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，路径链读出）**
The tagged segment expression reads out the original path-chain operator on
every reachable path.
-/
theorem tagged_path_segment_expression_chain_eq (p : N.ReachablePath) :
    N.tagged_path_segment_expression.chain p = N.path_chain p.nodes := by
  simp [tagged_path_segment_expression, TaggedPathSegmentExpression.chain,
    TaggedPathSegmentExpression.operators, path_chain, Function.comp_def]

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，节点标签读出）**
The tagged segment expression reads out the ordered node labels on every
reachable path.
-/
theorem tagged_path_segment_expression_tags_eq (p : N.ReachablePath) :
    N.tagged_path_segment_expression.tags p = p.nodes := by
  simp [tagged_path_segment_expression, TaggedPathSegmentExpression.tags,
    Function.comp_def]

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，局域算子列读出）**
Forgetting the labels leaves precisely the ordered local-operator factors.
-/
theorem tagged_path_segment_expression_operators_eq (p : N.ReachablePath) :
    N.tagged_path_segment_expression.operators p = p.nodes.map N.node_op := by
  simp [tagged_path_segment_expression, TaggedPathSegmentExpression.operators,
    Function.comp_def]

/--
The actual input set of the factor at position `n` of a reachable path is the
image of that path segment under the preceding prefix.
-/
def path_factor_input_domain (p : N.ReachablePath) (n : Fin p.nodes.length) :
    Set X :=
  N.chain_eval_nodes (p.nodes.take n.val) '' N.path_domain p.nodes

/--
The node-input set reconstructed solely from path segments, ordered labels,
and prefix evaluation.
-/
def tagged_recovered_node_input_domain (β : V) : Set X :=
  {y | ∃ (p : N.ReachablePath) (n : Fin p.nodes.length),
    p.nodes.get n = β ∧ y ∈ N.path_factor_input_domain p n}

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，节点实际输入域）**
The tagged path-position formula recovers exactly the actual input domain of
each node.
-/
theorem tagged_recovered_node_input_domain_eq (β : V) :
    N.tagged_recovered_node_input_domain β = N.node_actual_input_domain β := by
  ext y
  constructor
  · rintro ⟨p, n, hlabel, x, hxPath, rfl⟩
    rcases hxPath with ⟨hxU, hpath⟩
    let xp : {x : X // x ∈ N.U} := ⟨x, hxU⟩
    have hdecomp :
        N.path_of xp =
          p.nodes.take n.val ++ β :: p.nodes.drop (n.val + 1) := by
      calc
        N.path_of xp = p.nodes := hpath
        _ = p.nodes.take n.val ++ p.nodes.drop n.val :=
          (List.take_append_drop n.val p.nodes).symm
        _ = p.nodes.take n.val ++
            p.nodes.get n :: p.nodes.drop (n.val + 1) := by
              rw [List.cons_get_drop_succ]
        _ = p.nodes.take n.val ++ β :: p.nodes.drop (n.val + 1) := by
              rw [hlabel]
    have hmem0 := terminal_path_prefix_input_mem N.choice_next_mem
      (N.entry_mem xp) (N.path_terminal xp)
      (⟨n.val, by simp [xp, hpath]⟩ :
        Fin (N.path_of xp).length)
    have hgeteq :
        (N.path_of xp).get
            (⟨n.val, by simp [xp, hpath]⟩ :
              Fin (N.path_of xp).length) = β := by
      simpa [xp, hpath] using hlabel
    rw [hgeteq] at hmem0
    have hmem :
        N.chain_eval_nodes (p.nodes.take n.val) x ∈ N.node_dom β := by
      simpa [FiniteOperatorNetwork.chain_eval_nodes, xp, hpath,
        FiniteOperatorNetwork.node_dom] using hmem0
    exact ⟨xp, p.nodes.take n.val, p.nodes.drop (n.val + 1),
      hdecomp, rfl, hmem⟩
  · rintro ⟨xp, pref, suffix, hpath, rfl, _hdom⟩
    let p : N.ReachablePath :=
      ⟨N.path_of xp, ⟨xp.val, xp.property, rfl⟩⟩
    have hnlt : pref.length < p.nodes.length := by
      simp [p, hpath]
    let n : Fin p.nodes.length := ⟨pref.length, hnlt⟩
    have hlabel : p.nodes.get n = β := by
      simp [p, n, hpath]
    refine ⟨p, n, hlabel, xp.val, ?_, ?_⟩
    · exact ⟨xp.property, rfl⟩
    · simp [p, n, hpath]

/-- The entry block reconstructed from path domains and first node labels. -/
def tagged_recovered_entry_domain (β : V) : Set X :=
  {x | ∃ p : N.ReachablePath,
    x ∈ N.path_domain p.nodes ∧ p.nodes.head? = some β}

/-- The first node of a terminal path is its prescribed starting node. -/
theorem terminal_path_head_eq {node_op : V → Operator X bot}
    {choice : V → X → OutputChoice V} {β : V} {y : X} {p : List V}
    (h : TerminalPathFrom node_op choice β y p) : p.head? = some β := by
  cases h <;> rfl

/--
On a terminal path, a `next γ` decision at an occurring prefix forces the next
stored label to be `γ`.
-/
theorem terminal_path_suffix_of_next_at_prefix
    {node_op : V → Operator X bot} {choice : V → X → OutputChoice V}
    {start β γ : V} {x : X} {path pref suffix : List V}
    (hpath : TerminalPathFrom node_op choice start x path)
    (hdecomp : path = pref ++ β :: suffix)
    (hnext :
      choice β
        ((node_op β).func (chain_eval_nodes_core node_op pref x)) =
          OutputChoice.next γ) :
    ∃ tail : List V, suffix = γ :: tail := by
  induction hpath generalizing pref β suffix γ with
  | @stop start x hstop =>
      cases pref with
      | nil =>
          have hparts := List.cons.inj hdecomp
          have hstart : start = β := hparts.1
          have hsuffix : suffix = [] := hparts.2.symm
          subst β
          subst suffix
          have hcontra : OutputChoice.stop = OutputChoice.next γ :=
            hstop.symm.trans hnext
          cases hcontra
      | cons a pref =>
          have hlen := congrArg List.length hdecomp
          simp at hlen
  | @next start target x rest hfirst hrest ih =>
      cases pref with
      | nil =>
          have hparts := List.cons.inj hdecomp
          have hstart : start = β := hparts.1
          have hsuffix : rest = suffix := hparts.2
          subst β
          subst suffix
          have htarget : target = γ :=
            OutputChoice.next.inj (hfirst.symm.trans hnext)
          subst γ
          cases hrest with
          | stop _ => exact ⟨[], rfl⟩
          | next _ _ => exact ⟨_, rfl⟩
      | cons a pref =>
          have hparts := List.cons.inj hdecomp
          have hstart : start = a := hparts.1
          have htail : rest = pref ++ β :: suffix := hparts.2
          subst a
          exact ih htail (by
            simpa [chain_eval_nodes_core] using hnext)

/-- Two adjacent labels on a terminal path determine the corresponding
successor decision at the preceding prefix. -/
theorem terminal_path_choice_at_adjacent_prefix
    {node_op : V → Operator X bot} {choice : V → X → OutputChoice V}
    {start β γ : V} {x : X} {path pref suffix : List V}
    (hpath : TerminalPathFrom node_op choice start x path)
    (hdecomp : path = pref ++ β :: γ :: suffix) :
    choice β ((node_op β).func (chain_eval_nodes_core node_op pref x)) =
      OutputChoice.next γ := by
  induction hpath generalizing pref β γ suffix with
  | @stop start x hstop =>
      have hlen := congrArg List.length hdecomp
      simp at hlen
      omega
  | @next start target x rest hfirst hrest ih =>
      cases pref with
      | nil =>
          simp only [List.nil_append] at hdecomp
          have hparts := List.cons.inj hdecomp
          have hstart : start = β := hparts.1
          have hrest_eq : rest = γ :: suffix := hparts.2
          subst β
          have hhead := terminal_path_head_eq hrest
          rw [hrest_eq] at hhead
          have htarget : target = γ := (Option.some.inj hhead).symm
          subst target
          simpa [chain_eval_nodes_core] using hfirst
      | cons a pref =>
          simp only [List.cons_append] at hdecomp
          have hparts := List.cons.inj hdecomp
          have hstart : start = a := hparts.1
          have htail : rest = pref ++ β :: γ :: suffix := hparts.2
          subst a
          simpa [chain_eval_nodes_core] using ih htail

/-- Prefix evaluation respects concatenation of node lists. -/
theorem chain_eval_nodes_core_append (node_op : V → Operator X bot)
    (left right : List V) (x : X) :
    chain_eval_nodes_core node_op (left ++ right) x =
      chain_eval_nodes_core node_op right
        (chain_eval_nodes_core node_op left x) := by
  induction left generalizing x with
  | nil => rfl
  | cons β rest ih =>
      simp only [List.cons_append, chain_eval_nodes_core]
      exact ih ((node_op β).func x)

/-- Every reachable node has a nonempty actual input domain. -/
theorem node_actual_input_domain_nonempty (β : V) :
    (N.node_actual_input_domain β).Nonempty := by
  rcases N.node_reachable β with ⟨x, hβ⟩
  let p : N.ReachablePath :=
    ⟨N.path_of x, ⟨x.val, x.property, rfl⟩⟩
  obtain ⟨n, hn⟩ := List.get_of_mem hβ
  let w : N.PathPosition := ⟨p, n⟩
  rcases N.path_position_input_domain_nonempty w with ⟨y, hy⟩
  refine ⟨y, ?_⟩
  rw [← N.tagged_recovered_node_input_domain_eq β]
  refine ⟨p, n, ?_, ?_⟩
  · simpa [p] using hn
  · simpa [path_factor_input_domain, path_position_input_domain, w] using hy

/-- Every source input belongs to the actual domain of its entry node. -/
theorem entry_mem_node_actual_input_domain
    (x : {x : X // x ∈ N.U}) :
    x.val ∈ N.node_actual_input_domain (N.entry x) := by
  let p : N.ReachablePath :=
    ⟨N.path_of x, ⟨x.val, x.property, rfl⟩⟩
  have hlen : 0 < p.nodes.length := by
    simpa [p, Nat.pos_iff_ne_zero] using N.path_nonempty x
  let n : Fin p.nodes.length := ⟨0, hlen⟩
  have hlabel : p.nodes.get n = N.entry x := by
    have hne : p.nodes ≠ [] := List.ne_nil_of_length_pos hlen
    have hhead := terminal_path_head_eq (N.path_terminal x)
    have hhead_value : p.nodes.head hne = N.entry x := by
      apply Option.some.inj
      calc
        some (p.nodes.head hne) = p.nodes.head? :=
          (List.head?_eq_some_head hne).symm
        _ = some (N.entry x) := by simpa [p] using hhead
    have hget : p.nodes.head hne = p.nodes.get ⟨0, hlen⟩ := by
      simpa [List.get_eq_getElem] using List.head_eq_getElem_zero hne
    exact hget.symm.trans hhead_value
  rw [← N.tagged_recovered_node_input_domain_eq (N.entry x)]
  refine ⟨p, n, hlabel, x.val, ?_, ?_⟩
  · exact ⟨x.property, rfl⟩
  · simp [p, n,
      FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core]

/-- A realised successor transition lands in the successor's actual domain. -/
theorem next_output_mem_node_actual_input_domain
    {β γ : V} {y : X}
    (hy : y ∈ N.node_actual_input_domain β)
    (hnext : N.choice β ((N.node_op β).func y) = OutputChoice.next γ) :
    (N.node_op β).func y ∈ N.node_actual_input_domain γ := by
  rcases hy with ⟨x, pref, suffix, hpath, hy, hydom⟩
  have hnext' :
      N.choice β
          ((N.node_op β).func (N.chain_eval_nodes pref x.val)) =
        OutputChoice.next γ := by
    simpa [hy] using hnext
  rcases terminal_path_suffix_of_next_at_prefix
      (N.path_terminal x) hpath hnext' with ⟨tail, hsuffix⟩
  refine ⟨x, pref ++ [β], tail, ?_, ?_, ?_⟩
  · rw [hsuffix] at hpath
    simpa [List.append_assoc] using hpath
  · rw [FiniteOperatorNetwork.chain_eval_nodes,
      chain_eval_nodes_core_append]
    simp [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core, hy]
  · exact N.choice_next_mem hydom hnext

/-- Restricting every factor to its actual domain preserves each terminal path. -/
theorem terminal_path_effective
    {β : V} {y : X} {path : List V}
    (hy : y ∈ N.node_actual_input_domain β)
    (hpath : TerminalPathFrom N.node_op N.choice β y path) :
    TerminalPathFrom N.effective_node_operator N.choice β y path := by
  induction hpath with
  | @stop β y hstop =>
      have heq := N.effective_node_operator_apply_eq β y hy
      apply TerminalPathFrom.stop
      simpa [heq] using hstop
  | @next β γ y rest hnext hrest ih =>
      have heq := N.effective_node_operator_apply_eq β y hy
      have hy' := N.next_output_mem_node_actual_input_domain hy hnext
      apply TerminalPathFrom.next
      · simpa [heq] using hnext
      · simpa [heq] using ih hy'

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，入口输入片）**
The tagged first-label formula recovers exactly the entry input block.
-/
theorem tagged_recovered_entry_domain_eq (β : V) :
    N.tagged_recovered_entry_domain β = N.entry_domain β := by
  ext x
  constructor
  · rintro ⟨p, ⟨hxU, hpath⟩, hhead⟩
    have hstart := terminal_path_head_eq (N.path_terminal ⟨x, hxU⟩)
    rw [hpath] at hstart
    exact ⟨hxU, Option.some.inj (hstart.symm.trans hhead)⟩
  · rintro ⟨hxU, hentry⟩
    let xp : {x : X // x ∈ N.U} := ⟨x, hxU⟩
    let p : N.ReachablePath :=
      ⟨N.path_of xp, ⟨x, hxU, rfl⟩⟩
    refine ⟨p, ⟨hxU, rfl⟩, ?_⟩
    have hstart := terminal_path_head_eq (N.path_terminal xp)
    simpa [p, xp, hentry] using hstart

/--
The effective edge domain consists exactly of outputs occurring immediately
after a `β`-factor and immediately before a `γ`-factor on an actual path.
-/
def effective_edge_domain (β γ : V) : Set X :=
  {z | ∃ (x : {x : X // x ∈ N.U}) (pref suffix : List V),
    N.path_of x = pref ++ β :: γ :: suffix ∧
      z = N.chain_eval_nodes (pref ++ [β]) x.val}

/--
The edge-domain formula read from path segments and adjacent tagged factors.
-/
def tagged_recovered_edge_domain (β γ : V) : Set X :=
  {z | ∃ (p : N.ReachablePath) (n : Nat)
      (hn : n + 1 < p.nodes.length),
    p.nodes.get ⟨n, Nat.lt_of_succ_lt hn⟩ = β ∧
      p.nodes.get ⟨n + 1, hn⟩ = γ ∧
      z ∈ N.chain_eval_nodes (p.nodes.take (n + 1)) ''
        N.path_domain p.nodes}

/-- A list splits at any two adjacent valid positions. -/
theorem list_eq_take_two_get_drop {α : Type} (l : List α) (n : Nat)
    (hn : n + 1 < l.length) :
    l = l.take n ++
      l.get ⟨n, Nat.lt_of_succ_lt hn⟩ ::
        l.get ⟨n + 1, hn⟩ :: l.drop (n + 2) := by
  calc
    l = l.take n ++ l.drop n := (List.take_append_drop n l).symm
    _ = l.take n ++
        l.get ⟨n, Nat.lt_of_succ_lt hn⟩ :: l.drop (n + 1) := by
      rw [← List.cons_get_drop_succ
        (n := (⟨n, Nat.lt_of_succ_lt hn⟩ : Fin l.length))]
    _ = l.take n ++
        l.get ⟨n, Nat.lt_of_succ_lt hn⟩ ::
          l.get ⟨n + 1, hn⟩ :: l.drop (n + 2) := by
      rw [← List.cons_get_drop_succ
        (n := (⟨n + 1, hn⟩ : Fin l.length))]

/-- The prefix through a valid position is `take n` followed by that entry. -/
theorem take_succ_eq_take_append_get {α : Type} (l : List α) (n : Nat)
    (hn : n < l.length) :
    l.take (n + 1) = l.take n ++ [l.get ⟨n, hn⟩] := by
  rw [← List.concat_eq_append]
  exact (List.take_concat_get (l := l) (i := n) hn).symm

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，有效边域）**
The adjacent-factor formula recovers exactly each effective edge domain.
-/
theorem tagged_recovered_edge_domain_eq (β γ : V) :
    N.tagged_recovered_edge_domain β γ = N.effective_edge_domain β γ := by
  ext z
  constructor
  · rintro ⟨p, n, hn, hβ, hγ, x, ⟨hxU, hpath⟩, rfl⟩
    let xp : {x : X // x ∈ N.U} := ⟨x, hxU⟩
    have hsplit := list_eq_take_two_get_drop p.nodes n hn
    rw [hβ, hγ] at hsplit
    have htake := take_succ_eq_take_append_get p.nodes n
      (Nat.lt_of_succ_lt hn)
    rw [hβ] at htake
    refine ⟨xp, p.nodes.take n, p.nodes.drop (n + 2), ?_, ?_⟩
    · exact hpath.trans hsplit
    · rw [← htake]
  · rintro ⟨xp, pref, suffix, hpath, rfl⟩
    let p : N.ReachablePath :=
      ⟨N.path_of xp, ⟨xp.val, xp.property, rfl⟩⟩
    have hn : pref.length + 1 < p.nodes.length := by
      simp [p, hpath]
    refine ⟨p, pref.length, hn, ?_, ?_, xp.val, ?_, ?_⟩
    · simp [p, hpath]
    · simp [p, hpath]
    · exact ⟨xp.property, rfl⟩
    · have htake := take_succ_eq_take_append_get p.nodes pref.length
        (Nat.lt_of_succ_lt hn)
      have hlabel :
          p.nodes.get ⟨pref.length, Nat.lt_of_succ_lt hn⟩ = β := by
        simp [p, hpath]
      have hpref : p.nodes.take pref.length = pref := by
        simp [p, hpath]
      rw [hlabel] at htake
      rw [hpref] at htake
      exact congrArg (fun nodes => N.chain_eval_nodes nodes xp.val) htake

/--
The effective terminal domain consists of outputs of actual paths whose last
factor has label `β`.
-/
def effective_terminal_domain (β : V) : Set X :=
  {z | ∃ (x : {x : X // x ∈ N.U}) (pref : List V),
    N.path_of x = pref ++ [β] ∧
      z = N.chain_eval_nodes (pref ++ [β]) x.val}

/-- The terminal-domain formula read from terminal tagged factors. -/
def tagged_recovered_terminal_domain (β : V) : Set X :=
  {z | ∃ (p : N.ReachablePath) (pref : List V),
    p.nodes = pref ++ [β] ∧
      z ∈ N.chain_eval_nodes p.nodes '' N.path_domain p.nodes}

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，有效终止域）**
The terminal-factor formula recovers exactly each effective terminal domain.
-/
theorem tagged_recovered_terminal_domain_eq (β : V) :
    N.tagged_recovered_terminal_domain β = N.effective_terminal_domain β := by
  ext z
  constructor
  · rintro ⟨p, pref, hnodes, x, ⟨hxU, hpath⟩, rfl⟩
    let xp : {x : X // x ∈ N.U} := ⟨x, hxU⟩
    refine ⟨xp, pref, hpath.trans hnodes, ?_⟩
    rw [hnodes]
  · rintro ⟨xp, pref, hpath, rfl⟩
    let p : N.ReachablePath :=
      ⟨N.path_of xp, ⟨xp.val, xp.property, rfl⟩⟩
    refine ⟨p, pref, ?_, xp.val, ?_, ?_⟩
    · simpa [p] using hpath
    · exact ⟨xp.property, rfl⟩
    · simp [p, hpath]

/-- Prefix evaluation with an arbitrary node-operator family. -/
theorem chain_eval_nodes_core_take_succ (node_op : V → Operator X bot)
    {nodes : List V} {n : Nat} (hn : n < nodes.length) (x : X) :
    chain_eval_nodes_core node_op (nodes.take (n + 1)) x =
      (node_op (nodes.get ⟨n, hn⟩)).func
        (chain_eval_nodes_core node_op (nodes.take n) x) := by
  induction nodes generalizing n x with
  | nil =>
      cases hn
  | cons β rest ih =>
      cases n with
      | zero =>
          simp [chain_eval_nodes_core]
      | succ n =>
          have hnrest : n < rest.length := by
            simpa using Nat.succ_lt_succ_iff.mp hn
          simpa [chain_eval_nodes_core] using
            ih hnrest ((node_op β).func x)

/-- Evaluation along a stored path using the effectively restricted factors. -/
noncomputable def effective_chain_eval_nodes (nodes : List V) (x : X) : X :=
  chain_eval_nodes_core N.effective_node_operator nodes x

/--
Every effective prefix evaluates exactly as the corresponding original prefix
on its path segment.
-/
theorem effective_prefix_eval_eq (p : N.ReachablePath) {x : X}
    (hx : x ∈ N.path_domain p.nodes) :
    ∀ n : Nat, n ≤ p.nodes.length →
      N.effective_chain_eval_nodes (p.nodes.take n) x =
        N.chain_eval_nodes (p.nodes.take n) x := by
  intro n hn
  induction n with
  | zero =>
      simp [effective_chain_eval_nodes, FiniteOperatorNetwork.chain_eval_nodes,
        chain_eval_nodes_core]
  | succ n ih =>
      have hnlt : n < p.nodes.length := by omega
      have heffstep := chain_eval_nodes_core_take_succ
        N.effective_node_operator hnlt x
      have hstep := N.chain_eval_nodes_take_succ hnlt x
      have hprefix := ih (Nat.le_of_lt hnlt)
      have hy_recovered :
          N.chain_eval_nodes (p.nodes.take n) x ∈
            N.tagged_recovered_node_input_domain
              (p.nodes.get ⟨n, hnlt⟩) :=
        ⟨p, ⟨n, hnlt⟩, rfl, x, hx, rfl⟩
      have hy_actual :
          N.chain_eval_nodes (p.nodes.take n) x ∈
            N.node_actual_input_domain (p.nodes.get ⟨n, hnlt⟩) := by
        rw [← N.tagged_recovered_node_input_domain_eq
          (p.nodes.get ⟨n, hnlt⟩)]
        exact hy_recovered
      have hfactor := N.effective_node_operator_apply_eq
        (p.nodes.get ⟨n, hnlt⟩)
        (N.chain_eval_nodes (p.nodes.take n) x) hy_actual
      calc
        N.effective_chain_eval_nodes (p.nodes.take (n + 1)) x =
            (N.effective_node_operator (p.nodes.get ⟨n, hnlt⟩)).func
              (N.effective_chain_eval_nodes (p.nodes.take n) x) := by
          simpa [effective_chain_eval_nodes] using heffstep
        _ = (N.effective_node_operator (p.nodes.get ⟨n, hnlt⟩)).func
              (N.chain_eval_nodes (p.nodes.take n) x) := by
          rw [hprefix]
        _ = (N.node_op (p.nodes.get ⟨n, hnlt⟩)).func
              (N.chain_eval_nodes (p.nodes.take n) x) := hfactor
        _ = N.chain_eval_nodes (p.nodes.take (n + 1)) x := hstep.symm

/-- The source-domain evaluation obtained from the effective node operators. -/
noncomputable def effective_eval (x : {x : X // x ∈ N.U}) : X :=
  N.effective_chain_eval_nodes (N.path_of x) x.val

/-- The effective evaluation completed by `bot` outside the source domain. -/
noncomputable def effective_extensional_operator : Operator X bot := by
  classical
  refine ⟨fun x => if hx : x ∈ N.U then N.effective_eval ⟨x, hx⟩ else bot, ?_⟩
  simp [N.bot_not_mem]

/-- Effective and original path evaluation agree on every source input. -/
theorem effective_eval_eq (x : {x : X // x ∈ N.U}) :
    N.effective_eval x = N.eval x := by
  let p : N.ReachablePath :=
    ⟨N.path_of x, ⟨x.val, x.property, rfl⟩⟩
  have h := N.effective_prefix_eval_eq p
    (x := x.val) ⟨x.property, rfl⟩ p.nodes.length (by rfl)
  rw [List.take_length] at h
  simpa [effective_eval, effective_chain_eval_nodes,
    FiniteOperatorNetwork.eval, FiniteOperatorNetwork.chain_eval_nodes, p] using h

/--
OET anchor: h-e84d11a2bc70b939
**命题 #h-e84d11a2bc70b939（有效约化保持外延）**
The extensional evaluation assembled from the effective node restrictions
agrees with the original network operator on the complete source domain.
-/
theorem effective_extensional_operator_local_equivalent :
    LocalEquivalent N.effective_extensional_operator N.extensional_operator N.U := by
  intro x hx
  simp [effective_extensional_operator,
    FiniteOperatorNetwork.extensional_operator, hx, N.effective_eval_eq ⟨x, hx⟩]

/--
OET anchor: h-adb38f8458662a70
**§ #h-adb38f8458662a70（有效约化网络）**
Restricting every local factor to its actual input domain produces a finite
operator network with the original source domain, routing rule, and stored
terminal paths.
-/
noncomputable def effective_reduction : FiniteOperatorNetwork X bot V := by
  classical
  refine
    { U := N.U
      bot_not_mem := N.bot_not_mem
      node_fintype := N.node_fintype
      node_op := N.effective_node_operator
      node_dom_nonempty := ?_
      entry := N.entry
      entry_mem := ?_
      choice := N.choice
      choice_next_mem := ?_
      depth_bound := N.depth_bound
      path_of := N.path_of
      path_terminal := ?_
      path_length_le_depth := N.path_length_le_depth
      node_reachable := N.node_reachable }
  · intro β
    rw [N.dom_effective_node_operator_eq β]
    exact N.node_actual_input_domain_nonempty β
  · intro x
    rw [N.dom_effective_node_operator_eq (N.entry x)]
    exact N.entry_mem_node_actual_input_domain x
  · intro β γ y hy hnext
    have hy_actual : y ∈ N.node_actual_input_domain β := by
      simpa [N.dom_effective_node_operator_eq β] using hy
    have heq := N.effective_node_operator_apply_eq β y hy_actual
    have hnext_original :
        N.choice β ((N.node_op β).func y) = OutputChoice.next γ := by
      simpa [heq] using hnext
    rw [N.dom_effective_node_operator_eq γ]
    simpa [heq] using
      N.next_output_mem_node_actual_input_domain hy_actual hnext_original
  · intro x
    exact N.terminal_path_effective
      (N.entry_mem_node_actual_input_domain x) (N.path_terminal x)

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，入口输入片）**
有效约化保持由标记路径首因子恢复出的入口输入分划。
-/
theorem effective_reduction_entry_domain_eq (β : V) :
    N.effective_reduction.entry_domain β = N.entry_domain β := by
  rfl

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，节点实际输入域）**
有效约化的节点域正好是由同标签路径位置恢复出的实际输入域。
-/
theorem effective_reduction_node_dom_eq (β : V) :
    N.effective_reduction.node_dom β = N.node_actual_input_domain β := by
  exact N.dom_effective_node_operator_eq β

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，有效边域）**
有效约化的边域正好是由相邻标记因子恢复出的有效边域。
-/
theorem effective_reduction_edge_domain_eq (β γ : V) :
    N.effective_reduction.edge_domain β γ = N.effective_edge_domain β γ := by
  ext z
  change
    ((∃ y ∈ dom (N.effective_node_operator β),
        (N.effective_node_operator β).func y = z) ∧
      N.choice β z = OutputChoice.next γ) ↔
      z ∈ N.effective_edge_domain β γ
  constructor
  · rintro ⟨⟨y, hy, hyz⟩, hnext⟩
    have hy_actual : y ∈ N.node_actual_input_domain β := by
      rw [← N.dom_effective_node_operator_eq β]
      exact hy
    have heq := N.effective_node_operator_apply_eq β y hy_actual
    have hnext_original :
        N.choice β ((N.node_op β).func y) = OutputChoice.next γ := by
      rw [← hyz, heq] at hnext
      exact hnext
    rcases hy_actual with ⟨x, pref, suffix, hpath, hyval, hydom⟩
    have hnext_at_prefix :
        N.choice β
            ((N.node_op β).func (N.chain_eval_nodes pref x.val)) =
          OutputChoice.next γ := by
      simpa [hyval] using hnext_original
    rcases terminal_path_suffix_of_next_at_prefix
        (N.path_terminal x) hpath hnext_at_prefix with ⟨tail, hsuffix⟩
    refine ⟨x, pref, tail, ?_, ?_⟩
    · rw [hsuffix] at hpath
      simpa using hpath
    · calc
        z = (N.effective_node_operator β).func y := hyz.symm
        _ = (N.node_op β).func y := heq
        _ = (N.node_op β).func (N.chain_eval_nodes pref x.val) := by rw [hyval]
        _ = N.chain_eval_nodes (pref ++ [β]) x.val := by
          change
            chain_eval_nodes_core N.node_op [β]
                (chain_eval_nodes_core N.node_op pref x.val) =
              chain_eval_nodes_core N.node_op (pref ++ [β]) x.val
          exact (chain_eval_nodes_core_append N.node_op pref [β] x.val).symm
  · rintro ⟨x, pref, suffix, hpath, rfl⟩
    let y := N.chain_eval_nodes pref x.val
    have hy_actual : y ∈ N.node_actual_input_domain β := by
      refine ⟨x, pref, γ :: suffix, hpath, rfl, ?_⟩
      have hpos := terminal_path_prefix_input_mem N.choice_next_mem
        (N.entry_mem x) (N.path_terminal x)
        (⟨pref.length, by simp [hpath]⟩ : Fin (N.path_of x).length)
      simpa [FiniteOperatorNetwork.node_dom,
        FiniteOperatorNetwork.chain_eval_nodes, hpath, y] using hpos
    have heq := N.effective_node_operator_apply_eq β y hy_actual
    have hchoice :
        N.choice β ((N.node_op β).func y) = OutputChoice.next γ := by
      exact terminal_path_choice_at_adjacent_prefix
        (N.path_terminal x) hpath
    have hchain :
        N.chain_eval_nodes (pref ++ [β]) x.val = (N.node_op β).func y := by
      change
        chain_eval_nodes_core N.node_op (pref ++ [β]) x.val =
          (N.node_op β).func (chain_eval_nodes_core N.node_op pref x.val)
      exact chain_eval_nodes_core_append N.node_op pref [β] x.val
    refine ⟨⟨y, ?_, ?_⟩, ?_⟩
    · rw [N.dom_effective_node_operator_eq β]
      exact hy_actual
    · calc
        (N.effective_node_operator β).func y = (N.node_op β).func y := heq
        _ = N.chain_eval_nodes (pref ++ [β]) x.val := hchain.symm
    · rw [hchain]
      exact hchoice

/-- In a deterministic finite network, a node output is terminal exactly when
it lies in the node image and the successor choice is `stop`. -/
theorem mem_terminal_domain_iff_choice_stop
    (M : FiniteOperatorNetwork X bot V) {β : V} {z : X} :
    z ∈ M.terminal_domain β ↔
      z ∈ M.node_image β ∧ M.choice β z = OutputChoice.stop := by
  change
    (z ∈ M.node_image β ∧ z ∉ ⋃ γ : V, M.edge_domain β γ) ↔
      z ∈ M.node_image β ∧ M.choice β z = OutputChoice.stop
  constructor
  · rintro ⟨hzimage, hnoedge⟩
    refine ⟨hzimage, ?_⟩
    cases hchoice : M.choice β z with
    | stop => rfl
    | next γ =>
        exfalso
        apply hnoedge
        apply Set.mem_iUnion.mpr
        exact ⟨γ, hzimage, hchoice⟩
  · rintro ⟨hzimage, hstop⟩
    refine ⟨hzimage, ?_⟩
    intro hedge
    rcases Set.mem_iUnion.mp hedge with ⟨γ, hzedge⟩
    have hcontra : OutputChoice.stop = OutputChoice.next γ :=
      hstop.symm.trans hzedge.2
    cases hcontra

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络，有效终止域）**
有效约化的终止域正好是由标记路径末因子恢复出的有效终止域。
-/
theorem effective_reduction_terminal_domain_eq (β : V) :
    N.effective_reduction.terminal_domain β =
      N.effective_terminal_domain β := by
  ext z
  constructor
  · intro hz
    rcases (mem_terminal_domain_iff_choice_stop N.effective_reduction).mp hz with
      ⟨hzimage, hstop⟩
    change
      ∃ y ∈ dom (N.effective_node_operator β),
        (N.effective_node_operator β).func y = z at hzimage
    rcases hzimage with ⟨y, hy, hyz⟩
    have hy_actual : y ∈ N.node_actual_input_domain β := by
      rw [← N.dom_effective_node_operator_eq β]
      exact hy
    have heq := N.effective_node_operator_apply_eq β y hy_actual
    rcases hy_actual with ⟨x, pref, suffix, hpath, hyval, hydom⟩
    cases suffix with
    | nil =>
        refine ⟨x, pref, ?_, ?_⟩
        · simpa using hpath
        · calc
            z = (N.effective_node_operator β).func y := hyz.symm
            _ = (N.node_op β).func y := heq
            _ = (N.node_op β).func (N.chain_eval_nodes pref x.val) := by
              rw [hyval]
            _ = N.chain_eval_nodes (pref ++ [β]) x.val := by
              change
                chain_eval_nodes_core N.node_op [β]
                    (chain_eval_nodes_core N.node_op pref x.val) =
                  chain_eval_nodes_core N.node_op (pref ++ [β]) x.val
              exact
                (chain_eval_nodes_core_append N.node_op pref [β] x.val).symm
    | cons γ tail =>
        have hchoice :
            N.choice β
                ((N.node_op β).func (N.chain_eval_nodes pref x.val)) =
              OutputChoice.next γ := by
          exact terminal_path_choice_at_adjacent_prefix
            (N.path_terminal x) hpath
        have hzorig : z = (N.node_op β).func y := hyz.symm.trans heq
        have hchoice_z : N.choice β z = OutputChoice.next γ := by
          rw [hzorig, hyval]
          exact hchoice
        have hcontra : OutputChoice.stop = OutputChoice.next γ :=
          hstop.symm.trans hchoice_z
        cases hcontra
  · rintro ⟨x, pref, hpath, rfl⟩
    let y := N.chain_eval_nodes pref x.val
    have hy_actual : y ∈ N.node_actual_input_domain β := by
      refine ⟨x, pref, [], ?_, rfl, ?_⟩
      · simpa using hpath
      · have hpos := terminal_path_prefix_input_mem N.choice_next_mem
          (N.entry_mem x) (N.path_terminal x)
          (⟨pref.length, by simp [hpath]⟩ : Fin (N.path_of x).length)
        simpa [FiniteOperatorNetwork.node_dom,
          FiniteOperatorNetwork.chain_eval_nodes, hpath, y] using hpos
    have heq := N.effective_node_operator_apply_eq β y hy_actual
    have hchain :
        N.chain_eval_nodes (pref ++ [β]) x.val = (N.node_op β).func y := by
      change
        chain_eval_nodes_core N.node_op (pref ++ [β]) x.val =
          (N.node_op β).func (chain_eval_nodes_core N.node_op pref x.val)
      exact chain_eval_nodes_core_append N.node_op pref [β] x.val
    have hzimage :
        N.chain_eval_nodes (pref ++ [β]) x.val ∈
          N.effective_reduction.node_image β := by
      change
        ∃ y ∈ dom (N.effective_node_operator β),
          (N.effective_node_operator β).func y =
            N.chain_eval_nodes (pref ++ [β]) x.val
      refine ⟨y, ?_, ?_⟩
      · rw [N.dom_effective_node_operator_eq β]
        exact hy_actual
      · exact heq.trans hchain.symm
    apply (mem_terminal_domain_iff_choice_stop N.effective_reduction).mpr
    refine ⟨hzimage, ?_⟩
    cases hchoice :
        N.choice β (N.chain_eval_nodes (pref ++ [β]) x.val) with
    | stop => exact hchoice
    | next γ =>
        have hnext_original :
            N.choice β ((N.node_op β).func y) = OutputChoice.next γ := by
          rw [← hchain]
          exact hchoice
        rcases terminal_path_suffix_of_next_at_prefix
            (N.path_terminal x) (by simpa using hpath) hnext_original with
          ⟨tail, hfalse⟩
        simp at hfalse

/-- Restricting a node to its actual inputs restricts its image accordingly. -/
theorem effective_reduction_node_image_eq (β : V) :
    N.effective_reduction.node_image β =
      (N.node_op β).func '' N.node_actual_input_domain β := by
  ext z
  change
    (∃ y ∈ dom (N.effective_node_operator β),
      (N.effective_node_operator β).func y = z) ↔
      ∃ y ∈ N.node_actual_input_domain β, (N.node_op β).func y = z
  rw [N.dom_effective_node_operator_eq β]
  constructor
  · rintro ⟨y, hy, hyz⟩
    exact ⟨y, hy, (N.effective_node_operator_apply_eq β y hy).symm.trans hyz⟩
  · rintro ⟨y, hy, hyz⟩
    exact ⟨y, hy, (N.effective_node_operator_apply_eq β y hy).trans hyz⟩

/--
OET anchor: h-e84d11a2bc70b939
**命题（有效约化保持外延，有效边域的交集公式）**
The actual edge outputs are exactly the original edge domain intersected
with the local image of the source node's actual input domain.
-/
theorem effective_edge_domain_eq_image_inter (β γ : V) :
    N.effective_edge_domain β γ =
      (N.node_op β).func '' N.node_actual_input_domain β ∩ N.edge_domain β γ := by
  rw [← N.effective_reduction_edge_domain_eq β γ]
  ext z
  change
    (z ∈ N.effective_reduction.node_image β ∧
      N.choice β z = OutputChoice.next γ) ↔
      z ∈ (N.node_op β).func '' N.node_actual_input_domain β ∧
        (z ∈ N.node_image β ∧ N.choice β z = OutputChoice.next γ)
  rw [N.effective_reduction_node_image_eq β]
  constructor
  · rintro ⟨hz, hnext⟩
    refine ⟨hz, ?_, hnext⟩
    exact Set.image_mono (N.node_actual_input_domain_subset_node_dom β) hz
  · rintro ⟨hz, _, hnext⟩
    exact ⟨hz, hnext⟩

/--
OET anchor: h-e84d11a2bc70b939
**命题（有效约化保持外延，有效终止域的交集公式）**
The actual terminal outputs are exactly the original terminal domain
intersected with the local image of the node's actual input domain.
-/
theorem effective_terminal_domain_eq_image_inter (β : V) :
    N.effective_terminal_domain β =
      (N.node_op β).func '' N.node_actual_input_domain β ∩ N.terminal_domain β := by
  rw [← N.effective_reduction_terminal_domain_eq β]
  ext z
  rw [mem_terminal_domain_iff_choice_stop, Set.mem_inter_iff,
    mem_terminal_domain_iff_choice_stop, N.effective_reduction_node_image_eq β]
  change
    (z ∈ (N.node_op β).func '' N.node_actual_input_domain β ∧
      N.choice β z = OutputChoice.stop) ↔
      z ∈ (N.node_op β).func '' N.node_actual_input_domain β ∧
        (z ∈ N.node_image β ∧ N.choice β z = OutputChoice.stop)
  constructor
  · rintro ⟨hz, hstop⟩
    refine ⟨hz, ?_, hstop⟩
    exact Set.image_mono (N.node_actual_input_domain_subset_node_dom β) hz
  · rintro ⟨hz, _, hstop⟩
    exact ⟨hz, hstop⟩

/-- The canonical effective reduction evaluates by the restricted path chain. -/
theorem effective_reduction_eval_eq (x : {x : X // x ∈ N.U}) :
    N.effective_reduction.eval x = N.effective_eval x := by
  rfl

/--
OET anchor: h-e84d11a2bc70b939
**命题 #h-e84d11a2bc70b939（有效约化保持外延）**
The canonical effective-reduction network and the original network have the
same extensional evaluation on the complete source domain.
-/
theorem effective_reduction_extensional_local_equivalent :
    LocalEquivalent N.effective_reduction.extensional_operator
      N.extensional_operator N.U := by
  intro x hx
  calc
    N.effective_reduction.extensional_operator.func x =
        N.effective_reduction.eval ⟨x, hx⟩ := by
      simp [FiniteOperatorNetwork.extensional_operator, effective_reduction, hx]
    _ = N.effective_eval ⟨x, hx⟩ := N.effective_reduction_eval_eq ⟨x, hx⟩
    _ = N.eval ⟨x, hx⟩ := N.effective_eval_eq ⟨x, hx⟩
    _ = N.extensional_operator.func x := by
      simp [FiniteOperatorNetwork.extensional_operator, hx]

/--
OET anchor: h-31fdfdb343da7ff2
The formulas recovered from tagged factors give all local data of the actual
effective-reduction network, not merely separate candidate sets.
-/
theorem tagged_reconstruction_of_effective_reduction :
    (∀ β, N.effective_reduction.node_op β =
      restrict_operator (N.node_op β) (N.tagged_recovered_node_input_domain β)) ∧
    (∀ β, N.effective_reduction.entry_domain β = N.tagged_recovered_entry_domain β) ∧
    (∀ β γ, N.effective_reduction.edge_domain β γ = N.tagged_recovered_edge_domain β γ) ∧
    (∀ β, N.effective_reduction.terminal_domain β = N.tagged_recovered_terminal_domain β) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro β
    rw [N.tagged_recovered_node_input_domain_eq]
    rfl
  · intro β
    rw [N.effective_reduction_entry_domain_eq, N.tagged_recovered_entry_domain_eq]
  · intro β γ
    rw [N.effective_reduction_edge_domain_eq, N.tagged_recovered_edge_domain_eq]
  · intro β
    rw [N.effective_reduction_terminal_domain_eq, N.tagged_recovered_terminal_domain_eq]

variable {N}

/--
OET anchor: h-31fdfdb343da7ff2
**命题 #h-31fdfdb343da7ff2（标记分段算子表达决定有效网络）**
An isomorphism of tagged segment expressions preserves source domains, path
segments, ordered node labels up to one global node relabeling, and every
corresponding factor on its actual path-position input set.  Equality of the
whole path-chain operators is a consequence, not a stored premise.
-/
structure TaggedSegmentExpressionIsomorphism
    (N : FiniteOperatorNetwork X bot V) (M : FiniteOperatorNetwork X bot W) where
  source_eq : N.U = M.U
  node_equiv : V ≃ W
  path_equiv : N.ReachablePath ≃ M.ReachablePath
  path_domain_eq :
    ∀ p : N.ReachablePath,
      N.path_domain p.nodes =
        M.path_domain ((path_equiv p).nodes)
  path_nodes_eq :
    ∀ p : N.ReachablePath,
      (path_equiv p).nodes = p.nodes.map node_equiv
  factor_local_equiv :
    ∀ (p : N.ReachablePath) (n : Fin p.nodes.length),
      LocalEquivalent
        (N.node_op (p.nodes.get n))
        (M.node_op (node_equiv (p.nodes.get n)))
        (N.path_factor_input_domain p n)

/-- Corresponding tagged paths have the same number of ordered factors. -/
theorem TaggedSegmentExpressionIsomorphism.path_length_eq
    {N : FiniteOperatorNetwork X bot V} {M : FiniteOperatorNetwork X bot W}
    (h : TaggedSegmentExpressionIsomorphism N M) (p : N.ReachablePath) :
    p.nodes.length = (h.path_equiv p).nodes.length := by
  rw [h.path_nodes_eq p, List.length_map]

/--
Factorwise local equivalence on the actual path-position inputs propagates
through every prefix of a corresponding tagged path.
-/
theorem TaggedSegmentExpressionIsomorphism.prefix_eval_eq
    {N : FiniteOperatorNetwork X bot V} {M : FiniteOperatorNetwork X bot W}
    (h : TaggedSegmentExpressionIsomorphism N M) (p : N.ReachablePath)
    {x : X} (hx : x ∈ N.path_domain p.nodes) :
    ∀ n : Nat, n ≤ p.nodes.length →
      N.chain_eval_nodes (p.nodes.take n) x =
        M.chain_eval_nodes ((p.nodes.take n).map h.node_equiv) x := by
  intro n hn
  induction n with
  | zero =>
      simp [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core]
  | succ n ih =>
      have hnlt : n < p.nodes.length := by omega
      have hmaplt : n < (p.nodes.map h.node_equiv).length := by
        simpa using hnlt
      have hNstep := N.chain_eval_nodes_take_succ hnlt x
      have hMstep := M.chain_eval_nodes_take_succ hmaplt x
      have hprefix := ih (Nat.le_of_lt hnlt)
      have hy :
          N.chain_eval_nodes (p.nodes.take n) x ∈
            N.path_factor_input_domain p ⟨n, hnlt⟩ :=
        ⟨x, hx, rfl⟩
      have hfactor := h.factor_local_equiv p ⟨n, hnlt⟩
        (N.chain_eval_nodes (p.nodes.take n) x) hy
      calc
        N.chain_eval_nodes (p.nodes.take (n + 1)) x =
            (N.node_op (p.nodes.get ⟨n, hnlt⟩)).func
              (N.chain_eval_nodes (p.nodes.take n) x) := hNstep
        _ = (M.node_op (h.node_equiv (p.nodes.get ⟨n, hnlt⟩))).func
              (N.chain_eval_nodes (p.nodes.take n) x) := hfactor
        _ = (M.node_op (h.node_equiv (p.nodes.get ⟨n, hnlt⟩))).func
              (M.chain_eval_nodes ((p.nodes.take n).map h.node_equiv) x) := by
                rw [hprefix]
        _ = M.chain_eval_nodes ((p.nodes.take (n + 1)).map h.node_equiv) x := by
              simpa using hMstep.symm

/--
The path-chain local equivalence required by extensional evaluation is derived
from the ordered factor correspondence.
-/
theorem TaggedSegmentExpressionIsomorphism.path_chain_local_equiv
    {N : FiniteOperatorNetwork X bot V} {M : FiniteOperatorNetwork X bot W}
    (h : TaggedSegmentExpressionIsomorphism N M) (p : N.ReachablePath) :
    LocalEquivalent (N.path_chain p.nodes)
      (M.path_chain ((h.path_equiv p).nodes))
      (N.path_domain p.nodes) := by
  intro x hx
  have hpref := h.prefix_eval_eq p hx p.nodes.length (by rfl)
  rw [List.take_length] at hpref
  rw [N.path_chain_apply_eq_chain_eval_nodes,
    M.path_chain_apply_eq_chain_eval_nodes, h.path_nodes_eq p]
  exact hpref

/--
OET anchor: h-2fb93a4e99c7e5f4
**定义（外延等价与有效等价）**
Extensional equivalence is local equivalence of the two network extensional
operators on the common source domain.
-/
def ExtensionalEquivalent
    (N : FiniteOperatorNetwork X bot V) (M : FiniteOperatorNetwork X bot W) : Prop :=
  N.U = M.U ∧
    LocalEquivalent N.extensional_operator M.extensional_operator N.U

/--
OET anchor: h-2fb93a4e99c7e5f4
**定义（外延等价与有效等价）**
Effective equivalence is isomorphism of tagged segment expressions.
-/
def EffectiveEquivalent
    (N : FiniteOperatorNetwork X bot V) (M : FiniteOperatorNetwork X bot W) : Prop :=
  Nonempty (TaggedSegmentExpressionIsomorphism N M)

/--
OET anchor: h-2fb93a4e99c7e5f4
**命题 #h-2fb93a4e99c7e5f4（有效等价推出外延等价）**
Effective equivalence of tagged segment expressions implies extensional
equivalence of the induced network operators.
-/
theorem effective_equivalent_implies_extensional
    {N : FiniteOperatorNetwork X bot V} {M : FiniteOperatorNetwork X bot W}
    (h : EffectiveEquivalent N M) :
    ExtensionalEquivalent N M := by
  rcases h with ⟨h⟩
  refine ⟨h.source_eq, ?_⟩
  intro x hx
  let p : N.ReachablePath :=
    ⟨N.path_of ⟨x, hx⟩, ⟨x, hx, rfl⟩⟩
  let q : M.ReachablePath := h.path_equiv p
  have hxNp : x ∈ N.path_domain p.nodes := by
    exact ⟨hx, rfl⟩
  have hxMq : x ∈ M.path_domain q.nodes := by
    have hxMq' :
        x ∈ M.path_domain ((h.path_equiv p).nodes) := by
      rw [← h.path_domain_eq p]
      exact hxNp
    simpa [q] using hxMq'
  rcases hxMq with ⟨hxMU, hMpath⟩
  calc
    N.extensional_operator.func x =
        N.chain_eval_nodes p.nodes x := by
      simpa [p] using
        N.extensional_apply_eq_chain_eval_path ⟨x, hx⟩
    _ = (N.path_chain p.nodes).func x :=
      (N.path_chain_apply_eq_chain_eval_nodes p.nodes x).symm
    _ = (M.path_chain q.nodes).func x := by
      simpa [q] using h.path_chain_local_equiv p x hxNp
    _ = M.chain_eval_nodes q.nodes x :=
      M.path_chain_apply_eq_chain_eval_nodes q.nodes x
    _ = M.chain_eval_nodes (M.path_of ⟨x, hxMU⟩) x := by
      rw [hMpath]
    _ = M.extensional_operator.func x :=
      (M.extensional_apply_eq_chain_eval_path ⟨x, hxMU⟩).symm

/--
OET anchor: h-2fb93a4e99c7e5f4
**命题 #h-2fb93a4e99c7e5f4（有效等价推出外延等价，反向反例）**
On the singleton source in `Fin 2`, one identity node and two serial identity
nodes have the same extensional operator but cannot have isomorphic tagged
segment expressions.
-/
theorem extensional_equivalence_not_implies_effective_counterexample :
    ∃ (N : FiniteOperatorNetwork (Fin 2) 0 Unit)
      (M : FiniteOperatorNetwork (Fin 2) 0 (Fin 2)),
      ExtensionalEquivalent N M ∧ ¬ EffectiveEquivalent N M := by
  classical
  let N : FiniteOperatorNetwork (Fin 2) 0 Unit :=
    NetworkObject.single_node_network
      (id_operator : Operator (Fin 2) 0) fin2_id_operator_ne_bot
  let M : FiniteOperatorNetwork (Fin 2) 0 (Fin 2) :=
    fin2_two_node_id_network.to_finite
  refine ⟨N, M, ?_, ?_⟩
  · constructor
    · ext x
      fin_cases x <;>
        simp [N, M, NetworkObject.single_node_network,
          fin2_two_node_id_network, OperatorNetwork.to_finite, dom, id_operator]
    · intro x hx
      have hext := node_count_not_extensional_invariant
      simpa [N, M] using congrArg (fun op : Operator (Fin 2) 0 => op.func x) hext.1
  · rintro ⟨hiso⟩
    have hcard := Fintype.card_congr hiso.node_equiv
    norm_num at hcard

end FiniteOperatorNetwork

end formal_oet.vol_01.ch_05_operator_networks
