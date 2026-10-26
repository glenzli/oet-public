import Mathlib.Data.Set.Card.Arithmetic
import formal_oet.vol_01.ch_05_operator_networks.network_refinement

namespace formal_oet.vol_01.ch_05_operator_networks.refinement_termination

open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open scoped BigOperators

section RefinementTermination

/--
OET anchor: h-2498621c42325300 **命题（加细链辅助）** 一列对象中相邻两项满足一步加细关系。 -/
def RefinementChain {α : Type} (R : RefinementRule α) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => R a b ∧ RefinementChain R (b :: rest)

/--
OET anchor: h-2498621c42325300 **命题（下降量辅助）** 规则 `R` 使自然数值 `μ` 严格下降。 -/
def StrictlyDecreases {α : Type} (R : RefinementRule α) (μ : α → Nat) : Prop :=
  ∀ {a b : α}, R a b → μ b < μ a

/--
OET anchor: h-2498621c42325300
**命题（加细终止的充分条件，通用下降量）**
若每一步加细都使自然数值 `μ` 严格下降，则任意从 `a` 出发的
有限加细链长度不超过 `μ a + 1`。因此不存在无限严格下降加细过程。
-/
theorem refinement_chain_length_le_measure {α : Type}
    {R : RefinementRule α} {μ : α → Nat}
    (hdec : StrictlyDecreases R μ) :
    ∀ {a : α} {tail : List α},
      RefinementChain R (a :: tail) →
        (a :: tail).length ≤ μ a + 1 := by
  intro a tail hchain
  induction tail generalizing a with
  | nil =>
      simp
  | cons b rest ih =>
      rcases hchain with ⟨hab, hrest⟩
      have htail := ih (a := b) hrest
      have hdrop : μ b < μ a := hdec hab
      have htail_to_a : (b :: rest).length ≤ μ a :=
        le_trans htail (Nat.succ_le_of_lt hdrop)
      simpa only [List.length_cons] using Nat.succ_le_succ htail_to_a

/-- A natural-valued strict descent cannot continue through all natural
indices. -/
theorem no_infinite_refinement_chain {α : Type}
    {R : RefinementRule α} {μ : α → Nat}
    (hdec : StrictlyDecreases R μ) :
    ¬ ∃ sequence : Nat → α, ∀ n : Nat, R (sequence n) (sequence (n + 1)) := by
  rintro ⟨sequence, hstep⟩
  have hbound : ∀ n : Nat, μ (sequence n) + n ≤ μ (sequence 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        have hdrop : μ (sequence (n + 1)) < μ (sequence n) := hdec (hstep n)
        omega
  have hcontra := hbound (μ (sequence 0) + 1)
  omega

/-- The contribution of a genuine finite nonempty partition is strictly
smaller than the contribution of the unsplit non-singleton set. -/
theorem proper_partition_contribution_lt (q parent_size : Nat)
    (sizes : Fin q → Nat) (hq : 2 ≤ q)
    (hpositive : ∀ a : Fin q, 0 < sizes a)
    (hcard : (∑ a : Fin q, sizes a) = parent_size) :
    (∑ a : Fin q, (sizes a - 1)) < parent_size - 1 := by
  have hsum : (∑ a : Fin q, (sizes a - 1)) + q = parent_size := by
    calc
      (∑ a : Fin q, (sizes a - 1)) + q =
          ∑ a : Fin q, ((sizes a - 1) + 1) := by
            rw [Finset.sum_add_distrib]
            simp
      _ = ∑ a : Fin q, sizes a := by
        apply Finset.sum_congr rfl
        intro a _ha
        exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (hpositive a)))
      _ = parent_size := hcard
  omega

/-- Cardinal data for one node-domain split in the measure
`Σβ (|Uβ| - 1)`. Deleted unreachable nodes are represented by the upper
bound on the new measure. -/
structure NodeDomainPartitionStep (before after : Nat) where
  q : Nat
  sizes : Fin q → Nat
  parent_size : Nat
  rest_measure : Nat
  q_ge_two : 2 ≤ q
  part_nonempty : ∀ a : Fin q, 0 < sizes a
  partition_card : (∑ a : Fin q, sizes a) = parent_size
  before_eq : before = rest_measure + (parent_size - 1)
  after_le : after ≤ rest_measure + ∑ a : Fin q, (sizes a - 1)

/-- A true finite node-domain partition strictly decreases the node-domain
measure. -/
theorem NodeDomainPartitionStep.decreases {before after : Nat}
    (h : NodeDomainPartitionStep before after) : after < before := by
  have hlocal := proper_partition_contribution_lt h.q h.parent_size h.sizes
    h.q_ge_two h.part_nonempty h.partition_card
  have hbefore := h.before_eq
  have hafter := h.after_le
  omega

/-- Rank data for replacing one factor by two factors whose restricted rank
sum is strictly smaller. Deleting unreachable nodes cannot increase the new
total rank and is represented by `after_le`. -/
structure AlgebraicRankStep (before after : Nat) where
  old_rank : Nat
  first_rank : Nat
  second_rank : Nat
  rest_rank : Nat
  factor_rank_lt : first_rank + second_rank < old_rank
  before_eq : before = rest_rank + old_rank
  after_le : after ≤ rest_rank + first_rank + second_rank

/-- A permitted rank-decreasing algebraic split strictly decreases total
algebraic rank. -/
theorem AlgebraicRankStep.decreases {before after : Nat}
    (h : AlgebraicRankStep before after) : after < before := by
  have hlocal := h.factor_rank_lt
  have hbefore := h.before_eq
  have hafter := h.after_le
  omega

/-- The node-domain measure used in the textbook termination proof.  The
network carries its own finite node-type instance, so the definition does
not require a global `Fintype V` instance. -/
noncomputable def nodeDomainMeasure {X V : Type} {bot : X}
    (N : FiniteOperatorNetwork X bot V) : Nat := by
  letI : Fintype V := N.node_fintype
  exact ∑ β : V, ((N.node_dom β).ncard - 1)

/-- The total algebraic rank of the local operators of a finite network. -/
noncomputable def algebraicRankMeasure {X V : Type} {bot : X}
    (rank : Operator X bot → Nat) (N : FiniteOperatorNetwork X bot V) : Nat := by
  letI : Fintype V := N.node_fintype
  exact ∑ β : V, rank (N.node_op β)

/-- Weight of an old non-target node or of one partition piece. -/
private noncomputable def nodeDomainSourceWeight
    {X V V' : Type} {bot : X}
    {N : FiniteOperatorNetwork X bot V}
    {N' : FiniteOperatorNetwork X bot V'}
    (href : N.NodeDomainRefinement N') :
    ({β : V // β ≠ href.target} ⊕ Fin href.part_count) → Nat
  | Sum.inl β => (N.node_dom β.val).ncard - 1
  | Sum.inr a => (href.piece a).ncard - 1

/-- An actual finite node-domain refinement supplies the abstract partition
step used by the termination argument.  The only extra hypotheses are the
textbook hypotheses that the split is proper and that the old node domains
are finite; the measure comparison is derived from the refinement's source
map and operator-compatibility fields. -/
noncomputable def NodeDomainRefinement.toNodeDomainPartitionStep
    {X V V' : Type} {bot : X}
    {N : FiniteOperatorNetwork X bot V}
    {N' : FiniteOperatorNetwork X bot V'}
    (href : N.NodeDomainRefinement N')
    (hq : 2 ≤ href.part_count)
    (hfinite : ∀ β : V, (N.node_dom β).Finite) :
    NodeDomainPartitionStep (nodeDomainMeasure N) (nodeDomainMeasure N') := by
  classical
  letI : Fintype V := N.node_fintype
  letI : Fintype V' := N'.node_fintype
  let oldWeight : {β : V // β ≠ href.target} → Nat :=
    fun β => (N.node_dom β.val).ncard - 1
  let pieceWeight : Fin href.part_count → Nat :=
    fun a => (href.piece a).ncard - 1
  have hpiece_subset (a : Fin href.part_count) :
      href.piece a ⊆ N.node_dom href.target := by
    rw [← href.piece_cover]
    exact Set.subset_iUnion href.piece a
  have hpiece_finite (a : Fin href.part_count) :
      (href.piece a).Finite :=
    (hfinite href.target).subset (hpiece_subset a)
  have hpartition_card :
      (∑ a : Fin href.part_count, (href.piece a).ncard) =
        (N.node_dom href.target).ncard := by
    have hunion := Set.ncard_iUnion_of_finite hpiece_finite
      (fun a b hab => href.piece_disjoint hab)
    rw [finsum_eq_sum_of_fintype, href.piece_cover] at hunion
    exact hunion.symm
  have hbefore :
      nodeDomainMeasure N =
        (∑ β : {β : V // β ≠ href.target}, oldWeight β) +
          ((N.node_dom href.target).ncard - 1) := by
    change (∑ β : V, ((N.node_dom β).ncard - 1)) = _
    calc
      (∑ β : V, ((N.node_dom β).ncard - 1)) =
          (N.node_dom href.target).ncard - 1 +
            ∑ β : {β : V // β ≠ href.target},
              ((N.node_dom β.val).ncard - 1) :=
        Fintype.sum_eq_add_sum_subtype_ne
          (fun β : V => (N.node_dom β).ncard - 1) href.target
      _ = (∑ β : {β : V // β ≠ href.target}, oldWeight β) +
          ((N.node_dom href.target).ncard - 1) := by
        simp only [oldWeight, Nat.add_comm]
  have hnew_weight (β' : V') :
      (N'.node_dom β').ncard - 1 =
        nodeDomainSourceWeight href (href.source β') := by
    cases hs : href.source β' with
    | inl β =>
        have hop := href.old_node_op_compat β' β hs
        simp only [nodeDomainSourceWeight]
        rw [N'.node_dom_eq_dom, N.node_dom_eq_dom, hop]
    | inr a =>
        have hop := href.piece_node_op_compat β' a hs
        simp only [nodeDomainSourceWeight]
        rw [N'.node_dom_eq_dom, hop, href.local_domain a]
  have hafter_image :
      nodeDomainMeasure N' =
        ∑ s ∈ Finset.univ.image href.source,
          nodeDomainSourceWeight href s := by
    change (∑ β' : V', ((N'.node_dom β').ncard - 1)) = _
    calc
      (∑ β' : V', ((N'.node_dom β').ncard - 1)) =
          ∑ β' : V', nodeDomainSourceWeight href (href.source β') := by
            apply Finset.sum_congr rfl
            intro β' _hβ'
            exact hnew_weight β'
      _ = ∑ s ∈ Finset.univ.image href.source,
          nodeDomainSourceWeight href s := by
            symm
            exact Finset.sum_image
              (fun _ _ _ _ heq => href.source_injective heq)
  have hafter_full :
      nodeDomainMeasure N' ≤
        ∑ s : ({β : V // β ≠ href.target} ⊕ Fin href.part_count),
          nodeDomainSourceWeight href s := by
    rw [hafter_image]
    exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by
      intro _s _hs _hnot
      omega)
  have hafter :
      nodeDomainMeasure N' ≤
        (∑ β : {β : V // β ≠ href.target}, oldWeight β) +
          ∑ a : Fin href.part_count, pieceWeight a := by
    simpa only [Fintype.sum_sum_type, nodeDomainSourceWeight,
      oldWeight, pieceWeight] using hafter_full
  exact
    { q := href.part_count
      sizes := fun a => (href.piece a).ncard
      parent_size := (N.node_dom href.target).ncard
      rest_measure := ∑ β : {β : V // β ≠ href.target}, oldWeight β
      q_ge_two := hq
      part_nonempty := fun a =>
        (Set.ncard_pos (hpiece_finite a)).2 (href.piece_nonempty a)
      partition_card := hpartition_card
      before_eq := hbefore
      after_le := hafter }

/--
OET anchor: h-2498621c42325300
For an actual node-domain refinement, the concrete textbook measure strictly
decreases under the stated finite proper-partition hypotheses. -/
theorem NodeDomainRefinement.nodeDomainMeasure_decreases
    {X V V' : Type} {bot : X}
    {N : FiniteOperatorNetwork X bot V}
    {N' : FiniteOperatorNetwork X bot V'}
    (href : N.NodeDomainRefinement N')
    (hq : 2 ≤ href.part_count)
    (hfinite : ∀ β : V, (N.node_dom β).Finite) :
    nodeDomainMeasure N' < nodeDomainMeasure N :=
  (NodeDomainRefinement.toNodeDomainPartitionStep href hq hfinite).decreases

/-- Weight on the source code of an algebraic refinement. -/
private noncomputable def algebraicSourceWeight
    {X V V' : Type} {bot : X}
    {N : FiniteOperatorNetwork X bot V}
    {N' : FiniteOperatorNetwork X bot V'}
    (rank : Operator X bot → Nat) (href : N.AlgebraicRefinement N') :
    ({β : V // β ≠ href.target} ⊕ Bool) → Nat
  | Sum.inl β => rank (N.node_op β.val)
  | Sum.inr false => rank (restrict_operator href.first_factor (N.node_dom href.target))
  | Sum.inr true => rank (restrict_operator href.second_factor
      (href.first_factor.func '' N.node_dom href.target))

/-- An actual algebraic refinement supplies the abstract rank step used by
the termination proof.  The strict inequality is exactly the admissibility
condition imposed on the chosen rank; all global bookkeeping is derived. -/
noncomputable def AlgebraicRefinement.toAlgebraicRankStep
    {X V V' : Type} {bot : X}
    {N : FiniteOperatorNetwork X bot V}
    {N' : FiniteOperatorNetwork X bot V'}
    (rank : Operator X bot → Nat) (href : N.AlgebraicRefinement N')
    (hrank :
      rank (restrict_operator href.first_factor (N.node_dom href.target)) +
        rank (restrict_operator href.second_factor
          (href.first_factor.func '' N.node_dom href.target)) <
            rank (N.node_op href.target)) :
    AlgebraicRankStep (algebraicRankMeasure rank N)
      (algebraicRankMeasure rank N') := by
  classical
  letI : Fintype V := N.node_fintype
  letI : Fintype V' := N'.node_fintype
  let restRank : Nat :=
    ∑ β : {β : V // β ≠ href.target}, rank (N.node_op β.val)
  have hbefore :
      algebraicRankMeasure rank N =
        restRank + rank (N.node_op href.target) := by
    rw [algebraicRankMeasure]
    simpa only [restRank, Nat.add_comm] using
      (Fintype.sum_eq_add_sum_subtype_ne
        (fun β : V => rank (N.node_op β)) href.target)
  have hnew_weight (β' : V') :
      rank (N'.node_op β') =
        algebraicSourceWeight rank href (href.source β') := by
    cases hs : href.source β' with
    | inl β =>
        simpa only [algebraicSourceWeight] using
          congrArg rank (href.old_node_op_compat β' β hs)
    | inr flag =>
        cases flag with
        | false =>
            simpa only [algebraicSourceWeight] using
              congrArg rank (href.first_node_op_compat β' hs)
        | true =>
            simpa only [algebraicSourceWeight] using
              congrArg rank (href.second_node_op_compat β' hs)
  have hafter_full :
      algebraicRankMeasure rank N' =
        ∑ s : ({β : V // β ≠ href.target} ⊕ Bool),
          algebraicSourceWeight rank href s := by
    rw [algebraicRankMeasure]
    calc
      (∑ β' : V', rank (N'.node_op β')) =
          ∑ β' : V', algebraicSourceWeight rank href (href.source β') := by
            apply Finset.sum_congr rfl
            intro β' _hβ'
            exact hnew_weight β'
      _ = ∑ s : ({β : V // β ≠ href.target} ⊕ Bool),
          algebraicSourceWeight rank href s :=
            Fintype.sum_bijective href.source href.source_bijective _ _
              (fun _ => rfl)
  have hafter :
      algebraicRankMeasure rank N' =
        restRank +
          rank (restrict_operator href.first_factor (N.node_dom href.target)) +
          rank (restrict_operator href.second_factor
            (href.first_factor.func '' N.node_dom href.target)) := by
    rw [hafter_full, Fintype.sum_sum_type]
    simp only [algebraicSourceWeight, restRank, Fintype.sum_bool]
    omega
  exact
    { old_rank := rank (N.node_op href.target)
      first_rank := rank (restrict_operator href.first_factor
        (N.node_dom href.target))
      second_rank := rank (restrict_operator href.second_factor
        (href.first_factor.func '' N.node_dom href.target))
      rest_rank := restRank
      factor_rank_lt := hrank
      before_eq := hbefore
      after_le := hafter.le }

/--
OET anchor: h-2498621c42325300
For an actual algebraic refinement, the concrete total-rank measure strictly
decreases under the stated admissible-rank hypothesis. -/
theorem AlgebraicRefinement.algebraicRankMeasure_decreases
    {X V V' : Type} {bot : X}
    {N : FiniteOperatorNetwork X bot V}
    {N' : FiniteOperatorNetwork X bot V'}
    (rank : Operator X bot → Nat) (href : N.AlgebraicRefinement N')
    (hrank :
      rank (restrict_operator href.first_factor (N.node_dom href.target)) +
        rank (restrict_operator href.second_factor
          (href.first_factor.func '' N.node_dom href.target)) <
            rank (N.node_op href.target)) :
    algebraicRankMeasure rank N' < algebraicRankMeasure rank N :=
  (AlgebraicRefinement.toAlgebraicRankStep rank href hrank).decreases

/--
OET anchor: h-2498621c42325300
**命题（节点域加细终止的下降量形式）**
当每步节点域加细由有限非空真分划给出，且删除不可达节点不增加
其余贡献时，节点域下降量严格下降，纯节点域加细链有限有界。
-/
theorem node_occurrence_domain_refinement_chain_finite {α : Type}
    {R : RefinementRule α} {μ : α → Nat}
    (hstep : ∀ {a b : α}, R a b → NodeDomainPartitionStep (μ a) (μ b))
    {a : α} {tail : List α}
    (hchain : RefinementChain R (a :: tail)) :
    (a :: tail).length ≤ μ a + 1 := by
  apply refinement_chain_length_le_measure (R := R) (μ := μ)
  · intro x y hxy
    exact (hstep hxy).decreases
  · exact hchain

/--
OET anchor: h-2498621c42325300
**命题（代数加细终止的下降量形式）**
当每步代数加细把一个因子替换为受限秩和严格更小的两个因子，且
删除不可达节点不增加其余秩时，总代数秩严格下降，纯代数加细链有限有界。
-/
theorem algebraic_refinement_chain_finite {α : Type}
    {R : RefinementRule α} {rank : α → Nat}
    (hstep : ∀ {a b : α}, R a b → AlgebraicRankStep (rank a) (rank b))
    {a : α} {tail : List α}
    (hchain : RefinementChain R (a :: tail)) :
    (a :: tail).length ≤ rank a + 1 := by
  apply refinement_chain_length_le_measure (R := R) (μ := rank)
  · intro x y hxy
    exact (hstep hxy).decreases
  · exact hchain

/--
OET anchor: h-2498621c42325300
**命题（加细终止的充分条件）**

节点域加细分支的最终包装：有限真分划所给出的节点域下降量
排除无穷节点域加细序列。
-/
theorem node_domain_refinement_termination_textbook
    {α : Type} {R_dom : RefinementRule α} {domain_measure : α → Nat} :
    (∀ {a b : α}, R_dom a b →
        NodeDomainPartitionStep (domain_measure a) (domain_measure b)) →
      ¬ ∃ sequence : Nat → α,
          ∀ n : Nat, R_dom (sequence n) (sequence (n + 1)) := by
  intro hdomain
  exact no_infinite_refinement_chain (R := R_dom) (μ := domain_measure)
    (fun {_a _b} hab => (hdomain hab).decreases)

/--
OET anchor: h-2498621c42325300
**命题（加细终止的充分条件，代数加细分支）**
-/
theorem algebraic_refinement_termination_textbook
    {α : Type} {R_alg : RefinementRule α} {algebraic_rank : α → Nat}
    (halgebraic : ∀ {a b : α}, R_alg a b →
      AlgebraicRankStep (algebraic_rank a) (algebraic_rank b)) :
    ¬ ∃ sequence : Nat → α,
        ∀ n : Nat, R_alg (sequence n) (sequence (n + 1)) := by
  exact no_infinite_refinement_chain (R := R_alg) (μ := algebraic_rank)
    (fun {_a _b} hab => (halgebraic hab).decreases)

/--
OET anchor: h-2498621c42325300
**命题（加细终止的充分条件，混合加细分支）**
-/
theorem mixed_refinement_termination_textbook
    {α : Type} {R_mix : RefinementRule α} {mixed_measure : α → Nat}
    (hmixed : StrictlyDecreases R_mix mixed_measure) :
    ¬ ∃ sequence : Nat → α,
        ∀ n : Nat, R_mix (sequence n) (sequence (n + 1)) :=
  no_infinite_refinement_chain hmixed

/--
OET anchor: h-2498621c42325300
The mixed-step measure need only be defined on networks reachable from the
fixed starting network; it is not required on the entire representation space.
-/
theorem mixed_refinement_termination_from
    {α : Type} (R : RefinementRule α) (start : α)
    (measure : {x : α // Relation.ReflTransGen R start x} → Nat)
    (hdecrease : ∀ {x y : α} (hx : Relation.ReflTransGen R start x)
      (hy : Relation.ReflTransGen R start y), R x y → measure ⟨y, hy⟩ < measure ⟨x, hx⟩) :
    ¬ ∃ sequence : Nat → α, sequence 0 = start ∧
      ∀ n : Nat, R (sequence n) (sequence (n + 1)) := by
  rintro ⟨sequence, hstart, hstep⟩
  have hreach : ∀ n, Relation.ReflTransGen R start (sequence n) := by
    intro n
    induction n with
    | zero => rw [hstart]
    | succ n ih => exact ih.tail (hstep n)
  apply no_infinite_refinement_chain
    (R := fun x y : {x : α // Relation.ReflTransGen R start x} => R x.val y.val)
    (μ := measure) (fun {x y} h => hdecrease x.property y.property h)
  exact ⟨fun n => ⟨sequence n, hreach n⟩, hstep⟩

end RefinementTermination

end formal_oet.vol_01.ch_05_operator_networks.refinement_termination
