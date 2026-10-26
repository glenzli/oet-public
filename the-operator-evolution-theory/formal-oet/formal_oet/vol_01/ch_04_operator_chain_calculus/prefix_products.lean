import Mathlib.Topology.Instances.ENNReal.Lemmas
import formal_oet.vol_01.ch_04_operator_chain_calculus.distance_recurrence

namespace formal_oet.vol_01.ch_04_operator_chain_calculus

noncomputable section

/-- OET anchor: h-36b3776ed03a6cb4 **小节（长链的前缀乘积分析）** -/
abbrev long_chain_prefix_product_section_marker : Unit := ()

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators


variable {X I : Type} {bot : X}
local instance instDecidableEqIPrefixProducts : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/--
The `k`-step prefix operator
`ϕ_{k-1} ∘ ... ∘ ϕ_0`.

The source text uses one-based indexing.  This Lean definition uses the
zero-based sequence `ϕ 0, ϕ 1, ...`; thus `chain_prefix_operator ϕ (n + 1)`
corresponds to the textual prefix ending at `φ_{n+1}`.
-/
noncomputable def chain_prefix_operator (ϕ : ℕ → Operator X bot) :
    ℕ → Operator X bot
  | 0 => OperatorChain []
  | n + 1 => OperatorChain [ϕ n, chain_prefix_operator ϕ n]

/--
The ordered prefix product
`M_{k-1} · ... · M_0`, with the empty product equal to the identity matrix.
-/
noncomputable def matrix_prefix_product [Fintype I]
    (M : ℕ → I → I → ENNReal) :
    ℕ → I → I → ENNReal
  | 0 => matrix_id
  | n + 1 => matrix_mul (M n) (matrix_prefix_product M n)

/-- Prefix evaluation follows the prescribed image-domain sequence. -/
theorem chain_prefix_maps_to_sequence
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n) :
    ∀ k : ℕ, Set.MapsTo (chain_prefix_operator ϕ k).func (U 0) (U k) := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simpa [chain_prefix_operator] using hx
  | succ n ih =>
      intro x hx
      have hz : (chain_prefix_operator ϕ n).func x ∈ U n := ih hx
      have him :
          (ϕ n).func ((chain_prefix_operator ϕ n).func x) ∈
            (ϕ n).func '' U n :=
        Set.mem_image_of_mem (ϕ n).func hz
      simpa [chain_prefix_operator, hU_step n] using him

/-- The first domain condition excludes `bot` from the initial prefix domain. -/
theorem initial_set_has_no_bot_of_chain_domain
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n)) :
    ∀ x ∈ U 0, x ≠ bot := by
  intro x hx hxb
  have hxdom : x ∈ dom (ϕ 0) := hU_dom 0 hx
  dsimp [dom] at hxdom
  rw [hxb, (ϕ 0).preserves_bot] at hxdom
  exact hxdom rfl

/--
OET anchor: h-95d270a294f96c14
**命题 #h-95d270a294f96c14（一般链前缀乘积的渐近判据，L 前缀乘积）**
Each selected local Lip matrix propagates to the ordered prefix product.
-/
theorem chain_prefix_lip_matrix [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (L : ℕ → I → I → ENNReal)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hL : ∀ n : ℕ, IsLipMatrix d (ϕ n) (U n) (L n)) :
    ∀ k : ℕ,
      IsLipMatrix d (chain_prefix_operator ϕ k) (U 0)
        (matrix_prefix_product L k) := by
  intro k
  induction k with
  | zero =>
      exact right_chain_lip_matrix d [] (U 0) matrix_id
        (RightChainLipBounded.nil (U 0)
          (initial_set_has_no_bot_of_chain_domain ϕ U hU_dom))
  | succ n ih =>
      have h_im :
          ∀ x ∈ U 0, (chain_prefix_operator ϕ n).func x ∈ U n :=
        chain_prefix_maps_to_sequence ϕ U hU_step n
      have hcomp :=
        lip_matrix_comp d (chain_prefix_operator ϕ n) (ϕ n)
          (U 0) (U n) (matrix_prefix_product L n) (L n)
          h_im ih (hL n)
      simpa [chain_prefix_operator, matrix_prefix_product] using hcomp

/--
OET anchor: h-95d270a294f96c14
**命题 #h-95d270a294f96c14（一般链前缀乘积的渐近判据，K 前缀乘积）**
Each selected local co-Lip matrix propagates to the ordered prefix product.
-/
theorem chain_prefix_colip_matrix [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (K : ℕ → I → I → ENNReal)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hU0_ne : (U 0).Nonempty)
    (hK : ∀ n : ℕ, IsCoLipMatrix d (ϕ n) (U n) (K n)) :
    ∀ k : ℕ,
      IsCoLipMatrix d (chain_prefix_operator ϕ k) (U 0)
        (matrix_prefix_product K k) := by
  intro k
  induction k with
  | zero =>
      exact right_chain_colip_matrix d [] (U 0) matrix_id
        (RightChainCoLipBounded.nil (U 0)
          (initial_set_has_no_bot_of_chain_domain ϕ U hU_dom) hU0_ne)
  | succ n ih =>
      have h_im :
          ∀ x ∈ U 0, (chain_prefix_operator ϕ n).func x ∈ U n :=
        chain_prefix_maps_to_sequence ϕ U hU_step n
      have hcomp :=
        colip_matrix_comp d (chain_prefix_operator ϕ n) (ϕ n)
          (U 0) (U n) (matrix_prefix_product K n) (K n)
          h_im ih (hK n)
      simpa [chain_prefix_operator, matrix_prefix_product] using hcomp

/--
OET anchor: h-95d270a294f96c14
**命题 #h-95d270a294f96c14（一般链前缀乘积的渐近判据，点态 L 上界）**
The L prefix product gives the displayed pointwise upper bound.
-/
theorem chain_prefix_lip_distance_upper [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (L : ℕ → I → I → ENNReal)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hL : ∀ n : ℕ, IsLipMatrix d (ϕ n) (U n) (L n))
    (k : ℕ) (x y : X) (hx : x ∈ U 0) (hy : y ∈ U 0) (j : I) :
    d j ((chain_prefix_operator ϕ k).func x)
        ((chain_prefix_operator ϕ k).func y) ≤
      matrix_vector_bound (matrix_prefix_product L k) (DistanceVector d x y) j := by
  exact (chain_prefix_lip_matrix d ϕ U L hU_step hU_dom hL k).2 x hx y hy j

/--
OET anchor: h-95d270a294f96c14
**命题 #h-95d270a294f96c14（一般链前缀乘积的渐近判据，点态 K 下界）**
The K prefix product gives the displayed pointwise lower bound.
-/
theorem chain_prefix_colip_distance_lower [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (K : ℕ → I → I → ENNReal)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hU0_ne : (U 0).Nonempty)
    (hK : ∀ n : ℕ, IsCoLipMatrix d (ϕ n) (U n) (K n))
    (k : ℕ) (x y : X) (hx : x ∈ U 0) (hy : y ∈ U 0) (j : I) :
    matrix_vector_bound (matrix_prefix_product K k) (DistanceVector d x y) j ≤
      d j ((chain_prefix_operator ϕ k).func x)
        ((chain_prefix_operator ϕ k).func y) := by
  exact (chain_prefix_colip_matrix d ϕ U K hU_step hU_dom hU0_ne hK k).2.2
    x hx y hy j

/--
OET anchor: h-95d270a294f96c14
**命题 #h-95d270a294f96c14（一般链前缀乘积的渐近判据，L 上界趋零读法）**
If the displayed L upper bound tends to zero, then the target distance
tends to zero.
-/
theorem chain_prefix_lip_distance_tends_zero_of_upper_bound
    [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (L : ℕ → I → I → ENNReal)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hL : ∀ n : ℕ, IsLipMatrix d (ϕ n) (U n) (L n))
    (x y : X) (hx : x ∈ U 0) (hy : y ∈ U 0) (j : I)
    (h_bound_zero :
      ∀ ε : ENNReal, 0 < ε →
        ∃ N : ℕ, ∀ k ≥ N,
          matrix_vector_bound (matrix_prefix_product L k) (DistanceVector d x y) j < ε) :
    ∀ ε : ENNReal, 0 < ε →
      ∃ N : ℕ, ∀ k ≥ N,
        d j ((chain_prefix_operator ϕ k).func x)
          ((chain_prefix_operator ϕ k).func y) < ε := by
  intro ε hε
  rcases h_bound_zero ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro k hk
  exact lt_of_le_of_lt
    (chain_prefix_lip_distance_upper d ϕ U L hU_step hU_dom hL k x y hx hy j)
    (hN k hk)

/--
OET anchor: h-95d270a294f96c14
**命题 #h-95d270a294f96c14（一般链前缀乘积的渐近判据，有限初距下的条目衰减特例）**
If all source distances are finite and every source-to-target prefix entry
tends to zero, then the displayed L upper bound tends to zero.
-/
theorem chain_prefix_lip_upper_bound_tendsto_zero_of_entries
    [Fintype I]
    (L : ℕ → I → I → ENNReal) (x y : X) (j : I)
    (h_entry_zero :
      ∀ i : I,
        Filter.Tendsto
          (fun k : ℕ => matrix_prefix_product L k i j)
          Filter.atTop (nhds 0))
    (h_finite_dist : ∀ i : I, d i x y ≠ ⊤) :
    Filter.Tendsto
      (fun k : ℕ =>
        matrix_vector_bound (matrix_prefix_product L k) (DistanceVector d x y) j)
      Filter.atTop (nhds 0) := by
  dsimp [matrix_vector_bound, DistanceVector]
  have hsum :
      Filter.Tendsto
        (fun k : ℕ =>
          ∑ i : I, matrix_prefix_product L k i j * d i x y)
        Filter.atTop (nhds (∑ _i : I, (0 : ENNReal))) := by
    refine tendsto_finset_sum Finset.univ ?_
    intro i _hi
    have hmul :
        Filter.Tendsto
          (fun k : ℕ => matrix_prefix_product L k i j * d i x y)
          Filter.atTop (nhds ((0 : ENNReal) * d i x y)) :=
      ENNReal.Tendsto.mul_const (h_entry_zero i) (Or.inr (h_finite_dist i))
    simpa using hmul
  simpa using hsum

/--
OET anchor: h-95d270a294f96c14
**命题 #h-95d270a294f96c14（一般链前缀乘积的渐近判据，有限初距下的距离衰减特例）**
The entrywise decay special case implies decay of the target component
distance.
-/
theorem chain_prefix_lip_distance_tendsto_zero_of_entries
    [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (L : ℕ → I → I → ENNReal)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hL : ∀ n : ℕ, IsLipMatrix d (ϕ n) (U n) (L n))
    (x y : X) (hx : x ∈ U 0) (hy : y ∈ U 0) (j : I)
    (h_entry_zero :
      ∀ i : I,
        Filter.Tendsto
          (fun k : ℕ => matrix_prefix_product L k i j)
          Filter.atTop (nhds 0))
    (h_finite_dist : ∀ i : I, d i x y ≠ ⊤) :
    Filter.Tendsto
      (fun k : ℕ =>
        d j ((chain_prefix_operator ϕ k).func x)
          ((chain_prefix_operator ϕ k).func y))
      Filter.atTop (nhds 0) := by
  have h_upper :=
    chain_prefix_lip_upper_bound_tendsto_zero_of_entries d L x y j
      h_entry_zero h_finite_dist
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Filter.Tendsto (fun _k : ℕ => (0 : ENNReal)) Filter.atTop (nhds 0) from
      tendsto_const_nhds)
    h_upper
    (fun _k => zero_le _)
    (fun k =>
      chain_prefix_lip_distance_upper d ϕ U L hU_step hU_dom hL
        k x y hx hy j)

/-- Tail-unboundedness for an `ENNReal` sequence. -/
def PrefixUnboundedAlongTails (a : ℕ → ENNReal) : Prop :=
  ∀ B : ENNReal, B < ⊤ → ∀ N : ℕ, ∃ k ≥ N, B < a k

/-- Convergence to `⊤` for an `ENNReal` sequence, written as a tail condition. -/
def PrefixTendsToTop (a : ℕ → ENNReal) : Prop :=
  ∀ B : ENNReal, B < ⊤ → ∃ N : ℕ, ∀ n ≥ N, B < a n

/--
Tail-unbounded sequences remain tail-unbounded after multiplication by a
positive `ENNReal` constant.
-/
theorem prefix_unbounded_mul_const_of_pos
    (a : ℕ → ENNReal) (c : ENNReal)
    (ha : PrefixUnboundedAlongTails a) (hc : 0 < c) :
    PrefixUnboundedAlongTails (fun n => a n * c) := by
  intro B hB N
  have hB_ne_top : B ≠ ⊤ := ne_of_lt hB
  have hc_ne_zero : c ≠ 0 := ne_of_gt hc
  have hdiv_top : B / c < ⊤ := ENNReal.div_lt_top hB_ne_top hc_ne_zero
  rcases ha (B / c) hdiv_top N with ⟨n, hnN, hn⟩
  refine ⟨n, hnN, ?_⟩
  exact (ENNReal.div_lt_iff (Or.inl hc_ne_zero) (Or.inr hB_ne_top)).mp hn

/--
Sequences tending to `⊤` remain tending to `⊤` after multiplication by a
positive `ENNReal` constant.
-/
theorem prefix_tends_to_top_mul_const_of_pos
    (a : ℕ → ENNReal) (c : ENNReal)
    (ha : PrefixTendsToTop a) (hc : 0 < c) :
    PrefixTendsToTop (fun n => a n * c) := by
  intro B hB
  have hB_ne_top : B ≠ ⊤ := ne_of_lt hB
  have hc_ne_zero : c ≠ 0 := ne_of_gt hc
  have hdiv_top : B / c < ⊤ := ENNReal.div_lt_top hB_ne_top hc_ne_zero
  rcases ha (B / c) hdiv_top with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  exact (ENNReal.div_lt_iff (Or.inl hc_ne_zero) (Or.inr hB_ne_top)).mp (hN n hn)

/--
OET anchor: h-95d270a294f96c14
**命题 #h-95d270a294f96c14（一般链前缀乘积的渐近判据，K 子序列无界读法）**
If one K-prefix coefficient is unbounded along a subsequence and the
corresponding source distance is positive, then the target distance is
unbounded along the same subsequence.
-/
theorem chain_prefix_colip_distance_unbounded_of_entry_subsequence
    [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (K : ℕ → I → I → ENNReal)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hU0_ne : (U 0).Nonempty)
    (hK : ∀ n : ℕ, IsCoLipMatrix d (ϕ n) (U n) (K n))
    (subseq : ℕ → ℕ) (i j : I) (x y : X)
    (hx : x ∈ U 0) (hy : y ∈ U 0)
    (hd_pos : 0 < d i x y)
    (h_coeff_unbounded :
      PrefixUnboundedAlongTails
        (fun n : ℕ => matrix_prefix_product K (subseq n) i j)) :
    PrefixUnboundedAlongTails
      (fun n : ℕ =>
        d j ((chain_prefix_operator ϕ (subseq n)).func x)
          ((chain_prefix_operator ϕ (subseq n)).func y)) := by
  have h_lower_unbounded :
      PrefixUnboundedAlongTails
        (fun n : ℕ => matrix_prefix_product K (subseq n) i j * d i x y) :=
    prefix_unbounded_mul_const_of_pos
      (fun n : ℕ => matrix_prefix_product K (subseq n) i j)
      (d i x y) h_coeff_unbounded hd_pos
  intro B hB N
  rcases h_lower_unbounded B hB N with ⟨n, hnN, hBn⟩
  refine ⟨n, hnN, ?_⟩
  have h_single :
      matrix_prefix_product K (subseq n) i j * d i x y ≤
        matrix_vector_bound (matrix_prefix_product K (subseq n))
          (DistanceVector d x y) j := by
    dsimp [matrix_vector_bound, DistanceVector]
    exact Finset.single_le_sum
      (fun k _ => zero_le (matrix_prefix_product K (subseq n) k j * d k x y))
      (Finset.mem_univ i)
  have h_colip :=
    chain_prefix_colip_distance_lower d ϕ U K hU_step hU_dom hU0_ne hK
      (subseq n) x y hx hy j
  exact lt_of_lt_of_le hBn (le_trans h_single h_colip)

/--
OET anchor: h-95d270a294f96c14
**命题 #h-95d270a294f96c14（一般链前缀乘积的渐近判据，K 子序列趋向无穷读法）**
If one K-prefix coefficient tends to `⊤` along a subsequence and the
corresponding source distance is positive, then the target distance tends
to `⊤` along the same subsequence.
-/
theorem chain_prefix_colip_distance_tends_to_top_of_entry_subsequence
    [Fintype I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (K : ℕ → I → I → ENNReal)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hU0_ne : (U 0).Nonempty)
    (hK : ∀ n : ℕ, IsCoLipMatrix d (ϕ n) (U n) (K n))
    (subseq : ℕ → ℕ) (i j : I) (x y : X)
    (hx : x ∈ U 0) (hy : y ∈ U 0)
    (hd_pos : 0 < d i x y)
    (h_coeff_top :
      PrefixTendsToTop
        (fun n : ℕ => matrix_prefix_product K (subseq n) i j)) :
    PrefixTendsToTop
      (fun n : ℕ =>
        d j ((chain_prefix_operator ϕ (subseq n)).func x)
          ((chain_prefix_operator ϕ (subseq n)).func y)) := by
  have h_lower_top :
      PrefixTendsToTop
        (fun n : ℕ => matrix_prefix_product K (subseq n) i j * d i x y) :=
    prefix_tends_to_top_mul_const_of_pos
      (fun n : ℕ => matrix_prefix_product K (subseq n) i j)
      (d i x y) h_coeff_top hd_pos
  intro B hB
  rcases h_lower_top B hB with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hnN
  have h_single :
      matrix_prefix_product K (subseq n) i j * d i x y ≤
        matrix_vector_bound (matrix_prefix_product K (subseq n))
          (DistanceVector d x y) j := by
    dsimp [matrix_vector_bound, DistanceVector]
    exact Finset.single_le_sum
      (fun k _ => zero_le (matrix_prefix_product K (subseq n) k j * d k x y))
      (Finset.mem_univ i)
  have h_colip :=
    chain_prefix_colip_distance_lower d ϕ U K hU_step hU_dom hU0_ne hK
      (subseq n) x y hx hy j
  exact lt_of_lt_of_le (hN n hnN) (le_trans h_single h_colip)

/--
OET anchor: h-95d270a294f96c14
**命题（一般链前缀乘积的渐近判据，L 证书分支）**

正文有限非空指标集、非空初始域与正整数前缀语境下的 L 分支包装。
-/
theorem general_chain_prefix_lip_certificate_textbook
    [Fintype I] [Nonempty I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (L : ℕ → I → I → ENNReal)
    (hU0_ne : (U 0).Nonempty)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hL : ∀ n : ℕ, IsLipMatrix d (ϕ n) (U n) (L n)) :
    ∀ k : ℕ, 0 < k →
      IsLipMatrix d (chain_prefix_operator ϕ k) (U 0)
          (matrix_prefix_product L k) ∧
        ∀ x ∈ U 0, ∀ y ∈ U 0, ∀ j : I,
          d j ((chain_prefix_operator ϕ k).func x)
              ((chain_prefix_operator ϕ k).func y) ≤
            matrix_vector_bound (matrix_prefix_product L k)
              (DistanceVector d x y) j := by
  have _ := hU0_ne
  intro k _hk
  have hcert := chain_prefix_lip_matrix d ϕ U L hU_step hU_dom hL k
  exact ⟨hcert, hcert.2⟩

/--
OET anchor: h-95d270a294f96c14
**命题（一般链前缀乘积的渐近判据，L 渐近分支）**

对固定点对与目标分量，前缀上界趋零推出目标距离趋零；有限初始距离与
逐条目衰减是该条件的充分条件。
-/
theorem general_chain_prefix_lip_decay_textbook
    [Fintype I] [Nonempty I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (L : ℕ → I → I → ENNReal)
    (hU0_ne : (U 0).Nonempty)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hL : ∀ n : ℕ, IsLipMatrix d (ϕ n) (U n) (L n))
    (x y : X) (hx : x ∈ U 0) (hy : y ∈ U 0) (j : I) :
    ((∀ ε : ENNReal, 0 < ε →
        ∃ N : ℕ, ∀ k ≥ N,
          matrix_vector_bound (matrix_prefix_product L k)
              (DistanceVector d x y) j < ε) →
      ∀ ε : ENNReal, 0 < ε →
        ∃ N : ℕ, ∀ k ≥ N,
          d j ((chain_prefix_operator ϕ k).func x)
              ((chain_prefix_operator ϕ k).func y) < ε) ∧
    ((∀ i : I, d i x y ≠ ⊤) →
      (∀ i : I,
        Filter.Tendsto (fun k : ℕ => matrix_prefix_product L k i j)
          Filter.atTop (nhds 0)) →
      Filter.Tendsto
        (fun k : ℕ =>
          d j ((chain_prefix_operator ϕ k).func x)
            ((chain_prefix_operator ϕ k).func y))
        Filter.atTop (nhds 0)) := by
  have _ := hU0_ne
  constructor
  · exact chain_prefix_lip_distance_tends_zero_of_upper_bound
      d ϕ U L hU_step hU_dom hL x y hx hy j
  · intro hfinite hentries
    exact chain_prefix_lip_distance_tendsto_zero_of_entries
      d ϕ U L hU_step hU_dom hL x y hx hy j hentries hfinite

/--
OET anchor: h-95d270a294f96c14
**命题（一般链前缀乘积的渐近判据，K 证书分支）**

正文有限非空指标集、非空初始域与正整数前缀语境下的 K 分支包装。
-/
theorem general_chain_prefix_colip_certificate_textbook
    [Fintype I] [Nonempty I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (K : ℕ → I → I → ENNReal)
    (hU0_ne : (U 0).Nonempty)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hK : ∀ n : ℕ, IsCoLipMatrix d (ϕ n) (U n) (K n)) :
    ∀ k : ℕ, 0 < k →
      IsCoLipMatrix d (chain_prefix_operator ϕ k) (U 0)
          (matrix_prefix_product K k) ∧
        ∀ x ∈ U 0, ∀ y ∈ U 0, ∀ j : I,
          matrix_vector_bound (matrix_prefix_product K k)
              (DistanceVector d x y) j ≤
            d j ((chain_prefix_operator ϕ k).func x)
              ((chain_prefix_operator ϕ k).func y) := by
  intro k _hk
  have hcert := chain_prefix_colip_matrix d ϕ U K
    hU_step hU_dom hU0_ne hK k
  exact ⟨hcert, hcert.2.2⟩

/--
OET anchor: h-95d270a294f96c14
**命题（一般链前缀乘积的渐近判据，K 子序列分支）**

正整数严格递增子序列上一项 K 前缀系数趋向无穷且对应源距离为正时，
目标分量距离沿同一子序列趋向无穷。
-/
theorem general_chain_prefix_colip_subsequence_textbook
    [Fintype I] [Nonempty I]
    (ϕ : ℕ → Operator X bot) (U : ℕ → Set X)
    (K : ℕ → I → I → ENNReal)
    (hU0_ne : (U 0).Nonempty)
    (hU_step : ∀ n : ℕ, U (n + 1) = (ϕ n).func '' U n)
    (hU_dom : ∀ n : ℕ, U n ⊆ dom (ϕ n))
    (hK : ∀ n : ℕ, IsCoLipMatrix d (ϕ n) (U n) (K n))
    (subseq : ℕ → ℕ) (hsubseq : StrictMono subseq)
    (hpositive : ∀ n : ℕ, 0 < subseq n)
    (i j : I) (x y : X) (hx : x ∈ U 0) (hy : y ∈ U 0)
    (hd_pos : 0 < d i x y)
    (h_coeff_top : PrefixTendsToTop
      (fun n : ℕ => matrix_prefix_product K (subseq n) i j)) :
    PrefixTendsToTop
      (fun n : ℕ =>
        d j ((chain_prefix_operator ϕ (subseq n)).func x)
          ((chain_prefix_operator ϕ (subseq n)).func y)) := by
  have _ := hsubseq
  have _ := hpositive
  exact chain_prefix_colip_distance_tends_to_top_of_entry_subsequence
    d ϕ U K hU_step hU_dom hU0_ne hK subseq i j x y hx hy hd_pos h_coeff_top

end

end formal_oet.vol_01.ch_04_operator_chain_calculus
