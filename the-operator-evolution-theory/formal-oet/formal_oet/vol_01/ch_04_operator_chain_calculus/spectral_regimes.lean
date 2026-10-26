import formal_oet.vol_01.ch_04_operator_chain_calculus.entropy_recurrence
import formal_oet.vol_01.ch_04_operator_chain_calculus.distance_recurrence
import formal_oet.vol_01.ch_04_operator_chain_calculus.k_spectrum
import formal_oet.vol_01.ch_04_operator_chain_calculus.prefix_products
import formal_oet.vol_01.ch_04_operator_chain_calculus.finite_matrix_spectral
import formal_oet.vol_01.ch_02_operator_bounds.matrix_composition

namespace formal_oet.vol_01.ch_04_operator_chain_calculus

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy

open scoped BigOperators


variable {X I : Type} {bot : X}
local instance instDecidableEqISpectralRegimes : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-cb1aac0882bde4ae
**命题 #h-cb1aac0882bde4ae（常系数 L/K 证书的谱充分判据）**
L 分支中，谱半径小于一时，Gelfand 公式推出常矩阵幂逐条目趋零。
-/
theorem l_spectrum_subunit_entries_tend_zero [Fintype I]
    (L : I → I → ENNReal) (hfinite : FiniteValuedMatrix L)
    (hrho : ennreal_matrix_spectral_radius L < 1) :
    ∀ i j : I, Filter.Tendsto
      (fun k => matrix_prefix_product (fun _ : ℕ => L) k i j)
      Filter.atTop (nhds 0) :=
  prefix_product_entries_tendsto_zero_of_spectral_radius_lt_one L hfinite hrho

/-- A self-composition chain preserves an invariant subset. -/
theorem constant_chain_maps_to_invariant
    (ϕ : Operator X bot) (U : Set X)
    (hmap : Set.MapsTo ϕ.func U U) :
    ∀ k : ℕ, Set.MapsTo (chain_prefix_operator (fun _ : ℕ => ϕ) k).func U U := by
  intro k
  induction k with
  | zero =>
      intro x hx
      simpa [chain_prefix_operator] using hx
  | succ n ih =>
      intro x hx
      have hx_n : (chain_prefix_operator (fun _ : ℕ => ϕ) n).func x ∈ U := ih hx
      simpa [chain_prefix_operator] using hmap hx_n

/--
OET anchor: h-cb1aac0882bde4ae
**命题 #h-cb1aac0882bde4ae（常系数 L/K 证书的谱充分判据，L 幂证书）**
If a single Lip certificate is valid on an invariant domain, then its ordered
constant prefix products certify all self-composition prefixes.
-/
theorem constant_lip_matrix_power_certificate
    [Fintype I]
    (ϕ : Operator X bot) (U : Set X) (L : I → I → ENNReal)
    (hmap : Set.MapsTo ϕ.func U U)
    (hL : IsLipMatrix d ϕ U L) :
    ∀ k : ℕ,
      IsLipMatrix d (chain_prefix_operator (fun _ : ℕ => ϕ) k) U
        (matrix_prefix_product (fun _ : ℕ => L) k) := by
  intro k
  induction k with
  | zero =>
      exact right_chain_lip_matrix d [] U matrix_id
        (RightChainLipBounded.nil U
          (fun x hx hxb => by
            have hxdom : x ∈ dom ϕ := hL.1 hx
            dsimp [dom] at hxdom
            rw [hxb, ϕ.preserves_bot] at hxdom
            exact hxdom rfl))
  | succ n ih =>
      have h_im :
          ∀ x ∈ U, (chain_prefix_operator (fun _ : ℕ => ϕ) n).func x ∈ U :=
        constant_chain_maps_to_invariant ϕ U hmap n
      have hcomp :=
        lip_matrix_comp d (chain_prefix_operator (fun _ : ℕ => ϕ) n) ϕ
          U U (matrix_prefix_product (fun _ : ℕ => L) n) L
          h_im ih hL
      simpa [chain_prefix_operator, matrix_prefix_product] using hcomp

/--
OET anchor: h-cb1aac0882bde4ae
**命题 #h-cb1aac0882bde4ae（常系数 L/K 证书的谱充分判据，L 幂点态上界）**
The constant Lip power certificate gives the displayed pointwise upper bound.
-/
theorem constant_lip_power_distance_upper
    [Fintype I]
    (ϕ : Operator X bot) (U : Set X) (L : I → I → ENNReal)
    (hmap : Set.MapsTo ϕ.func U U)
    (hL : IsLipMatrix d ϕ U L)
    (k : ℕ) (x y : X) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j ((chain_prefix_operator (fun _ : ℕ => ϕ) k).func x)
        ((chain_prefix_operator (fun _ : ℕ => ϕ) k).func y) ≤
      matrix_vector_bound (matrix_prefix_product (fun _ : ℕ => L) k)
        (DistanceVector d x y) j := by
  exact (constant_lip_matrix_power_certificate d ϕ U L hmap hL k).2 x hx y hy j

/--
OET anchor: h-cb1aac0882bde4ae
**命题 #h-cb1aac0882bde4ae（常系数 L/K 证书的谱充分判据，K 幂证书）**
If a single co-Lip certificate is valid on an invariant domain, then its
ordered constant prefix products certify all self-composition prefixes.
-/
theorem constant_colip_matrix_power_certificate
    [Fintype I]
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hmap : Set.MapsTo ϕ.func U U)
    (hK : IsCoLipMatrix d ϕ U K) :
    ∀ k : ℕ,
      IsCoLipMatrix d (chain_prefix_operator (fun _ : ℕ => ϕ) k) U
        (matrix_prefix_product (fun _ : ℕ => K) k) := by
  intro k
  induction k with
  | zero =>
      exact right_chain_colip_matrix d [] U matrix_id
        (RightChainCoLipBounded.nil U
          (fun x hx hxb => by
            have hxdom : x ∈ dom ϕ := hK.2.1 hx
            dsimp [dom] at hxdom
            rw [hxb, ϕ.preserves_bot] at hxdom
            exact hxdom rfl)
          hK.1)
  | succ n ih =>
      have h_im :
          ∀ x ∈ U, (chain_prefix_operator (fun _ : ℕ => ϕ) n).func x ∈ U :=
        constant_chain_maps_to_invariant ϕ U hmap n
      have hcomp :=
        colip_matrix_comp d (chain_prefix_operator (fun _ : ℕ => ϕ) n) ϕ
          U U (matrix_prefix_product (fun _ : ℕ => K) n) K
          h_im ih hK
      simpa [chain_prefix_operator, matrix_prefix_product] using hcomp

/--
OET anchor: h-cb1aac0882bde4ae
**命题 #h-cb1aac0882bde4ae（常系数 L/K 证书的谱充分判据，K 幂点态下界）**
The constant co-Lip power certificate gives the displayed pointwise lower bound.
-/
theorem constant_colip_power_distance_lower
    [Fintype I]
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hmap : Set.MapsTo ϕ.func U U)
    (hK : IsCoLipMatrix d ϕ U K)
    (k : ℕ) (x y : X) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    matrix_vector_bound (matrix_prefix_product (fun _ : ℕ => K) k)
        (DistanceVector d x y) j ≤
      d j ((chain_prefix_operator (fun _ : ℕ => ϕ) k).func x)
        ((chain_prefix_operator (fun _ : ℕ => ϕ) k).func y) := by
  exact (constant_colip_matrix_power_certificate d ϕ U K hmap hK k).2.2
    x hx y hy j

/--
OET anchor: h-cb1aac0882bde4ae
**命题 #h-cb1aac0882bde4ae（常系数 L/K 证书的谱充分判据，K 子序列趋向无穷）**
If one constant K-power coefficient tends to `⊤` along a subsequence and the
source distance is positive, then the target distance tends to `⊤` along that
subsequence.
-/
theorem constant_colip_power_distance_tends_to_top_of_entry_subsequence
    [Fintype I]
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hmap : Set.MapsTo ϕ.func U U)
    (hK : IsCoLipMatrix d ϕ U K)
    (subseq : ℕ → ℕ) (i j : I) (x y : X)
    (hx : x ∈ U) (hy : y ∈ U)
    (hd_pos : 0 < d i x y)
    (h_coeff_top :
      PrefixTendsToTop
        (fun n : ℕ => matrix_prefix_product (fun _ : ℕ => K) (subseq n) i j)) :
    PrefixTendsToTop
      (fun n : ℕ =>
        d j ((chain_prefix_operator (fun _ : ℕ => ϕ) (subseq n)).func x)
          ((chain_prefix_operator (fun _ : ℕ => ϕ) (subseq n)).func y)) := by
  have h_lower_top :
      PrefixTendsToTop
        (fun n : ℕ =>
          matrix_prefix_product (fun _ : ℕ => K) (subseq n) i j * d i x y) :=
    prefix_tends_to_top_mul_const_of_pos
      (fun n : ℕ => matrix_prefix_product (fun _ : ℕ => K) (subseq n) i j)
      (d i x y) h_coeff_top hd_pos
  intro B hB
  rcases h_lower_top B hB with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hnN
  have h_single :
      matrix_prefix_product (fun _ : ℕ => K) (subseq n) i j * d i x y ≤
        matrix_vector_bound (matrix_prefix_product (fun _ : ℕ => K) (subseq n))
          (DistanceVector d x y) j := by
    dsimp [matrix_vector_bound, DistanceVector]
    exact Finset.single_le_sum
      (fun k _ =>
        zero_le (matrix_prefix_product (fun _ : ℕ => K) (subseq n) k j * d k x y))
      (Finset.mem_univ i)
  have h_colip :=
    constant_colip_power_distance_lower d ϕ U K hmap hK
      (subseq n) x y hx hy j
  exact lt_of_lt_of_le (hN n hnN) (le_trans h_single h_colip)

/--
若点对落入极小零化半径以下，则下一步在目标分量精确零化。

将统一零化下界用于当前点对，得到单步截断。
-/
theorem zeroing_step_of_min_annihilation_radius
    (ϕ : Operator X bot) (U : Set X) (i j : I) (ν : ENNReal)
    (hν_le : ν ≤ min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hxy : d i x y < ν) :
    d j (ϕ.func x) (ϕ.func y) = 0 := by
  have h_min_le_ann :
      min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U ≤
        annihilation_radius d ϕ i (singleton_nonempty_finset j) U y :=
    iInf₂_le y hy
  have hxy_ann : d i x y <
      annihilation_radius d ϕ i (singleton_nonempty_finset j) U y :=
    lt_of_lt_of_le hxy (le_trans hν_le h_min_le_ann)
  rcases lt_iSup_iff.mp hxy_ann with ⟨r, hr⟩
  rcases lt_iSup_iff.mp hr with ⟨hr_fin_pos, hr'⟩
  rcases lt_iSup_iff.mp hr' with ⟨h_subset, hxy_r⟩
  have hx_ball : x ∈ OpenBall d i y r ∩ U := ⟨hxy_r, hx⟩
  exact distance_recurrence_zeroing_of_ball d ϕ U i j y x r hx_ball h_subset

/--
OET anchor: h-cb1aac0882bde4ae
**命题 #h-cb1aac0882bde4ae（常系数 L/K 证书的谱充分判据）**
K 分支中，谱半径大于一时，标准有限矩阵谱理论推出某条目沿尾部无界。
-/
theorem k_spectrum_superunit_limsup [Fintype I]
    (K : I → I → ENNReal) (hfinite : FiniteValuedMatrix K)
    (hrho : 1 < ennreal_matrix_spectral_radius K) :
    ∃ i j : I, UnboundedAlongTails
      (fun k => matrix_prefix_product (fun _ : ℕ => K) k i j) :=
  prefix_product_has_unbounded_entry_of_one_lt_spectral_radius K hfinite hrho

/-- A canonical positive strictly increasing index sequence extracted from a
tail-unbounded `ENNReal` sequence. -/
noncomputable def unbounded_subsequence_index
    (a : ℕ → ENNReal) (ha : UnboundedAlongTails a) : ℕ → ℕ
  | 0 => Classical.choose (ha 0 ENNReal.zero_lt_top 1)
  | n + 1 => Classical.choose
      (ha (n + 1 : ℕ) (ENNReal.natCast_lt_top (n + 1))
        (unbounded_subsequence_index a ha n + 1))

/-- Every selected index is positive. -/
theorem unbounded_subsequence_index_positive
    (a : ℕ → ENNReal) (ha : UnboundedAlongTails a) (n : ℕ) :
    0 < unbounded_subsequence_index a ha n := by
  cases n with
  | zero =>
      have hspec := Classical.choose_spec (ha 0 ENNReal.zero_lt_top 1)
      simpa only [unbounded_subsequence_index] using
        lt_of_lt_of_le Nat.zero_lt_one hspec.1
  | succ n =>
      have hspec := Classical.choose_spec
        (ha (n + 1 : ℕ) (ENNReal.natCast_lt_top (n + 1))
          (unbounded_subsequence_index a ha n + 1))
      have hpos : 0 < Classical.choose
          (ha (n + 1 : ℕ) (ENNReal.natCast_lt_top (n + 1))
            (unbounded_subsequence_index a ha n + 1)) :=
        lt_of_lt_of_le Nat.zero_lt_one
          (le_trans (Nat.le_add_left 1 _) hspec.1)
      simpa only [unbounded_subsequence_index] using hpos

/-- The `n`th selected value exceeds the finite threshold `n`. -/
theorem unbounded_subsequence_index_value
    (a : ℕ → ENNReal) (ha : UnboundedAlongTails a) (n : ℕ) :
    (n : ENNReal) < a (unbounded_subsequence_index a ha n) := by
  cases n with
  | zero =>
      have hspec := Classical.choose_spec (ha 0 ENNReal.zero_lt_top 1)
      simpa only [unbounded_subsequence_index, Nat.cast_zero] using hspec.2
  | succ n =>
      have hspec := Classical.choose_spec
        (ha (n + 1 : ℕ) (ENNReal.natCast_lt_top (n + 1))
          (unbounded_subsequence_index a ha n + 1))
      simpa only [unbounded_subsequence_index] using hspec.2

/-- The selected index sequence is strictly increasing. -/
theorem unbounded_subsequence_index_strict_mono
    (a : ℕ → ENNReal) (ha : UnboundedAlongTails a) :
    StrictMono (unbounded_subsequence_index a ha) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hspec := Classical.choose_spec
    (ha (n + 1 : ℕ) (ENNReal.natCast_lt_top (n + 1))
      (unbounded_subsequence_index a ha n + 1))
  exact lt_of_lt_of_le (Nat.lt_succ_self _) hspec.1

/-- Every tail-unbounded `ENNReal` sequence admits a positive strictly
increasing subsequence tending to `⊤`. -/
theorem unbounded_along_tails_has_tendsto_top_subsequence
    (a : ℕ → ENNReal) (ha : UnboundedAlongTails a) :
    ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ (∀ n : ℕ, 0 < subseq n) ∧
      PrefixTendsToTop (fun n : ℕ => a (subseq n)) := by
  let subseq := unbounded_subsequence_index a ha
  refine ⟨subseq, unbounded_subsequence_index_strict_mono a ha, ?_, ?_⟩
  · intro n
    exact unbounded_subsequence_index_positive a ha n
  · intro B hB
    have hB_ne_top : B ≠ ⊤ := ne_of_lt hB
    obtain ⟨N, hN⟩ := exists_nat_gt B.toReal
    have hB_cast : B < (N : ENNReal) := by
      apply (ENNReal.toReal_lt_toReal hB_ne_top (ENNReal.natCast_ne_top N)).mp
      simpa using hN
    refine ⟨N, ?_⟩
    intro n hn
    have hNn : (N : ENNReal) ≤ (n : ENNReal) := by
      exact_mod_cast hn
    exact hB_cast.trans_le
      (hNn.trans (le_of_lt (unbounded_subsequence_index_value a ha n)))

/--
具体 K 幂系数沿尾部无界且源分量点对正距离时，目标分量距离不可能最终精确归零。
-/
theorem k_spectrum_obstructs_exact_zeroing [Fintype I]
    (ϕ : Operator X bot) (U : Set X) (Kpow : ℕ → I → I → ENNReal)
    (i j : I) (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hK_iter :
      ∀ n : ℕ, IsCoLipMatrix d (OperatorChain (List.replicate n ϕ)) U (Kpow n))
    (h_coeff_unbounded : UnboundedAlongTails (fun n : ℕ => Kpow n i j))
    (hd_pos : 0 < d i x y) :
    UnboundedAlongTails
        (fun n : ℕ =>
          d j ((OperatorChain (List.replicate n ϕ)).func x)
            ((OperatorChain (List.replicate n ϕ)).func y)) ∧
      ¬ EventuallyZero
        (fun n : ℕ =>
          d j ((OperatorChain (List.replicate n ϕ)).func x)
            ((OperatorChain (List.replicate n ϕ)).func y)) := by
  let lower : ℕ → ENNReal := fun n => Kpow n i j * d i x y
  let dist : ℕ → ENNReal :=
    fun n =>
      d j ((OperatorChain (List.replicate n ϕ)).func x)
        ((OperatorChain (List.replicate n ϕ)).func y)
  have h_lower_unbounded :
      UnboundedAlongTails (fun n : ℕ => Kpow n i j * d i x y) :=
    unbounded_mul_const_of_pos (fun n : ℕ => Kpow n i j) (d i x y)
      h_coeff_unbounded hd_pos
  have h_lower_le_dist : ∀ n : ℕ, lower n ≤ dist n := by
    intro n
    have h_single :
        lower n ≤ matrix_vector_bound (Kpow n) (DistanceVector d x y) j := by
      dsimp [lower, matrix_vector_bound, DistanceVector]
      exact Finset.single_le_sum
        (fun k _ => zero_le (Kpow n k j * d k x y)) (Finset.mem_univ i)
    have h_colip :
        matrix_vector_bound (Kpow n) (DistanceVector d x y) j ≤ dist n := by
      dsimp [dist]
      exact distance_recurrence_colip_lower d
        (OperatorChain (List.replicate n ϕ)) U (Kpow n) (hK_iter n) x hx y hy j
    exact le_trans h_single h_colip
  have h_dist_unbounded : UnboundedAlongTails dist := by
    intro B hB N
    rcases h_lower_unbounded B hB N with ⟨n, hnN, hBn⟩
    exact ⟨n, hnN, lt_of_lt_of_le hBn (h_lower_le_dist n)⟩
  have hpositive : HasPositiveLowerSubsequence lower := by
    intro N
    rcases h_lower_unbounded 0 ENNReal.coe_lt_top N with ⟨n, hnN, hnpos⟩
    exact ⟨n, hnN, hnpos⟩
  exact ⟨h_dist_unbounded,
    positive_lower_subsequence_obstructs_eventual_zero lower dist hpositive h_lower_le_dist⟩

/--
OET anchor: h-cb1aac0882bde4ae
**命题（常系数 L/K 证书的谱充分判据，L 收缩充分证书）**

正文的有限值常系数 L 证书与谱半径小于一共同推出所有有限初始距离
点对的逐分量距离趋零。
-/
theorem constant_lip_subunit_spectral_criterion_textbook
    [Fintype I] [Nonempty I]
    (ϕ : Operator X bot) (U : Set X) (L : I → I → ENNReal)
    (hU_dom : U ⊆ dom ϕ) (hmap : Set.MapsTo ϕ.func U U)
    (hL : IsLipMatrix d ϕ U L) (hfinite : FiniteValuedMatrix L)
    (hrho : ennreal_matrix_spectral_radius L < 1) :
    (∀ k : ℕ, 0 < k →
      IsLipMatrix d (chain_prefix_operator (fun _ : ℕ => ϕ) k) U
          (matrix_prefix_product (fun _ : ℕ => L) k) ∧
        ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
          d j ((chain_prefix_operator (fun _ : ℕ => ϕ) k).func x)
              ((chain_prefix_operator (fun _ : ℕ => ϕ) k).func y) ≤
            matrix_vector_bound
              (matrix_prefix_product (fun _ : ℕ => L) k)
              (DistanceVector d x y) j) ∧
      ∀ x ∈ U, ∀ y ∈ U, (∀ i : I, d i x y ≠ ⊤) → ∀ j : I,
        Filter.Tendsto
          (fun k : ℕ =>
            d j ((chain_prefix_operator (fun _ : ℕ => ϕ) k).func x)
              ((chain_prefix_operator (fun _ : ℕ => ϕ) k).func y))
          Filter.atTop (nhds 0) := by
  have _ := hU_dom
  constructor
  · intro k _hk
    have hcert := constant_lip_matrix_power_certificate d ϕ U L hmap hL k
    exact ⟨hcert, hcert.2⟩
  · intro x hx y hy hfinite_dist j
    have hentries : ∀ i : I, Filter.Tendsto
        (fun k : ℕ => matrix_prefix_product (fun _ : ℕ => L) k i j)
        Filter.atTop (nhds 0) :=
      fun i => prefix_product_entries_tendsto_zero_of_spectral_radius_lt_one
        L hfinite hrho i j
    have hupper := chain_prefix_lip_upper_bound_tendsto_zero_of_entries
      d (fun _ : ℕ => L) x y j hentries hfinite_dist
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Filter.Tendsto (fun _k : ℕ => (0 : ENNReal))
          Filter.atTop (nhds 0) from tendsto_const_nhds)
      hupper
      (fun _k => zero_le _)
      (fun k => constant_lip_power_distance_upper
        d ϕ U L hmap hL k x y hx hy j)

/--
OET anchor: h-cb1aac0882bde4ae
**命题（常系数 L/K 证书的谱充分判据，K 子序列扩张证书）**

谱半径大于一给出一个固定矩阵条目及正整数严格递增子序列；任一在对应
源分量上具有正距离的点对，其目标分量距离沿同一子序列趋向无穷。
-/
theorem constant_colip_superunit_spectral_criterion_textbook
    [Fintype I] [Nonempty I]
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hU_dom : U ⊆ dom ϕ) (hmap : Set.MapsTo ϕ.func U U)
    (hK : IsCoLipMatrix d ϕ U K) (hfinite : FiniteValuedMatrix K)
    (hrho : 1 < ennreal_matrix_spectral_radius K) :
    (∀ k : ℕ, 0 < k →
      IsCoLipMatrix d (chain_prefix_operator (fun _ : ℕ => ϕ) k) U
          (matrix_prefix_product (fun _ : ℕ => K) k) ∧
        ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
          matrix_vector_bound
              (matrix_prefix_product (fun _ : ℕ => K) k)
              (DistanceVector d x y) j ≤
            d j ((chain_prefix_operator (fun _ : ℕ => ϕ) k).func x)
              ((chain_prefix_operator (fun _ : ℕ => ϕ) k).func y)) ∧
      ∃ i j : I, ∃ subseq : ℕ → ℕ,
        StrictMono subseq ∧ (∀ n : ℕ, 0 < subseq n) ∧
          PrefixTendsToTop
            (fun n : ℕ =>
              matrix_prefix_product (fun _ : ℕ => K) (subseq n) i j) ∧
          ∀ x ∈ U, ∀ y ∈ U, 0 < d i x y →
            PrefixTendsToTop
              (fun n : ℕ =>
                d j ((chain_prefix_operator (fun _ : ℕ => ϕ) (subseq n)).func x)
                  ((chain_prefix_operator (fun _ : ℕ => ϕ) (subseq n)).func y)) := by
  have _ := hU_dom
  constructor
  · intro k _hk
    have hcert := constant_colip_matrix_power_certificate d ϕ U K hmap hK k
    exact ⟨hcert, hcert.2.2⟩
  · rcases prefix_product_has_unbounded_entry_of_one_lt_spectral_radius
      K hfinite hrho with
      ⟨i, j, hunbounded⟩
    rcases unbounded_along_tails_has_tendsto_top_subsequence
        (fun k => matrix_prefix_product (fun _ : ℕ => K) k i j) hunbounded with
      ⟨subseq, hmono, hpositive, htends⟩
    refine ⟨i, j, subseq, hmono, hpositive, htends, ?_⟩
    intro x hx y hy hd_pos
    exact constant_colip_power_distance_tends_to_top_of_entry_subsequence
      d ϕ U K hmap hK subseq i j x y hx hy hd_pos htends

end

end formal_oet.vol_01.ch_04_operator_chain_calculus
