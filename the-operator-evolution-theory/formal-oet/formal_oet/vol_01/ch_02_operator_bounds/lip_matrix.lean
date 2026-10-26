import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Basic


namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations
open Finset

variable {X I : Type} {bot : X} [Fintype I]
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-af85899693cc8750
**定义（子集受限 Lip 矩阵）**：
`IsLipMatrix ϕ U L` 表示矩阵 L = (L_{i, j}) 是算子 ϕ 在子集 U 上的合法 Lipschitz 矩阵。
$$d_j(\phi(x), \phi(y)) \leq \sum_{i \in I} L_{i \to j} \cdot d_i(x, y)$$
这里 L i j 表示 $L_{i \to j}$。
-/
def IsLipMatrix (ϕ : Operator X bot) (U : Set X) (L : I → I → ENNReal) : Prop :=
  U ⊆ dom ϕ ∧
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

/--
OET anchor: h-4ff5c58d71e1651f
**引理（受限 Lip 矩阵族的单调性）**
限制域缩小时，合法 Lip 矩阵族按包含关系扩大。
-/
theorem restricted_lip_matrix_family_antitone (ϕ : Operator X bot) (U V : Set X)
    (hUV : U ⊆ V) :
    {L | IsLipMatrix d ϕ V L} ⊆ {L | IsLipMatrix d ϕ U L} := by
  intro L hL
  refine ⟨hUV.trans hL.1, ?_⟩
  intro x hx y hy j
  exact hL.2 x (hUV hx) y (hUV hy) j

/--
OET anchor: h-4ff5c58d71e1651f
全定义域上的合法 Lip 矩阵在任意子集上仍然合法。
-/
theorem global_lip_matrix_family_subset (ϕ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕ) :
    {L | IsLipMatrix d ϕ (dom ϕ) L} ⊆ {L | IsLipMatrix d ϕ U L} :=
  restricted_lip_matrix_family_antitone d ϕ U (dom ϕ) hU

/--
OET anchor: h-af85899693cc8750
**定义（子集受限 co-Lipschitz 矩阵）**：
`IsCoLipMatrix ϕ U K` 表示矩阵 K = (K_{i, j}) 是算子 ϕ 在子集 U 上的合法 co-Lipschitz 矩阵。
$$d_j(\phi(x), \phi(y)) \geq \sum_{i \in I} K_{i \to j} \cdot d_i(x, y)$$
-/
def IsCoLipMatrix (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal) : Prop :=
  U.Nonempty ∧
  U ⊆ dom ϕ ∧
  ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≥ ∑ i : I, K i j * d i x y

/--
OET anchor: h-893b1d33535f7245
**引理（受限 co-Lip 矩阵族的单调性）**
限制到非空子集时，合法 co-Lip 矩阵族按包含关系扩大。
-/
theorem restricted_colip_matrix_family_antitone (ϕ : Operator X bot) (U V : Set X)
    (hU_ne : U.Nonempty) (hUV : U ⊆ V) :
    {K | IsCoLipMatrix d ϕ V K} ⊆ {K | IsCoLipMatrix d ϕ U K} := by
  intro K hK
  refine ⟨hU_ne, hUV.trans hK.2.1, ?_⟩
  intro x hx y hy j
  exact hK.2.2 x (hUV hx) y (hUV hy) j

/--
OET anchor: h-893b1d33535f7245
全定义域上的合法 co-Lip 矩阵在任意非空子集上仍然合法。
-/
theorem global_colip_matrix_family_subset (ϕ : Operator X bot) (U : Set X)
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) :
    {K | IsCoLipMatrix d ϕ (dom ϕ) K} ⊆ {K | IsCoLipMatrix d ϕ U K} :=
  restricted_colip_matrix_family_antitone d ϕ U (dom ϕ) hU_ne hU

/--
OET anchor: h-c4369c63c86cbacf
**注（单分量情形下的标量 Lip 界）**
当指标集只有一个分量时，Lip 矩阵不等式退化为单个标量不等式。
-/
theorem single_component_lip_matrix_ineq [Subsingleton I] (ϕ : Operator X bot) (U : Set X)
    (L : I → I → ENNReal) (i : I) (hL : IsLipMatrix d ϕ U L) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  intro x hx y hy
  rcases hL with ⟨_, hineq⟩
  have h := hineq x hx y hy i
  have hsum_eq : (∑ k : I, L k i * d k x y) = L i i * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hk
      have hki : k = i := Subsingleton.elim k i
      exact (hk hki).elim
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simpa [hsum_eq] using h

/--
OET anchor: h-88784dcbfff0ea66
**注（co-Lip 通道退化的点对判据）**
若某个点对在输出分量上归零而在源分量上有正距离，则该 co-Lip 通道系数必须为零。
-/
theorem colip_entry_eq_zero_of_output_zero_input_pos (ϕ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (i j : I) (x y : X)
    (hK : IsCoLipMatrix d ϕ U K) (hx : x ∈ U) (hy : y ∈ U)
    (hout : d j (ϕ.func x) (ϕ.func y) = 0) (hin : 0 < d i x y) :
    K i j = 0 := by
  rcases hK with ⟨_, _, hineq⟩
  have hsum_le_zero : (∑ k : I, K k j * d k x y) ≤ 0 := by
    simpa [hout] using hineq x hx y hy j
  have hterm_le_sum : K i j * d i x y ≤ ∑ k : I, K k j * d k x y := by
    simpa using
      (Finset.single_le_sum (s := Finset.univ) (a := i)
        (f := fun k : I => K k j * d k x y)
        (by
          intro _ _
          exact zero_le _)
        (Finset.mem_univ i))
  have hterm_zero : K i j * d i x y = 0 :=
    le_antisymm (le_trans hterm_le_sum hsum_le_zero) (zero_le _)
  by_contra hne
  have hpos : 0 < K i j := lt_of_le_of_ne (zero_le _) (Ne.symm hne)
  have hmul_pos : 0 < K i j * d i x y := ENNReal.mul_pos hne (ne_of_gt hin)
  exact (not_lt_of_ge (by rw [hterm_zero]) hmul_pos)

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-b959b42f25710105
**命题 #h-b959b42f25710105（两个算子的点对像距扰动界，点对像距双向扰动）**
If two operators are pointwise close on `U`, then pairwise image distances for
the second are bounded by those for the first plus the two endpoint errors.
-/
theorem operator_pair_image_distance_perturbation
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (eps : I → ENNReal)
    (hdom1 : U ⊆ dom ϕ1) (hdom2 : U ⊆ dom ϕ2)
    (hclose : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ eps j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤
        d j (ϕ1.func x) (ϕ1.func y) + (eps j + eps j) := by
  have _ := hdom1
  have _ := hdom2
  intro x hx y hy j
  have htri₁ :=
    (hd j).triangle (ϕ2.func x) (ϕ1.func x) (ϕ2.func y)
  have htri₂ :=
    (hd j).triangle (ϕ1.func x) (ϕ1.func y) (ϕ2.func y)
  have hleft : d j (ϕ2.func x) (ϕ1.func x) ≤ eps j := by
    rw [(hd j).symm (ϕ2.func x) (ϕ1.func x)]
    exact hclose x hx j
  have hright : d j (ϕ1.func y) (ϕ2.func y) ≤ eps j :=
    hclose y hy j
  have hmid :
      d j (ϕ1.func x) (ϕ2.func y) ≤
        d j (ϕ1.func x) (ϕ1.func y) + eps j := by
    exact le_trans htri₂ (add_le_add (le_refl _) hright)
  calc
    d j (ϕ2.func x) (ϕ2.func y)
        ≤ d j (ϕ2.func x) (ϕ1.func x) +
          d j (ϕ1.func x) (ϕ2.func y) := htri₁
    _ ≤ eps j + (d j (ϕ1.func x) (ϕ1.func y) + eps j) :=
        add_le_add hleft hmid
    _ = d j (ϕ1.func x) (ϕ1.func y) + (eps j + eps j) := by
        simp [add_comm, add_assoc]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-b959b42f25710105
**命题 #h-b959b42f25710105（两个算子的点对像距扰动界，反向点对扰动）**
The symmetric pointwise closeness condition gives the reverse pairwise
perturbation bound.
-/
theorem operator_pair_image_distance_perturbation_rev
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (eps : I → ENNReal)
    (hdom1 : U ⊆ dom ϕ1) (hdom2 : U ⊆ dom ϕ2)
    (hclose : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ eps j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ1.func x) (ϕ1.func y) ≤
        d j (ϕ2.func x) (ϕ2.func y) + (eps j + eps j) := by
  apply operator_pair_image_distance_perturbation d hd ϕ2 ϕ1 U eps hdom2 hdom1
  intro z hz j
  rw [(hd j).symm (ϕ2.func z) (ϕ1.func z)]
  exact hclose z hz j

/--
OET anchor: h-b959b42f25710105
**命题 #h-b959b42f25710105（两个算子的点对像距扰动界，Lip 上界桥接）**
A Lip certificate for the first operator gives an additive upper bound for the
second operator under pointwise perturbation.
-/
theorem operator_pair_lip_bound_of_pointwise_perturbation
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (eps : I → ENNReal)
    (L : I → I → ENNReal)
    (hdom1 : U ⊆ dom ϕ1) (hdom2 : U ⊆ dom ϕ2)
    (hclose : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ eps j)
    (hL : IsLipMatrix d ϕ1 U L) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (ϕ2.func x) (ϕ2.func y) ≤
        (∑ i : I, L i j * d i x y) + (eps j + eps j) := by
  have _ := hdom1
  intro x hx y hy j
  have hpair :=
    operator_pair_image_distance_perturbation d hd ϕ1 ϕ2 U eps hdom1 hdom2 hclose
      x hx y hy j
  have hlip := hL.2 x hx y hy j
  exact le_trans hpair (add_le_add hlip (le_refl _))

/--
OET anchor: h-b959b42f25710105
**命题 #h-b959b42f25710105（两个算子的点对像距扰动界，co-Lip 下界桥接）**
A co-Lip certificate for the first operator survives as an additive-side lower
bound for the second operator under pointwise perturbation.
-/
theorem operator_pair_colip_bound_of_pointwise_perturbation
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (ϕ1 ϕ2 : Operator X bot) (U : Set X) (eps : I → ENNReal)
    (K : I → I → ENNReal)
    (hdom1 : U ⊆ dom ϕ1) (hdom2 : U ⊆ dom ϕ2)
    (hclose : ∀ z ∈ U, ∀ j : I, d j (ϕ1.func z) (ϕ2.func z) ≤ eps j)
    (hK : IsCoLipMatrix d ϕ1 U K) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i : I, K i j * d i x y) ≤
        d j (ϕ2.func x) (ϕ2.func y) + (eps j + eps j) := by
  have _ := hdom1
  intro x hx y hy j
  have hpair :=
    operator_pair_image_distance_perturbation_rev d hd ϕ1 ϕ2 U eps hdom1 hdom2 hclose
      x hx y hy j
  have hcolip := hK.2.2 x hx y hy j
  exact le_trans hcolip hpair

end formal_oet.vol_01.ch_02_operator_bounds
