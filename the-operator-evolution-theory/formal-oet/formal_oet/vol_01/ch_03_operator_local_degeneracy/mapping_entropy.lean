import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix
import formal_oet.vol_01.ch_03_operator_local_degeneracy.threshold_classification
import formal_oet.vol_01.ch_03_operator_local_degeneracy.computational_fiber
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Finset
open scoped BigOperators

variable {X I : Type} {bot : X} [finite_I : Fintype I]
variable (d : I → X → X → ENNReal)

local instance instDecidableEqXMappingEntropy : DecidableEq X := Classical.decEq X
local instance instDecidableEqIMappingEntropy : DecidableEq I := Classical.decEq I

theorem log2_ereal_mono {x y : ENNReal} (h : x ≤ y) : log2_ereal x ≤ log2_ereal y := by
  dsimp [log2_ereal]
  by_cases hx : x = 0
  · rw [if_pos hx]
    exact bot_le
  · rw [if_neg hx]
    by_cases hy : y = 0
    · rw [hy] at h
      have h_x0 : x = 0 := bot_unique h
      contradiction
    · rw [if_neg hy]
      by_cases hy_top : y = ⊤
      · rw [if_pos hy_top]
        exact le_top
      · rw [if_neg hy_top]
        by_cases hx_top : x = ⊤
        · rw [hx_top] at h
          have h_y_top : y = ⊤ := top_unique h
          contradiction
        · rw [if_neg hx_top]
          apply EReal.coe_le_coe_iff.mpr
          dsimp [Real.logb]
          apply div_le_div_of_nonneg_right
          · apply Real.log_le_log
            · exact ENNReal.toReal_pos hx hx_top
            · exact ENNReal.toReal_mono hy_top h
          · apply le_of_lt
            exact Real.log_pos one_lt_two
theorem ereal_sub_le_sub_left {a b c : EReal} (h : a ≤ b) : c - b ≤ c - a := by
  exact EReal.sub_le_sub le_rfl h

@[simp]
theorem log2_ereal_one : log2_ereal (1 : ENNReal) = 0 := by
  norm_num [log2_ereal, Real.logb]

/-- 基础内覆盖在单分量伪度量上的特化。 -/
abbrev IsEpsilonNet (i : I) (ε : ENNReal) (U : Set X)
    (centers : Finset X) : Prop :=
  InternalEpsilonNet (d i) ε U centers

/-- 复合度量 $d_J$ 的 $\varepsilon$-覆盖网 -/
abbrev IsEpsilonNetComp (J : NonemptyFinset I) (ε : ENNReal)
    (U : Set X) (centers : Finset X) : Prop :=
  InternalEpsilonNet (comp_pseudo_metric d J) ε U centers

/-- 子族覆盖数 $\mathcal N_J(\varepsilon,U)$。 -/
noncomputable def cov_num_comp (J : NonemptyFinset I) (ε : ENNReal) (U : Set X) : ENNReal :=
  covering_number (comp_pseudo_metric d J) ε U

omit [Fintype I] in
/-- 有限子族记号给出的覆盖数等于对应子族复合伪度量的覆盖数。 -/
theorem cov_num_comp_eq_subfamily_covering_number
    (J : NonemptyFinset I) (ε : ENNReal) (U : Set X) :
    cov_num_comp d J ε U =
      covering_number
        (subfamily_pseudometric d (↑J.val : Set I)) ε U := by
  rw [cov_num_comp, comp_pseudo_metric_eq_subfamily]

omit [Fintype I] in
/-- The singleton subfamily covering number is the single-component one. -/
theorem cov_num_comp_singleton_eq_cov_num
    (i : I) (ε : ENNReal) (U : Set X) :
    cov_num_comp d (singleton_nonempty_finset i) ε U =
      covering_number (d i) ε U := by
  rw [cov_num_comp, comp_pseudo_metric_singleton]

omit [Fintype I] in
theorem cov_num_comp_le_of_epsilon_net (J : NonemptyFinset I) (ε : ENNReal) (U : Set X)
    (centers : Finset X) (hnet : IsEpsilonNetComp d J ε U centers) :
    cov_num_comp d J ε U ≤ (centers.card : ENNReal) := by
  dsimp [cov_num_comp]
  exact le_trans
    (iInf_le
      (fun centers : Finset X =>
        ⨅ (_ : IsEpsilonNetComp d J ε U centers), (centers.card : ENNReal))
      centers)
    (iInf_le
      (fun _ : IsEpsilonNetComp d J ε U centers => (centers.card : ENNReal))
      hnet)

/-- 覆盖数 $\mathcal{N}_i(\varepsilon, U)$，即基础覆盖数在单分量伪度量上的特化。 -/
noncomputable def cov_num (i : I) (ε : ENNReal) (U : Set X) : ENNReal :=
  covering_number (d i) ε U

omit [Fintype I] in
/-- A real-valued metric entropy has finite covering number. -/
theorem cov_num_lt_top_of_metric_entropy_eq_real
    (j : I) (ε : ENNReal) (U : Set X) (e : ℝ)
    (hentropy : metric_entropy (d j) ε U = (e : EReal)) :
    cov_num d j ε U < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro htop
  have hcover_top : covering_number (d j) ε U = ⊤ := by
    simpa [cov_num] using htop
  have hentropy_top : metric_entropy (d j) ε U = ⊤ := by
    simp [metric_entropy, log2_ereal, hcover_top]
  rw [hentropy_top] at hentropy
  exact EReal.coe_ne_top e hentropy.symm

omit [Fintype I] in
theorem cov_num_le_of_epsilon_net (i : I) (ε : ENNReal) (U : Set X)
    (centers : Finset X) (hnet : IsEpsilonNet d i ε U centers) :
    cov_num d i ε U ≤ (centers.card : ENNReal) := by
  dsimp [cov_num]
  exact le_trans
    (iInf_le (fun centers : Finset X => ⨅ (_ : IsEpsilonNet d i ε U centers), (centers.card : ENNReal)) centers)
    (iInf_le (fun _ : IsEpsilonNet d i ε U centers => (centers.card : ENNReal)) hnet)

omit [Fintype I] in
theorem one_le_cov_num_of_nonempty (i : I) (ε : ENNReal) (U : Set X)
    (hU : U.Nonempty) :
    (1 : ENNReal) ≤ cov_num d i ε U := by
  dsimp [cov_num]
  apply le_iInf
  intro centers
  apply le_iInf
  intro hnet
  rcases hU with ⟨x, hx⟩
  rcases hnet.2 x hx with ⟨c, hc, _⟩
  exact_mod_cast (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨c, hc⟩))

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
set_option linter.unusedVariables false in
omit [Fintype I] in
/--
OET anchor: h-56e96ed2cda64242
**命题（分量分划与映射熵差）- 零直径非空集合的覆盖数**
若非空集合中任意两点在分量 `i` 下零距，则其任意正精度覆盖数为 `1`。
-/
theorem cov_num_eq_one_of_nonempty_zero_diameter (i : I) (ε : ENNReal) (V : Set X)
    (hV : V.Nonempty)
    (hε : 0 < ε)
    (hzero : ∀ x ∈ V, ∀ y ∈ V, d i x y = 0) :
    cov_num d i ε V = 1 := by
  apply le_antisymm
  · rcases hV with ⟨v0, hv0⟩
    let centers : Finset X := {v0}
    have hnet : IsEpsilonNet d i ε V centers := by
      dsimp [IsEpsilonNet, centers]
      constructor
      · intro x hx
        have hx_eq : x = v0 := Finset.mem_singleton.mp hx
        simpa [hx_eq] using hv0
      · intro x hx
        use v0
        constructor
        · exact Finset.mem_singleton.mpr rfl
        · rw [hzero x hx v0 hv0]
          exact hε
    have hle : cov_num d i ε V ≤ (centers.card : ENNReal) :=
      cov_num_le_of_epsilon_net d i ε V centers hnet
    simpa [centers] using hle
  · exact one_le_cov_num_of_nonempty d i ε V hV

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-56e96ed2cda64242
**命题（分量分划与映射熵差）- 受限等距保持覆盖数**
若 `ϕ` 在 `U` 上保持分量 `i` 的点对距离，则像集与原集合的覆盖数相等。
-/
theorem cov_num_image_eq_of_component_distance_preserving
    (ϕ : Operator X bot) (U : Set X) (i : I) (ε : ENNReal)
    (hdist : ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = d i x y) :
    cov_num d i ε (ϕ.func '' U) = cov_num d i ε U := by
  apply le_antisymm
  · dsimp [cov_num]
    apply le_iInf
    intro centers_U
    apply le_iInf
    intro hnet_U
    let centers_V := centers_U.image ϕ.func
    have hnet_V : IsEpsilonNet d i ε (ϕ.func '' U) centers_V := by
      dsimp [IsEpsilonNet, centers_V] at hnet_U ⊢
      constructor
      · intro z hz
        rw [Finset.mem_coe, Finset.mem_image] at hz
        rcases hz with ⟨u, hu, hzu⟩
        have huU : u ∈ U := hnet_U.1 hu
        rw [← hzu]
        exact Set.mem_image_of_mem ϕ.func huU
      · intro z hz
        rcases hz with ⟨x, hxU, hz_eq⟩
        rcases hnet_U.2 x hxU with ⟨c, hc, hc_lt⟩
        have hcU : c ∈ U := hnet_U.1 hc
        use ϕ.func c
        constructor
        · exact Finset.mem_image_of_mem ϕ.func hc
        · rw [← hz_eq, hdist x hxU c hcU]
          exact hc_lt
    have hle : cov_num d i ε (ϕ.func '' U) ≤ (centers_V.card : ENNReal) :=
      cov_num_le_of_epsilon_net d i ε (ϕ.func '' U) centers_V hnet_V
    exact le_trans hle (Nat.cast_le.mpr Finset.card_image_le)
  · dsimp [cov_num]
    apply le_iInf
    intro centers_V
    apply le_iInf
    intro hnet_V
    have h_ex : ∀ v ∈ centers_V, ∃ u ∈ U, ϕ.func u = v := by
      intro v hv
      have hv_image : v ∈ ϕ.func '' U := hnet_V.1 hv
      exact (Set.mem_image ϕ.func U v).mp hv_image
    let pre (v : X) (hv : v ∈ centers_V) : X := Classical.choose (h_ex v hv)
    have hpre : ∀ v (hv : v ∈ centers_V), pre v hv ∈ U ∧ ϕ.func (pre v hv) = v := by
      intro v hv
      exact Classical.choose_spec (h_ex v hv)
    let centers_U := centers_V.attach.image (fun v : {x // x ∈ centers_V} => pre v.val v.prop)
    have hnet_U : IsEpsilonNet d i ε U centers_U := by
      dsimp [IsEpsilonNet, centers_U]
      constructor
      · intro u hu
        rw [Finset.mem_coe, Finset.mem_image] at hu
        rcases hu with ⟨v, _, huv⟩
        rw [← huv]
        exact (hpre v.val v.prop).1
      · intro x hxU
        have hφx : ϕ.func x ∈ ϕ.func '' U := Set.mem_image_of_mem ϕ.func hxU
        rcases hnet_V.2 (ϕ.func x) hφx with ⟨v, hv, hv_lt⟩
        use pre v hv
        constructor
        · rw [Finset.mem_image]
          exact ⟨⟨v, hv⟩, Finset.mem_attach centers_V ⟨v, hv⟩, rfl⟩
        · have hp := hpre v hv
          rw [← hdist x hxU (pre v hv) hp.1, hp.2]
          exact hv_lt
    have hle : cov_num d i ε U ≤ (centers_U.card : ENNReal) :=
      cov_num_le_of_epsilon_net d i ε U centers_U hnet_U
    have h_card : (centers_U.card : ENNReal) ≤ (centers_V.card : ENNReal) := by
      apply Nat.cast_le.mpr
      have h_attach : centers_V.attach.card = centers_V.card := Finset.card_attach
      rw [← h_attach]
      exact Finset.card_image_le
    exact le_trans hle h_card

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-56e96ed2cda64242
**命题（分量分划与映射熵差）- 常值分量输出覆盖数**
常值分量在非空受限域上的像集覆盖数为 `1`。
-/
theorem const_component_image_cov_num_eq_one
    (ϕ : Operator X bot) (U : Set X) (j : I) (ε : ENNReal)
    (hU : U.Nonempty)
    (hε : 0 < ε)
    (h_const : j ∈ ConstComponent d ϕ U) :
    cov_num d j ε (ϕ.func '' U) = 1 := by
  have h_image_nonempty : (ϕ.func '' U).Nonempty := hU.image ϕ.func
  apply cov_num_eq_one_of_nonempty_zero_diameter d j ε (ϕ.func '' U) h_image_nonempty hε
  intro y hy z hz
  rcases hy with ⟨x, hxU, hy_eq⟩
  rcases hz with ⟨w, hwU, hz_eq⟩
  rw [← hy_eq, ← hz_eq]
  exact h_const x hxU w hwU

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-56e96ed2cda64242
**命题（分量分划与映射熵差）- 恒等分量覆盖数保持**
恒等分量在对应分量下保持像集覆盖数。
-/
theorem id_component_image_cov_num_eq
    (ϕ : Operator X bot) (U : Set X) (j : I) (ε : ENNReal)
    (h_id : j ∈ IdComponent d ϕ U)
    (symm : ∀ x y : X, d j x y = d j y x)
    (triangle : ∀ x y z : X, d j x z ≤ d j x y + d j y z) :
    cov_num d j ε (ϕ.func '' U) = cov_num d j ε U := by
  have hdist : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) = d j x y :=
    id_component_preserves_component_distance d ϕ U j h_id symm triangle
  exact cov_num_image_eq_of_component_distance_preserving d ϕ U j ε hdist

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-f4a4cb93f576325e
**注（有限集上映射熵差的良定性）- 有限集覆盖数有限**
有限集在正精度下具有有限覆盖数。
-/
theorem cov_num_lt_top_of_finite (i : I) (ε : ENNReal) (U : Set X)
    (hU_fin : U.Finite)
    (hε : 0 < ε)
    (self_dist_zero : ∀ z, d i z z = 0) :
    cov_num d i ε U < ⊤ := by
  let centers := hU_fin.toFinset
  have hnet : IsEpsilonNet d i ε U centers := by
    dsimp [IsEpsilonNet, centers]
    constructor
    · intro x hx
      exact (hU_fin.mem_toFinset.mp hx)
    · intro x hx
      use x
      constructor
      · exact hU_fin.mem_toFinset.mpr hx
      · rw [self_dist_zero x]
        exact hε
  have hle : cov_num d i ε U ≤ (centers.card : ENNReal) :=
    cov_num_le_of_epsilon_net d i ε U centers hnet
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top centers.card))

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-f4a4cb93f576325e
**注（有限集上映射熵差的良定性）- 子族覆盖数有限**
有限集在任意非空有限子族的复合伪度量下具有有限覆盖数。
-/
theorem cov_num_comp_lt_top_of_finite (J : NonemptyFinset I) (ε : ENNReal) (U : Set X)
    (hU_fin : U.Finite)
    (hε : 0 < ε)
    (self_dist_zero : ∀ j z, d j z z = 0) :
    cov_num_comp d J ε U < ⊤ := by
  let centers := hU_fin.toFinset
  have hnet : IsEpsilonNetComp d J ε U centers := by
    dsimp [IsEpsilonNetComp, centers]
    constructor
    · intro x hx
      exact hU_fin.mem_toFinset.mp hx
    · intro x hx
      use x
      constructor
      · exact hU_fin.mem_toFinset.mpr hx
      · apply lt_of_le_of_lt _ hε
        exact le_of_eq ((comp_pseudo_metric_eq_zero_iff d J x x).mpr
          (fun j _ => self_dist_zero j x))
  have hle : cov_num_comp d J ε U ≤ (centers.card : ENNReal) :=
    cov_num_comp_le_of_epsilon_net d J ε U centers hnet
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top centers.card))


/-- 全有界假设 -/
def IsTotallyBounded (i : I) (U : Set X) : Prop :=
  ∀ ε > 0, ε ≠ ⊤ → cov_num d i ε U < ⊤

/-- 映射熵差良定性（非空且至少有一端有限，从而排除 -∞ - (-∞) 和 ⊤ - ⊤） -/
def EntropyDiffWellDefined (ϕ : Operator X bot) (U : Set X) (i j : I) (ε : ENNReal) : Prop :=
  U.Nonempty ∧ (cov_num d i ε U < ⊤ ∨ cov_num d j ε (ϕ.func '' U) < ⊤)

/-- 子族映射熵差良定性。 -/
def SubfamilyEntropyDiffWellDefined (ϕ : Operator X bot) (U : Set X)
    (K J : NonemptyFinset I) (ε : ENNReal) : Prop :=
  U.Nonempty ∧
    (cov_num_comp d K ε U < ⊤ ∨
      cov_num_comp d J ε (ϕ.func '' U) < ⊤)

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-f4a4cb93f576325e
**注（有限集上映射熵差的良定性）**
非空有限集及其像集的覆盖数均有限，因此映射熵差良定。
-/
theorem finite_set_mapping_entropy_diff_well_defined
    (ϕ : Operator X bot) (U : Set X) (i j : I) (ε : ENNReal)
    (hU_nonempty : U.Nonempty)
    (hU_fin : U.Finite)
    (hε : 0 < ε)
    (_hε_ne_top : ε ≠ ⊤)
    (self_dist_zero : ∀ k z, d k z z = 0) :
    cov_num d i ε U < ⊤ ∧
      cov_num d j ε (ϕ.func '' U) < ⊤ ∧
      EntropyDiffWellDefined d ϕ U i j ε := by
  have hU_cov : cov_num d i ε U < ⊤ :=
    cov_num_lt_top_of_finite d i ε U hU_fin hε (self_dist_zero i)
  have h_image_fin : (ϕ.func '' U).Finite := hU_fin.image ϕ.func
  have h_image_cov : cov_num d j ε (ϕ.func '' U) < ⊤ :=
    cov_num_lt_top_of_finite d j ε (ϕ.func '' U) h_image_fin hε (self_dist_zero j)
  exact ⟨hU_cov, h_image_cov, ⟨hU_nonempty, Or.inl hU_cov⟩⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-f4a4cb93f576325e
**注（有限集上映射熵差的良定性）**
非空有限集在任意非空子族 `K,J` 上的输入熵与像集熵均有限，
因此子族映射熵差良定。
-/
theorem finite_set_subfamily_mapping_entropy_diff_well_defined
    (ϕ : Operator X bot) (U : Set X) (K J : NonemptyFinset I) (ε : ENNReal)
    (hU_nonempty : U.Nonempty)
    (hUdom : U ⊆ dom ϕ)
    (hU_fin : U.Finite)
    (hε : 0 < ε)
    (_hε_ne_top : ε ≠ ⊤)
    (self_dist_zero : ∀ k z, d k z z = 0) :
    cov_num_comp d K ε U < ⊤ ∧
      cov_num_comp d J ε (ϕ.func '' U) < ⊤ ∧
      SubfamilyEntropyDiffWellDefined d ϕ U K J ε := by
  have _ := hUdom
  have hU_cov : cov_num_comp d K ε U < ⊤ :=
    cov_num_comp_lt_top_of_finite d K ε U hU_fin hε self_dist_zero
  have h_image_fin : (ϕ.func '' U).Finite := hU_fin.image ϕ.func
  have h_image_cov : cov_num_comp d J ε (ϕ.func '' U) < ⊤ :=
    cov_num_comp_lt_top_of_finite d J ε (ϕ.func '' U) h_image_fin hε self_dist_zero
  exact ⟨hU_cov, h_image_cov, ⟨hU_nonempty, Or.inl hU_cov⟩⟩

/-- 子族熵差的通用计算定义；良定性证明排除两个熵同时为正无穷。 -/
noncomputable def subfamily_mapping_entropy_diff (ϕ : Operator X bot) (U : Set X)
    (K J : NonemptyFinset I) (ε : ENNReal)
    (_ : SubfamilyEntropyDiffWellDefined d ϕ U K J ε) : EReal :=
  log2_ereal (cov_num_comp d K ε U) -
    log2_ereal (cov_num_comp d J ε (ϕ.func '' U))

/-- 部分映射熵差的单分量特化。 -/
noncomputable def mapping_entropy_diff (ϕ : Operator X bot) (U : Set X)
    (i j : I) (ε : ENNReal)
    (_ : EntropyDiffWellDefined d ϕ U i j ε) : EReal :=
  log2_ereal (cov_num d i ε U) - log2_ereal (cov_num d j ε (ϕ.func '' U))

set_option linter.unusedVariables false in
/--
OET anchor: h-cf9f43f2f47eb03e
**定义（映射熵差）**
正文子族映射熵差：输入域非空并包含于算子定义域，精度有限且为正，
且输入、输出两个覆盖数至少一个有限。
-/
noncomputable def textbook_subfamily_mapping_entropy_diff
    (ϕ : Operator X bot) (U : Set X) (hU : U.Nonempty) (hUdom : U ⊆ dom ϕ)
    (J_in J_out : NonemptyFinset I) (ε : ENNReal) (hε : 0 < ε) (hε_top : ε ≠ ⊤)
    (hfinite : cov_num_comp d J_in ε U < ⊤ ∨
      cov_num_comp d J_out ε (ϕ.func '' U) < ⊤) : EReal :=
  subfamily_mapping_entropy_diff d ϕ U J_in J_out ε ⟨hU, hfinite⟩

omit [Fintype I] in
/-- The subfamily and single-component well-definedness domains agree on singletons. -/
theorem singleton_subfamily_entropy_diff_well_defined_iff
    (ϕ : Operator X bot) (U : Set X) (i j : I) (ε : ENNReal) :
    SubfamilyEntropyDiffWellDefined d ϕ U
        (singleton_nonempty_finset i) (singleton_nonempty_finset j) ε ↔
      EntropyDiffWellDefined d ϕ U i j ε := by
  simp only [SubfamilyEntropyDiffWellDefined, EntropyDiffWellDefined]
  rw [cov_num_comp_singleton_eq_cov_num, cov_num_comp_singleton_eq_cov_num]
  rfl

omit [Fintype I] in
/-- The single-component entropy difference is the singleton subfamily case. -/
theorem mapping_entropy_diff_eq_singleton_subfamily
    (ϕ : Operator X bot) (U : Set X) (i j : I) (ε : ENNReal)
    (hsingle : EntropyDiffWellDefined d ϕ U i j ε)
    (hsub : SubfamilyEntropyDiffWellDefined d ϕ U
      (singleton_nonempty_finset i) (singleton_nonempty_finset j) ε) :
    mapping_entropy_diff d ϕ U i j ε hsingle =
      subfamily_mapping_entropy_diff d ϕ U
        (singleton_nonempty_finset i) (singleton_nonempty_finset j) ε hsub := by
  dsimp [mapping_entropy_diff, subfamily_mapping_entropy_diff, cov_num]
  rw [cov_num_comp_singleton_eq_cov_num, cov_num_comp_singleton_eq_cov_num]

set_option linter.unusedFintypeInType false in
/--
OET anchor: h-56e96ed2cda64242
**命题 #h-56e96ed2cda64242（分量分划与映射熵差）**

正文两个分支的最终包装，同时保留非空受限域、有限正探测尺度和完整扩展伪度量前提。
-/
theorem component_partition_mapping_entropy_textbook
    (ϕ : Operator X bot) (U : Set X) (hU : U.Nonempty)
    (hUdom : U ⊆ dom ϕ) (ε : ENNReal) (hε : 0 < ε) (hε_top : ε ≠ ⊤)
    (j : I) (hmetric : ExtendedPseudoMetric X bot (d j)) :
    (j ∈ ConstComponent d ϕ U →
      ∃ hwd : EntropyDiffWellDefined d ϕ U j j ε,
        cov_num d j ε (ϕ.func '' U) = 1 ∧
        metric_entropy (d j) ε (ϕ.func '' U) = 0 ∧
        mapping_entropy_diff d ϕ U j j ε hwd = metric_entropy (d j) ε U) ∧
    (j ∈ IdComponent d ϕ U →
      cov_num d j ε (ϕ.func '' U) = cov_num d j ε U ∧
      metric_entropy (d j) ε (ϕ.func '' U) = metric_entropy (d j) ε U ∧
      ∀ hwd : EntropyDiffWellDefined d ϕ U j j ε,
        mapping_entropy_diff d ϕ U j j ε hwd = 0) := by
  have _ := hUdom
  have _ := hε_top
  constructor
  · intro hconst
    have hcov := const_component_image_cov_num_eq_one d ϕ U j ε hU hε hconst
    have hcov_finite : cov_num d j ε (ϕ.func '' U) < ⊤ := by
      rw [hcov]
      exact ENNReal.one_lt_top
    let hwd : EntropyDiffWellDefined d ϕ U j j ε :=
      ⟨hU, Or.inr hcov_finite⟩
    have hcov' : covering_number (d j) ε (ϕ.func '' U) = 1 := by
      simpa [cov_num] using hcov
    refine ⟨hwd, hcov, ?_, ?_⟩
    · simp [metric_entropy, hcov']
    · dsimp [mapping_entropy_diff, metric_entropy, cov_num]
      rw [hcov']
      simp
  · intro hid
    have hcov := id_component_image_cov_num_eq d ϕ U j ε hid hmetric.symm hmetric.triangle
    have hcov' : covering_number (d j) ε (ϕ.func '' U) =
        covering_number (d j) ε U := by
      simpa [cov_num] using hcov
    refine ⟨hcov, ?_, ?_⟩
    · simp only [metric_entropy, hcov']
    · intro hwd
      dsimp [mapping_entropy_diff, cov_num]
      rw [hcov']
      rcases hwd.2 with hfinite | hfinite
      · have hfinite' : covering_number (d j) ε U < ⊤ := by
          simpa [cov_num] using hfinite
        have hnonzero : covering_number (d j) ε U ≠ 0 := by
          exact ne_of_gt (lt_of_lt_of_le zero_lt_one
            (one_le_cov_num_of_nonempty d j ε U hU))
        simp [log2_ereal, hnonzero, ne_of_lt hfinite']
      · have hfinite_image : covering_number (d j) ε (ϕ.func '' U) < ⊤ := by
          simpa [cov_num] using hfinite
        rw [hcov'] at hfinite_image
        have hnonzero : covering_number (d j) ε U ≠ 0 := by
          exact ne_of_gt (lt_of_lt_of_le zero_lt_one
            (one_le_cov_num_of_nonempty d j ε U hU))
        simp [log2_ereal, hnonzero, ne_of_lt hfinite_image]

omit [Fintype I] in
/--
**代数辅助引理（单通道 Lip 上界与覆盖数上界）**
用乘法形式表示为：$\mathcal{N}_j(L \varepsilon, \phi(U)) \le \mathcal{N}_i(\varepsilon, U)$
-/
theorem lip_cov_num_bound_aux (ϕ : Operator X bot) (U : Set X) (i j : I) (L ε : ENNReal)
    (h_lip : HasScalarLipBound d ϕ U i j L)
    (h_L_pos : 0 < L) (h_L_ne_top : L ≠ ⊤) :
    cov_num d j (L * ε) (ϕ.func '' U) ≤ cov_num d i ε U := by
  dsimp [cov_num]
  apply le_iInf
  intro centers_U
  apply le_iInf
  intro h_net_U
  have h_image_net : IsEpsilonNet d j (L * ε) (ϕ.func '' U) (centers_U.image ϕ.func) := by
    dsimp [IsEpsilonNet] at h_net_U ⊢
    constructor
    · intro z hz
      rw [Finset.coe_image] at hz
      exact Set.image_mono h_net_U.1 hz
    · intro z hz
      rcases hz with ⟨x, hx_U, hx_eq⟩
      rcases h_net_U.2 x hx_U with ⟨c, hc_in, hc_lt⟩
      use ϕ.func c
      constructor
      · exact Finset.mem_image_of_mem ϕ.func hc_in
      · rw [← hx_eq]
        have h_c_in_U := h_net_U.1 hc_in
        have h_bound := h_lip.2 x hx_U c h_c_in_U
        have h_L_ne_zero : L ≠ 0 := by
          intro h
          rw [h] at h_L_pos
          exact lt_irrefl 0 h_L_pos
        have h_strict : L * d i x c < L * ε := ENNReal.mul_lt_mul_right h_L_ne_zero h_L_ne_top hc_lt
        exact lt_of_le_of_lt h_bound h_strict

  have h_le1 := iInf_le (fun (c : Finset X) => ⨅ (_ : IsEpsilonNet d j (L * ε) (ϕ.func '' U) c), (c.card : ENNReal)) (centers_U.image ϕ.func)
  have h_le2 := iInf_le (fun (_ : IsEpsilonNet d j (L * ε) (ϕ.func '' U) (centers_U.image ϕ.func)) => ((centers_U.image ϕ.func).card : ENNReal)) h_image_net
  have h_card_le : ((centers_U.image ϕ.func).card : ENNReal) ≤ (centers_U.card : ENNReal) := by
    exact Nat.cast_le.mpr Finset.card_image_le
  exact le_trans (le_trans h_le1 h_le2) h_card_le


set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-5f1e227b06f3a2d1
**命题（单通道 Lip 上界与熵差下界）**
-/
theorem lip_entropy_bound_of_scalar_lip
    (ϕ : Operator X bot) (U : Set X) (i j : I) (ε L : ENNReal)
    (h_dom : U ⊆ dom ϕ)
    (h_nempty : U.Nonempty)
    (h_eps : 0 < ε)
    (h_eps_ne_top : ε ≠ ⊤)
    (h_tb : IsTotallyBounded d i U)
    (h_L_pos : 0 < L)
    (h_L_ne_top : L ≠ ⊤)
    (h_lip : ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) ≤ L * d i x y) :
    cov_num d i ε U < ⊤ ∧ cov_num d j ε (ϕ.func '' U) < ⊤ ∧
    ∃ hwd : EntropyDiffWellDefined d ϕ U i j ε,
      mapping_entropy_diff d ϕ U i j ε hwd ≥
        log2_ereal (cov_num d i ε U) -
          log2_ereal
            (cov_num d i (ε / L) U) := by
  have h_L_bound : HasScalarLipBound d ϕ U i j L := ⟨h_dom, h_lip⟩
  have h_mul_div : L * (ε / L) = ε :=
    ENNReal.mul_div_cancel' (fun h => False.elim ((ne_of_gt h_L_pos) h)) (fun h => False.elim (h_L_ne_top h))
  have h_cov := lip_cov_num_bound_aux d ϕ U i j L (ε / L) h_L_bound h_L_pos h_L_ne_top
  rw [h_mul_div] at h_cov

  have h_input_finite : cov_num d i ε U < ⊤ :=
    h_tb ε h_eps h_eps_ne_top
  have h_scaled_finite : cov_num d i (ε / L) U < ⊤ := by
    have h_div_pos : 0 < ε / L := by
      rw [pos_iff_ne_zero, Ne, ENNReal.div_eq_zero_iff]
      push Not
      exact ⟨ne_of_gt h_eps, h_L_ne_top⟩
    have h_div_ne_top : ε / L ≠ ⊤ := by
      intro h
      rw [ENNReal.div_eq_top] at h
      rcases h with ⟨_, h_L_zero⟩ | ⟨h_eps_top, _⟩
      · exact (ne_of_gt h_L_pos) h_L_zero
      · exact h_eps_ne_top h_eps_top
    exact h_tb (ε / L) h_div_pos h_div_ne_top
  have h_output_finite : cov_num d j ε (ϕ.func '' U) < ⊤ :=
    lt_of_le_of_lt h_cov h_scaled_finite
  let hwd : EntropyDiffWellDefined d ϕ U i j ε :=
    ⟨h_nempty, Or.inl h_input_finite⟩
  refine ⟨h_input_finite, h_output_finite, hwd, ?_⟩
  dsimp [mapping_entropy_diff]
  have h_cov_log := log2_ereal_mono h_cov
  exact ereal_sub_le_sub_left h_cov_log

omit [Fintype I] in
/--
**代数辅助引理（co-Lip 常数与覆盖数上界）**
用乘法形式表示为：$\mathcal{N}_i(\varepsilon, U) \le \mathcal{N}_j(K_{ji} \varepsilon, \phi(U))$
-/
theorem colip_cov_num_bound_aux (ϕ : Operator X bot) (U : Set X) (i j : I) (K_ji ε : ENNReal)
    (h_colip : ∀ x ∈ U, ∀ y ∈ U, K_ji * d i x y ≤ d j (ϕ.func x) (ϕ.func y))
    (h_K_pos : 0 < K_ji) (h_K_ne_top : K_ji ≠ ⊤) :
    cov_num d i ε U ≤ cov_num d j (K_ji * ε) (ϕ.func '' U) := by
  dsimp [cov_num]
  apply le_iInf
  intro centers_V
  apply le_iInf
  intro h_net_V

  -- Use Classical.choose to map centers_V back to U
  have h_ex : ∀ v ∈ centers_V, ∃ u ∈ U, ϕ.func u = v := by
    intro v hv
    have hv_in : v ∈ ϕ.func '' U := h_net_V.1 hv
    exact (Set.mem_image ϕ.func U v).mp hv_in
  -- Define the inverse mapping
  let inv_f (v : X) (hv : v ∈ centers_V) : X := Classical.choose (h_ex v hv)
  have h_inv_prop : ∀ v (hv : v ∈ centers_V), inv_f v hv ∈ U ∧ ϕ.func (inv_f v hv) = v := by
    intro v hv
    exact Classical.choose_spec (h_ex v hv)
  -- The preimages set
  let centers_U := centers_V.attach.image (fun (v : {x // x ∈ centers_V}) => inv_f v.val v.prop)
  have h_net_U : IsEpsilonNet d i ε U centers_U := by
    dsimp [IsEpsilonNet]
    constructor
    · intro u hu
      rw [Finset.mem_coe, Finset.mem_image] at hu
      rcases hu with ⟨v, _, hv_eq⟩
      rw [← hv_eq]
      exact (h_inv_prop v.val v.prop).1
    · intro x hx
      -- x ∈ U => ϕ x ∈ ϕ(U)
      have h_px : ϕ.func x ∈ ϕ.func '' U := Set.mem_image_of_mem ϕ.func hx
      -- Since centers_V is an (K_ji * ε)-net of ϕ(U)
      rcases h_net_V.2 (ϕ.func x) h_px with ⟨v, hv_in, hv_lt⟩
      use inv_f v hv_in
      constructor
      · rw [Finset.mem_image]
        use ⟨v, hv_in⟩
        constructor
        · exact Finset.mem_attach centers_V ⟨v, hv_in⟩
        · rfl
      · have h_inv := h_inv_prop v hv_in
        have h_bound := h_colip x hx (inv_f v hv_in) h_inv.1
        -- d j (ϕ x) (ϕ (inv_f v)) = d j (ϕ x) v < K_ji * ε
        have hd_eq : d j (ϕ.func x) (ϕ.func (inv_f v hv_in)) = d j (ϕ.func x) v := by rw [h_inv.2]
        rw [hd_eq] at h_bound
        -- K_ji * d i x (inv_f v) ≤ d j (ϕ x) v < K_ji * ε
        have h_strict : K_ji * d i x (inv_f v hv_in) < K_ji * ε := lt_of_le_of_lt h_bound hv_lt
        have h_K_ne_zero : K_ji ≠ 0 := ne_of_gt h_K_pos
        exact (ENNReal.mul_lt_mul_iff_right h_K_ne_zero h_K_ne_top).mp h_strict
  have h_le1 := iInf_le (fun (c : Finset X) => ⨅ (_ : IsEpsilonNet d i ε U c), (c.card : ENNReal)) centers_U
  have h_le2 := iInf_le (fun (_ : IsEpsilonNet d i ε U centers_U) => (centers_U.card : ENNReal)) h_net_U
  have h_card_le : (centers_U.card : ENNReal) ≤ (centers_V.card : ENNReal) := by
    apply Nat.cast_le.mpr
    have h_att : centers_V.attach.card = centers_V.card := Finset.card_attach
    rw [← h_att]
    exact Finset.card_image_le
  exact le_trans (le_trans h_le1 h_le2) h_card_le


/--
OET anchor: h-9d16603c422d3b11
**命题 #h-9d16603c422d3b11（co-Lip 常数与熵差上界）**
-/
theorem colip_entropy_bound_exact (ϕ : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal) (ε : ENNReal)
    (h_nempty : U.Nonempty)
    (hK : IsCoLipMatrix d ϕ U K)
    (h_K_pos : 0 < K i j) (h_K_ne_top : K i j ≠ ⊤)
    (h_eps : 0 < ε)
    (h_eps_ne_top : ε ≠ ⊤)
    (h_tb : IsTotallyBounded d i U) :
    cov_num d i ε U < ⊤ ∧
    cov_num d i (ε / K i j) U < ⊤ ∧
    ∃ hwd : EntropyDiffWellDefined d ϕ U i j ε,
      mapping_entropy_diff d ϕ U i j ε hwd ≤
        log2_ereal (cov_num d i ε U) -
          log2_ereal (cov_num d i (ε / K i j) U) := by
  have h_i_eps_finite : cov_num d i ε U < ⊤ := h_tb ε h_eps h_eps_ne_top
  have h_div_pos : 0 < ε / K i j := by
    rw [pos_iff_ne_zero, Ne, ENNReal.div_eq_zero_iff]
    push Not
    exact ⟨ne_of_gt h_eps, h_K_ne_top⟩
  have h_div_ne_top : ε / K i j ≠ ⊤ := by
    intro h
    rw [ENNReal.div_eq_top] at h
    rcases h with ⟨_, h_K_zero⟩ | ⟨h_eps_top, _⟩
    · exact (ne_of_gt h_K_pos) h_K_zero
    · exact h_eps_ne_top h_eps_top
  have h_i_div_finite : cov_num d i (ε / K i j) U < ⊤ :=
    h_tb (ε / K i j) h_div_pos h_div_ne_top
  let hwd : EntropyDiffWellDefined d ϕ U i j ε :=
    ⟨h_nempty, Or.inl h_i_eps_finite⟩
  refine ⟨h_i_eps_finite, h_i_div_finite, hwd, ?_⟩
  dsimp [mapping_entropy_diff]
  have h_colip : ∀ x ∈ U, ∀ y ∈ U,
      K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
    intro x hx y hy
    rcases hK with ⟨_, _, hK_ineq⟩
    have h_colip_sum := hK_ineq x hx y hy j
    have h_sum_lower : K i j * d i x y ≤ ∑ k : I, K k j * d k x y := by
      exact Finset.single_le_sum
        (fun (k : I) _ => zero_le (K k j * d k x y))
        (Finset.mem_univ i)
    exact le_trans h_sum_lower h_colip_sum
  have h_cov :=
    colip_cov_num_bound_aux d ϕ U i j (K i j) (ε / K i j)
      h_colip h_K_pos h_K_ne_top
  have h_mul_div : K i j * (ε / K i j) = ε :=
    ENNReal.mul_div_cancel'
      (fun h => False.elim ((ne_of_gt h_K_pos) h))
      (fun h => False.elim (h_K_ne_top h))
  rw [h_mul_div] at h_cov
  have h_cov_log := log2_ereal_mono h_cov
  exact ereal_sub_le_sub_left h_cov_log

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
omit [Fintype I] in
/--
OET anchor: h-9ecc7d0b4b541992
**命题 #h-9ecc7d0b4b541992（零测距纤维包含推出覆盖数约束）**
把任意输入 `τ`-内网经算子取像，即得到输出像的 `ε`-内网；因此不需要
假设最优内网存在。
-/
theorem zeroing_cov_num_le (φ : Operator X bot) (A : Set X)
    (i j : I) (τ ε : ENNReal) (hε : 0 < ε)
    (hzero : ∀ x ∈ A, ∀ y ∈ A,
      d i y x < τ → d j (φ.func y) (φ.func x) = 0) :
    cov_num d j ε (φ.func '' A) ≤ cov_num d i τ A := by
  classical
  dsimp [cov_num, covering_number]
  apply le_iInf
  intro centers
  apply le_iInf
  intro hnet
  have h_image_net :
      InternalEpsilonNet (d j) ε (φ.func '' A) (centers.image φ.func) := by
    constructor
    · intro z hz
      rw [Finset.coe_image] at hz
      rcases hz with ⟨c, hc, rfl⟩
      exact Set.mem_image_of_mem φ.func (hnet.1 hc)
    · rintro z ⟨x, hx, rfl⟩
      rcases hnet.2 x hx with ⟨c, hc, hxc⟩
      refine ⟨φ.func c, Finset.mem_image_of_mem φ.func hc, ?_⟩
      have hφzero : d j (φ.func x) (φ.func c) = 0 :=
        hzero c (hnet.1 hc) x hx hxc
      simpa [hφzero] using hε
  calc
    (⨅ (image_centers : Finset X)
        (_ : InternalEpsilonNet (d j) ε (φ.func '' A) image_centers),
        (image_centers.card : ENNReal)) ≤
        ((centers.image φ.func).card : ENNReal) := by
      exact iInf_le_of_le (centers.image φ.func)
        (iInf_le_of_le h_image_net le_rfl)
    _ ≤ (centers.card : ENNReal) := by
      exact_mod_cast Finset.card_image_le

omit [Fintype I] in
/-- OET anchor: h-9ecc7d0b4b541992
统一零化半径下界给出任意子集的内部覆盖数约束；不要求全有界或有限零化半径。 -/
theorem operator_zero_radius_cov_num_bound
    (φ : Operator X bot) (A B : Set X) (hBA : B ⊆ A)
    (i j : I) (τ ε : ENNReal) (hε : 0 < ε)
    (hν : τ ≤ min_annihilation_radius d φ i (singleton_nonempty_finset j) A) :
    cov_num d j ε (φ.func '' B) ≤ cov_num d i τ B := by
  apply zeroing_cov_num_le d φ B i j τ ε hε
  intro x hx y hy hdist
  exact zero_of_lt_min_annihilation_radius d φ A i j x y τ hν (hBA hx) (hBA hy) hdist

omit [Fintype I] in
/-- OET anchor: h-9ecc7d0b4b541992
一般覆盖数上界经对数单调性给出度量熵上界；正文使用非空且熵有定义的子集。 -/
theorem operator_zero_radius_metric_entropy_bound
    (φ : Operator X bot) (A B : Set X) (hBA : B ⊆ A)
    (i j : I) (τ ε : ENNReal) (hε : 0 < ε)
    (hν : τ ≤ min_annihilation_radius d φ i (singleton_nonempty_finset j) A) :
    metric_entropy (d j) ε (φ.func '' B) ≤ metric_entropy (d i) τ B := by
  exact log2_ereal_mono
    (operator_zero_radius_cov_num_bound d φ A B hBA i j τ ε hε hν)

omit [Fintype I] in
/-- OET anchor: h-610f439b6ff59f79
小输入域上的整体零化判据. Every positive finite output precision has
internal covering number one on the actual output domain. -/
theorem joint_zeroing_cov_num_eq_one
    (φ : Operator X bot) (A : Set X) (hA : A.Nonempty) (i j : I) (τ_σ τ_ν : ENNReal)
    (hdiam : input_diameter d i (A) < τ_σ)
    (hthreshold : τ_σ ≤ τ_ν)
    (hν : τ_ν ≤ min_annihilation_radius d φ i (singleton_nonempty_finset j) A)
    (ε : ENNReal) (hε : FinitePositiveRadius ε) :
    cov_num d j ε (φ.func '' A) = 1 := by
  apply cov_num_eq_one_of_nonempty_zero_diameter d j ε _
    (hA.image φ.func) hε.1
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (joint_zeroing_iff d φ A i j τ_σ τ_ν hdiam hthreshold).mp hν x hx y hy


omit [Fintype I] in
/--
**代数辅助引理（零化半径给出的输出熵上界）**
-/
theorem resolution_limit_annihilation_bound_aux (ϕ : Operator X bot) (U : Set X) (i j : I) (ν ε : ENNReal)
    (h_nu : min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U = ν)
    (h_eps_pos : 0 < ε) :
    cov_num d j ε (ϕ.func '' U) ≤ cov_num d i ν U := by
  apply operator_zero_radius_cov_num_bound d ϕ U U (Set.Subset.refl U) i j ν ε h_eps_pos
  exact le_of_eq h_nu.symm


set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-9ecc7d0b4b541992
**命题（零化阈值下的纤维包含与覆盖数约束）的同域熵界特例**
在一般子集覆盖界中取 `A = B = U`、阈值为有限正统一零化半径 `ν`。
输入域全有界时，输入 `ν`-覆盖数有限，并给出任意有限正输出精度的熵上界。
-/
theorem resolution_limit_annihilation_bound_exact (ϕ : Operator X bot) (U : Set X) (i j : I) (ν ε : ENNReal)
    (_h_dom : U ⊆ dom ϕ)
    (_h_nempty : U.Nonempty)
    (h_nu_val : min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U = ν)
    (h_nu_pos : 0 < ν)
    (h_nu_ne_top : ν ≠ ⊤)
    (h_eps_pos : 0 < ε)
    (_h_eps_ne_top : ε ≠ ⊤)
    (h_tb : IsTotallyBounded d i U) :
    cov_num d i ν U < ⊤ ∧
    log2_ereal (cov_num d j ε (ϕ.func '' U)) ≤ log2_ereal (cov_num d i ν U) := by
  constructor
  · exact h_tb ν h_nu_pos h_nu_ne_top
  · have h_cov := resolution_limit_annihilation_bound_aux d ϕ U i j ν ε h_nu_val h_eps_pos
    exact log2_ereal_mono h_cov

end
end formal_oet.vol_01.ch_03_operator_local_degeneracy
