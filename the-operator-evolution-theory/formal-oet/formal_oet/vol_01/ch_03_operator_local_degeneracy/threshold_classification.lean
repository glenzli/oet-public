import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X}
variable (d : I → X → X → ENNReal)
local instance : DecidableEq I := Classical.decEq I

/--
OET anchor: h-83287e414000b50b **定义（阈值分类）**
Two independent bits: the first records input scale below its threshold;
the second records zeroing radius at least its threshold. `true` represents 1.
-/
abbrev ThresholdBits := Bool × Bool

/--
OET anchor: h-83287e414000b50b
**定义（输入尺度函数族）**
尺度值只在非空集合上承载正文语义；`val` 在空集上的值是无约束的全域代表。
-/
structure ScaleFamily (X I : Type) where
  val : I → Set X → ENNReal
  monotone : ∀ (i : I) {A₁ A₂ : Set X},
    A₁.Nonempty → A₂.Nonempty → A₁ ⊆ A₂ → val i A₁ ≤ val i A₂

instance : CoeFun (ScaleFamily X I) (fun _ => I → Set X → ENNReal) where
  coe σ := σ.val

/-- OET anchor: h-83287e414000b50b
一般算子在受限域上的阈值分类。正文使用非空 `A ⊆ dom φ` 和两个有限正阈值；
公式本身对任意域和扩展阈值有定义，且两个坐标互不遮蔽。 -/
noncomputable def operator_threshold_readout (φ : Operator X bot) (A : Set X)
    (σ : ScaleFamily X I) (τ_σ τ_ν : ENNReal) (i j : I) : ThresholdBits := by
  classical
  exact (decide (σ i A < τ_σ),
    decide (τ_ν ≤ min_annihilation_radius d φ i (singleton_nonempty_finset j) A))

/-- OET anchor: h-76dc176ee249f20a
The input bit is 1 exactly when the input scale is below its threshold. -/
theorem operator_input_bit_eq_true_iff (σ : ScaleFamily (X := X) (I := I))
    (τ_σ τ_ν : ENNReal) (φ : Operator X bot) (A : Set X) (i j : I) :
    (operator_threshold_readout d φ A σ τ_σ τ_ν i j).1 = true ↔
      σ i A < τ_σ := by
  classical
  simp [operator_threshold_readout]

/-- OET anchor: h-76dc176ee249f20a
The input bit is 0 exactly when the input scale reaches its threshold. -/
theorem operator_input_bit_eq_false_iff (σ : ScaleFamily (X := X) (I := I))
    (τ_σ τ_ν : ENNReal) (φ : Operator X bot) (A : Set X) (i j : I) :
    (operator_threshold_readout d φ A σ τ_σ τ_ν i j).1 = false ↔
      τ_σ ≤ σ i A := by
  classical
  simp [operator_threshold_readout]

/-- OET anchor: h-76dc176ee249f20a
The zeroing bit is 1 exactly when the zeroing radius reaches its threshold,
regardless of the input-scale bit. -/
theorem operator_zero_bit_eq_true_iff (σ : ScaleFamily (X := X) (I := I))
    (τ_σ τ_ν : ENNReal) (φ : Operator X bot) (A : Set X) (i j : I) :
    (operator_threshold_readout d φ A σ τ_σ τ_ν i j).2 = true ↔
      τ_ν ≤ min_annihilation_radius d φ i (singleton_nonempty_finset j) A := by
  classical
  simp [operator_threshold_readout]

/-- OET anchor: h-76dc176ee249f20a
The zeroing bit is 0 exactly when the zeroing radius is below its threshold. -/
theorem operator_zero_bit_eq_false_iff (σ : ScaleFamily (X := X) (I := I))
    (τ_σ τ_ν : ENNReal) (φ : Operator X bot) (A : Set X) (i j : I) :
    (operator_threshold_readout d φ A σ τ_σ τ_ν i j).2 = false ↔
      min_annihilation_radius d φ i (singleton_nonempty_finset j) A < τ_ν := by
  classical
  simp [operator_threshold_readout]

/-- OET anchor: h-76dc176ee249f20a
Every readout is one of the four Boolean pairs. -/
theorem operator_threshold_readout_exhaustive (σ : ScaleFamily (X := X) (I := I))
    (τ_σ τ_ν : ENNReal) (φ : Operator X bot) (A : Set X) (i j : I) :
    operator_threshold_readout d φ A σ τ_σ τ_ν i j = (false, false) ∨
      operator_threshold_readout d φ A σ τ_σ τ_ν i j = (false, true) ∨
      operator_threshold_readout d φ A σ τ_σ τ_ν i j = (true, false) ∨
      operator_threshold_readout d φ A σ τ_σ τ_ν i j = (true, true) := by
  cases h : operator_threshold_readout d φ A σ τ_σ τ_ν i j with
  | mk a b => cases a <;> cases b <;> simp

/-- OET anchor: h-76dc176ee249f20a
Increasing the input threshold preserves a true input bit. -/
theorem operator_input_bit_monotone (σ : ScaleFamily (X := X) (I := I))
    {τ₁ τ₂ τ_ν : ENNReal} (hτ : τ₁ ≤ τ₂)
    {φ : Operator X bot} {A : Set X} {i j : I}
    (hinput : (operator_threshold_readout d φ A σ τ₁ τ_ν i j).1 = true) :
    (operator_threshold_readout d φ A σ τ₂ τ_ν i j).1 = true := by
  have hscale := (operator_input_bit_eq_true_iff d σ τ₁ τ_ν φ A i j).mp hinput
  exact (operator_input_bit_eq_true_iff d σ τ₂ τ_ν φ A i j).mpr
    (lt_of_lt_of_le hscale hτ)

/-- OET anchor: h-76dc176ee249f20a
A true zeroing bit at a larger threshold remains true at a smaller threshold. -/
theorem operator_zero_bit_antitone (σ : ScaleFamily (X := X) (I := I))
    {τ_σ τ₁ τ₂ : ENNReal} (hτ : τ₁ ≤ τ₂)
    {φ : Operator X bot} {A : Set X} {i j : I}
    (hzero : (operator_threshold_readout d φ A σ τ_σ τ₂ i j).2 = true) :
    (operator_threshold_readout d φ A σ τ_σ τ₁ i j).2 = true := by
  have hν := (operator_zero_bit_eq_true_iff d σ τ_σ τ₂ φ A i j).mp hzero
  exact (operator_zero_bit_eq_true_iff d σ τ_σ τ₁ φ A i j).mpr (le_trans hτ hν)

/-- A zeroing radius valid on a larger domain remains valid after restricting
the domain, so the restricted minimum radius cannot decrease. -/
theorem annihilation_localization_radius_mono
    (ϕ : Operator X bot) (U D : Set X) (i j : I)
    (hUD : U ⊆ D) :
    min_annihilation_radius d ϕ i (singleton_nonempty_finset j) D ≤
      min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U := by
  dsimp [min_annihilation_radius]
  apply le_iInf
  intro y
  apply le_iInf
  intro hyU
  have h_inf_D_le_ann_D :
      (⨅ z ∈ D, annihilation_radius d ϕ i (singleton_nonempty_finset j) D z) ≤
        annihilation_radius d ϕ i (singleton_nonempty_finset j) D y :=
    iInf₂_le y (hUD hyU)
  have h_ann_D_le_ann_U :
      annihilation_radius d ϕ i (singleton_nonempty_finset j) D y ≤
        annihilation_radius d ϕ i (singleton_nonempty_finset j) U y := by
    dsimp [annihilation_radius]
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply iSup_le
    intro h_sub_D
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have h_sub_U :
        OpenBall d i y r ∩ U ⊆
          ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func y) := by
      intro x hx
      have hxD : x ∈ OpenBall d i y r ∩ D := ⟨hx.1, hUD hx.2⟩
      have h_fib_D := h_sub_D hxD
      exact ⟨hx.2, h_fib_D.2⟩
    exact le_iSup_of_le h_sub_U le_rfl
  exact le_trans h_inf_D_le_ann_D h_ann_D_le_ann_U

/-- OET anchor: h-451ca2134cd62db4
域缩小下的输入尺度不增。此结论只用尺度函数族定义中的非空域单调性。 -/
theorem input_scale_mono_of_subset (σ : ScaleFamily X I) (i : I)
    {A B : Set X} (hB : B.Nonempty) (hBA : B ⊆ A) : σ i B ≤ σ i A :=
  σ.monotone i hB (hB.mono hBA) hBA

/--
OET anchor: h-451ca2134cd62db4
**命题 #h-451ca2134cd62db4（域缩小下的尺度与统一零化半径单调性）**
若输入尺度关于集合包含单调，则 输入尺度低于阈值的条件沿子域继承。
-/
theorem input_scale_lt_of_subset
    (scale : Set X → ENNReal) (tau : ENNReal)
    {B Bα : Set X}
    (hmono : ∀ {A₁ A₂ : Set X}, A₁ ⊆ A₂ → scale A₁ ≤ scale A₂)
    (hsub : Bα ⊆ B)
    (hscale : scale B < tau) :
    scale Bα < tau :=
  lt_of_le_of_lt (hmono hsub) hscale

/--
OET anchor: h-451ca2134cd62db4
**命题 #h-451ca2134cd62db4（域缩小下的尺度与统一零化半径单调性）**
有限分划中的每个胞只使用其为母域子集这一事实继承 输入尺度低于阈值的条件。
-/
theorem input_scale_lt_of_partition_cell
    (scale : Set X → ENNReal) (tau : ENNReal)
    {B : Set X} {F : Type} (cell : F → Set X)
    (hmono : ∀ {A₁ A₂ : Set X}, A₁ ⊆ A₂ → scale A₁ ≤ scale A₂)
    (hcell : ∀ α : F, cell α ⊆ B)
    (hscale : scale B < tau) :
    ∀ α : F, scale (cell α) < tau := by
  intro α
  exact input_scale_lt_of_subset scale tau hmono (hcell α) hscale

/--
OET anchor: h-451ca2134cd62db4
**命题 #h-451ca2134cd62db4（域缩小下的尺度与统一零化半径单调性）**
输入尺度函数族自身的单调性给出 输入尺度低于阈值的条件沿子域继承。
-/
theorem input_scale_lt_of_subset_scale_family
    (σ : ScaleFamily X I) (i : I) (tau : ENNReal)
    {U Uα : Set X}
    (hUα_nonempty : Uα.Nonempty) (hU_nonempty : U.Nonempty)
    (hsub : Uα ⊆ U)
    (hscale : σ i U < tau) :
    σ i Uα < tau :=
  lt_of_le_of_lt (σ.monotone i hUα_nonempty hU_nonempty hsub) hscale

/--
OET anchor: h-451ca2134cd62db4
**命题 #h-451ca2134cd62db4（域缩小下的尺度与统一零化半径单调性）**
有限分划中的每个胞由输入尺度函数族单调性继承 输入尺度低于阈值的条件。
-/
theorem input_scale_lt_of_partition_cell_scale_family
    (σ : ScaleFamily X I) (i : I) (tau : ENNReal)
    {U : Set X} {F : Type} (cell : F → Set X)
    (hU_nonempty : U.Nonempty)
    (hcell_nonempty : ∀ α : F, (cell α).Nonempty)
    (hcell : ∀ α : F, cell α ⊆ U)
    (hscale : σ i U < tau) :
    ∀ α : F, σ i (cell α) < tau := by
  intro α
  exact input_scale_lt_of_subset_scale_family σ i tau
    (hcell_nonempty α) hU_nonempty (hcell α) hscale

/--
OET anchor: h-451ca2134cd62db4
**命题 #h-451ca2134cd62db4（域缩小下的尺度与统一零化半径单调性）**
对同一局域算子，统一零化半径沿子域限制单调不减。
-/
theorem zero_radius_mono_of_subset
    (ϕ : Operator X bot) {B Bα : Set X} (i j : I)
    (hsub : Bα ⊆ B) :
    min_annihilation_radius d ϕ i (singleton_nonempty_finset j) B ≤
      min_annihilation_radius d ϕ i (singleton_nonempty_finset j) Bα :=
  annihilation_localization_radius_mono d ϕ Bα B i j hsub

/--
OET anchor: h-451ca2134cd62db4
**命题 #h-451ca2134cd62db4（域缩小下的尺度与统一零化半径单调性）**
`Fin 3` 上由两个非吸收代表给出的两点直径尺度。
-/
noncomputable def fin3_two_point_diam_scale (A : Set (Fin 3)) : ENNReal := by
  classical
  exact if (1 : Fin 3) ∈ A ∧ (2 : Fin 3) ∈ A then 1 else 0

/--
OET anchor: h-451ca2134cd62db4
**命题 #h-451ca2134cd62db4（域缩小下的尺度与统一零化半径单调性）**
该输入尺度关于集合包含单调。
-/
theorem fin3_two_point_diam_scale_monotone :
    ∀ A B : Set (Fin 3), A ⊆ B →
      fin3_two_point_diam_scale A ≤ fin3_two_point_diam_scale B := by
  classical
  intro A B hAB
  unfold fin3_two_point_diam_scale
  by_cases hA : (1 : Fin 3) ∈ A ∧ (2 : Fin 3) ∈ A
  · have hB : (1 : Fin 3) ∈ B ∧ (2 : Fin 3) ∈ B :=
      ⟨hAB hA.1, hAB hA.2⟩
    simp [hA, hB]
  · by_cases hB : (1 : Fin 3) ∈ B ∧ (2 : Fin 3) ∈ B <;> simp [hA, hB]

/--
OET anchor: h-451ca2134cd62db4
**命题 #h-451ca2134cd62db4（域缩小下的尺度与统一零化半径单调性）**
输入尺度低于阈值的条件的反向一般不成立：子域可低于阈值而母域不低于阈值。
-/
theorem input_scale_lt_reverse_fails_under_refinement :
    ({(1 : Fin 3)} : Set (Fin 3)) ⊆ ({(1 : Fin 3), (2 : Fin 3)} : Set (Fin 3)) ∧
      fin3_two_point_diam_scale ({(1 : Fin 3)} : Set (Fin 3)) < (1 / 2 : ENNReal) ∧
        ¬ fin3_two_point_diam_scale
          ({(1 : Fin 3), (2 : Fin 3)} : Set (Fin 3)) < (1 / 2 : ENNReal) := by
  classical
  constructor
  · intro x hx
    simp only [Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    exact Or.inl hx
  constructor
  · have h21 : (2 : Fin 3) ≠ 1 := by decide
    norm_num [fin3_two_point_diam_scale, h21]
  · norm_num [fin3_two_point_diam_scale]

/--
OET anchor: h-9ecc7d0b4b541992
**命题 #h-9ecc7d0b4b541992（零化阈值下的纤维包含与覆盖数约束，半径抽取）**
从统一零化半径下界与严格距离条件推出单分量零测距。
-/
theorem zero_of_lt_min_annihilation_radius (φ : Operator X bot)
    (U : Set X) (i j : I) (x y : X) (τ : ENNReal)
    (hτ : τ ≤ min_annihilation_radius d φ i (singleton_nonempty_finset j) U)
    (hx : x ∈ U) (hy : y ∈ U) (hxy : d i y x < τ) :
    d j (φ.func y) (φ.func x) = 0 := by
  have h_inf_le :
      min_annihilation_radius d φ i (singleton_nonempty_finset j) U ≤
        annihilation_radius d φ i (singleton_nonempty_finset j) U x :=
    iInf₂_le x hx
  have hlt :
      d i y x <
        annihilation_radius d φ i (singleton_nonempty_finset j) U x :=
    lt_of_lt_of_le hxy (le_trans hτ h_inf_le)
  rcases lt_iSup_iff.mp hlt with ⟨r, hr⟩
  rcases lt_iSup_iff.mp hr with ⟨hr_fin, hr'⟩
  rcases lt_iSup_iff.mp hr' with ⟨hsub, hyr⟩
  have hy_ball : y ∈ OpenBall d i x r ∩ U := ⟨hyr, hy⟩
  have hy_fiber := hsub hy_ball
  have hzero :=
    (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j)
      (φ.func y) (φ.func x)).mp hy_fiber.2
  exact hzero j (Finset.mem_singleton.mpr rfl)

/--
OET anchor: h-6ad76403c3bfeb84
**命题 #h-6ad76403c3bfeb84（统一零化半径给出的分离阈值，低于统一零化半径必归零）**
低于受限算子的统一零化半径时，输出在对应分量上零测距。
-/
theorem zero_of_lt_zero_radius
    (φ : Operator X bot) (A : Set X) (i j : I) (x y : X)
    (hx : x ∈ A)
    (hy : y ∈ A)
    (hxy : d i y x < min_annihilation_radius d φ i (singleton_nonempty_finset j) A) :
    d j (φ.func y)
      (φ.func x) = 0 :=
  zero_of_lt_min_annihilation_radius d φ
    A i j x y
    (min_annihilation_radius d φ i (singleton_nonempty_finset j) A) le_rfl hx hy hxy

/--
OET anchor: h-6ad76403c3bfeb84
**命题 #h-6ad76403c3bfeb84（统一零化半径给出的分离阈值，输出正分离时的输入距离下界）**
若受限算子的输出在目标分量上正分离，则输入距离不低于统一零化半径。
-/
theorem zero_radius_le_of_output_pos
    (φ : Operator X bot) (A : Set X) (i j : I) (x y : X)
    (hx : x ∈ A)
    (hy : y ∈ A)
    (hpos : 0 < d j (φ.func y)
      (φ.func x)) :
    min_annihilation_radius d φ i (singleton_nonempty_finset j) A ≤ d i y x := by
  by_contra hnot
  have hlt : d i y x < min_annihilation_radius d φ i (singleton_nonempty_finset j) A :=
    not_le.mp hnot
  have hzero := zero_of_lt_zero_radius d φ A i j x y hx hy hlt
  exact (ne_of_gt hpos) hzero

/--
OET anchor: h-6ad76403c3bfeb84
**命题 #h-6ad76403c3bfeb84（统一零化半径给出的分离阈值，低零化半径下的亚阈值输出分离见证）**
Every finite positive scale strictly above the local zeroing radius and below
its threshold admits a positive output separation. The interval premise already
implies that the zeroing radius is below the threshold.
-/
theorem subthreshold_separation_witness
    (τ_ν : ENNReal) (φ : Operator X bot) (A : Set X) (i j : I)
    (α : ENNReal)
    (hα_between : min_annihilation_radius d φ i (singleton_nonempty_finset j) A < α ∧ α < τ_ν)
    (hα_fin : FinitePositiveRadius α) :
    ∃ x ∈ A,
      ∃ y ∈ A,
        ∃ ε : ENNReal,
          FinitePositiveRadius ε ∧
            d i x y < α ∧
              ε ≤ d j (φ.func x)
                (φ.func y) := by
  classical
  have hzero_lt : min_annihilation_radius d φ i (singleton_nonempty_finset j) A < α := hα_between.1
  dsimp [min_annihilation_radius] at hzero_lt
  have hy_exists :
      ∃ y ∈ A,
        annihilation_radius d φ i
          (singleton_nonempty_finset j) A y < α := by
    by_contra hnone
    have hall :
        ∀ y, y ∈ A →
          α ≤ annihilation_radius d φ i
            (singleton_nonempty_finset j) A y := by
      intro y hy
      exact le_of_not_gt (by
        intro hlt
        exact hnone ⟨y, hy, hlt⟩)
    have hle_inf :
        α ≤
          ⨅ y, ⨅ _hy : y ∈ A,
            annihilation_radius d φ i
              (singleton_nonempty_finset j) A y := by
      exact le_iInf (fun y => le_iInf (fun hy => hall y hy))
    exact (not_lt_of_ge hle_inf) hzero_lt
  rcases hy_exists with ⟨y, hy, hy_ann_lt⟩
  by_contra hnot
  have h_ball_sub :
      OpenBall d i y α ∩ A ⊆
        ComputationalFiber d φ
          (singleton_nonempty_finset j) A
          (φ.func y) := by
    intro x hx
    by_contra hxfib
    have hdist_pos :
        0 < d j (φ.func x)
          (φ.func y) := by
      have hdist_ne :
          d j (φ.func x)
            (φ.func y) ≠ 0 := by
        intro hzero
        apply hxfib
        refine ⟨hx.2, ?_⟩
        apply (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j)
          (φ.func x)
          (φ.func y)).mpr
        intro k hk
        have hk_eq : k = j := Finset.mem_singleton.mp hk
        simpa [hk_eq] using hzero
      exact lt_of_le_of_ne' (zero_le _) hdist_ne
    let ε : ENNReal :=
      min (d j (φ.func x)
        (φ.func y)) 1
    have hε_pos : 0 < ε := by
      exact lt_min hdist_pos (by norm_num)
    have hε_ne_top : ε ≠ ⊤ := by
      exact ne_of_lt (lt_of_le_of_lt (min_le_right _ _) ENNReal.one_lt_top)
    have hε_le :
        ε ≤ d j (φ.func x)
          (φ.func y) :=
      min_le_left _ _
    apply hnot
    refine ⟨x, hx.2, y, hy, ε, ⟨⟨hε_pos, hε_ne_top⟩, ?_, hε_le⟩⟩
    exact hx.1
  have hα_le_ann :
      α ≤ annihilation_radius d φ i
        (singleton_nonempty_finset j) A y :=
    le_iSup_of_le α (le_iSup_of_le hα_fin (le_iSup_of_le h_ball_sub le_rfl))
  exact (not_le_of_gt hy_ann_lt) hα_le_ann

/--
OET anchor: h-9ecc7d0b4b541992
**命题 #h-9ecc7d0b4b541992（零化阈值下的纤维包含与覆盖数约束，纤维包含）**
零化半径下界在当前输入域上给出半径 `τ_ν` 的单分量计算纤维包含。
-/
theorem zero_radius_fiber_inclusion
    (τ_ν : ENNReal) (φ : Operator X bot) (A : Set X) (i j : I)
    (hν : τ_ν ≤ min_annihilation_radius d φ i (singleton_nonempty_finset j) A) :
    ∀ x ∈ A,
      OpenBall d i x τ_ν ∩ A ⊆
        ComputationalFiber d φ (singleton_nonempty_finset j)
          A
          (φ.func x) := by
  intro x hx y hy
  refine ⟨hy.2, ?_⟩
  apply (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j)
    (φ.func y)
    (φ.func x)).mpr
  intro k hk
  have hk_eq : k = j := Finset.mem_singleton.mp hk
  rw [hk_eq]
  exact zero_of_lt_min_annihilation_radius d φ
    A
    i j x y τ_ν hν hx hy.2 hy.1

/-- The actual diameter used by the default input scale: a supremum over all pairs. -/
def input_diameter (i : I) (D : Set X) : ENNReal :=
  ⨆ x ∈ D, ⨆ y ∈ D, d i x y

/-- Each pair in the evaluated domain is bounded by its actual diameter. -/
theorem component_distance_le_input_diameter (i : I) (D : Set X)
    (x y : X) (hx : x ∈ D) (hy : y ∈ D) :
    d i x y ≤ input_diameter d i D :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

/-- OET anchor: h-83287e414000b50b
默认直径尺度，由任意域上全部点对距离的上确界给出。 -/
noncomputable def diameter_scale_family : ScaleFamily X I where
  val := input_diameter d
  monotone := by
    intro i A B _hA _hB hAB
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    exact component_distance_le_input_diameter d i B x y (hAB hx) (hAB hy)

/-- An output component constant on the evaluated domain has infinite
uniform zeroing radius for every input component. -/
theorem zero_radius_eq_top_of_output_zero
    (φ : Operator X bot) (A : Set X) (j : I)
    (hzero : ∀ x ∈ A,
      ∀ y ∈ A,
        d j (φ.func x)
          (φ.func y) = 0)
    (k : I) : min_annihilation_radius d φ k (singleton_nonempty_finset j) A = ⊤ := by
  apply top_unique
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  cases n with
  | zero => simp
  | succ n =>
      have hr : FinitePositiveRadius ((Nat.succ n : ℕ) : ENNReal) :=
        ⟨by exact_mod_cast Nat.succ_pos n, ENNReal.natCast_ne_top _⟩
      apply le_iSup_of_le ((Nat.succ n : ℕ) : ENNReal)
      apply le_iSup_of_le hr
      have hfib : OpenBall d k y (Nat.succ n) ∩ A ⊆
          ComputationalFiber d φ (singleton_nonempty_finset j) A (φ.func y) := by
        intro x hx
        refine ⟨hx.2, ?_⟩
        rw [comp_pseudo_metric_singleton]
        exact hzero x hx.2 y hy
      exact le_iSup_of_le hfib le_rfl

/-- OET anchor: h-610f439b6ff59f79
小输入域上的整体零化判据. When the actual diameter is below the ordered
thresholds, the zeroing test is equivalent to zero distance of every output pair.
The implication needs no extra finiteness assumptions beyond these inequalities. -/
theorem joint_zeroing_iff
    (φ : Operator X bot) (A : Set X) (i j : I) (τ_σ τ_ν : ENNReal)
    (hdiam : input_diameter d i A < τ_σ)
    (hthreshold : τ_σ ≤ τ_ν) :
    τ_ν ≤ min_annihilation_radius d φ i (singleton_nonempty_finset j) A ↔
      ∀ x ∈ A,
        ∀ y ∈ A,
          d j (φ.func x)
            (φ.func y) = 0 := by
  constructor
  · intro hν x hx y hy
    apply zero_of_lt_min_annihilation_radius d φ A i j y x τ_ν hν hy hx
    exact lt_of_le_of_lt (component_distance_le_input_diameter d i _ x y hx hy)
      (lt_of_lt_of_le hdiam hthreshold)
  · intro hzero
    rw [zero_radius_eq_top_of_output_zero d φ A j hzero i]
    exact le_top

/-- The joint zeroing condition forces every radius
into the same output component to be infinite. -/
theorem joint_zeroing_all_radii_top
    (φ : Operator X bot) (A : Set X) (i j : I) (τ_σ τ_ν : ENNReal)
    (hdiam : input_diameter d i A < τ_σ)
    (hthreshold : τ_σ ≤ τ_ν)
    (hν : τ_ν ≤ min_annihilation_radius d φ i (singleton_nonempty_finset j) A) :
    ∀ k : I, min_annihilation_radius d φ k (singleton_nonempty_finset j) A = ⊤ :=
  zero_radius_eq_top_of_output_zero d φ A j
    ((joint_zeroing_iff d φ A i j τ_σ τ_ν hdiam hthreshold).mp hν)

end
end formal_oet.vol_01.ch_03_operator_local_degeneracy
