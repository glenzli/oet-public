import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X} [Fintype I]
local instance instDecidableEqIZeroingComposition : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-1217d1061a2c95ce
**命题 #h-1217d1061a2c95ce（统一零化半径的复合下界，(i)）**
复合零化半径至少继承前因子零化半径。
-/
theorem front_zeroing_radius_propagates
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i l j : I)
    (h_preserve : ∀ y₁ ∈ ϕ₁.func '' U, ∀ y₂ ∈ ϕ₁.func '' U,
      d l y₁ y₂ = 0 → d j (ϕ₂.func y₁) (ϕ₂.func y₂) = 0) :
    min_annihilation_radius d ϕ₁ i (singleton_nonempty_finset l) U ≤
      min_annihilation_radius d (OperatorChain [ϕ₂, ϕ₁]) i
        (singleton_nonempty_finset j) U := by
  dsimp [min_annihilation_radius]
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply ann_radius_ge
  intro r _hr_fin hr_lt x hx
  have hx_U : x ∈ U := hx.2
  have h_d_lt_min :
      d i x y < ⨅ z ∈ U, annihilation_radius d ϕ₁ i (singleton_nonempty_finset l) U z :=
    lt_trans hx.1 hr_lt
  have h_min_le_ann :
      (⨅ z ∈ U, annihilation_radius d ϕ₁ i (singleton_nonempty_finset l) U z) ≤
        annihilation_radius d ϕ₁ i (singleton_nonempty_finset l) U y :=
    iInf₂_le y hy
  have h_lt_ann :
      d i x y < annihilation_radius d ϕ₁ i (singleton_nonempty_finset l) U y :=
    lt_of_lt_of_le h_d_lt_min h_min_le_ann
  dsimp [annihilation_radius] at h_lt_ann
  rcases lt_iSup_iff.mp h_lt_ann with ⟨r₁, hr₁⟩
  rcases lt_iSup_iff.mp hr₁ with ⟨_hr₁_fin, hr₁'⟩
  rcases lt_iSup_iff.mp hr₁' with ⟨h_subset, hdist_lt_r₁⟩
  have hx_in_ball : x ∈ OpenBall d i y r₁ ∩ U := ⟨hdist_lt_r₁, hx_U⟩
  have h_fiber := h_subset hx_in_ball
  have h_l_zero : d l (ϕ₁.func x) (ϕ₁.func y) = 0 := by
    have h_iff :=
      comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset l)
        (ϕ₁.func x) (ϕ₁.func y)
    exact (h_iff.mp h_fiber.2) l (Finset.mem_singleton.mpr rfl)
  dsimp [ComputationalFiber]
  constructor
  · exact hx_U
  · apply (comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j)
      ((OperatorChain [ϕ₂, ϕ₁]).func x)
      ((OperatorChain [ϕ₂, ϕ₁]).func y)).mpr
    intro k hk
    have hk_eq : k = j := Finset.mem_singleton.mp hk
    rw [hk_eq]
    dsimp [OperatorChain]
    exact h_preserve (ϕ₁.func x) (Set.mem_image_of_mem ϕ₁.func hx_U)
      (ϕ₁.func y) (Set.mem_image_of_mem ϕ₁.func hy) h_l_zero

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-1217d1061a2c95ce
**命题 #h-1217d1061a2c95ce（统一零化半径的复合下界，(ii)）**
复合零化半径至少包含后因子零化半径的 Lip 拉回。
-/
theorem back_zeroing_pullback_radius
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i l j : I) (L : ENNReal)
    (hL_pos : 0 < L) (hL_finite : L ≠ ⊤)
    (h_lip : HasScalarLipBound d ϕ₁ U i l L) :
    min_annihilation_radius d ϕ₂ l (singleton_nonempty_finset j) (ϕ₁.func '' U) / L ≤
      min_annihilation_radius d (OperatorChain [ϕ₂, ϕ₁]) i
        (singleton_nonempty_finset j) U := by
  have _ := hL_pos
  have _ := hL_finite
  dsimp [min_annihilation_radius]
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply ann_radius_ge
  intro r _hr_fin hr_lt x hx
  have hx_U : x ∈ U := hx.2
  have h_d_lt_div :
      d i x y <
        (⨅ z ∈ ϕ₁.func '' U,
          annihilation_radius d ϕ₂ l (singleton_nonempty_finset j) (ϕ₁.func '' U) z) / L :=
    lt_trans hx.1 hr_lt
  have h_lip_bound : d l (ϕ₁.func x) (ϕ₁.func y) ≤ L * d i x y :=
    h_lip.2 x hx_U y hy
  have h_min_le_ann :
      (⨅ z ∈ ϕ₁.func '' U,
          annihilation_radius d ϕ₂ l (singleton_nonempty_finset j) (ϕ₁.func '' U) z) ≤
        annihilation_radius d ϕ₂ l (singleton_nonempty_finset j)
          (ϕ₁.func '' U) (ϕ₁.func y) := by
    exact iInf₂_le (ϕ₁.func y) (Set.mem_image_of_mem ϕ₁.func hy)
  have h_mul_lt_min :
      L * d i x y <
        (⨅ z ∈ ϕ₁.func '' U,
          annihilation_radius d ϕ₂ l (singleton_nonempty_finset j) (ϕ₁.func '' U) z) :=
    ENNReal.mul_lt_of_lt_div' h_d_lt_div
  have h_lt_ann :
      d l (ϕ₁.func x) (ϕ₁.func y) <
        annihilation_radius d ϕ₂ l (singleton_nonempty_finset j)
          (ϕ₁.func '' U) (ϕ₁.func y) :=
    lt_of_le_of_lt h_lip_bound (lt_of_lt_of_le h_mul_lt_min h_min_le_ann)
  dsimp [annihilation_radius] at h_lt_ann
  rcases lt_iSup_iff.mp h_lt_ann with ⟨r₂, hr₂⟩
  rcases lt_iSup_iff.mp hr₂ with ⟨_hr₂_fin, hr₂'⟩
  rcases lt_iSup_iff.mp hr₂' with ⟨h_subset, hdist_lt_r₂⟩
  have hx_in_ball :
      ϕ₁.func x ∈ OpenBall d l (ϕ₁.func y) r₂ ∩ (ϕ₁.func '' U) :=
    ⟨hdist_lt_r₂, Set.mem_image_of_mem ϕ₁.func hx_U⟩
  have h_fiber := h_subset hx_in_ball
  dsimp [ComputationalFiber]
  constructor
  · exact hx_U
  · simpa [OperatorChain] using h_fiber.2

end

end formal_oet.vol_01.ch_03_operator_local_degeneracy
