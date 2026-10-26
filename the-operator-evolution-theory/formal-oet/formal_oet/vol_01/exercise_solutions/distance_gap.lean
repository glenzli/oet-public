import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix

set_option linter.style.longLine false
set_option linter.style.emptyLine false

namespace formal_oet.vol_01.exercise_solutions.distance_gap

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open Finset

variable {X I : Type} {bot : X} [Fintype I]
local instance instDecidableEqIDistanceGap : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-092ba6f495b988c1
**习题（零化半径与距离间隙，(i)）**
若同一受限域与通道上 $r^{\mathrm N} > 0$ 且 $K_{i \to j} > 0$，则输入距离不落在 $(0, r^{\mathrm N})$ 内。
-/
theorem distance_gap_of_positive_annihilation_radius_and_colip
    (ϕ : Operator X bot) (U : Set X) (i j : I) (y : X) (hy : y ∈ U)
    (h_nu_pos : 0 < annihilation_radius d ϕ i (singleton_nonempty_finset j) U y)
    (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕ U K)
    (h_K_pos : 0 < K i j) :
    ∀ x ∈ U, d i x y = 0 ∨ annihilation_radius d ϕ i (singleton_nonempty_finset j) U y ≤ d i x y := by
  have _ := h_nu_pos
  intro x hx
  by_contra h_not
  simp only [not_or, not_le] at h_not
  have h_d_pos : 0 < d i x y := pos_iff_ne_zero.mpr h_not.1
  have h_d_lt : d i x y < annihilation_radius d ϕ i (singleton_nonempty_finset j) U y := h_not.2

  have h_exists : ∃ r : ENNReal, FinitePositiveRadius r ∧ OpenBall d i y r ∩ U ⊆ ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func y) ∧ d i x y < r := by
    have h_sup := lt_iSup_iff.mp h_d_lt
    rcases h_sup with ⟨r, h_r_lt⟩
    have h_sup2 := lt_iSup_iff.mp h_r_lt
    rcases h_sup2 with ⟨hr_pos, h_lt⟩
    have h_sup3 := lt_iSup_iff.mp h_lt
    rcases h_sup3 with ⟨h_sub, h_final⟩
    exact ⟨r, hr_pos, h_sub, h_final⟩

  rcases h_exists with ⟨r, _, h_subset, h_r_lt⟩
  have h_in_ball : x ∈ OpenBall d i y r := h_r_lt
  have h_in_inter : x ∈ OpenBall d i y r ∩ U := ⟨h_in_ball, hx⟩
  have h_in_fiber : x ∈ ComputationalFiber d ϕ (singleton_nonempty_finset j) U (ϕ.func y) := h_subset h_in_inter

  have h_fiber_zero : comp_pseudo_metric d (singleton_nonempty_finset j) (ϕ.func x) (ϕ.func y) = 0 := h_in_fiber.2
  have hd_j_zero : d j (ϕ.func x) (ϕ.func y) = 0 := by
    have h_iff := comp_pseudo_metric_eq_zero_iff d (singleton_nonempty_finset j) (ϕ.func x) (ϕ.func y)
    exact (h_iff.mp h_fiber_zero) j (Finset.mem_singleton.mpr rfl)

  rcases hK with ⟨_, _, hK_ineq⟩
  have h_colip := hK_ineq x hx y hy j
  have h_sum_lower : K i j * d i x y ≤ ∑ k : I, K k j * d k x y := by
    exact Finset.single_le_sum (fun (k : I) _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)

  have h_prod_pos : 0 < K i j * d i x y := by
    have h1 : K i j ≠ 0 := ne_of_gt h_K_pos
    have h2 : d i x y ≠ 0 := ne_of_gt h_d_pos
    have h_mul_ne_zero : K i j * d i x y ≠ 0 := by
      intro h
      cases mul_eq_zero.mp h with
      | inl hl => exact h1 hl
      | inr hr => exact h2 hr
    exact pos_iff_ne_zero.mpr h_mul_ne_zero

  have h_le : 0 < d j (ϕ.func x) (ϕ.func y) := by
    calc
      (0:ENNReal) < K i j * d i x y := h_prod_pos
      _ ≤ ∑ k : I, K k j * d k x y := h_sum_lower
      _ ≤ d j (ϕ.func x) (ϕ.func y) := h_colip

  have h_contra : (0:ENNReal) < 0 := by
    calc
      (0:ENNReal) < d j (ϕ.func x) (ϕ.func y) := h_le
      _ = 0 := hd_j_zero

  exact lt_irrefl 0 h_contra

/--
OET anchor: h-092ba6f495b988c1
**习题（零化半径与距离间隙，(ii)）**
若统一零化下界与同一通道的 co-Lip 系数均为正，则 $U$ 上的输入距离或为零，或不小于该统一下界。
-/
theorem uniform_distance_gap_of_positive_annihilation_radius_and_colip
    (ϕ : Operator X bot) (U : Set X) (i j : I)
    (h_min_nu_pos : 0 < min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U)
    (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕ U K)
    (h_K_pos : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, d i x y = 0 ∨ min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U ≤ d i x y := by
  intro x hx y hy
  have h_nu_pos : 0 < annihilation_radius d ϕ i (singleton_nonempty_finset j) U y := by
    calc
      0 < min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U := h_min_nu_pos
      _ ≤ annihilation_radius d ϕ i (singleton_nonempty_finset j) U y := iInf₂_le y hy
  have h_pt := distance_gap_of_positive_annihilation_radius_and_colip
    d ϕ U i j y hy h_nu_pos K hK h_K_pos x hx
  rcases h_pt with h_zero | h_le
  · exact Or.inl h_zero
  · apply Or.inr
    have h_min_le : min_annihilation_radius d ϕ i (singleton_nonempty_finset j) U ≤ annihilation_radius d ϕ i (singleton_nonempty_finset j) U y := iInf₂_le y hy
    exact le_trans h_min_le h_le

end

end formal_oet.vol_01.exercise_solutions.distance_gap
