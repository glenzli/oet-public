import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.singular_geometry
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.orthogonal_and_calculus

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n : ℕ} [NeZero n] (T : E →ₗ[ℝ] E) (hn : Module.finrank ℝ E = n) (b : E)

def affine_euclidean_map (x : E) : E := T x + b

theorem affine_euclidean_difference (x y : E) :
    affine_euclidean_map T b x - affine_euclidean_map T b y = T (x - y) := by
  simp [affine_euclidean_map, map_sub]

include hn in
theorem affine_singular_bounds (x y : E) :
    T.singularValues (n - 1) * ‖x - y‖ ≤
      ‖affine_euclidean_map T b x - affine_euclidean_map T b y‖ ∧
    ‖affine_euclidean_map T b x - affine_euclidean_map T b y‖ ≤
      T.singularValues 0 * ‖x - y‖ := by
  rw [affine_euclidean_difference]
  exact singular_value_norm_bounds T hn (x - y)

include hn in
theorem singular_value_ratio_attained (i : Fin n) :
    T.singularValues i ∈ pair_distance_ratio_set (fun x y : E => ‖x - y‖)
      (affine_euclidean_map T b) := by
  refine ⟨singular_basis T hn i, 0, ?_, ?_, ?_⟩
  · intro h
    have hh := (singular_basis T hn).norm_eq_one i
    rw [h, norm_zero] at hh
    norm_num at hh
  · simp only [sub_zero, (singular_basis T hn).norm_eq_one]; norm_num
  · dsimp only
    rw [affine_euclidean_difference, sub_zero, norm_singular_basis,
      (singular_basis T hn).norm_eq_one, div_one]

include hn in
theorem affine_singular_extrema :
    IsGreatest (pair_distance_ratio_set (fun x y : E => ‖x - y‖)
      (affine_euclidean_map T b)) (T.singularValues 0) ∧
    IsLeast (pair_distance_ratio_set (fun x y : E => ‖x - y‖)
      (affine_euclidean_map T b)) (T.singularValues (n - 1)) := by
  constructor
  · refine ⟨singular_value_ratio_attained T hn b ⟨0, NeZero.pos n⟩, ?_⟩
    rintro r ⟨x, y, _, hpos, rfl⟩
    exact (div_le_iff₀ hpos).mpr (affine_singular_bounds T hn b x y).2
  · refine ⟨singular_value_ratio_attained T hn b ⟨n - 1, by have := NeZero.pos n; omega⟩, ?_⟩
    rintro r ⟨x, y, _, hpos, rfl⟩
    exact (le_div_iff₀ hpos).mpr (affine_singular_bounds T hn b x y).1

include hn in
theorem affine_injective_iff_singular_min_pos :
    Function.Injective (affine_euclidean_map T b) ↔ 0 < T.singularValues (n - 1) := by
  have hi : Function.Injective (affine_euclidean_map T b) ↔ Function.Injective T := by
    constructor
    · intro h x y he
      apply h
      simp only [affine_euclidean_map, he]
    · intro h x y he
      apply h
      exact add_right_cancel he
  rw [hi, T.injective_iff_forall_lt_finrank_singularValues_pos, hn]
  constructor
  · intro h
    exact h (n - 1) (by have := NeZero.pos n; omega)
  · intro h i hi
    exact lt_of_lt_of_le h (T.singularValues_antitone (by omega))

include hn in
/--
OET anchor: h-e1bc9665adf4aeca
仿射算子的欧氏双侧界 (i)：全空间最优上下界及单射判据。
The extrema are attained on actual unit singular vectors of the linear part.
The dimension is positive, as stipulated for the coordinate model in the coordinate-model appendix.
-/
theorem affine_exact_euclidean_moduli :
    sSup (pair_distance_ratio_set (fun x y : E => ‖x - y‖)
      (affine_euclidean_map T b)) = T.singularValues 0 ∧
    sInf (pair_distance_ratio_set (fun x y : E => ‖x - y‖)
      (affine_euclidean_map T b)) = T.singularValues (n - 1) ∧
    (∀ x y, T.singularValues (n - 1) * ‖x - y‖ ≤
        ‖affine_euclidean_map T b x - affine_euclidean_map T b y‖ ∧
      ‖affine_euclidean_map T b x - affine_euclidean_map T b y‖ ≤
        T.singularValues 0 * ‖x - y‖) ∧
    (Function.Injective (affine_euclidean_map T b) ↔ 0 < T.singularValues (n - 1)) := by
  exact ⟨(affine_singular_extrema T hn b).1.csSup_eq,
    (affine_singular_extrema T hn b).2.csInf_eq,
    affine_singular_bounds T hn b, affine_injective_iff_singular_min_pos T hn b⟩

/--
OET anchor: h-e1bc9665adf4aeca
The whole-space optimal affine constants need not remain optimal after restriction
to an arbitrary subset. The identity on the real line has both optimal constants
equal to one, whereas on the nonempty singleton domain an upper constant zero
and, separately, a lower constant two are valid. These are separate improvements,
not a claimed pair of constants satisfying lower ≤ upper.
-/
theorem affine_restriction_need_not_preserve_optimal_moduli :
    let F : ℝ → ℝ := affine_euclidean_map LinearMap.id 0
    sSup (pair_distance_ratio_set (fun x y : ℝ => ‖x - y‖) F) = 1 ∧
    sInf (pair_distance_ratio_set (fun x y : ℝ => ‖x - y‖) F) = 1 ∧
    ({0} : Set ℝ).Nonempty ∧
    ∃ ℓ k : ℝ, 0 ≤ ℓ ∧ ℓ < 1 ∧ 1 < k ∧
      (∀ x ∈ ({0} : Set ℝ), ∀ y ∈ ({0} : Set ℝ),
        ‖F x - F y‖ ≤ ℓ * ‖x - y‖) ∧
      (∀ x ∈ ({0} : Set ℝ), ∀ y ∈ ({0} : Set ℝ),
        k * ‖x - y‖ ≤ ‖F x - F y‖) := by
  let T : ℝ →ₗ[ℝ] ℝ := LinearMap.id
  have hdim : Module.finrank ℝ ℝ = 1 := by simp
  have hsing : T.singularValues 0 = 1 :=
    singular_values_of_norm_scaling T hdim 1 (by intro v; simp [T]) (0 : Fin 1)
  have hmod := affine_exact_euclidean_moduli (n := 1) T hdim (0 : ℝ)
  dsimp only
  refine ⟨?_, ?_, ⟨0, by simp⟩, 0, 2, by norm_num, by norm_num,
    by norm_num, ?_, ?_⟩
  · simpa only [hsing] using hmod.1
  · simpa only [Nat.sub_self, hsing] using hmod.2.1
  · intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst x
    subst y
    simp
  · intro x hx y hy
    simp only [Set.mem_singleton_iff] at hx hy
    subst x
    subst y
    simp

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
