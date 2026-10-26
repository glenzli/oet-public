import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.euclidean_geometry
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.jacobi_coordinate_bridge

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open scoped BigOperators
noncomputable section

def rotation45 (x : CoordinateVector 2) : CoordinateVector 2 :=
  ![(x 0 - x 1) / Real.sqrt 2, (x 0 + x 1) / Real.sqrt 2]

theorem rotation45_sub (x y : CoordinateVector 2) : rotation45 (x - y) = rotation45 x - rotation45 y := by
  ext i
  fin_cases i <;> simp [rotation45] <;> ring

theorem rotation45_norm (x : CoordinateVector 2) :
    ‖euclidean_coordinates (rotation45 x)‖ = ‖euclidean_coordinates x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, euclidean_coordinates, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.toLp_apply, rotation45, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ring

/--
OET anchor: h-69edb7c1cac5d49b
坐标 co-Lip 证书与范数下界，第 (ii) 项：具体旋转给出欧氏等距见证。
-/
theorem rotation45_isometry (x y : CoordinateVector 2) :
    ‖euclidean_coordinates (rotation45 x - rotation45 y)‖ = ‖euclidean_coordinates (x - y)‖ := by
  rw [← rotation45_sub]
  exact rotation45_norm _

def rotation45_operator : Operator (CoordinatePoint 2 Set.univ) none :=
  coordinate_model_operator Set.univ Set.univ rotation45 (fun _ _ => Set.mem_univ _)

/--
OET anchor: h-69edb7c1cac5d49b
坐标 co-Lip 证书与范数下界，第 (ii) 项：旋转的所有扩展值坐标 co-Lip 矩阵均为零。
No finite-entry assumption is made; the two concrete cancelling pairs force all entries to zero.
-/
theorem rotation45_coordinate_colip_zero (K : Fin 2 → Fin 2 → ENNReal)
    (hK : IsCoLipMatrix coordinate_dist rotation45_operator
      (coordinate_model_set Set.univ Set.univ) K) : K = 0 := by
  let zero_point : CoordinatePoint 2 Set.univ := some ⟨0, Set.mem_univ _⟩
  let equal_point : CoordinatePoint 2 Set.univ := some ⟨![1, 1], Set.mem_univ _⟩
  let opposite_point : CoordinatePoint 2 Set.univ := some ⟨![1, -1], Set.mem_univ _⟩
  have hz : zero_point ∈ coordinate_model_set Set.univ Set.univ :=
    ⟨⟨0, Set.mem_univ _⟩, Set.mem_univ _, rfl⟩
  have he : equal_point ∈ coordinate_model_set Set.univ Set.univ :=
    ⟨⟨![1, 1], Set.mem_univ _⟩, Set.mem_univ _, rfl⟩
  have ho : opposite_point ∈ coordinate_model_set Set.univ Set.univ :=
    ⟨⟨![1, -1], Set.mem_univ _⟩, Set.mem_univ _, rfl⟩
  have hfirst : (∑ i : Fin 2, K i 0) ≤ 0 := by
    have h := hK.2.2 equal_point he zero_point hz 0
    simpa [equal_point, zero_point, rotation45_operator, coordinate_model_operator,
      coordinate_dist, rotation45, Fin.sum_univ_two] using h
  have hsecond : (∑ i : Fin 2, K i 1) ≤ 0 := by
    have h := hK.2.2 opposite_point ho zero_point hz 1
    simpa [opposite_point, zero_point, rotation45_operator, coordinate_model_operator,
      coordinate_dist, rotation45, Fin.sum_univ_two] using h
  funext i j
  have h (j : Fin 2) (hs : (∑ k : Fin 2, K k j) ≤ 0) : K i j = 0 :=
    le_antisymm ((Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)).trans hs) bot_le
  fin_cases j
  · exact h 0 hfirst
  · exact h 1 hsecond

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
