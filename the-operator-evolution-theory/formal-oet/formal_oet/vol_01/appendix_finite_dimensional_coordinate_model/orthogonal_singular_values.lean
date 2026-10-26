import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.affine_singular_moduli
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Sort

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open scoped BigOperators
noncomputable section

private theorem count_ofFn_eq_card {n : ℕ} (f : Fin n → ℝ) (a : ℝ) :
    (List.ofFn f).count a = (Finset.univ.filter (fun i => f i = a)).card := by
  classical
  simpa using (Fin.card_filter_univ_eq_vector_get_eq_count a (List.Vector.ofFn f)).symm

private theorem antitone_eq_of_multiplicity {n : ℕ} (f g : Fin n → ℝ)
    (hf : Antitone f) (hg : Antitone g)
    (hcount : ∀ a, (Finset.univ.filter (fun i => f i = a)).card =
      (Finset.univ.filter (fun i => g i = a)).card) : f = g := by
  classical
  have hp : (List.ofFn f).Perm (List.ofFn g) := by
    apply List.perm_iff_count.mpr
    intro a
    simpa only [count_ofFn_eq_card] using hcount a
  have he : List.ofFn f = List.ofFn g := List.Perm.eq_of_pairwise' (r := fun a b : ℝ => b ≤ a)
    (List.pairwise_ofFn.mpr (fun _ _ hij => hf hij.le))
    (List.pairwise_ofFn.mpr (fun _ _ hij => hg hij.le)) hp
  exact List.ofFn_injective he

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Similarity identifies actual eigenspaces, including multiplicities. -/
def eigenspace_equiv_of_intertwining (T S : E →ₗ[ℝ] E) (U : E ≃ₗ[ℝ] E)
    (hU : ∀ x, S (U x) = U (T x)) (a : ℝ) :
    Module.End.eigenspace T a ≃ₗ[ℝ] Module.End.eigenspace S a where
  toFun x := ⟨U x, by
    rw [Module.End.mem_eigenspace_iff]
    rw [hU, (Module.End.mem_eigenspace_iff.mp x.property), map_smul]⟩
  invFun x := ⟨U.symm x, by
    rw [Module.End.mem_eigenspace_iff]
    apply U.injective
    rw [← hU, U.apply_symm_apply, (Module.End.mem_eigenspace_iff.mp x.property),
      map_smul, U.apply_symm_apply]⟩
  left_inv x := by ext; exact U.symm_apply_apply x
  right_inv x := by ext; exact U.apply_symm_apply x
  map_add' x y := by ext; exact U.map_add x y
  map_smul' a x := by ext; exact U.map_smul a x

theorem symmetric_eigenvalues_eq_of_intertwining
    (T S : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (U : E ≃ₗ[ℝ] E) (hU : ∀ x, S (U x) = U (T x))
    {n : ℕ} (hn : Module.finrank ℝ E = n) : hT.eigenvalues hn = hS.eigenvalues hn := by
  apply antitone_eq_of_multiplicity _ _ (hT.eigenvalues_antitone hn) (hS.eigenvalues_antitone hn)
  intro a
  calc
    _ = Module.finrank ℝ (Module.End.eigenspace T a) := by
      simpa using hT.card_filter_eigenvalues_eq hn a
    _ = Module.finrank ℝ (Module.End.eigenspace S a) :=
      (eigenspace_equiv_of_intertwining T S U hU a).finrank_eq
    _ = _ := by simpa using (hS.card_filter_eigenvalues_eq hn a).symm

/-- The actual two-sided orthogonal coordinate change from the text. -/
def orthogonal_transform (T : E →ₗ[ℝ] E) (U V : E ≃ₗᵢ[ℝ] E) : E →ₗ[ℝ] E :=
  V.toLinearMap ∘ₗ T ∘ₗ U.symm.toLinearMap

theorem orthogonal_transform_gram (T : E →ₗ[ℝ] E) (U V : E ≃ₗᵢ[ℝ] E) (x : E) :
    ((orthogonal_transform T U V).adjoint ∘ₗ orthogonal_transform T U V) (U x) =
      U ((T.adjoint ∘ₗ T) x) := by
  simp only [orthogonal_transform, LinearMap.adjoint_comp]
  rw [U.symm.adjoint_toLinearMap_eq_symm, V.adjoint_toLinearMap_eq_symm]
  simp

/--
OET anchor: h-e1bc9665adf4aeca
仿射算子的欧氏双侧界 (ii)：正交换基不变性及坐标支撑的边界。
Equality of every canonical Mathlib singular value, with multiplicity. The
orthogonal operators are actual linear isometries; spectral invariance is proved.
-/
theorem orthogonal_transform_singular_values (T : E →ₗ[ℝ] E) (U V : E ≃ₗᵢ[ℝ] E) :
    (orthogonal_transform T U V).singularValues = T.singularValues := by
  have he := symmetric_eigenvalues_eq_of_intertwining (T.adjoint ∘ₗ T)
    ((orthogonal_transform T U V).adjoint ∘ₗ orthogonal_transform T U V)
    T.isSymmetric_adjoint_comp_self (orthogonal_transform T U V).isSymmetric_adjoint_comp_self
    U.toLinearEquiv (orthogonal_transform_gram T U V) rfl
  ext k
  by_cases hk : k < Module.finrank ℝ E
  · rw [(orthogonal_transform T U V).singularValues_of_lt rfl hk,
      T.singularValues_of_lt rfl hk, he]
  · rw [(orthogonal_transform T U V).singularValues_of_finrank_le (Nat.le_of_not_gt hk),
      T.singularValues_of_finrank_le (Nat.le_of_not_gt hk)]

/--
OET anchor: h-e1bc9665adf4aeca
仿射算子的欧氏双侧界 (ii)：正交换基不变性及坐标支撑的边界。
The exact upper and lower distance-ratio moduli agree for the actual maps.
-/
theorem orthogonal_transform_exact_moduli (T : E →ₗ[ℝ] E) (U V : E ≃ₗᵢ[ℝ] E)
    {n : ℕ} [NeZero n] (hn : Module.finrank ℝ E = n) (b c : E) :
    sSup (pair_distance_ratio_set (fun x y : E => ‖x - y‖)
      (affine_euclidean_map (orthogonal_transform T U V) b)) =
      sSup (pair_distance_ratio_set (fun x y : E => ‖x - y‖) (affine_euclidean_map T c)) ∧
    sInf (pair_distance_ratio_set (fun x y : E => ‖x - y‖)
      (affine_euclidean_map (orthogonal_transform T U V) b)) =
      sInf (pair_distance_ratio_set (fun x y : E => ‖x - y‖) (affine_euclidean_map T c)) := by
  rw [(affine_exact_euclidean_moduli (orthogonal_transform T U V) hn b).1,
    (affine_exact_euclidean_moduli T hn c).1,
    (affine_exact_euclidean_moduli (orthogonal_transform T U V) hn b).2.1,
    (affine_exact_euclidean_moduli T hn c).2.1, orthogonal_transform_singular_values]
  exact ⟨rfl, rfl⟩

def support_projection_matrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]
def support_rotation_matrix : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / Real.sqrt 2, -(1 / Real.sqrt 2); 1 / Real.sqrt 2, 1 / Real.sqrt 2]

theorem support_rotation_orthogonal :
    support_rotation_matrix * support_rotation_matrix.transpose = 1 ∧
    support_rotation_matrix.transpose * support_rotation_matrix = 1 := by
  have hq : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp only [one_div] at hq
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, support_rotation_matrix, Matrix.one_apply] <;>
    nlinarith [hq]

theorem support_rotation_conjugate :
    support_rotation_matrix * support_projection_matrix * support_rotation_matrix.transpose =
      !![(1 / 2 : ℝ), 1 / 2; 1 / 2, 1 / 2] := by
  have hq : (1 / Real.sqrt 2) ^ 2 = (1 / 2 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  simp only [one_div] at hq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, support_rotation_matrix, support_projection_matrix] <;>
    nlinarith [hq]

/--
OET anchor: h-e1bc9665adf4aeca
仿射算子的欧氏双侧界 (ii)：正交换基不变性及坐标支撑的边界。
The displayed actual orthogonal matrix changes the support from one entry to
four and changes the absolute-value matrix.
-/
theorem orthogonal_support_counterexample :
    support_rotation_matrix * support_rotation_matrix.transpose = 1 ∧
    (Finset.univ.filter (fun ij : Fin 2 × Fin 2 => support_projection_matrix ij.1 ij.2 ≠ 0)).card = 1 ∧
    (Finset.univ.filter (fun ij : Fin 2 × Fin 2 =>
      (support_rotation_matrix * support_projection_matrix * support_rotation_matrix.transpose)
        ij.1 ij.2 ≠ 0)).card = 4 ∧
    (fun i j => |support_projection_matrix i j|) ≠
      (fun i j => |(support_rotation_matrix * support_projection_matrix *
        support_rotation_matrix.transpose) i j|) := by
  classical
  refine ⟨support_rotation_orthogonal.1, ?_, ?_, ?_⟩
  · have he : (Finset.univ.filter (fun ij : Fin 2 × Fin 2 =>
        support_projection_matrix ij.1 ij.2 ≠ 0)) = {(0, 0)} := by
      ext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> norm_num [support_projection_matrix]
    rw [he]
    simp
  · rw [support_rotation_conjugate]
    have he : (Finset.univ.filter (fun ij : Fin 2 × Fin 2 =>
        (!![(1 / 2 : ℝ), 1 / 2; 1 / 2, 1 / 2]) ij.1 ij.2 ≠ 0)) = Finset.univ := by
      ext ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> norm_num
    rw [he]
    decide
  · intro h
    have he := congrFun (congrFun h 0) 0
    rw [support_rotation_conjugate] at he
    norm_num [support_projection_matrix] at he

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
