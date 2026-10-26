import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.actual_norm_aggregation
import formal_oet.vol_01.ch_02_operator_bounds.path_algebra

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open WithLp
open scoped BigOperators
noncomputable section
variable {n : ℕ} [NeZero n]
local instance : DecidableEq (Fin n) := Classical.decEq _

theorem certificate_entry_max_nonneg (L : RealCertificate (Fin n)) (hL : ∀ i j, 0 ≤ L i j) :
    0 ≤ certificate_entry_max L :=
  (hL 0 0).trans (Finset.le_sup' (fun ij : Fin n × Fin n => L ij.1 ij.2) (Finset.mem_univ (0, 0)))

theorem matrix_one_le_sparse_column_bound (L : RealCertificate (Fin n))
    (hL : ∀ i j, 0 ≤ L i j) :
    matrix_one_bound L ≤ column_support_size L * certificate_entry_max L := by
  apply Finset.sup'_le
  intro i _
  have he : (∑ j, L i j) = ∑ j ∈ output_upper_support L i, L i j := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro j _ hj
    have hz : ¬ 0 < L i j := by simpa [output_upper_support] using hj
    exact le_antisymm (not_lt.mp hz) (hL i j)
  rw [he]
  calc
    _ ≤ ∑ _j ∈ output_upper_support L i, certificate_entry_max L :=
      Finset.sum_le_sum (fun j _ => Finset.le_sup' (fun ij : Fin n × Fin n => L ij.1 ij.2)
        (Finset.mem_univ (i, j)))
    _ = (output_upper_support L i).card * certificate_entry_max L := by simp
    _ ≤ column_support_size L * certificate_entry_max L := by
      apply mul_le_mul_of_nonneg_right _ (certificate_entry_max_nonneg L hL)
      exact_mod_cast Finset.le_sup (f := fun i => (output_upper_support L i).card) (Finset.mem_univ i)

def certificate_frobenius_norm (L : RealCertificate (Fin n)) : ℝ :=
  Real.sqrt (∑ ij : Fin n × Fin n, L ij.1 ij.2 ^ 2)

theorem euclidean_operator_le_frobenius (L : RealCertificate (Fin n)) :
    ‖euclidean_certificate_operator L‖ ≤ certificate_frobenius_norm L := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  change ‖euclidean_certificate_operator L u‖ ^ 2 ≤
    (Real.sqrt (∑ ij : Fin n × Fin n, L ij.1 ij.2 ^ 2) * ‖u‖) ^ 2
  rw [mul_pow,
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  change (∑ j, (∑ i, L i j * u i) ^ 2) ≤ _
  calc
    _ ≤ ∑ j : Fin n, (∑ i : Fin n, L i j ^ 2) * (∑ i : Fin n, (u i) ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => L i j) (fun i => u i)
    _ = _ := by rw [← Finset.sum_mul, Fintype.sum_prod_type, Finset.sum_comm]

theorem frobenius_le_sparse_bound (L : RealCertificate (Fin n)) (hL : ∀ i j, 0 ≤ L i j) :
    certificate_frobenius_norm L ≤ Real.sqrt (certificate_support_size L) * certificate_entry_max L := by
  have hm := certificate_entry_max_nonneg L hL
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hm)).mp
  change (Real.sqrt (∑ ij : Fin n × Fin n, L ij.1 ij.2 ^ 2)) ^ 2 ≤ _
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  let S := Finset.univ.filter (fun ij : Fin n × Fin n => 0 < L ij.1 ij.2)
  have he : (∑ ij : Fin n × Fin n, L ij.1 ij.2 ^ 2) = ∑ ij ∈ S, L ij.1 ij.2 ^ 2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro ij _ hij
    have hz : L ij.1 ij.2 = 0 := le_antisymm (by simpa [S] using hij) (hL _ _)
    simp [hz]
  rw [he]
  calc
    _ ≤ ∑ _ij ∈ S, certificate_entry_max L ^ 2 := by
      apply Finset.sum_le_sum
      intro ij _
      exact pow_le_pow_left₀ (hL _ _)
        (Finset.le_sup' (fun ij : Fin n × Fin n => L ij.1 ij.2) (Finset.mem_univ ij)) 2
    _ = _ := by simp [S, certificate_support_size]

/--
Actual row, column and Euclidean operator norms are bounded by support counts.
The Frobenius estimate is derived from finite Cauchy-Schwarz, not supplied.
-/
theorem sparse_actual_matrix_norm_bounds (L : RealCertificate (Fin n))
    (hL : ∀ i j, 0 ≤ L i j) :
    matrix_infinity_bound L ≤ row_support_size L * certificate_entry_max L ∧
    matrix_one_bound L ≤ column_support_size L * certificate_entry_max L ∧
    ‖euclidean_certificate_operator L‖ ≤ Real.sqrt (certificate_support_size L) * certificate_entry_max L :=
  ⟨matrix_infinity_le_sparse_row_bound L hL, matrix_one_le_sparse_column_bound L hL,
    (euclidean_operator_le_frobenius L).trans (frobenius_le_sparse_bound L hL)⟩

theorem coordinate_full_dist_readout {A : Set (CoordinateVector n)}
    (x y : CoordinatePoint n A) (hx : x ≠ none) (hy : y ≠ none) :
    coordinate_full_dist x y = ENNReal.ofReal ‖coordinate_readout x - coordinate_readout y‖ := by
  cases x with
  | none => exact (hx rfl).elim
  | some x =>
    cases y with
    | none => exact (hy rfl).elim
    | some y => exact coordinate_full_dist_eq_sup_norm x y

/--
Both stated propagation bounds hold for the original absorbing-point operator
and original extended distances, with its actual chosen finite Lip matrix.
-/
theorem sparse_actual_lip_distances {A : Set (CoordinateVector n)}
    (φ : Operator (CoordinatePoint n A) none) (Q : Set (CoordinatePoint n A))
    (L : Fin n → Fin n → ENNReal) (hf : ∀ i j, L i j ≠ ⊤)
    (hL : IsLipMatrix coordinate_dist φ Q L)
    (x y : CoordinatePoint n A) (hx : x ∈ Q) (hy : y ∈ Q) :
    coordinate_full_dist (φ.func x) (φ.func y) ≤
      ENNReal.ofReal (row_support_size (real_realization L) *
        certificate_entry_max (real_realization L)) *
        coordinate_full_dist x y ∧
    euclidean_distance (φ.func x) (φ.func y) ≤
      ENNReal.ofReal (Real.sqrt (certificate_support_size (real_realization L)) *
        certificate_entry_max (real_realization L)) * euclidean_distance x y := by
  have hs := sparse_actual_matrix_norm_bounds (real_realization L) (fun _ _ => ENNReal.toReal_nonneg)
  constructor
  · have h := (finite_lip_matrix_actual_norm_aggregation φ Q L hf hL (fun _ => 1)
      (fun _ => zero_lt_one) x y hx hy).1
    simp only [vector_sup_abs_eq_norm] at h
    rw [coordinate_full_dist_readout _ _ (hL.1 hx) (hL.1 hy),
      coordinate_full_dist_readout _ _ (domain_point_ne_bot φ x (hL.1 hx))
        (domain_point_ne_bot φ y (hL.1 hy)), ← ENNReal.ofReal_mul' (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (h.trans (mul_le_mul_of_nonneg_right hs.1 (norm_nonneg _)))
  · exact (finite_lip_matrix_weighted_and_euclidean_distance φ Q L hf hL (fun _ => 1)
      (fun _ => zero_lt_one) x y hx hy).2.trans
        (mul_le_mul_left (ENNReal.ofReal_le_ofReal hs.2.2) _)

/--
OET anchor: h-36ae8406e21d3213
**推论（行支撑控制的距离上界）**
The row-count coefficient controls the actual full-coordinate output distance
on the chosen operator domain, with the original finite ENNReal Lip certificate.
-/
theorem actual_row_count_lip_distance {A : Set (CoordinateVector n)}
    (φ : Operator (CoordinatePoint n A) none) (Q : Set (CoordinatePoint n A))
    (L : Fin n → Fin n → ENNReal) (hf : ∀ i j, L i j ≠ ⊤)
    (hL : IsLipMatrix coordinate_dist φ Q L)
    (x y : CoordinatePoint n A) (hx : x ∈ Q) (hy : y ∈ Q) :
    coordinate_full_dist (φ.func x) (φ.func y) ≤
      ENNReal.ofReal (row_support_size (real_realization L) *
        certificate_entry_max (real_realization L)) *
        coordinate_full_dist x y :=
  (sparse_actual_lip_distances φ Q L hf hL x y hx hy).1

/--
OET anchor: h-f09514ceb9b32a5a
**习题（非零计数与其他范数）**
The total number of nonzero entries controls the actual Euclidean propagation
bound for a finite Lip certificate; it is separate from the row-count theorem.
-/
theorem actual_total_count_euclidean_lip_distance {A : Set (CoordinateVector n)}
    (φ : Operator (CoordinatePoint n A) none) (Q : Set (CoordinatePoint n A))
    (L : Fin n → Fin n → ENNReal) (hf : ∀ i j, L i j ≠ ⊤)
    (hL : IsLipMatrix coordinate_dist φ Q L)
    (x y : CoordinatePoint n A) (hx : x ∈ Q) (hy : y ∈ Q) :
    euclidean_distance (φ.func x) (φ.func y) ≤
      ENNReal.ofReal (Real.sqrt (certificate_support_size (real_realization L)) *
        certificate_entry_max (real_realization L)) * euclidean_distance x y :=
  (sparse_actual_lip_distances φ Q L hf hL x y hx hy).2

/-- Maximum intersection with the actual input difference support. -/
def maximum_support_overlap {X : Type} (L : RealCertificate (Fin n))
    (source : X → CoordinateVector n) (x y : X) : ℕ :=
  Finset.univ.sup (fun j => (input_upper_support L j ∩ difference_support source x y).card)

/--
OET anchor: h-ad5d1c84e576f84a
**习题（证书支撑交叠下的分量传播界）**
Both the component and all-component conclusions use the original extended
distances and the actual finite matrix on the operator's restricted domain.
-/
theorem actual_support_overlap_distances {A : Set (CoordinateVector n)}
    (φ : Operator (CoordinatePoint n A) none) (Q : Set (CoordinatePoint n A))
    (L : Fin n → Fin n → ENNReal) (hf : ∀ i j, L i j ≠ ⊤)
    (hL : IsLipMatrix coordinate_dist φ Q L)
    (x y : CoordinatePoint n A) (hx : x ∈ Q) (hy : y ∈ Q) :
    (∀ j, coordinate_dist j (φ.func x) (φ.func y) ≤
      ENNReal.ofReal (certificate_entry_max (real_realization L) *
        (input_upper_support (real_realization L) j ∩
          difference_support coordinate_readout x y).card) * coordinate_full_dist x y) ∧
    coordinate_full_dist (φ.func x) (φ.func y) ≤
      ENNReal.ofReal (certificate_entry_max (real_realization L) *
        maximum_support_overlap (real_realization L) coordinate_readout x y) *
          coordinate_full_dist x y := by
  have h := component_bound_by_support_overlap (real_realization L)
    coordinate_readout (fun z => coordinate_readout (φ.func z)) Q
    (fun _ _ => ENNReal.toReal_nonneg) (finite_is_lip_matrix_real_bound φ Q L hf hL)
    x y hx hy
  simp only [vector_sup_abs_eq_norm] at h
  have hc : ∀ j, coordinate_dist j (φ.func x) (φ.func y) ≤
      ENNReal.ofReal (certificate_entry_max (real_realization L) *
        (input_upper_support (real_realization L) j ∩
          difference_support coordinate_readout x y).card) * coordinate_full_dist x y := by
    intro j
    rw [coordinate_distance_readout j _ _ (hL.1 hx) (hL.1 hy),
      coordinate_full_dist_readout _ _ (domain_point_ne_bot φ x (hL.1 hx))
        (domain_point_ne_bot φ y (hL.1 hy)), ← ENNReal.ofReal_mul' (norm_nonneg _)]
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_comm (certificate_entry_max (real_realization L))] using h j
  refine ⟨hc, ?_⟩
  change (Finset.univ.sup (fun j => coordinate_dist j (φ.func x) (φ.func y))) ≤ _
  apply Finset.sup_le
  intro j _
  apply (hc j).trans
  apply mul_le_mul_left
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _
    (certificate_entry_max_nonneg _ (fun _ _ => ENNReal.toReal_nonneg))
  exact_mod_cast Finset.le_sup
    (f := fun j => (input_upper_support (real_realization L) j ∩
      difference_support coordinate_readout x y).card) (Finset.mem_univ j)

/-- A real scalar read from the chosen finite ENNReal matrix, not an assumed bound. -/
def sparse_step_factor (L : Fin n → Fin n → ENNReal) : ℝ :=
  row_support_size (real_realization L) * certificate_entry_max (real_realization L)

theorem sparse_step_factor_nonneg (L : Fin n → Fin n → ENNReal) :
    0 ≤ sparse_step_factor L :=
  mul_nonneg (Nat.cast_nonneg _)
    (certificate_entry_max_nonneg _ (fun _ _ => ENNReal.toReal_nonneg))

/--
OET anchor: h-ef39fb9c4b025f07
**习题（逐步扰动与稀疏传播）**
The zero-residual specialization is proved for actual OET operator chains.
Each step matrix is assumed only
on the image of the preceding chain, exactly as in the textbook. Lists are
written outermost first; the scalar product is independent of this convention.
-/
theorem actual_sparse_chain_bound {A : Set (CoordinateVector n)}
    (operators : List (Operator (CoordinatePoint n A) none))
    (Q : Set (CoordinatePoint n A)) (matrices : List (Fin n → Fin n → ENNReal))
    (hchain : RightChainLipCertificateList coordinate_dist operators Q matrices)
    (hf : ∀ L ∈ matrices, ∀ i j, L i j ≠ ⊤)
    (x y : CoordinatePoint n A) (hx : x ∈ Q) (hy : y ∈ Q) :
    coordinate_full_dist ((OperatorChain operators).func x) ((OperatorChain operators).func y) ≤
      ENNReal.ofReal ((matrices.map sparse_step_factor).prod) * coordinate_full_dist x y := by
  induction hchain with
  | nil U hU => simpa [OperatorChain] using le_refl (coordinate_full_dist x y)
  | cons φ tail U L Ls htail hstep ih =>
    have hmid := ih (fun M hM => hf M (by simp [hM])) hx hy
    have hfinal := (sparse_actual_lip_distances φ _ L (hf L (by simp)) hstep
      _ _ (Set.mem_image_of_mem _ hx) (Set.mem_image_of_mem _ hy)).1
    change coordinate_full_dist (φ.func ((OperatorChain tail).func x))
      (φ.func ((OperatorChain tail).func y)) ≤ _
    calc
      _ ≤ ENNReal.ofReal (sparse_step_factor L) *
          coordinate_full_dist ((OperatorChain tail).func x) ((OperatorChain tail).func y) := hfinal
      _ ≤ ENNReal.ofReal (sparse_step_factor L) *
          (ENNReal.ofReal ((Ls.map sparse_step_factor).prod) * coordinate_full_dist x y) :=
        mul_le_mul_right hmid _
      _ = _ := by
        simp only [List.map_cons, List.prod_cons,
          ENNReal.ofReal_mul (sparse_step_factor_nonneg L), mul_assoc]

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
