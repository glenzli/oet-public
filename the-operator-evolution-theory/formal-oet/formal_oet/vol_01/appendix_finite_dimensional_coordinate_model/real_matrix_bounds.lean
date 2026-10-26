import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.coordinate_gauge
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model

noncomputable section

open scoped BigOperators

variable {I X : Type} [Fintype I] [Nonempty I]
local instance inst_decidable_eq_i : DecidableEq I := Classical.decEq I

/-- A real matrix written with the OET input-to-output index order. -/
abbrev RealCertificate (I : Type) := I → I → ℝ

/-- The real realization of an entrywise finite ENNReal certificate. -/
def real_realization (A : I → I → ENNReal) : RealCertificate I :=
  fun i j => (A i j).toReal

/-- The maximum absolute coordinate of a finite vector. -/
def vector_sup_abs (u : I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => |u i|

/-- The output-row sum of an input-to-output certificate. -/
def output_row_sum (L : RealCertificate I) (j : I) : ℝ :=
  ∑ i : I, L i j

/-- The maximum output-row sum. -/
def matrix_infinity_bound (L : RealCertificate I) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (output_row_sum L)

/-- The maximum input-column sum. -/
def matrix_one_bound (L : RealCertificate I) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => ∑ j : I, L i j

/-- The weighted one-norm certificate from the coordinate-model appendix. -/
def weighted_one_bound (L : RealCertificate I) (w : I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i =>
    (1 / w i) * ∑ j : I, w j * L i j

/-- The weighted one norm. -/
def weighted_one_norm (w : I → ℝ) (u : I → ℝ) : ℝ :=
  ∑ i : I, w i * |u i|

/-- The real coordinate form of a finite coordinate Lip certificate. -/
def CoordinateLipBound (L : RealCertificate I) (f : X → I → ℝ)
    (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    |f x j - f y j| ≤ ∑ i : I, L i j * |f x i - f y i|

/-- A coordinate bound between a source readout and a target readout. -/
def CoordinateMapLipBound (L : RealCertificate I)
    (source target : X → I → ℝ) (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    |target x j - target y j| ≤
      ∑ i : I, L i j * |source x i - source y i|

/-- The real coordinate form of a finite coordinate co-Lip certificate. -/
def CoordinateCoLipBound (K : RealCertificate I)
    (source target : X → I → ℝ) (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    ∑ i : I, K i j * |source x i - source y i| ≤
      |target x j - target y j|

theorem coordinate_map_lip_sup_bound
    (L : RealCertificate I) (source target : X → I → ℝ) (U : Set X)
    (hL_nonneg : ∀ i j, 0 ≤ L i j)
    (hL : CoordinateMapLipBound L source target U)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    vector_sup_abs (target x - target y) ≤
      matrix_infinity_bound L * vector_sup_abs (source x - source y) := by
  apply Finset.sup'_le
  intro j _
  have hj := hL x hx y hy j
  calc
    |target x j - target y j| ≤
        ∑ i : I, L i j * |source x i - source y i| := hj
    _ ≤ ∑ i : I, L i j * vector_sup_abs (source x - source y) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hL_nonneg i j)
      change |source x i - source y i| ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun k : I => |source x k - source y k|)
      exact Finset.le_sup' (fun k : I => |source x k - source y k|)
        (Finset.mem_univ i)
    _ = output_row_sum L j * vector_sup_abs (source x - source y) := by
      simp [output_row_sum, Finset.sum_mul]
    _ ≤ matrix_infinity_bound L * vector_sup_abs (source x - source y) := by
      apply mul_le_mul_of_nonneg_right
      · exact Finset.le_sup' (output_row_sum L) (Finset.mem_univ j)
      · exact le_trans (abs_nonneg (source x (Classical.choice ‹Nonempty I›) -
            source y (Classical.choice ‹Nonempty I›)))
          (Finset.le_sup' (fun k : I => |source x k - source y k|)
            (Finset.mem_univ (Classical.choice ‹Nonempty I›)))

theorem coordinate_map_lip_weighted_one_bound
    (L : RealCertificate I) (source target : X → I → ℝ) (U : Set X)
    (w : I → ℝ) (hw : ∀ i, 0 < w i)
    (hL_nonneg : ∀ i j, 0 ≤ L i j)
    (hL : CoordinateMapLipBound L source target U)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    weighted_one_norm w (target x - target y) ≤
      weighted_one_bound L w * weighted_one_norm w (source x - source y) := by
  have _ := hL_nonneg
  calc
    weighted_one_norm w (target x - target y) =
        ∑ j : I, w j * |target x j - target y j| := by
          simp [weighted_one_norm]
    _ ≤ ∑ j : I, w j * (∑ i : I, L i j * |source x i - source y i|) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hL x hx y hy j) (le_of_lt (hw j))
    _ = ∑ i : I, (∑ j : I, w j * L i j) * |source x i - source y i| := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ i : I,
        (weighted_one_bound L w * w i) * |source x i - source y i| := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right
      · have hi := Finset.le_sup'
          (fun k : I => (1 / w k) * ∑ j : I, w j * L k j) (Finset.mem_univ i)
        have hwi : w i ≠0 := ne_of_gt (hw i)
        calc
          ∑ j : I, w j * L i j =
              ((1 / w i) * ∑ j : I, w j * L i j) * w i := by field_simp
          _ ≤ weighted_one_bound L w * w i :=
            mul_le_mul_of_nonneg_right hi (le_of_lt (hw i))
      · exact abs_nonneg _
    _ = weighted_one_bound L w * weighted_one_norm w (source x - source y) := by
      simp only [weighted_one_norm, Pi.sub_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/--
A standard Euclidean matrix-norm certificate. It packages only monotonicity of
the Euclidean norm on nonnegative vectors and the induced operator-norm bound.
-/
structure EuclideanMatrixNormCertificate (L : RealCertificate I) where
  operator_norm : ℝ
  euclidean_norm : (I → ℝ) → ℝ
  component_bound_to_norm :
    ∀ u v : I → ℝ,
      (∀ i, 0 ≤ u i) → (∀ j, 0 ≤ v j) →
      (∀ j, v j ≤ ∑ i : I, L i j * u i) →
      euclidean_norm v ≤ operator_norm * euclidean_norm u

/-- Comparison of a chosen finite-dimensional norm with the coordinate sup norm. -/
structure FiniteNormComparison where
  norm : (I → ℝ) → ℝ
  lower_constant : ℝ
  upper_constant : ℝ
  lower_positive : 0 < lower_constant
  upper_positive : 0 < upper_constant
  lower_bound : ∀ u, lower_constant * vector_sup_abs u ≤ norm u
  upper_bound : ∀ u, norm u ≤ upper_constant * vector_sup_abs u

/--
Auxiliary real-coordinate estimate. The actual matrix construction and the original
ENNReal model are connected in `euclidean_matrix_bound.lean` and `actual_norm_aggregation.lean`.
**命题（坐标 Lip 矩阵的范数聚合）**
坐标有限 Lip 证书给出最大范数、加权一范数与欧氏范数的标量上界。
The Euclidean interface is instantiated from a concrete continuous linear map in
`actual_euclidean_matrix_certificate`.
-/
theorem coordinate_lip_matrix_norm_aggregation
    (L : RealCertificate I) (source target : X → I → ℝ) (U : Set X)
    (w : I → ℝ) (hw : ∀ i, 0 < w i)
    (hL_nonneg : ∀ i j, 0 ≤ L i j)
    (hL : CoordinateMapLipBound L source target U)
    (euclidean : EuclideanMatrixNormCertificate L)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    vector_sup_abs (target x - target y) ≤
        matrix_infinity_bound L * vector_sup_abs (source x - source y) ∧
    weighted_one_norm w (target x - target y) ≤
        weighted_one_bound L w * weighted_one_norm w (source x - source y) ∧
    euclidean.euclidean_norm (fun j => |target x j - target y j|) ≤
        euclidean.operator_norm *
          euclidean.euclidean_norm (fun i => |source x i - source y i|) := by
  refine ⟨coordinate_map_lip_sup_bound L source target U hL_nonneg hL x y hx hy,
    coordinate_map_lip_weighted_one_bound L source target U w hw hL_nonneg hL x y hx hy,
    ?_⟩
  apply euclidean.component_bound_to_norm
  · intro i; exact abs_nonneg _
  · intro j; exact abs_nonneg _
  · exact hL x hx y hy

/--
Auxiliary real-coordinate estimate. The actual matrix construction and the original
ENNReal model are connected in `euclidean_matrix_bound.lean` and `actual_norm_aggregation.lean`.
**命题（坐标 Lip 矩阵的范数聚合，任意范数分支）**
范数等价常数把最大范数上界转为所选范数的上界。
-/
theorem coordinate_lip_arbitrary_norm_aggregation
    (L : RealCertificate I) (source target : X → I → ℝ) (U : Set X)
    (hL_nonneg : ∀ i j, 0 ≤ L i j)
    (hL : CoordinateMapLipBound L source target U)
    (comparison : FiniteNormComparison (I := I))
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    comparison.norm (target x - target y) ≤
      (comparison.upper_constant / comparison.lower_constant) *
        matrix_infinity_bound L * comparison.norm (source x - source y) := by
  have hsup := coordinate_map_lip_sup_bound L source target U hL_nonneg hL x y hx hy
  have hlpos := comparison.lower_positive
  let j₀ : I := Classical.choice ‹Nonempty I›
  have hmatrix_nonneg : 0 ≤ matrix_infinity_bound L := by
    calc
      0 ≤ output_row_sum L j₀ := Finset.sum_nonneg fun i _ => hL_nonneg i j₀
      _ ≤ matrix_infinity_bound L :=
        Finset.le_sup' (output_row_sum L) (Finset.mem_univ j₀)
  calc
    comparison.norm (target x - target y) ≤
        comparison.upper_constant * vector_sup_abs (target x - target y) :=
      comparison.upper_bound _
    _ ≤ comparison.upper_constant *
        (matrix_infinity_bound L * vector_sup_abs (source x - source y)) :=
      mul_le_mul_of_nonneg_left hsup (le_of_lt comparison.upper_positive)
    _ ≤ (comparison.upper_constant / comparison.lower_constant) *
        matrix_infinity_bound L * comparison.norm (source x - source y) := by
      have hs := comparison.lower_bound (source x - source y)
      have hc_nonneg :
          0 ≤ (comparison.upper_constant / comparison.lower_constant) *
            matrix_infinity_bound L :=
        mul_nonneg
          (div_nonneg (le_of_lt comparison.upper_positive)
            (le_of_lt comparison.lower_positive)) hmatrix_nonneg
      have hc := mul_le_mul_of_nonneg_left hs hc_nonneg
      calc
        comparison.upper_constant *
            (matrix_infinity_bound L * vector_sup_abs (source x - source y)) =
            ((comparison.upper_constant / comparison.lower_constant) *
              matrix_infinity_bound L) *
                (comparison.lower_constant * vector_sup_abs (source x - source y)) := by
          field_simp [ne_of_gt comparison.lower_positive]
        _ ≤ ((comparison.upper_constant / comparison.lower_constant) *
              matrix_infinity_bound L) * comparison.norm (source x - source y) := hc
        _ = (comparison.upper_constant / comparison.lower_constant) *
              matrix_infinity_bound L * comparison.norm (source x - source y) := by ring

/-- The coordinate co-Lip scalar extracted from a finite nonnegative matrix. -/
def coordinate_colip_modulus (K : RealCertificate I) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun i =>
    Finset.univ.sup' Finset.univ_nonempty fun j => K i j

theorem coordinate_colip_modulus_nonneg (K : RealCertificate I)
    (hK_nonneg : ∀ i j, 0 ≤ K i j) :
    0 ≤ coordinate_colip_modulus K := by
  apply Finset.le_inf'
  intro i _
  let j₀ : I := Classical.choice ‹Nonempty I›
  exact le_trans (hK_nonneg i j₀)
    (Finset.le_sup' (fun j : I => K i j) (Finset.mem_univ j₀))

theorem coordinate_colip_sup_lower
    (K : RealCertificate I) (source target : X → I → ℝ) (U : Set X)
    (hK_nonneg : ∀ i j, 0 ≤ K i j)
    (hK : CoordinateCoLipBound K source target U)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    coordinate_colip_modulus K * vector_sup_abs (source x - source y) ≤
      vector_sup_abs (target x - target y) := by
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i : I => |source x i - source y i|)
  obtain ⟨j₀, _, hj₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j : I => K i₀ j)
  have hmod : coordinate_colip_modulus K ≤ K i₀ j₀ := by
    calc
      coordinate_colip_modulus K ≤
          Finset.univ.sup' Finset.univ_nonempty (fun j : I => K i₀ j) :=
        Finset.inf'_le _ (Finset.mem_univ i₀)
      _ = K i₀ j₀ := hj₀
  calc
    coordinate_colip_modulus K * vector_sup_abs (source x - source y) =
        coordinate_colip_modulus K * |source x i₀ - source y i₀| := by
      unfold vector_sup_abs
      simp only [Pi.sub_apply]
      rw [hi₀]
    _ ≤ K i₀ j₀ * |source x i₀ - source y i₀| := by
      exact mul_le_mul_of_nonneg_right hmod (abs_nonneg _)
    _ ≤ ∑ i : I, K i j₀ * |source x i - source y i| := by
      apply Finset.single_le_sum (s := Finset.univ)
        (f := fun i : I => K i j₀ * |source x i - source y i|)
      · intro i _; exact mul_nonneg (hK_nonneg i j₀) (abs_nonneg _)
      · exact Finset.mem_univ i₀
    _ ≤ |target x j₀ - target y j₀| := hK x hx y hy j₀
    _ ≤ vector_sup_abs (target x - target y) := by
      change |target x j₀ - target y j₀| ≤
        Finset.univ.sup' Finset.univ_nonempty
          (fun j : I => |target x j - target y j|)
      exact Finset.le_sup' (fun j : I => |target x j - target y j|)
        (Finset.mem_univ j₀)

/--
OET anchor: h-69edb7c1cac5d49b
**命题（坐标 co-Lip 矩阵给出的范数下界）**
有限非负坐标 co-Lip 证书给出最大范数下界；正下界模推出单射。
-/
theorem coordinate_colip_matrix_norm_lower
    (K : RealCertificate I) (source target : X → I → ℝ) (U : Set X)
    (hK_nonneg : ∀ i j, 0 ≤ K i j)
    (hK : CoordinateCoLipBound K source target U)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) :
    coordinate_colip_modulus K * vector_sup_abs (source x - source y) ≤
      vector_sup_abs (target x - target y) :=
  coordinate_colip_sup_lower K source target U hK_nonneg hK x y hx hy

/--
OET anchor: h-69edb7c1cac5d49b
**命题（坐标 co-Lip 矩阵给出的范数下界，任意范数与单射分支）**
-/
theorem coordinate_colip_arbitrary_norm_and_injective
    (K : RealCertificate I) (source target : X → I → ℝ) (U : Set X)
    (hK_nonneg : ∀ i j, 0 ≤ K i j)
    (hK : CoordinateCoLipBound K source target U)
    (comparison : FiniteNormComparison (I := I))
    (hsource : Function.Injective source) :
    (∀ x ∈ U, ∀ y ∈ U,
      (comparison.lower_constant / comparison.upper_constant) *
          coordinate_colip_modulus K * comparison.norm (source x - source y) ≤
        comparison.norm (target x - target y)) ∧
    (0 < coordinate_colip_modulus K →
      Set.InjOn target U) := by
  constructor
  · intro x hx y hy
    have hsup := coordinate_colip_sup_lower K source target U hK_nonneg hK x y hx hy
    have hk_nonneg := coordinate_colip_modulus_nonneg K hK_nonneg
    calc
      (comparison.lower_constant / comparison.upper_constant) *
          coordinate_colip_modulus K * comparison.norm (source x - source y) ≤
          comparison.lower_constant *
            (coordinate_colip_modulus K * vector_sup_abs (source x - source y)) := by
        have hs := comparison.upper_bound (source x - source y)
        have hc_nonneg : 0 ≤
            (comparison.lower_constant / comparison.upper_constant) *
              coordinate_colip_modulus K :=
          mul_nonneg
            (div_nonneg (le_of_lt comparison.lower_positive)
              (le_of_lt comparison.upper_positive)) hk_nonneg
        have hc := mul_le_mul_of_nonneg_left hs hc_nonneg
        calc
          (comparison.lower_constant / comparison.upper_constant) *
              coordinate_colip_modulus K * comparison.norm (source x - source y) ≤
              ((comparison.lower_constant / comparison.upper_constant) *
                coordinate_colip_modulus K) *
                  (comparison.upper_constant * vector_sup_abs (source x - source y)) := hc
          _ = comparison.lower_constant *
                (coordinate_colip_modulus K * vector_sup_abs (source x - source y)) := by
            field_simp [ne_of_gt comparison.upper_positive]
      _ ≤ comparison.lower_constant * vector_sup_abs (target x - target y) :=
        mul_le_mul_of_nonneg_left hsup (le_of_lt comparison.lower_positive)
      _ ≤ comparison.norm (target x - target y) := comparison.lower_bound _
  · intro hkpos x hx y hy htarget
    apply hsource
    funext i
    by_contra hne
    have hsource_pos : 0 < vector_sup_abs (source x - source y) := by
      have hi : 0 < |source x i - source y i| := abs_pos.mpr (sub_ne_zero.mpr hne)
      exact lt_of_lt_of_le hi (by
        change |source x i - source y i| ≤
          Finset.univ.sup' Finset.univ_nonempty
            (fun k : I => |source x k - source y k|)
        exact Finset.le_sup' (fun k : I => |source x k - source y k|)
          (Finset.mem_univ i))
    have hpositive : 0 < coordinate_colip_modulus K *
        vector_sup_abs (source x - source y) := mul_pos hkpos hsource_pos
    have hlower := coordinate_colip_sup_lower K source target U hK_nonneg hK x y hx hy
    have htarget_zero : vector_sup_abs (target x - target y) = 0 := by
      rw [htarget]
      simp [vector_sup_abs]
    rw [htarget_zero] at hlower
    exact (not_lt_of_ge hlower) hpositive

/-- Positive entries feeding one output coordinate, written `\operatorname{supp}_j(\mathbf L)`
in the text. -/
def input_upper_support (L : RealCertificate I) (j : I) : Finset I :=
  Finset.univ.filter fun i => 0 < L i j

/-- Positive entries reached from one input coordinate. -/
def output_upper_support (L : RealCertificate I) (i : I) : Finset I :=
  Finset.univ.filter fun j => 0 < L i j

/-- Maximum entry of the selected finite nonnegative certificate, written `L_{\max}`
in the text. -/
def certificate_entry_max (L : RealCertificate I) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun ij : I × I => L ij.1 ij.2

/-- Maximum row support cardinality. -/
def row_support_size (L : RealCertificate I) : ℕ :=
  Finset.univ.sup fun j : I => (input_upper_support L j).card

/-- Maximum column support cardinality. -/
def column_support_size (L : RealCertificate I) : ℕ :=
  Finset.univ.sup fun i : I => (output_upper_support L i).card

/-- Total support cardinality. -/
def certificate_support_size (L : RealCertificate I) : ℕ :=
  (Finset.univ.filter fun ij : I × I => 0 < L ij.1 ij.2).card

theorem output_row_sum_le_support_mul_max
    (L : RealCertificate I) (hL_nonneg : ∀ i j, 0 ≤ L i j) (j : I) :
    output_row_sum L j ≤
      (input_upper_support L j).card * certificate_entry_max L := by
  calc
    output_row_sum L j = ∑ i ∈ input_upper_support L j, L i j := by
      rw [output_row_sum]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hnpos : ¬ 0 < L i j := by
        simpa [input_upper_support] using hi
      exact le_antisymm (not_lt.mp hnpos) (hL_nonneg i j)
    _ ≤ ∑ _i ∈ input_upper_support L j, certificate_entry_max L := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.le_sup'
        (fun ij : I × I => L ij.1 ij.2) (Finset.mem_univ (i, j))
    _ = (input_upper_support L j).card * certificate_entry_max L := by
      simp [nsmul_eq_mul]

theorem matrix_infinity_le_sparse_row_bound
    (L : RealCertificate I) (hL_nonneg : ∀ i j, 0 ≤ L i j) :
    matrix_infinity_bound L ≤
      row_support_size L * certificate_entry_max L := by
  apply Finset.sup'_le
  intro j _
  calc
    output_row_sum L j ≤
        (input_upper_support L j).card * certificate_entry_max L :=
      output_row_sum_le_support_mul_max L hL_nonneg j
    _ ≤ row_support_size L * certificate_entry_max L := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Finset.le_sup
          (s := Finset.univ) (f := fun k : I => (input_upper_support L k).card)
          (Finset.mem_univ j)
      · have ij : I × I := (Classical.choice ‹Nonempty I›,
            Classical.choice ‹Nonempty I›)
        exact le_trans (hL_nonneg ij.1 ij.2)
          (Finset.le_sup' (fun kl : I × I => L kl.1 kl.2) (Finset.mem_univ ij))

/-- The support of a coordinate difference. -/
def difference_support (source : X → I → ℝ) (x y : X) : Finset I :=
  Finset.univ.filter fun i => source x i ≠ source y i

/--
OET anchor: h-ad5d1c84e576f84a
**习题（证书支撑交叠下的分量传播界）**
单个输出分量的上界只计入证书支撑与输入差异支撑的交。
-/
theorem component_bound_by_support_overlap
    (L : RealCertificate I) (source target : X → I → ℝ) (U : Set X)
    (hL_nonneg : ∀ i j, 0 ≤ L i j)
    (hL : CoordinateMapLipBound L source target U)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    |target x j - target y j| ≤
      ((input_upper_support L j ∩ difference_support source x y).card : ℝ) *
        certificate_entry_max L * vector_sup_abs (source x - source y) := by
  calc
    |target x j - target y j| ≤
        ∑ i : I, L i j * |source x i - source y i| := hL x hx y hy j
    _ = ∑ i ∈ input_upper_support L j ∩ difference_support source x y,
          L i j * |source x i - source y i| := by
      symm
      apply Finset.sum_subset (by intro i hi; simp at hi ⊢)
      intro i _ hi
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and,
        input_upper_support, difference_support, not_and_or, not_lt] at hi
      rcases hi with hiL | hid
      · have hz : L i j = 0 := le_antisymm hiL (hL_nonneg i j)
        simp [hz]
      · simp [not_not.mp hid]
    _ ≤ ∑ _i ∈ input_upper_support L j ∩ difference_support source x y,
          certificate_entry_max L * vector_sup_abs (source x - source y) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul
      · exact Finset.le_sup'
          (fun ij : I × I => L ij.1 ij.2) (Finset.mem_univ (i, j))
      · change |source x i - source y i| ≤
          Finset.univ.sup' Finset.univ_nonempty
            (fun k : I => |source x k - source y k|)
        exact Finset.le_sup' (fun k : I => |source x k - source y k|)
          (Finset.mem_univ i)
      · exact abs_nonneg _
      · exact le_trans (hL_nonneg i j)
          (Finset.le_sup' (fun ij : I × I => L ij.1 ij.2)
            (Finset.mem_univ (i, j)))
    _ = ((input_upper_support L j ∩ difference_support source x y).card : ℝ) *
          certificate_entry_max L * vector_sup_abs (source x - source y) := by
      simp [nsmul_eq_mul]
      ring

end

end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
