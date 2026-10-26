import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix

namespace formal_oet.vol_01.ch_02_operator_bounds

set_option linter.style.longLine false

open formal_oet.vol_01.ch_01_foundations
open Finset

variable {X I : Type} {bot : X} [Fintype I]
variable (d : I → X → X → ENNReal)

/--
Source: vol-01-gauge-spaces-and-operators/02-operator-bounds.md,
分量通道（正文中的单行求和化简）.
If all entries in output row `j` vanish except possibly input `i`,
the Lip sum reduces to that input term. The coefficient may be zero or infinite.
-/
theorem lip_bound_of_single_input_row
    (ϕ : Operator X bot) (U : Set X) (L : I → I → ENNReal) (i j : I)
    (hL : IsLipMatrix d ϕ U L)
    (h_row_zero : ∀ k, k ≠ i → L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ L i j * d i x y := by
  intro x hx y hy
  have h_bound := hL.2 x hx y hy j
  have h_sum : ∑ k : I, L k j * d k x y = L i j * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      rw [h_row_zero k hki, zero_mul]
    · intro hi
      exact False.elim (hi (mem_univ i))
  rw [h_sum] at h_bound
  exact h_bound

/- A positive co-Lip entry reflects output zero-distance to its input channel. -/
theorem positive_colip_entry_reflects_zero
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d ϕ U K)
    (h_pos : K i j > 0) :
    ∀ x ∈ U, ∀ y ∈ U, d j (ϕ.func x) (ϕ.func y) = 0 → d i x y = 0 := by
  intro x hx y hy h_eq
  rcases hK with ⟨_, _, hK_ineq⟩
  have h_bound := hK_ineq x hx y hy j
  rw [h_eq] at h_bound
  have h_single : K i j * d i x y ≤ ∑ k : I, K k j * d k x y := by
    apply Finset.single_le_sum (f := fun i => K i j * d i x y)
    · intro _ _
      exact zero_le _
    · exact Finset.mem_univ i
  have h_zero : K i j * d i x y = 0 := by
    apply le_antisymm
    · exact le_trans h_single h_bound
    · exact zero_le _
  cases mul_eq_zero.mp h_zero with
  | inl hl =>
    exact False.elim (ne_of_gt h_pos hl)
  | inr hr =>
      exact hr

/--
OET anchor: h-6a98a58b5bc95360
**习题（对角输入项的标量双侧界）**
固定输出分量只需 Lip 上界的对角输入项条件；co-Lip 下界由非负和的单项得到。
-/
theorem bi_lip_scalar_bound (ϕ : Operator X bot) (U : Set X)
    (K L : I → I → ENNReal) (j : I)
    (hK : IsCoLipMatrix d ϕ U K)
    (hL : IsLipMatrix d ϕ U L)
    (h_row_zero : ∀ i, i ≠ j → L i j = 0) :
    ∀ x ∈ U, ∀ y ∈ U, K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧ d j (ϕ.func x) (ϕ.func y) ≤ L j j * d j x y := by
  intro x hx y hy
  constructor
  · exact le_trans
      (Finset.single_le_sum (fun i _ => zero_le (K i j * d i x y)) (mem_univ j))
      (hK.2.2 x hx y hy j)
  · exact lip_bound_of_single_input_row d ϕ U L j j hL h_row_zero x hx y hy

/--
OET anchor: h-f82672ec0dd48f28
**命题 #h-f82672ec0dd48f28（正 co-Lip 通道的可分辨保持）**
正 co-Lip 条目保持对应输入通道的可分辨性；全体对角条目为正时，
算子反射规范族的全分量零距关系。
-/
theorem positive_colip_channels_preserve_distinguishability
    (ϕ : Operator X bot) (U : Set X) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕ U K)
    :
    (∀ i j, K i j > 0 →
      ∀ x ∈ U, ∀ y ∈ U,
        d i x y > 0 → d j (ϕ.func x) (ϕ.func y) > 0) ∧
    ((∀ j, K j j > 0) →
      ∀ x ∈ U, ∀ y ∈ U,
        GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y) := by
  constructor
  · intro i j hij x hx y hy hxy
    by_contra hout
    have hout_zero : d j (ϕ.func x) (ϕ.func y) = 0 :=
      le_antisymm (not_lt.mp hout) (zero_le _)
    have hin_zero := positive_colip_entry_reflects_zero d ϕ U K i j hK hij x hx y hy hout_zero
    exact (ne_of_gt hxy) hin_zero
  · intro hdiag x hx y hy hout j
    exact positive_colip_entry_reflects_zero d ϕ U K j j hK (hdiag j)
      x hx y hy (hout j)

end formal_oet.vol_01.ch_02_operator_bounds
