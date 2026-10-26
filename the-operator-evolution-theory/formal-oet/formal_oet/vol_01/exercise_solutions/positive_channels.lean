import formal_oet.vol_01.appendix_separating_gauge_specialization.operator_and_chain
import formal_oet.vol_01.ch_02_operator_bounds.gauge_choice

namespace formal_oet.vol_01.exercise_solutions.positive_channels

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_02_operator_bounds.gauge_choice

noncomputable section

/--
OET anchor: h-218697f5beb9e317
每个输入分量至少有一个正 co-Lip 通道即可在分离规范空间中推出单射。
-/
theorem positive_channels_injective {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (hK : IsCoLipMatrix d φ U K)
    (hchannels : ∀ i, ∃ j, 0 < K i j) : Set.InjOn φ.func U := by
  intro x hx y hy hxy
  apply hsep x y
  intro i
  obtain ⟨j, hj⟩ := hchannels i
  exact positive_colip_entry_reflects_zero d φ U K i j hK hj x hx y hy
    (by rw [hxy, hd_self])

def swap_operator : Operator PlanePoint none :=
  ⟨Option.map (fun x => (x.2, x.1)), rfl⟩

def swap_matrix : Fin 2 → Fin 2 → ENNReal := ![![0, 1], ![1, 0]]

/--
OET anchor: h-218697f5beb9e317
坐标交换的非对角 co-Lip 矩阵在实际二维坐标规范上合法。
-/
theorem swap_colip : IsCoLipMatrix coordinate_dist swap_operator finite_part swap_matrix := by
  refine ⟨⟨some (0, 0), ⟨(0, 0), rfl⟩⟩, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    simp [dom, swap_operator]
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ j
    fin_cases j <;> simp [swap_matrix, swap_operator, coordinate_dist, read_coordinate,
      Fin.sum_univ_two]

/--
OET anchor: h-218697f5beb9e317
坐标规范确实分离整个吸收元扩展平面。
-/
theorem coordinate_dist_separating : IsSeparating coordinate_dist := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => rfl
    | some y => have hz := h 0; simp [coordinate_dist] at hz
  | some x =>
    cases y with
    | none => have hz := h 0; simp [coordinate_dist] at hz
    | some y =>
      have h0 := h 0
      have h1 := h 1
      simp [coordinate_dist, read_coordinate, ENNReal.ofReal_eq_zero] at h0 h1
      exact congrArg some (Prod.ext (sub_eq_zero.mp h0) (sub_eq_zero.mp h1))

/--
OET anchor: h-218697f5beb9e317
单射性由正通道条件推出，而该证书没有正对角条目。
-/
theorem swap_injective_without_positive_diagonal :
    Set.InjOn swap_operator.func finite_part ∧
      (∀ i, ∃ j, 0 < swap_matrix i j) ∧ (∀ i, swap_matrix i i = 0) := by
  have hc : ∀ i, ∃ j, 0 < swap_matrix i j := by
    intro i
    fin_cases i
    · exact ⟨1, by simp [swap_matrix]⟩
    · exact ⟨0, by simp [swap_matrix]⟩
  refine ⟨positive_channels_injective coordinate_dist
    (fun i x => (coordinate_dist_is_extended i).dist_self x)
    coordinate_dist_separating swap_operator finite_part swap_matrix swap_colip hc, hc, ?_⟩
  intro i
  fin_cases i <;> simp [swap_matrix]

/--
OET anchor: h-218697f5beb9e317
该单射的任意合法 co-Lip 矩阵均无正对角项。
-/
theorem swap_any_colip_diagonal_zero (K : Fin 2 → Fin 2 → ENNReal)
    (hK : IsCoLipMatrix coordinate_dist swap_operator finite_part K) :
    ∀ i, K i i = 0 := by
  have h0 := hK.2.2 (some (1, 0)) ⟨(1, 0), rfl⟩
    (some (0, 0)) ⟨(0, 0), rfl⟩ 0
  have h1 := hK.2.2 (some (0, 1)) ⟨(0, 1), rfl⟩
    (some (0, 0)) ⟨(0, 0), rfl⟩ 1
  norm_num [coordinate_dist, read_coordinate, swap_operator, Fin.sum_univ_two] at h0 h1
  intro i
  fin_cases i
  · exact h0
  · exact h1

end
end formal_oet.vol_01.exercise_solutions.positive_channels
