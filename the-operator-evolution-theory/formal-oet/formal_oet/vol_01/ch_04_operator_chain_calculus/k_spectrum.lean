import formal_oet.vol_01.ch_04_operator_chain_calculus.entropy_recurrence

namespace formal_oet.vol_01.ch_04_operator_chain_calculus

/--
下界序列具有正下界子列：任意尾部之后仍可找到正的下界。
K 下界序列的抽象辅助条件。
-/
def HasPositiveLowerSubsequence (lower : ℕ → ENNReal) : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, 0 < lower n

/-- 某距离序列最终归零。 -/
def EventuallyZero (dist : ℕ → ENNReal) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, dist n = 0

/--
若某个 co-Lip 推出的下界在任意尾部仍为正，并且该下界逐步压住真实距离，
则真实距离不可能最终精确归零。
-/
theorem positive_lower_subsequence_obstructs_eventual_zero
    (lower dist : ℕ → ENNReal)
    (h_pos : HasPositiveLowerSubsequence lower)
    (h_lower : ∀ n, lower n ≤ dist n) :
    ¬ EventuallyZero dist := by
  rintro ⟨N, h_zero⟩
  rcases h_pos N with ⟨n, hnN, hln_pos⟩
  have hdn_pos : 0 < dist n := lt_of_lt_of_le hln_pos (h_lower n)
  rw [h_zero n hnN] at hdn_pos
  exact lt_irrefl (0 : ENNReal) hdn_pos

/--
矩阵幂版本的同一判据：令 `lower n = K^n_{i→j} · d_i(x,x')` 后即可使用。
-/
theorem k_power_lower_obstructs_eventual_zero
    (Kpow : ℕ → ENNReal) (D : ENNReal) (dist : ℕ → ENNReal)
    (h_pos : HasPositiveLowerSubsequence (fun n => Kpow n * D))
    (h_lower : ∀ n, Kpow n * D ≤ dist n) :
    ¬ EventuallyZero dist := by
  exact positive_lower_subsequence_obstructs_eventual_zero
    (fun n => Kpow n * D) dist h_pos h_lower

/--
若 `d i` 在 `U` 上恒为零，则 `U` 中不存在正 `d i`-距离点对。
-/
theorem degenerate_source_component_no_positive_pair
    {I : Type} (d : I → X → X → ENNReal) (U : Set X) (i : I)
    (hdeg : ∀ x ∈ U, ∀ y ∈ U, d i x y = 0) :
    ¬ ∃ x, x ∈ U ∧ ∃ y, y ∈ U ∧ 0 < d i x y := by
  rintro ⟨x, hx, y, hy, hpos⟩
  rw [hdeg x hx y hy] at hpos
  exact (lt_irrefl (0 : ENNReal)) hpos

end formal_oet.vol_01.ch_04_operator_chain_calculus
