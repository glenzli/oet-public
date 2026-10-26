import formal_oet.vol_01.ch_03_operator_local_degeneracy.mapping_entropy
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_04_operator_chain_calculus

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

/-- The one-based finite chain `ϕₖ ∘ ⋯ ∘ ϕ₁`. -/
def finite_one_based_chain {X : Type} {bot : X}
    (ϕ : ℕ → Operator X bot) (k : ℕ) : Operator X bot :=
  OperatorChain ((List.range k).reverse.map fun m => ϕ (m + 1))

/--
单步熵差。
《算子链演算》的熵递推只使用有限实值熵的代数望远镜等式。
-/
def entropy_drop (E : ℕ → ℝ) (m : ℕ) : ℝ := E m - E (m + 1)

theorem ereal_coe_finset_sum {A : Type} (s : Finset A) (f : A → ℝ) :
    (∑ a ∈ s, ((f a : ℝ) : EReal)) = (((∑ a ∈ s, f a) : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/--
零起点版本的熵望远镜等式。
-/
theorem entropy_telescoping_zero_index (E : ℕ → ℝ) (k : ℕ) :
    E k + (Finset.range k).sum (fun m => entropy_drop E m) = E 0 := by
  induction k with
  | zero =>
      simp [entropy_drop]
  | succ k ih =>
      rw [Finset.sum_range_succ]
      dsimp [entropy_drop] at *
      linarith

/--
OET anchor: h-2cb9c1e3d59895b0
**推论 #h-2cb9c1e3d59895b0（算子链的熵递推等式）的有限实值熵递推核心**
按正文的一起点编号：
`E_{k+1} + ∑_{m=1}^{k} ΔE_m = E_1`。
-/
theorem entropy_telescoping_one_index (E : ℕ → ℝ) (k : ℕ) :
    E (k + 1) + (Finset.range k).sum (fun m => entropy_drop E (m + 1)) = E 1 := by
  simpa [entropy_drop, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
    using entropy_telescoping_zero_index (fun n => E (n + 1)) k

/-- The proof-independent value of a well-defined single-component entropy drop. -/
noncomputable def mapping_entropy_drop_value {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (i : I) (ε : ENNReal) : EReal :=
  metric_entropy (d i) ε U - metric_entropy (d i) ε (ϕ.func '' U)

theorem mapping_entropy_drop_value_eq_mapping_entropy_diff
    {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (i : I) (ε : ENNReal) (hwd : EntropyDiffWellDefined d ϕ U i i ε) :
    mapping_entropy_drop_value d ϕ U i ε =
      mapping_entropy_diff d ϕ U i i ε hwd := by
  rfl

set_option linter.unusedFintypeInType false in
/--
OET anchor: h-2cb9c1e3d59895b0
**推论 #h-2cb9c1e3d59895b0（算子链的熵递推等式）**

正文命题的算子链版本。初始域可以是复合定义域的任意非空子集，亦允许空链；
每个熵由有限实数 `E m` 表示，熵差在实际像域上读取。
-/
theorem chain_entropy_recurrence_textbook
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : ℕ → Operator X bot)
    (U : ℕ → Set X) (E : ℕ → ℝ) (i : I) (ε : ENNReal)
    (hε : 0 < ε) (hε_top : ε ≠ ⊤) (k : ℕ)
    (hU1 : U 1 ⊆ dom (finite_one_based_chain ϕ k))
    (hU1_nonempty : (U 1).Nonempty)
    (himage : ∀ m, 1 ≤ m → m ≤ k → U (m + 1) = (ϕ m).func '' U m)
    (hentropy : ∀ m, 1 ≤ m → m ≤ k + 1 →
      metric_entropy (d i) ε (U m) = (E m : EReal)) :
    ∃ hwd : ∀ m : Fin k,
        EntropyDiffWellDefined d (ϕ (m.val + 1)) (U (m.val + 1)) i i ε,
      metric_entropy (d i) ε (U (k + 1)) =
        metric_entropy (d i) ε (U 1) -
          ∑ m : Fin k,
            mapping_entropy_diff d (ϕ (m.val + 1)) (U (m.val + 1)) i i ε (hwd m) := by
  have _ := hε
  have _ := hε_top
  have _ := hU1
  have hU_nonempty : ∀ r : ℕ, r < k → (U (r + 1)).Nonempty := by
    intro r
    induction r with
    | zero =>
        intro _hr
        simpa using hU1_nonempty
    | succ r ih =>
        intro hr
        have hprev : (U (r + 1)).Nonempty := ih (by omega)
        rw [himage (r + 1) (by omega) (by omega)]
        exact hprev.image (ϕ (r + 1)).func
  let hwd : ∀ m : Fin k,
      EntropyDiffWellDefined d (ϕ (m.val + 1)) (U (m.val + 1)) i i ε :=
    fun m =>
      ⟨hU_nonempty m.val m.isLt,
        Or.inl (cov_num_lt_top_of_metric_entropy_eq_real d i ε
          (U (m.val + 1)) (E (m.val + 1))
          (hentropy (m.val + 1) (by omega) (by omega)))⟩
  have hstep : ∀ m : Fin k,
      mapping_entropy_diff d (ϕ (m.val + 1)) (U (m.val + 1)) i i ε (hwd m) =
        ((entropy_drop E (m.val + 1) : ℝ) : EReal) := by
    intro m
    change metric_entropy (d i) ε (U (m.val + 1)) -
        metric_entropy (d i) ε ((ϕ (m.val + 1)).func '' U (m.val + 1)) = _
    rw [← himage (m.val + 1) (by omega) (by omega)]
    rw [hentropy (m.val + 1) (by omega) (by omega),
      hentropy (m.val + 2) (by omega) (by omega)]
    simp [entropy_drop]
  have hsum :
      (∑ m : Fin k,
        mapping_entropy_diff d (ϕ (m.val + 1)) (U (m.val + 1)) i i ε (hwd m)) =
      (((∑ m : Fin k, entropy_drop E (m.val + 1)) : ℝ) : EReal) := by
    calc
      _ = ∑ m : Fin k, ((entropy_drop E (m.val + 1) : ℝ) : EReal) := by
        apply Finset.sum_congr rfl
        intro m _hm
        exact hstep m
      _ = (((∑ m : Fin k, entropy_drop E (m.val + 1)) : ℝ) : EReal) := by
        exact ereal_coe_finset_sum (Finset.univ : Finset (Fin k))
          (fun m => entropy_drop E (m.val + 1))
  have hreal : E (k + 1) = E 1 -
      (∑ m : Fin k, entropy_drop E (m.val + 1)) := by
    have hrec := entropy_telescoping_one_index E k
    rw [Fin.sum_univ_eq_sum_range (fun r => entropy_drop E (r + 1)) k]
    linarith
  refine ⟨hwd, ?_⟩
  rw [hentropy (k + 1) (by omega) (le_refl _),
    hentropy 1 (by omega) (by omega), hsum]
  simpa using congrArg (fun z : ℝ => (z : EReal)) hreal

/-- The real finite-sequence core used by the textbook uniform-drop corollary. -/
theorem entropy_uniform_drop_reaches_zero (E : ℕ → ℝ) (k_star : ℕ)
    (δ : ℝ)
    (h_nonnegative : ∀ m, 1 ≤ m → m ≤ k_star + 1 → 0 ≤ E m)
    (h_initial : E 1 ≤ (k_star : ℝ) * δ)
    (h_drop : ∀ m, 1 ≤ m → m ≤ k_star → 0 < E m → δ ≤ entropy_drop E m) :
    ∃ m, 1 ≤ m ∧ m ≤ k_star + 1 ∧ E m = 0 := by
  by_contra hnone
  push Not at hnone
  have hpos : ∀ m, 1 ≤ m → m ≤ k_star + 1 → 0 < E m := by
    intro m hm1 hm
    exact lt_of_le_of_ne (h_nonnegative m hm1 hm) (Ne.symm (hnone m hm1 hm))
  have h_each : ∀ m ∈ Finset.range k_star, δ ≤ entropy_drop E (m + 1) := by
    intro m hm
    have hle_k : m + 1 ≤ k_star := Nat.succ_le_of_lt (Finset.mem_range.mp hm)
    exact h_drop (m + 1) (by omega) hle_k
      (hpos (m + 1) (by omega) (hle_k.trans (Nat.le_succ k_star)))
  have hsum_lower :
      (k_star : ℝ) * δ ≤
        (Finset.range k_star).sum (fun m => entropy_drop E (m + 1)) := by
    simpa using Finset.sum_le_sum h_each
  have htel := entropy_telescoping_one_index E k_star
  have hle_zero : E (k_star + 1) ≤ 0 := by
    linarith
  have hzero : E (k_star + 1) = 0 :=
    le_antisymm hle_zero (h_nonnegative (k_star + 1) (by omega) (le_refl _))
  exact hnone (k_star + 1) (by omega) (le_refl _) hzero

/--
OET anchor: h-b7e77b504317782a
OET anchor: h-f52ddbdb4056399a
**习题（一致正熵差下界给出的有限步熵归零）(i)：有限熵前缀**

当前缀熵为正时，题设给出每一步的熵差下界。以下只需这些有限下界与初始熵有限，
便可导出整个前缀的有限实数表示及逐步递推不等式；也允许零步前缀。
-/
theorem entropy_lower_bounded_drop_finite_prefix
    {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : ℕ → Operator X bot)
    (U : ℕ → Set X) (i : I) (ε : ENNReal) (e₁ δ : ℝ) (r : ℕ)
    (hU_nonempty : ∀ m, 1 ≤ m → m ≤ r + 1 → (U m).Nonempty)
    (himage : ∀ m, 1 ≤ m → m ≤ r → U (m + 1) = (ϕ m).func '' U m)
    (hE₁ : metric_entropy (d i) ε (U 1) = (e₁ : EReal))
    (hwd : ∀ m, 1 ≤ m → m ≤ r →
      EntropyDiffWellDefined d (ϕ m) (U m) i i ε)
    (hdrop : ∀ m (hm1 : 1 ≤ m) (hmr : m ≤ r),
      (δ : EReal) ≤ mapping_entropy_diff d (ϕ m) (U m) i i ε (hwd m hm1 hmr)) :
    ∃ E : ℕ → ℝ,
      (∀ m, 1 ≤ m → m ≤ r + 1 → metric_entropy (d i) ε (U m) = (E m : EReal)) ∧
      E 1 = e₁ ∧
      (∀ m, 1 ≤ m → m ≤ r + 1 → 0 ≤ E m) ∧
      (∀ m, 1 ≤ m → m ≤ r → E (m + 1) ≤ E m - δ) := by
  have hnonnegative : ∀ m, 1 ≤ m → m ≤ r + 1 →
      (0 : EReal) ≤ metric_entropy (d i) ε (U m) := by
    intro m hm1 hm
    exact metric_entropy_nonneg (d i) ε (U m) (hU_nonempty m hm1 hm)
  have hnot_bot : ∀ m, 1 ≤ m → m ≤ r + 1 →
      metric_entropy (d i) ε (U m) ≠ ⊥ := by
    intro m hm1 hm hbot
    have hnonneg := hnonnegative m hm1 hm
    rw [hbot] at hnonneg
    simp at hnonneg
  have hfinite_aux : ∀ n, n ≤ r → metric_entropy (d i) ε (U (n + 1)) ≠ ⊤ := by
    intro n hn
    induction n with
    | zero =>
        rw [hE₁]
        exact EReal.coe_ne_top e₁
    | succ n ih =>
        have hcur_top : metric_entropy (d i) ε (U (n + 1)) ≠ ⊤ := ih (by omega)
        have hcur_eq : metric_entropy (d i) ε (U (n + 1)) =
            ((metric_entropy (d i) ε (U (n + 1))).toReal : EReal) :=
          (EReal.coe_toReal hcur_top (hnot_bot (n + 1) (by omega) (by omega))).symm
        intro hnext_top
        have hδmap := hdrop (n + 1) (by omega) (by omega)
        rw [← mapping_entropy_drop_value_eq_mapping_entropy_diff d
          (ϕ (n + 1)) (U (n + 1)) i ε (hwd (n + 1) (by omega) (by omega))] at hδmap
        dsimp [mapping_entropy_drop_value] at hδmap
        rw [← himage (n + 1) (by omega) (by omega), hcur_eq, hnext_top] at hδmap
        simp at hδmap
  have hfinite : ∀ m, 1 ≤ m → m ≤ r + 1 → metric_entropy (d i) ε (U m) ≠ ⊤ := by
    intro m hm1 hm
    have heq : m - 1 + 1 = m := by omega
    rw [← heq]
    exact hfinite_aux (m - 1) (by omega)
  let E : ℕ → ℝ := fun m => (metric_entropy (d i) ε (U m)).toReal
  have hentropy : ∀ m, 1 ≤ m → m ≤ r + 1 →
      metric_entropy (d i) ε (U m) = (E m : EReal) := by
    intro m hm1 hm
    exact (EReal.coe_toReal (hfinite m hm1 hm) (hnot_bot m hm1 hm)).symm
  refine ⟨E, hentropy, ?_, ?_, ?_⟩
  · apply EReal.coe_eq_coe_iff.mp
    exact (hentropy 1 (by omega) (by omega)).symm.trans hE₁
  · intro m hm1 hm
    exact EReal.coe_nonneg.mp ((hentropy m hm1 hm).symm ▸ hnonnegative m hm1 hm)
  · intro m hm1 hmr
    have hδmap := hdrop m hm1 hmr
    rw [← mapping_entropy_drop_value_eq_mapping_entropy_diff d
      (ϕ m) (U m) i ε (hwd m hm1 hmr)] at hδmap
    dsimp [mapping_entropy_drop_value] at hδmap
    rw [← himage m hm1 hmr,
      hentropy m hm1 (by omega), hentropy (m + 1) (by omega) (by omega)] at hδmap
    have hreal : δ ≤ E m - E (m + 1) := by exact_mod_cast hδmap
    linarith

set_option linter.unusedFintypeInType false in
set_option linter.unusedVariables false in
/--
OET anchor: h-b7e77b504317782a
OET anchor: h-f52ddbdb4056399a
**习题（一致正熵差下界给出的有限步熵归零）(ii)：归零步数**

习题的上取整步数版本。若前缀尚未归零，调用 (i) 的有限熵前缀结论，
再由实数熵递推得到至多 `ceil (e₁ / δ)` 步后归零。
-/
theorem entropy_uniform_drop_reaches_zero_textbook
    {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : ℕ → Operator X bot)
    (U : ℕ → Set X) (i : I) (ε : ENNReal)
    (hε : 0 < ε) (hε_top : ε ≠ ⊤)
    (e₁ δ : ℝ) (he₁ : 0 ≤ e₁) (hδ : 0 < δ)
    (k : ℕ) (hk : Nat.ceil (e₁ / δ) ≤ k)
    (hU1 : U 1 = dom (finite_one_based_chain ϕ k))
    (hU_nonempty : ∀ m, 1 ≤ m → m ≤ k + 1 → (U m).Nonempty)
    (himage : ∀ m, 1 ≤ m → m ≤ k → U (m + 1) = (ϕ m).func '' U m)
    (hE₁ : metric_entropy (d i) ε (U 1) = (e₁ : EReal))
    (hwd : ∀ m, 1 ≤ m → m ≤ k →
      EntropyDiffWellDefined d (ϕ m) (U m) i i ε)
    (hdrop : ∀ m (hm1 : 1 ≤ m) (hmk : m ≤ Nat.ceil (e₁ / δ)),
      0 < metric_entropy (d i) ε (U m) →
      (δ : EReal) ≤ mapping_entropy_diff d (ϕ m) (U m) i i ε
        (hwd m hm1 (hmk.trans hk)))
    (hmetric : ExtendedPseudoMetric X bot (d i)) :
    ∃ m, 1 ≤ m ∧ m ≤ Nat.ceil (e₁ / δ) + 1 ∧
      metric_entropy (d i) ε (U m) = 0 := by
  let k_star := Nat.ceil (e₁ / δ)
  have hk_star : k_star ≤ k := hk
  have hnonnegative : ∀ m, 1 ≤ m → m ≤ k_star + 1 →
      (0 : EReal) ≤ metric_entropy (d i) ε (U m) := by
    intro m hm1 hm
    have hmk1 : m ≤ k + 1 := hm.trans (Nat.succ_le_succ hk_star)
    have hcov : (1 : ENNReal) ≤ covering_number (d i) ε (U m) :=
      one_le_cov_num_of_nonempty d i ε (U m) (hU_nonempty m hm1 hmk1)
    calc
      (0 : EReal) = log2_ereal (1 : ENNReal) := by simp
      _ ≤ log2_ereal (covering_number (d i) ε (U m)) := log2_ereal_mono hcov
      _ = metric_entropy (d i) ε (U m) := rfl
  by_contra hnone
  push Not at hnone
  have hpositive : ∀ m, 1 ≤ m → m ≤ k_star + 1 →
      (0 : EReal) < metric_entropy (d i) ε (U m) := by
    intro m hm1 hm
    exact lt_of_le_of_ne (hnonnegative m hm1 hm) (Ne.symm (hnone m hm1 hm))
  obtain ⟨E, hentropy, hE₁_real, hnonnegative_real, hstep⟩ :=
    entropy_lower_bounded_drop_finite_prefix d ϕ U i ε e₁ δ k_star
      (fun m hm1 hm => hU_nonempty m hm1 (by omega))
      (fun m hm1 hm => himage m hm1 (hm.trans hk_star)) hE₁
      (fun m hm1 hm => hwd m hm1 (hm.trans hk_star))
      (fun m hm1 hm => hdrop m hm1 hm (hpositive m hm1 (by omega)))
  have hinitial : E 1 ≤ (k_star : ℝ) * δ := by
    rw [hE₁_real]
    have hceil : e₁ / δ ≤ (k_star : ℝ) := Nat.le_ceil (e₁ / δ)
    exact (div_le_iff₀ hδ).mp hceil
  have hdrop_real : ∀ m, 1 ≤ m → m ≤ k_star → 0 < E m →
      δ ≤ entropy_drop E m := by
    intro m hm1 hm _hmpos
    have hle := hstep m hm1 hm
    dsimp [entropy_drop]
    linarith
  rcases entropy_uniform_drop_reaches_zero E k_star δ hnonnegative_real hinitial
      hdrop_real with ⟨m, hm1, hm, hEm⟩
  exact hnone m hm1 hm (by rw [hentropy m hm1 hm, hEm]; simp)

end

end formal_oet.vol_01.ch_04_operator_chain_calculus
