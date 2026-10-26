import formal_oet.vol_01.ch_04_operator_chain_calculus.decomposition_core
import formal_oet.vol_01.ch_04_operator_chain_calculus.prefix_products


namespace formal_oet.vol_01.ch_04_operator_chain_calculus

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy

variable {X I : Type} {bot : X} [Fintype I]
local instance instDecidableEqILocalEquivalenceChain : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-a1caa879309ff2e3
**定义（局部等价）**
局部等价同时等价于域限制算子相等。
-/
theorem local_equivalent_restrict_operator_eq
    (ϕ ψ : Operator X bot) (U : Set X) :
    LocalEquivalent ϕ ψ U ↔ restrict_operator ϕ U = restrict_operator ψ U := by
  exact local_equivalent_iff_restrict_eq ϕ ψ U

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-5bedef30d593a0bc
**引理 #h-5bedef30d593a0bc(iii)（局部等价的受限 N 矩阵一致性）**
局部等价保持逐点零化半径。
-/
theorem local_equiv_annihilation_radius_eq
    (ϕ ψ : Operator X bot) (U : Set X)
    (i : I) (J : NonemptyFinset I) (y : X)
    (hy : y ∈ U) (h_eq : LocalEquivalent ϕ ψ U) :
    annihilation_radius d ϕ i J U y = annihilation_radius d ψ i J U y := by
  apply le_antisymm
  · dsimp [annihilation_radius]
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply iSup_le
    intro h_sub
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have h_sub_ψ :
        OpenBall d i y r ∩ U ⊆
          ComputationalFiber d ψ J U (ψ.func y) := by
      intro x hx
      have h_fiber := h_sub hx
      exact ⟨h_fiber.1, by simpa [h_eq x h_fiber.1, h_eq y hy] using h_fiber.2⟩
    exact le_iSup_of_le h_sub_ψ le_rfl
  · dsimp [annihilation_radius]
    apply iSup_le
    intro r
    apply iSup_le
    intro hr
    apply iSup_le
    intro h_sub
    apply le_iSup_of_le r
    apply le_iSup_of_le hr
    have h_sub_ϕ :
        OpenBall d i y r ∩ U ⊆
          ComputationalFiber d ϕ J U (ϕ.func y) := by
      intro x hx
      have h_fiber := h_sub hx
      exact ⟨h_fiber.1, by simpa [h_eq x h_fiber.1, h_eq y hy] using h_fiber.2⟩
    exact le_iSup_of_le h_sub_ϕ le_rfl

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-5bedef30d593a0bc
**引理 #h-5bedef30d593a0bc(iii)（局部等价的受限 N 矩阵一致性）**
局部等价保持受限零化矩阵。
-/
theorem local_equiv_annihilation_matrix_eq
    (ϕ ψ : Operator X bot) (U : Set X)
    (h_eq : LocalEquivalent ϕ ψ U) :
    ∀ i j : I, AnnihilationMatrix d ϕ U i j = AnnihilationMatrix d ψ U i j := by
  intro i j
  dsimp [AnnihilationMatrix, min_annihilation_radius]
  apply le_antisymm
  · apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact le_trans (iInf₂_le y hy)
      (le_of_eq (local_equiv_annihilation_radius_eq d ϕ ψ U j
        (singleton_nonempty_finset i) y hy h_eq))
  · apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact le_trans (iInf₂_le y hy)
      (ge_of_eq (local_equiv_annihilation_radius_eq d ϕ ψ U j
        (singleton_nonempty_finset i) y hy h_eq))

/--
OET anchor: h-5bedef30d593a0bc
**引理 #h-5bedef30d593a0bc（局部等价的受限矩阵一致性）**
L/K/N 三组受限矩阵一致性的合并形式。
-/
theorem local_equiv_restricted_matrices
    (ϕ ψ : Operator X bot) (U : Set X)
    (h_eq : LocalEquivalent ϕ ψ U) :
    (∀ L : I → I → ENNReal,
      IsLipMatrix d ϕ U L ↔ IsLipMatrix d ψ U L) ∧
    (∀ K : I → I → ENNReal,
      IsCoLipMatrix d ϕ U K ↔ IsCoLipMatrix d ψ U K) ∧
    (∀ i j : I,
      AnnihilationMatrix d ϕ U i j = AnnihilationMatrix d ψ U i j) := by
  exact ⟨
    fun L => local_equiv_lip_matrix_iff d ϕ ψ U L h_eq,
    fun K => local_equiv_colip_matrix_iff d ϕ ψ U K h_eq,
    local_equiv_annihilation_matrix_eq d ϕ ψ U h_eq⟩

/-- The forward prefix has the same composite as the internal reverse-order list. -/
theorem chain_prefix_operator_eq_reverse_range
    (step : ℕ → Operator X bot) (n : ℕ) :
    chain_prefix_operator step n = OperatorChain ((List.range n).reverse.map step) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      ext x
      simp only [chain_prefix_operator, List.range_succ, List.reverse_append,
        List.reverse_singleton, List.singleton_append, List.map_cons]
      change (step n).func ((chain_prefix_operator step n).func x) =
        (step n).func ((OperatorChain ((List.range n).reverse.map step)).func x)
      rw [ih]

/-- Surviving a longer prefix implies surviving every shorter prefix. -/
theorem chain_prefix_domain_antitone
    (step : ℕ → Operator X bot) {n k : ℕ} (hnk : n ≤ k) :
    dom (chain_prefix_operator step k) ⊆ dom (chain_prefix_operator step n) := by
  induction k with
  | zero =>
      have : n = 0 := by omega
      subst n
      exact Set.Subset.rfl
  | succ k ih =>
      by_cases heq : n = k + 1
      · subst n
        exact Set.Subset.rfl
      · have hn : n ≤ k := by omega
        intro x hx
        apply ih hn
        intro hbot
        apply hx
        change (step k).func ((chain_prefix_operator step k).func x) = bot
        rw [hbot, (step k).preserves_bot]

/--
OET anchor: h-5a1b95150c3a4df2
**定义（实际输入域序列）**
The initial set is nonempty and lies in the domain of the whole composite.
Zero-based `image n` corresponds to the book's `U_{n+1}`; the empty chain is allowed.
-/
structure ActualInputDomainSequence
    (step_op : ℕ → Operator X bot) (length : ℕ) (U₁ : Set X) where
  nonempty : U₁.Nonempty
  initial_domain : U₁ ⊆ dom (chain_prefix_operator step_op length)
  image : ℕ → Set X
  initial : image 0 = U₁
  step : ∀ n : ℕ, n < length → image (n + 1) = (step_op n).func '' image n

/-- The recursively specified domains are precisely the prefix images. -/
theorem actual_input_domain_sequence_image_eq
    {step : ℕ → Operator X bot} {length : ℕ} {U₁ : Set X}
    (h : ActualInputDomainSequence step length U₁) :
    ∀ n ≤ length, h.image n = (chain_prefix_operator step n).func '' U₁ := by
  intro n hn
  induction n with
  | zero => simpa [chain_prefix_operator, OperatorChain] using h.initial
  | succ n ih =>
      rw [h.step n (by omega), ih (by omega)]
      ext x
      simp [chain_prefix_operator, OperatorChain, Set.image_image, Function.comp_def]

/--
OET anchor: h-5a1b95150c3a4df2
**实际输入域序列的定义域合法性**
Survival of the whole chain ensures that every actual input belongs to the next domain.
-/
theorem actual_input_domain_sequence_in_domain
    {step : ℕ → Operator X bot} {length : ℕ} {U₁ : Set X}
    (h : ActualInputDomainSequence step length U₁) (n : ℕ) (hn : n < length) :
    h.image n ⊆ dom (step n) := by
  rw [actual_input_domain_sequence_image_eq h n (by omega)]
  rintro x ⟨y, hy, rfl⟩
  have hnext := chain_prefix_domain_antitone step (n := n + 1) (by omega)
    (h.initial_domain hy)
  exact hnext

/-- Actual image sets remain nonempty, including the final image. -/
theorem actual_input_domain_sequence_nonempty
    {step : ℕ → Operator X bot} {length : ℕ} {U₁ : Set X}
    (h : ActualInputDomainSequence step length U₁) (n : ℕ) (hn : n ≤ length) :
    (h.image n).Nonempty := by
  rw [actual_input_domain_sequence_image_eq h n hn]
  exact h.nonempty.image _

/--
OET anchor: h-5a1b95150c3a4df2
**定义（实际输入域序列）的构造**
Every nonempty initial subset of the composite domain supplies the stated image sequence.
-/
def actual_input_domain_sequence
    (step_op : ℕ → Operator X bot) (length : ℕ) (U₁ : Set X)
    (hU : U₁.Nonempty) (hdom : U₁ ⊆ dom (chain_prefix_operator step_op length)) :
    ActualInputDomainSequence step_op length U₁ where
  nonempty := hU
  initial_domain := hdom
  image n := (chain_prefix_operator step_op n).func '' U₁
  initial := by simp [chain_prefix_operator, OperatorChain]
  step n _ := by
    ext x
    simp [chain_prefix_operator, OperatorChain, Set.image_image, Function.comp_def]

/--
OET anchor: h-95e7f90e21e41cae
**命题 #h-95e7f90e21e41cae（逐步局部等价的传播一致性）**
实际输入域序列一致性所需的逐步局部等价数据。
-/
structure StepwiseInputEquivalenceSpec
    (stepϕ stepψ : ℕ → Operator X bot) (length : ℕ) (U₁ : Set X) where
  image_seq_ϕ : ActualInputDomainSequence stepϕ length U₁
  image_seq_ψ : ActualInputDomainSequence stepψ length U₁
  step_local_equiv :
    ∀ n : ℕ, n < length →
      LocalEquivalent (stepϕ n) (stepψ n) (image_seq_ϕ.image n)

/--
OET anchor: h-95e7f90e21e41cae
**命题 #h-95e7f90e21e41cae(i)（实际输入域序列一致）**
逐步局部等价推出实际输入域序列一致性。
-/
theorem stepwise_local_equiv_input_sequences_equal
    (stepϕ stepψ : ℕ → Operator X bot) (length : ℕ)
    (U₁ : Set X)
    (h : StepwiseInputEquivalenceSpec stepϕ stepψ length U₁) :
    ∀ n : ℕ, n ≤ length → h.image_seq_ϕ.image n = h.image_seq_ψ.image n := by
  intro n hn
  induction n with
  | zero =>
      rw [h.image_seq_ϕ.initial, h.image_seq_ψ.initial]
  | succ n ih =>
      have hn_lt : n < length := Nat.lt_of_succ_le hn
      have hn_le : n ≤ length := Nat.le_of_lt hn_lt
      have h_prev := ih hn_le
      rw [h.image_seq_ϕ.step n hn_lt, h.image_seq_ψ.step n hn_lt]
      apply Set.Subset.antisymm
      · intro z hz
        rcases hz with ⟨x, hx, hxz⟩
        have hxψ : x ∈ h.image_seq_ψ.image n := by
          simpa [h_prev] using hx
        refine ⟨x, hxψ, ?_⟩
        rw [← hxz]
        exact (h.step_local_equiv n hn_lt x hx).symm
      · intro z hz
        rcases hz with ⟨x, hx, hxz⟩
        have hxϕ : x ∈ h.image_seq_ϕ.image n := by
          simpa [h_prev] using hx
        refine ⟨x, hxϕ, ?_⟩
        rw [← hxz]
        exact h.step_local_equiv n hn_lt x hxϕ

/--
OET anchor: h-95e7f90e21e41cae
**命题 #h-95e7f90e21e41cae(ii)（链复合行为局部等价）**
逐步局部等价推出复合算子局部等价。
-/
theorem stepwise_local_equiv_composite_local_equiv
    (cϕ cψ : List (Operator X bot)) (U₁ : Set X)
    (h : StepwiseLocalEquivalent cϕ cψ U₁) :
    LocalEquivalent (OperatorChain cϕ) (OperatorChain cψ) U₁ :=
  stepwise_local_equiv_operator_chain h

/--
OET anchor: h-95e7f90e21e41cae
**命题 #h-95e7f90e21e41cae(iii)（链的受限矩阵一致）**
逐步局部等价推出受限矩阵一致性。
-/
theorem stepwise_local_equiv_restricted_matrices_equal
    (cϕ cψ : List (Operator X bot)) (U₁ : Set X)
    (h : StepwiseLocalEquivalent cϕ cψ U₁) :
    (∀ L : I → I → ENNReal,
      IsLipMatrix d (OperatorChain cϕ) U₁ L ↔
        IsLipMatrix d (OperatorChain cψ) U₁ L) ∧
    (∀ K : I → I → ENNReal,
      IsCoLipMatrix d (OperatorChain cϕ) U₁ K ↔
        IsCoLipMatrix d (OperatorChain cψ) U₁ K) ∧
    (∀ i j : I,
      AnnihilationMatrix d (OperatorChain cϕ) U₁ i j =
        AnnihilationMatrix d (OperatorChain cψ) U₁ i j) := by
  have h_local :
      LocalEquivalent (OperatorChain cϕ) (OperatorChain cψ) U₁ :=
    stepwise_local_equiv_operator_chain h
  exact local_equiv_restricted_matrices d (OperatorChain cϕ)
    (OperatorChain cψ) U₁ h_local

/-- The forward image-sequence hypotheses imply the recursive list hypotheses. -/
theorem stepwise_input_equivalence_to_list
    (stepϕ stepψ : ℕ → Operator X bot) (length : ℕ) (U₁ : Set X)
    (h : StepwiseInputEquivalenceSpec stepϕ stepψ length U₁) :
    ∀ n ≤ length,
      StepwiseLocalEquivalent ((List.range n).reverse.map stepϕ)
        ((List.range n).reverse.map stepψ) U₁ := by
  intro n hn
  induction n with
  | zero => exact StepwiseLocalEquivalent.nil U₁
  | succ n ih =>
      simp only [List.range_succ, List.reverse_append, List.reverse_singleton,
        List.singleton_append, List.map_cons]
      apply StepwiseLocalEquivalent.cons (ih (by omega))
      rw [← chain_prefix_operator_eq_reverse_range]
      intro x hx
      apply h.step_local_equiv n (by omega) x
      rw [actual_input_domain_sequence_image_eq h.image_seq_ϕ n (by omega)]
      exact hx

/--
OET anchor: h-95e7f90e21e41cae
**命题（逐步局部等价的传播一致性）**
One set of lawful forward image-sequence hypotheses proves all three conclusions:
identical image domains, identical composite values, and equal restricted L/K/N data.
-/
theorem stepwise_local_equivalence_textbook
    (stepϕ stepψ : ℕ → Operator X bot) (length : ℕ) (U₁ : Set X)
    (h : StepwiseInputEquivalenceSpec stepϕ stepψ length U₁) :
    (∀ n ≤ length, h.image_seq_ϕ.image n = h.image_seq_ψ.image n) ∧
    LocalEquivalent (chain_prefix_operator stepϕ length)
      (chain_prefix_operator stepψ length) U₁ ∧
    (∀ L : I → I → ENNReal,
      IsLipMatrix d (chain_prefix_operator stepϕ length) U₁ L ↔
        IsLipMatrix d (chain_prefix_operator stepψ length) U₁ L) ∧
    (∀ K : I → I → ENNReal,
      IsCoLipMatrix d (chain_prefix_operator stepϕ length) U₁ K ↔
        IsCoLipMatrix d (chain_prefix_operator stepψ length) U₁ K) ∧
    (∀ i j : I,
      AnnihilationMatrix d (chain_prefix_operator stepϕ length) U₁ i j =
        AnnihilationMatrix d (chain_prefix_operator stepψ length) U₁ i j) := by
  have hlist := stepwise_input_equivalence_to_list stepϕ stepψ length U₁ h length le_rfl
  have hlocal := stepwise_local_equiv_operator_chain hlist
  rw [← chain_prefix_operator_eq_reverse_range, ← chain_prefix_operator_eq_reverse_range]
    at hlocal
  exact ⟨stepwise_local_equiv_input_sequences_equal stepϕ stepψ length U₁ h,
    hlocal, local_equiv_restricted_matrices d _ _ U₁ hlocal⟩

/-- Local-equivalence projection from the internal synthesis predicate. -/
theorem domain_decomposition_synthesis_local_equiv
    (ϕ ψ : Operator X bot) (U : Set X)
    (h : DomainSynthesis ψ ϕ U) :
    LocalEquivalent ψ ϕ U := h.1

/-- Equality projection from the internal synthesis predicate. -/
theorem domain_decomposition_synthesis_eq_iff
    (ϕ ψ : Operator X bot) (U : Set X)
    (h : DomainSynthesis ψ ϕ U) :
    ψ = ϕ ↔ U = dom ϕ :=
  domain_synthesis_eq_iff ψ ϕ U h

end

end formal_oet.vol_01.ch_04_operator_chain_calculus
