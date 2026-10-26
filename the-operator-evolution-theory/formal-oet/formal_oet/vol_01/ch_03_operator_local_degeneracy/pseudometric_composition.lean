import formal_oet.vol_01.ch_03_operator_local_degeneracy.computational_fiber
import Mathlib.Data.Real.ENatENNReal

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy.pseudometric_composition

open formal_oet.vol_01.ch_01_foundations

noncomputable section

/-- The real line with an absorbing point. -/
abbrev RealPoint := Option ℝ

/-- The single gauge reads absolute values rather than the points themselves. -/
def absolute_distance (_ : Unit) : RealPoint → RealPoint → ENNReal
  | some x, some y => ENNReal.ofReal (abs (abs x - abs y))
  | none, none => 0
  | _, _ => ⊤

/-- OET anchor: h-5a431d16f9d7ba6a
习题的绝对值读出距离满足扩展伪度量公理。
-/
theorem absolute_distance_is_extended :
    ExtendedPseudoMetric RealPoint none (absolute_distance ()) := by
  refine
    { nonabsorbing := ⟨some 0, by simp⟩
      dist_self := ?_
      symm := ?_
      triangle := ?_
      isolate_bot := ?_ }
  · intro x
    cases x <;> simp [absolute_distance]
  · intro x y
    cases x <;> cases y <;> simp [absolute_distance, abs_sub_comm]
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp only [absolute_distance]
    all_goals try simp
    rename_i x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le (abs x) (abs y) (abs z))
  · intro x hx
    cases x with
    | none => exact (hx rfl).elim
    | some x => rfl

def inner_operator : Operator RealPoint none :=
  ⟨Option.map (fun x => 2 * x - 1), rfl⟩

def sample_domain : Set RealPoint := {some 0, some 1}

/-- OET anchor: h-5a431d16f9d7ba6a
两个样本点都属于算子及其自复合的定义域。
-/
theorem sample_domain_valid :
    sample_domain ⊆ dom inner_operator ∧
      sample_domain ⊆ dom (OperatorChain [inner_operator, inner_operator]) := by
  constructor <;> intro x hx
  all_goals
    simp only [sample_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;>
      simp [dom, OperatorChain, inner_operator]

/-- OET anchor: h-5a431d16f9d7ba6a
算子的输出是不同的零距点；该分量先为常值，自复合后变为有效。
-/
theorem constant_then_active :
    () ∈ ConstComponent absolute_distance inner_operator sample_domain ∧
      () ∈ ActComponent absolute_distance
        (OperatorChain [inner_operator, inner_operator]) sample_domain ∧
      inner_operator.func (some 0) ≠ inner_operator.func (some 1) := by
  refine ⟨?_, ⟨?_, ?_⟩, ?_⟩
  · intro x hx y hy
    simp only [sample_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [inner_operator, absolute_distance]
  · intro hid
    have h := hid.2 (some 0) (by simp [sample_domain])
    norm_num [OperatorChain, inner_operator, absolute_distance] at h
  · intro hc
    have h := hc (some 0) (by simp [sample_domain]) (some 1) (by simp [sample_domain])
    norm_num [OperatorChain, inner_operator, absolute_distance] at h
  · norm_num [inner_operator]

/-- OET anchor: h-5a431d16f9d7ba6a
第一次作用后，以零点的输出为目标的计算纤维是整个样本域。
-/
theorem first_fiber_eq_sample_domain :
    ComputationalFiber absolute_distance inner_operator (singleton_nonempty_finset ())
      sample_domain (inner_operator.func (some 0)) = sample_domain := by
  rw [singleton_computational_fiber_eq]
  ext x
  constructor
  · exact And.left
  · intro hx
    exact ⟨hx, constant_then_active.1 x hx (some 0) (by simp [sample_domain])⟩

/-- OET anchor: h-5a431d16f9d7ba6a
自复合后，以零点的输出为目标的计算纤维只剩零点。
-/
theorem self_composition_fiber_eq_singleton :
    ComputationalFiber absolute_distance (OperatorChain [inner_operator, inner_operator])
      (singleton_nonempty_finset ()) sample_domain
      ((OperatorChain [inner_operator, inner_operator]).func (some 0)) = {some 0} := by
  rw [singleton_computational_fiber_eq]
  ext x
  constructor
  · rintro ⟨hx, hzero⟩
    simp only [sample_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rfl
    · norm_num [OperatorChain, inner_operator, absolute_distance] at hzero
  · intro hx
    have hx0 : x = some 0 := hx
    subst x
    norm_num [sample_domain, OperatorChain, inner_operator, absolute_distance]

/-- OET anchor: h-5a431d16f9d7ba6a
若算子在样本域上取同一个实数值，自复合后的输出仍是同一个点。
-/
theorem pointwise_constant_self_composition (ϕ : Operator RealPoint none) (c : ℝ)
    (hϕ : ∀ x ∈ sample_domain, ϕ.func x = some c) :
    ∀ x ∈ sample_domain, (OperatorChain [ϕ, ϕ]).func x = ϕ.func (some c) := by
  intro x hx
  change ϕ.func (ϕ.func x) = ϕ.func (some c)
  rw [hϕ x hx]

/-- OET anchor: h-5a431d16f9d7ba6a
同点输出的自复合在未被吸收时，仍给出常值分量和整个样本域的计算纤维。
-/
theorem pointwise_constant_stays_constant (ϕ : Operator RealPoint none) (c : ℝ)
    (hϕ : ∀ x ∈ sample_domain, ϕ.func x = some c)
    (hdefined : ϕ.func (some c) ≠ none) :
    sample_domain ⊆ dom (OperatorChain [ϕ, ϕ]) ∧
      () ∈ ConstComponent absolute_distance
        (OperatorChain [ϕ, ϕ]) sample_domain ∧
      ComputationalFiber absolute_distance (OperatorChain [ϕ, ϕ])
        (singleton_nonempty_finset ()) sample_domain
        ((OperatorChain [ϕ, ϕ]).func (some 0)) = sample_domain := by
  have hsame := pointwise_constant_self_composition ϕ c hϕ
  have hconst : () ∈ ConstComponent absolute_distance
      (OperatorChain [ϕ, ϕ]) sample_domain := by
    intro x hx y hy
    rw [hsame x hx, hsame y hy]
    exact absolute_distance_is_extended.dist_self _
  refine ⟨?_, hconst, ?_⟩
  · intro x hx
    change (OperatorChain [ϕ, ϕ]).func x ≠ none
    rw [hsame x hx]
    exact hdefined
  · rw [singleton_computational_fiber_eq]
    ext x
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, hconst x hx (some 0) (by simp [sample_domain])⟩

/-- OET anchor: h-5a431d16f9d7ba6a
同点输出若在自复合后被吸收，则样本域与自复合的定义域不相交。
-/
theorem pointwise_constant_absorbed_domain (ϕ : Operator RealPoint none) (c : ℝ)
    (hϕ : ∀ x ∈ sample_domain, ϕ.func x = some c)
    (habsorbed : ϕ.func (some c) = none) :
    sample_domain ∩ dom (OperatorChain [ϕ, ϕ]) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hx.2 ((pointwise_constant_self_composition ϕ c hϕ x hx.1).trans habsorbed)

end

end formal_oet.vol_01.ch_03_operator_local_degeneracy.pseudometric_composition
