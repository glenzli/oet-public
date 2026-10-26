import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open Finset

/-- A finite carrier used by the explicit counterexamples in Chapter 3. -/
inductive SevenPoint where
  | bottom | a | b | p | q | r | s
deriving DecidableEq, Fintype

/-- Two component labels for the explicit counterexamples. -/
inductive TwoGauge where
  | i | m
deriving DecidableEq, Fintype

/-- Pull back the `0/⊤` discrete extended metric along an arbitrary code map. -/
noncomputable def top_pullback_distance {Y C : Type}
    (code : Y → C) (x y : Y) : ENNReal := by
  classical
  exact if code x = code y then 0 else ⊤

theorem top_pullback_distance_self {Y C : Type}
    (code : Y → C) (x : Y) :
    top_pullback_distance code x x = 0 := by
  classical
  simp [top_pullback_distance]

theorem top_pullback_distance_symm {Y C : Type}
    (code : Y → C) (x y : Y) :
    top_pullback_distance code x y = top_pullback_distance code y x := by
  classical
  simp only [top_pullback_distance, eq_comm]

theorem top_pullback_distance_triangle {Y C : Type}
    (code : Y → C) (x y z : Y) :
    top_pullback_distance code x z ≤
      top_pullback_distance code x y + top_pullback_distance code y z := by
  classical
  by_cases hxz : code x = code z
  · simp [top_pullback_distance, hxz]
  · have hsplit : code x ≠ code y ∨ code y ≠ code z := by
      by_contra h
      push Not at h
      exact hxz (h.1.trans h.2)
    rcases hsplit with hxy | hyz
    · simp [top_pullback_distance, hxz, hxy]
    · simp [top_pullback_distance, hxz, hyz]

theorem top_pullback_distance_bot {Y C : Type}
    (code : Y → C) (bottom x : Y) (hx : code x ≠ code bottom) :
    top_pullback_distance code x bottom = ⊤ := by
  classical
  simp [top_pullback_distance, hx]

/-- 离散商上的距离：零码表示吸收元，其他不同码之间的距离为 1。 -/
noncomputable def finite_pullback_distance {Y : Type}
    (code : Y → Nat) (x y : Y) : ENNReal :=
  if code x = code y then 0 else if code x = 0 ∨ code y = 0 then ⊤ else 1

theorem finite_pullback_distance_self {Y : Type} (code : Y → Nat) (x : Y) :
    finite_pullback_distance code x x = 0 := by
  simp [finite_pullback_distance]

theorem finite_pullback_distance_symm {Y : Type} (code : Y → Nat) (x y : Y) :
    finite_pullback_distance code x y = finite_pullback_distance code y x := by
  simp only [finite_pullback_distance, eq_comm, or_comm]

theorem finite_pullback_distance_triangle {Y : Type} (code : Y → Nat) (x y z : Y) :
    finite_pullback_distance code x z ≤
      finite_pullback_distance code x y + finite_pullback_distance code y z := by
  by_cases hxy : code x = code y
  · simp [finite_pullback_distance, hxy]
  by_cases hyz : code y = code z
  · simp [finite_pullback_distance, hyz]
  by_cases hx : code x = 0
  · simp_all [finite_pullback_distance]
  by_cases hz : code z = 0
  · simp_all [finite_pullback_distance]
  by_cases hy : code y = 0 <;> by_cases hxz : code x = code z <;>
    norm_num [finite_pullback_distance, hxy, hyz, hx, hy, hz, hxz]

/-- The first code identifies only `p` and `q`. -/
def merge_pq_code : SevenPoint → Nat
  | .bottom => 0
  | .a => 1
  | .b => 2
  | .p | .q => 3
  | .r => 4
  | .s => 5

/-- An injective code, with zero reserved for the absorber. -/
def discrete_code : SevenPoint → Nat
  | .bottom => 0
  | .a => 1
  | .b => 2
  | .p => 3
  | .q => 4
  | .r => 5
  | .s => 6

/-- 正文的七点反例：非吸收元之间的距离恰好取 0 或 1。 -/
def composition_counter_distance : TwoGauge → SevenPoint → SevenPoint → ENNReal
  | .i => finite_pullback_distance merge_pq_code
  | .m => finite_pullback_distance discrete_code

/--
OET anchor: h-2c5dc85febaac657
常值分量非封闭反例中的两个扩展伪度量满足自距、对称、三角及吸收元隔离公理。
-/
theorem composition_counter_distance_is_extended :
    (∀ k x, composition_counter_distance k x x = 0) ∧
      (∀ k x y,
        composition_counter_distance k x y = composition_counter_distance k y x) ∧
      (∀ k x y z,
        composition_counter_distance k x z ≤
          composition_counter_distance k x y + composition_counter_distance k y z) ∧
      (∀ k x, x ≠ SevenPoint.bottom →
        composition_counter_distance k x SevenPoint.bottom = ⊤) := by
  constructor
  · intro k x
    cases k <;> exact finite_pullback_distance_self _ _
  constructor
  · intro k x y
    cases k <;> exact finite_pullback_distance_symm _ _ _
  constructor
  · intro k x y z
    cases k <;> exact finite_pullback_distance_triangle _ _ _ _
  · intro k x hx
    cases k <;> cases x <;> simp_all
      [composition_counter_distance, finite_pullback_distance, merge_pq_code, discrete_code]

/-- The two-point source domain of the seven-point counterexample. -/
def counter_domain : Set SevenPoint := {SevenPoint.a, SevenPoint.b}

/-- The inner map collapses `a,b` in component `i` but keeps them distinct in `m`. -/
def inner_counter_operator : Operator SevenPoint SevenPoint.bottom where
  func
    | .a => .p
    | .b => .q
    | _ => .bottom
  preserves_bot := rfl

/-- The outer map separates the two inner outputs again in component `i`. -/
def outer_counter_operator : Operator SevenPoint SevenPoint.bottom where
  func
    | .p => .r
    | .q => .s
    | _ => .bottom
  preserves_bot := rfl

/--
OET anchor: h-2c5dc85febaac657
正文反例中的具体零距、跨分量距离和复合后的有限正距离。
-/
theorem composition_counterexample_distances :
    composition_counter_distance .i .p .q = 0 ∧
      composition_counter_distance .m .p .q = 1 ∧
      composition_counter_distance .i .r .s = 1 := by
  norm_num [composition_counter_distance, finite_pullback_distance, merge_pq_code, discrete_code]

/--
OET anchor: h-2c5dc85febaac657
常值分量右侧非封闭：与正文取值相同的七点有限模型。
-/
theorem const_component_right_nonclosure_counterexample :
    counter_domain ⊆
        dom (OperatorChain [outer_counter_operator, inner_counter_operator]) ∧
      TwoGauge.i ∈
        ConstComponent composition_counter_distance inner_counter_operator counter_domain ∧
      TwoGauge.i ∉
        ConstComponent composition_counter_distance
          (OperatorChain [outer_counter_operator, inner_counter_operator]) counter_domain := by
  have ha_mem : SevenPoint.a ∈ counter_domain := by simp [counter_domain]
  have hb_mem : SevenPoint.b ∈ counter_domain := by simp [counter_domain]
  constructor
  · intro x hx
    simp only [counter_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;>
      simp [dom, OperatorChain, inner_counter_operator, outer_counter_operator]
  constructor
  · intro x hx y hy
    simp only [counter_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [composition_counter_distance, finite_pullback_distance, merge_pq_code,
        inner_counter_operator]
  · intro hconst
    have h := hconst SevenPoint.a ha_mem SevenPoint.b hb_mem
    simp [composition_counter_distance, finite_pullback_distance, merge_pq_code,
      OperatorChain, inner_counter_operator, outer_counter_operator] at h

/-- 正文换位与无穷统一零化半径反例的三点载体。 -/
inductive ThreePoint where
  | bottom | a | b
deriving DecidableEq, Fintype

def three_point_code : ThreePoint → Nat
  | .bottom => 0
  | .a => 1
  | .b => 2

def three_point_domain : Set ThreePoint := {ThreePoint.a, ThreePoint.b}

/-- 换位例只使用一个分量。 -/
def swap_counter_distance : Unit → ThreePoint → ThreePoint → ENNReal :=
  fun _ => finite_pullback_distance three_point_code

/--
OET anchor: h-8f36f69dab71e689
三点单分量换位反例的伪度量公理及精确取值。
-/
theorem swap_counter_distance_is_extended :
    (∀ x, swap_counter_distance () x x = 0) ∧
      (∀ x y, swap_counter_distance () x y = swap_counter_distance () y x) ∧
      (∀ x y z, swap_counter_distance () x z ≤
        swap_counter_distance () x y + swap_counter_distance () y z) ∧
      (∀ x, x ≠ ThreePoint.bottom → swap_counter_distance () x .bottom = ⊤) ∧
      swap_counter_distance () .a .b = 1 := by
  refine ⟨finite_pullback_distance_self _, finite_pullback_distance_symm _,
    finite_pullback_distance_triangle _, ?_, ?_⟩
  · intro x hx
    cases x <;> simp_all [swap_counter_distance, finite_pullback_distance, three_point_code]
  · norm_num [swap_counter_distance, finite_pullback_distance, three_point_code]

def swap_counter_operator : Operator ThreePoint ThreePoint.bottom where
  func
    | .a => .b
    | .b => .a
    | .bottom => .bottom
  preserves_bot := rfl

/--
OET anchor: h-8f36f69dab71e689
换位复合反例：与正文相同的三点载体、单分量与距离 1。
-/
theorem swap_counterexample_is_active_but_square_is_identity :
    three_point_domain ⊆ dom (OperatorChain [swap_counter_operator, swap_counter_operator]) ∧
      () ∈ ActComponent swap_counter_distance swap_counter_operator three_point_domain ∧
      () ∈ ActComponent swap_counter_distance swap_counter_operator
        (swap_counter_operator.func '' three_point_domain) ∧
      () ∈ IdComponent swap_counter_distance
        (OperatorChain [swap_counter_operator, swap_counter_operator]) three_point_domain ∧
      () ∉ ActComponent swap_counter_distance
        (OperatorChain [swap_counter_operator, swap_counter_operator]) three_point_domain := by
  constructor
  · intro x hx
    simp only [three_point_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [dom, OperatorChain, swap_counter_operator]
  apply swap_pair_factors_active_but_composite_identity
    (d := swap_counter_distance)
    (ϕ1 := swap_counter_operator) (ϕ2 := swap_counter_operator)
    (i := ()) (a := ThreePoint.a) (b := ThreePoint.b)
  · rfl
  · rfl
  · rfl
  · rfl
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy ⊢
      rcases hy with rfl | rfl <;> simp [swap_counter_operator]
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨ThreePoint.b, by simp, rfl⟩
      · exact ⟨ThreePoint.a, by simp, rfl⟩
  · norm_num [swap_counter_distance, finite_pullback_distance, three_point_code]
  · simp [swap_counter_distance, finite_pullback_distance, three_point_code]
  · simp [swap_counter_distance, finite_pullback_distance, three_point_code]

/-- 三点恒等算子。 -/
def identity_counter_operator : Operator ThreePoint ThreePoint.bottom := ⟨id, rfl⟩

/--
OET anchor: h-fd32966bed4ea8d0
两个无穷统一零化半径反例均在恒等算子的合法非空受限域上考察。
-/
theorem identity_counter_domain :
    three_point_domain.Nonempty ∧ three_point_domain ⊆ dom identity_counter_operator := by
  constructor
  · exact ⟨ThreePoint.a, by simp [three_point_domain]⟩
  · intro x hx
    simp only [three_point_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp [dom, identity_counter_operator]

/-- 同分量无穷统一零化半径反例。 -/
def infinite_counter_distance : Unit → ThreePoint → ThreePoint → ENNReal :=
  fun _ => top_pullback_distance three_point_code

/-- 异分量反例：输入距离为无穷，输出距离为 1。 -/
def separation_counter_distance : TwoGauge → ThreePoint → ThreePoint → ENNReal
  | .i => top_pullback_distance three_point_code
  | .m => finite_pullback_distance three_point_code

/--
OET anchor: h-fd32966bed4ea8d0
同分量无穷统一零化半径反例的扩展伪度量公理及正距离的精确取值。
-/
theorem infinite_counter_distance_is_extended :
    (∀ x, infinite_counter_distance () x x = 0) ∧
      (∀ x y, infinite_counter_distance () x y = infinite_counter_distance () y x) ∧
      (∀ x y z, infinite_counter_distance () x z ≤
        infinite_counter_distance () x y + infinite_counter_distance () y z) ∧
      (∀ x, x ≠ ThreePoint.bottom → infinite_counter_distance () x .bottom = ⊤) ∧
      infinite_counter_distance () .a .b = ⊤ := by
  refine ⟨top_pullback_distance_self _, top_pullback_distance_symm _,
    top_pullback_distance_triangle _, ?_, ?_⟩
  · intro x hx
    cases x <;> simp_all [infinite_counter_distance, top_pullback_distance, three_point_code]
  · simp [infinite_counter_distance, top_pullback_distance, three_point_code]

/--
OET anchor: h-fd32966bed4ea8d0
异分量无穷统一零化半径反例的扩展伪度量公理及两个分量的精确取值。
-/
theorem separation_counter_distance_is_extended :
    (∀ k x, separation_counter_distance k x x = 0) ∧
      (∀ k x y, separation_counter_distance k x y = separation_counter_distance k y x) ∧
      (∀ k x y z, separation_counter_distance k x z ≤
        separation_counter_distance k x y + separation_counter_distance k y z) ∧
      (∀ k x, x ≠ ThreePoint.bottom → separation_counter_distance k x .bottom = ⊤) ∧
      separation_counter_distance .i .a .b = ⊤ ∧
      separation_counter_distance .m .a .b = 1 := by
  constructor
  · intro k
    cases k
    · exact top_pullback_distance_self _
    · exact finite_pullback_distance_self _
  constructor
  · intro k
    cases k
    · exact top_pullback_distance_symm _
    · exact finite_pullback_distance_symm _
  constructor
  · intro k
    cases k
    · exact top_pullback_distance_triangle _
    · exact finite_pullback_distance_triangle _
  refine ⟨?_, ?_, ?_⟩
  · intro k x hx
    cases k <;> cases x <;> simp_all
      [separation_counter_distance, top_pullback_distance,
        finite_pullback_distance, three_point_code]
  · simp [separation_counter_distance, top_pullback_distance, three_point_code]
  · norm_num [separation_counter_distance, finite_pullback_distance, three_point_code]

/--
OET anchor: h-fd32966bed4ea8d0
无穷统一零化半径不反推常值：正文 `i=j` 的三点单分量实例。
-/
theorem infinite_annihilation_radius_nonconstant_counterexample :
    AnnihilationMatrix infinite_counter_distance identity_counter_operator
        three_point_domain () () = ⊤ ∧
      () ∉ ConstComponent infinite_counter_distance
        identity_counter_operator three_point_domain := by
  apply annihilation_matrix_top_does_not_force_const_component_pattern
  · intro y hy x hx hnot
    simp only [three_point_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hy hx
    rcases hy with rfl | rfl <;> rcases hx with rfl | rfl
    all_goals simp_all [ComputationalFiber, comp_pseudo_metric_singleton,
      identity_counter_operator, three_point_domain, infinite_counter_distance,
      top_pullback_distance, three_point_code]
  · refine ⟨ThreePoint.a, by simp [three_point_domain],
      ThreePoint.b, by simp [three_point_domain], ?_⟩
    simp [identity_counter_operator, infinite_counter_distance,
      top_pullback_distance, three_point_code]

/--
OET anchor: h-fd32966bed4ea8d0
无穷统一零化半径不反推常值：正文 `i≠j`，输入无穷距离、输出距离 1 的三点实例。
-/
theorem distinct_components_infinite_radius_nonconstant_counterexample :
    AnnihilationMatrix separation_counter_distance identity_counter_operator
        three_point_domain TwoGauge.m TwoGauge.i = ⊤ ∧
      TwoGauge.m ∉
        ConstComponent separation_counter_distance
          identity_counter_operator three_point_domain := by
  apply annihilation_matrix_top_does_not_force_const_component_pattern
  · intro y hy x hx hnot
    simp only [three_point_domain, Set.mem_insert_iff, Set.mem_singleton_iff] at hy hx
    rcases hy with rfl | rfl <;> rcases hx with rfl | rfl
    all_goals simp_all [ComputationalFiber, comp_pseudo_metric_singleton,
      identity_counter_operator, three_point_domain, separation_counter_distance,
      top_pullback_distance, finite_pullback_distance, three_point_code]
  · refine ⟨ThreePoint.a, by simp [three_point_domain],
      ThreePoint.b, by simp [three_point_domain], ?_⟩
    norm_num [identity_counter_operator, separation_counter_distance,
      finite_pullback_distance, three_point_code]

end

end formal_oet.vol_01.ch_03_operator_local_degeneracy
