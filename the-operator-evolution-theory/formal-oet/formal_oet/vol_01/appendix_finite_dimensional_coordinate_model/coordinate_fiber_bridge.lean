import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.coordinate_gauge
import formal_oet.vol_01.appendix_separating_gauge_specialization.operator_and_chain

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.appendix_separating_gauge_specialization

noncomputable section

variable {n : ℕ} [NeZero n] {A : Set (CoordinateVector n)}

/-- Coordinates of a nonabsorbing point. The value at the absorber only makes
this function total; uses below establish that their points are nonabsorbing. -/
def coordinate_readout : CoordinatePoint n A → CoordinateVector n
  | none => 0
  | some x => x.val

omit [NeZero n] in
private theorem coordinate_zero_iff (i : Fin n) (x y : CoordinatePoint n A)
    (hx : x ≠ none) (hy : y ≠ none) :
    coordinate_dist i x y = 0 ↔ coordinate_readout x i = coordinate_readout y i := by
  cases x with
  | none => exact (hx rfl).elim
  | some x =>
    cases y with
    | none => exact (hy rfl).elim
    | some y =>
      simp only [coordinate_dist, coordinate_readout, ENNReal.ofReal_eq_zero]
      simp only [abs_nonpos_iff, sub_eq_zero]

omit [NeZero n] in
private theorem coordinate_readout_eq_iff (x y : CoordinatePoint n A)
    (hx : x ≠ none) (hy : y ≠ none) :
    coordinate_readout x = coordinate_readout y ↔ x = y := by
  cases x with
  | none => exact (hx rfl).elim
  | some x =>
    cases y with
    | none => exact (hy rfl).elim
    | some y => simp [coordinate_readout, Subtype.ext_iff]

/--
OET anchor: h-ad3957f2de83d301
Supports the opening coordinate interpretation of this section.
坐标纤维的水平集表达：使用原计算纤维及任意非吸收目标，目标不必属于像。
`coordinate_readout (φ.func (some x))` 是正文实际映射的坐标向量。
-/
theorem coordinate_computational_fiber_level_set
    (φ : Operator (CoordinatePoint n A) coordinate_bot) (Q : Set A)
    (hQ : (some '' Q) ⊆ dom φ) (j : Fin n) (y : A) :
    (fun x : A => some x) ⁻¹'
      ComputationalFiber (fun i : Fin n => coordinate_dist i) φ
        (singleton_nonempty_finset j) (some '' Q) (some y) =
    {x | x ∈ Q ∧ coordinate_readout (φ.func (some x)) j = y.val j} := by
  rw [singleton_computational_fiber_eq]
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_image,
    Option.some.injEq, exists_eq_right]
  constructor
  · rintro ⟨hx, hz⟩
    exact ⟨hx, (coordinate_zero_iff j _ _ (hQ ⟨x, hx, rfl⟩) (by simp)).mp hz⟩
  · rintro ⟨hx, hz⟩
    exact ⟨hx, (coordinate_zero_iff j _ _ (hQ ⟨x, hx, rfl⟩) (by simp)).mpr hz⟩

/--
OET anchor: h-ad3957f2de83d301
Supports the opening coordinate interpretation of this section.
全分量计算纤维识别为实际输出向量的水平集。
-/
theorem full_coordinate_computational_fiber_level_set
    (φ : Operator (CoordinatePoint n A) coordinate_bot) (Q : Set A)
    (hQ : (some '' Q) ⊆ dom φ) (y : A) :
    (fun x : A => some x) ⁻¹'
      ComputationalFiber (fun i : Fin n => coordinate_dist i) φ
        full_nonempty_finset (some '' Q) (some y) =
    {x | x ∈ Q ∧ coordinate_readout (φ.func (some x)) = y.val} := by
  rw [full_fiber_eq_point_preimage _
    (by intro i x; cases x <;> simp [coordinate_dist]) coordinate_family_is_separating]
  ext x
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_image,
    Option.some.injEq, exists_eq_right]
  constructor
  · rintro ⟨hx, hxy⟩
    exact ⟨hx, congrArg coordinate_readout hxy⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨hx, (coordinate_readout_eq_iff _ _ (hQ ⟨x, hx, rfl⟩) (by simp)).mp hxy⟩

/--
OET anchor: h-ad3957f2de83d301
Supports the opening coordinate interpretation of this section.
原单通路零化半径的坐标表达；候选半径仍为有限正数。
-/
theorem coordinate_annihilation_radius_level_set
    (φ : Operator (CoordinatePoint n A) coordinate_bot) (Q : Set A)
    (hQ : (some '' Q) ⊆ dom φ) (i j : Fin n) (y : A) (hy : y ∈ Q) :
    annihilation_radius (fun k : Fin n => coordinate_dist k) φ i
      (singleton_nonempty_finset j) (some '' Q) (some y) =
    ⨆ (r : ENNReal) (_ : FinitePositiveRadius r)
      (_ : ∀ x ∈ Q, ENNReal.ofReal |x.val i - y.val i| < r →
        coordinate_readout (φ.func (some x)) j =
          coordinate_readout (φ.func (some y)) j), r := by
  unfold annihilation_radius
  apply iSup_congr
  intro r
  apply iSup_congr
  intro hr
  apply iSup_congr_Prop ?_ (by intros; rfl)
  constructor
  · intro h x hx hxy
    have hz := h ⟨hxy, ⟨x, hx, rfl⟩⟩
    rw [singleton_computational_fiber_eq] at hz
    exact (coordinate_zero_iff j _ _ (hQ ⟨x, hx, rfl⟩) (hQ ⟨y, hy, rfl⟩)).mp hz.2
  · intro h z hz
    rcases hz.2 with ⟨x, hx, rfl⟩
    rw [singleton_computational_fiber_eq]
    exact ⟨⟨x, hx, rfl⟩,
      (coordinate_zero_iff j _ _ (hQ ⟨x, hx, rfl⟩) (hQ ⟨y, hy, rfl⟩)).mpr
        (h x hx hz.1)⟩

/--
OET anchor: h-ad3957f2de83d301
Supports the opening coordinate interpretation of this section.
全族输入、全族输出的原零化半径；输入距离为坐标最大距离。
-/
theorem full_coordinate_annihilation_radius_level_set
    (φ : Operator (CoordinatePoint n A) coordinate_bot) (Q : Set A)
    (hQ : (some '' Q) ⊆ dom φ) (y : A) (hy : y ∈ Q) :
    full_output_annihilation_radius (fun k : Fin n => coordinate_dist k) φ
      coordinate_full_dist (some '' Q) (some y) =
    ⨆ (r : ENNReal) (_ : FinitePositiveRadius r)
      (_ : ∀ x ∈ Q, coordinate_sup_distance x.val y.val < r →
        coordinate_readout (φ.func (some x)) =
          coordinate_readout (φ.func (some y))), r := by
  rw [full_output_annihilation_radius_eq_local_constant_radius _
    (by intro i x; cases x <;> simp [coordinate_dist]) coordinate_family_is_separating]
  unfold local_constant_radius
  apply iSup_congr
  intro r
  apply iSup_congr
  intro hr
  apply iSup_congr_Prop ?_ (by intros; rfl)
  constructor
  · intro h x hx hxy
    have hz := h ⟨hxy, ⟨x, hx, rfl⟩⟩
    exact congrArg coordinate_readout hz.2
  · intro h z hz
    rcases hz.2 with ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx, rfl⟩,
      (coordinate_readout_eq_iff _ _ (hQ ⟨x, hx, rfl⟩) (hQ ⟨y, hy, rfl⟩)).mp
        (h x hx hz.1)⟩

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
