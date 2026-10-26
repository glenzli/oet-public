import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.euclidean_geometry
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.jacobi_coordinate_bridge
import Mathlib.Algebra.Order.Floor.Ring

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.appendix_separating_gauge_specialization
open scoped BigOperators
noncomputable section

/-- Select one point of the set in each occupied color. The resulting net is
internal even when the set is neither closed nor convex. -/
theorem internal_cover_of_finite_coloring {X C : Type} [Fintype C]
    (d : X → X → ENNReal) (ε : ENNReal) (S : Set X) (f : S → C)
    (hdiam : ∀ x y : S, f x = f y → d x.val y.val < ε) :
    covering_number d ε S ≤ Fintype.card C := by
  classical
  by_cases hS : S.Nonempty
  · let x₀ : S := ⟨hS.choose, hS.choose_spec⟩
    let rep (c : C) : S := if h : ∃ x : S, f x = c then h.choose else x₀
    have hrep (x : S) : f (rep (f x)) = f x := by
      dsimp only [rep]
      rw [dif_pos ⟨x, rfl⟩]
      exact (show ∃ y : S, f y = f x from ⟨x, rfl⟩).choose_spec
    let centers := Finset.univ.image (fun c => (rep c).val)
    have hnet : InternalEpsilonNet d ε S centers := by
      constructor
      · intro y hy
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hy
        exact (rep c).property
      · intro x hx
        refine ⟨(rep (f ⟨x, hx⟩)).val, Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
        exact hdiam ⟨x, hx⟩ _ (hrep ⟨x, hx⟩).symm
    exact (iInf_le_of_le centers (iInf_le_of_le hnet le_rfl)).trans
      (by exact_mod_cast (Finset.card_image_le : centers.card ≤ (Finset.univ : Finset C).card))
  · rw [Set.not_nonempty_iff_eq_empty.mp hS, covering_number_empty]
    exact zero_le _

theorem floor_cell_diameter (a x y ε : ℝ) (hε : 0 < ε) (hx : a ≤ x) (hy : a ≤ y)
    (heq : ⌊(x - a) / ε⌋₊ = ⌊(y - a) / ε⌋₊) : |x - y| < ε := by
  have hxl := Nat.floor_le (div_nonneg (sub_nonneg.mpr hx) hε.le)
  have hyl := Nat.floor_le (div_nonneg (sub_nonneg.mpr hy) hε.le)
  have hxu := Nat.lt_floor_add_one ((x - a) / ε)
  have hyu := Nat.lt_floor_add_one ((y - a) / ε)
  rw [heq] at hxl hxu
  have h₁ : (x - a) / ε - (y - a) / ε < 1 := by linarith
  have h₂ : (y - a) / ε - (x - a) / ε < 1 := by linarith
  rw [← sub_div, div_lt_one hε] at h₁ h₂
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

variable {n : ℕ} [NeZero n] {A : Set (CoordinateVector n)}

/--
OET anchor: h-6f0f018319c18266
The literal floor-plus-one bound for the original full-coordinate distance.
Floor cells handle endpoints and zero-width intervals without a limiting argument.
-/
theorem actual_box_coordinate_cover (a b : CoordinateVector n) (ε : ℝ) (hε : 0 < ε)
    (S : Set (CoordinatePoint n A))
    (hS : ∀ x ∈ S, ∃ v : A, x = some v ∧ ∀ i, a i ≤ v.val i ∧ v.val i ≤ b i) :
    covering_number coordinate_full_dist (ENNReal.ofReal ε) S ≤
      ∏ i : Fin n, (⌊(b i - a i) / ε⌋₊ + 1 : ℕ) := by
  classical
  let v (x : S) : A := (hS x.val x.property).choose
  have hv (x : S) : x.val = some (v x) ∧ ∀ i, a i ≤ (v x).val i ∧ (v x).val i ≤ b i :=
    (hS x.val x.property).choose_spec
  let color (x : S) : (i : Fin n) → Fin (⌊(b i - a i) / ε⌋₊ + 1) := fun i =>
    ⟨⌊((v x).val i - a i) / ε⌋₊,
      Nat.lt_succ_of_le (Nat.floor_mono (div_le_div_of_nonneg_right
        (sub_le_sub_right ((hv x).2 i).2 (a i)) hε.le))⟩
  have h := internal_cover_of_finite_coloring coordinate_full_dist (ENNReal.ofReal ε) S color ?_
  · simpa [Fintype.card_pi, Fintype.card_fin, Nat.cast_prod] using h
  · intro x y heq
    rw [(hv x).1, (hv y).1, coordinate_full_dist_eq_sup_norm,
      ENNReal.ofReal_lt_ofReal_iff hε]
    apply (pi_norm_lt_iff hε).mpr
    intro i
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    apply floor_cell_diameter _ _ _ _ hε ((hv x).2 i).1 ((hv y).2 i).1
    exact congrArg Fin.val (congrFun heq i)

theorem euclidean_norm_le_sqrt_dimension (v : CoordinateVector n) :
    ‖euclidean_coordinates v‖ ≤ Real.sqrt n * ‖v‖ := by
  apply (euclidean_norm_le_support_mul_sup v).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.sqrt_le_sqrt
  have h : (coordinate_support v).card ≤ n := by
    simpa using (Finset.card_le_card (Finset.filter_subset _ _) :
      (coordinate_support v).card ≤ (Finset.univ : Finset (Fin n)).card)
  exact_mod_cast h

omit [NeZero n] in
/-- Each coordinate is bounded by the actual Euclidean norm, so their maximum
is bounded as well. -/
theorem sup_norm_le_euclidean_norm (v : CoordinateVector n) :
    ‖v‖ ≤ ‖euclidean_coordinates v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  simpa [euclidean_coordinates, PiLp.coe_symm_continuousLinearEquiv,
    PiLp.toLp_apply] using PiLp.norm_apply_le (euclidean_coordinates v) i

/--
OET anchor: h-5cd365cd756cb93e
The standard Euclidean specialization uses the exact constants 1 and sqrt(n).
Both internal covering-number comparisons apply to arbitrary sets in the
original absorbing-point model, not only to bounded boxes.
-/
theorem actual_euclidean_norm_and_covering_comparison
    (ε : ℝ) (hε : 0 < ε) (S : Set (CoordinatePoint n A)) :
    (∀ v : CoordinateVector n,
      ‖v‖ ≤ ‖euclidean_coordinates v‖ ∧
        ‖euclidean_coordinates v‖ ≤ Real.sqrt n * ‖v‖) ∧
    covering_number coordinate_full_dist (ENNReal.ofReal ε) S ≤
        covering_number euclidean_distance (ENNReal.ofReal ε) S ∧
    covering_number euclidean_distance (ENNReal.ofReal ε) S ≤
        covering_number coordinate_full_dist (ENNReal.ofReal (ε / Real.sqrt n)) S := by
  have hn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos n)
  have hcomparison := coordinate_norm_ball_and_covering_number_comparison
    euclidean_seminorm 1 (Real.sqrt n) ε zero_lt_one hn hε
    (by
      intro v
      change 1 * ‖v‖ ≤ ‖euclidean_coordinates v‖
      simpa using sup_norm_le_euclidean_norm v)
    (by
      intro v
      exact euclidean_norm_le_sqrt_dimension v) S
  refine ⟨fun v => ⟨sup_norm_le_euclidean_norm v, euclidean_norm_le_sqrt_dimension v⟩,
    ?_, ?_⟩
  · simpa [euclidean_distance] using hcomparison.2.2.1
  · simpa [euclidean_distance] using hcomparison.2.2.2

/--
OET anchor: h-6f0f018319c18266
The Euclidean bound uses the same actual internal centers and the exact factor sqrt(n).
-/
theorem actual_box_euclidean_cover (a b : CoordinateVector n) (ε : ℝ) (hε : 0 < ε)
    (S : Set (CoordinatePoint n A))
    (hS : ∀ x ∈ S, ∃ v : A, x = some v ∧ ∀ i, a i ≤ v.val i ∧ v.val i ≤ b i) :
    covering_number euclidean_distance (ENNReal.ofReal ε) S ≤
      ∏ i : Fin n, (⌊Real.sqrt n * (b i - a i) / ε⌋₊ + 1 : ℕ) := by
  have hn : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos n)
  have hcoord := actual_box_coordinate_cover a b (ε / Real.sqrt n) (div_pos hε hn) S hS
  have htransfer : covering_number euclidean_distance (ENNReal.ofReal ε) S ≤
      covering_number coordinate_full_dist (ENNReal.ofReal (ε / Real.sqrt n)) S := by
    apply covering_number_le_of_ball_containment
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => exact ENNReal.ofReal_pos.mpr hε
      | some y =>
        have htop : coordinate_full_dist (none : CoordinatePoint n A) (some y) = ⊤ := by
          apply top_unique
          exact Finset.le_sup (f := fun _ : Fin n => (⊤ : ENNReal)) (Finset.mem_univ 0)
        rw [htop] at hxy
        exact (not_lt_of_ge le_top hxy).elim
    | some x =>
      cases y with
      | none =>
        have htop : coordinate_full_dist (some x) (none : CoordinatePoint n A) = ⊤ := by
          apply top_unique
          exact Finset.le_sup (f := fun _ : Fin n => (⊤ : ENNReal)) (Finset.mem_univ 0)
        rw [htop] at hxy
        exact (not_lt_of_ge le_top hxy).elim
      | some y =>
        rw [coordinate_full_dist_eq_sup_norm, ENNReal.ofReal_lt_ofReal_iff (div_pos hε hn)] at hxy
        rw [euclidean_distance_some, ENNReal.ofReal_lt_ofReal_iff hε]
        exact (euclidean_norm_le_sqrt_dimension _).trans_lt (by nlinarith [(lt_div_iff₀ hn).mp hxy])
  apply htransfer.trans
  convert hcoord using 1
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  congr 2
  field_simp

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
