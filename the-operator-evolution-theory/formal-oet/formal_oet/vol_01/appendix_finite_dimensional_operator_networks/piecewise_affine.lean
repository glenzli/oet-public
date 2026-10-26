import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.block_routes

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks

open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork

noncomputable section

variable {X Y V : Type} {bot : X}

/-- A finite conjunction of affine equality or inequality constraints. -/
def IsLinearCell (is_affine_constraint : (X → Prop) → Prop) (Q : Set X) : Prop :=
  ∃ constraints : List (X → Prop),
    (∀ c ∈ constraints, is_affine_constraint c) ∧
    Q = {x | ∀ c ∈ constraints, c x}

/-- Intersection of a finite list of sets. -/
def list_intersection : List (Set X) → Set X
  | [] => Set.univ
  | Q :: Qs => Q ∩ list_intersection Qs

theorem linear_cell_list_intersection
    (is_affine_constraint : (X → Prop) → Prop)
    (Qs : List (Set X))
    (hQs : ∀ Q ∈ Qs, IsLinearCell is_affine_constraint Q) :
    IsLinearCell is_affine_constraint (list_intersection Qs) := by
  induction Qs with
  | nil =>
      refine ⟨[], by simp, ?_⟩
      ext x
      simp [list_intersection]
  | cons Q Qs ih =>
      rcases hQs Q (by simp) with ⟨cs, hcs, rfl⟩
      rcases ih (fun R hR => hQs R (by simp [hR])) with ⟨ds, hds, htail⟩
      refine ⟨cs ++ ds, ?_, ?_⟩
      · intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · exact hcs c hc
        · exact hds c hc
      · rw [list_intersection, htail]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, List.mem_append]
        constructor
        · rintro ⟨hcs_x, hds_x⟩ c (hc | hc)
          · exact hcs_x c hc
          · exact hds_x c hc
        · intro h
          exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩

theorem linear_cell_affine_preimage
    (is_affine_constraint_X : (X → Prop) → Prop)
    (is_affine_constraint_Y : (Y → Prop) → Prop)
    (G : X → Y)
    (hpre : ∀ c, is_affine_constraint_Y c →
      is_affine_constraint_X (fun x => c (G x)))
    (Q : Set Y) (hQ : IsLinearCell is_affine_constraint_Y Q) :
    IsLinearCell is_affine_constraint_X (G ⁻¹' Q) := by
  rcases hQ with ⟨constraints, hconstraints, rfl⟩
  refine ⟨constraints.map (fun c x => c (G x)), ?_, ?_⟩
  · intro c hc
    rcases List.mem_map.mp hc with ⟨d, hd, rfl⟩
    exact hpre d (hconstraints d hd)
  · ext x
    simp

/--
**引理（线性单元的交与仿射原像）**
线性单元对有限交和仿射原像封闭。
-/
theorem linear_cells_closed_under_intersection_and_affine_preimage
    (is_affine_constraint_X : (X → Prop) → Prop)
    (is_affine_constraint_Y : (Y → Prop) → Prop)
    (Qs : List (Set X))
    (hQs : ∀ Q ∈ Qs, IsLinearCell is_affine_constraint_X Q)
    (G : X → Y)
    (hpre : ∀ c, is_affine_constraint_Y c →
      is_affine_constraint_X (fun x => c (G x)))
    (Q : Set Y) (hQ : IsLinearCell is_affine_constraint_Y Q) :
    IsLinearCell is_affine_constraint_X (list_intersection Qs) ∧
    IsLinearCell is_affine_constraint_X (G ⁻¹' Q) :=
  ⟨linear_cell_list_intersection is_affine_constraint_X Qs hQs,
    linear_cell_affine_preimage is_affine_constraint_X is_affine_constraint_Y G hpre Q hQ⟩

/-- The two-piece affine step function used at a path boundary. -/
def affine_step (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1

/--
Function-level auxiliary counterexample; the finite network is constructed in
affine_step_network.lean.
**命题（分片仿射性不蕴含跨路径连续性）**
-/
theorem piecewise_affine_does_not_imply_cross_path_continuity
    : (∀ x : ℝ, x < 0 → affine_step x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → affine_step x = 1) ∧
      ¬ ContinuousAt affine_step 0 := by
  refine ⟨fun x hx => by simp [affine_step, hx],
    fun x hx => by simp [affine_step, not_lt.mpr hx], ?_⟩
  intro hcontinuous
  rw [Metric.continuousAt_iff] at hcontinuous
  rcases hcontinuous (1 / 2 : ℝ) (by norm_num) with ⟨delta, hdelta, hbound⟩
  let x : ℝ := -(delta / 2)
  have hxneg : x < 0 := by
    dsimp [x]
    linarith
  have hxdist : dist x 0 < delta := by
    rw [Real.dist_eq]
    dsimp [x]
    rw [sub_zero, abs_neg, abs_of_nonneg (by positivity : 0 ≤ delta / 2)]
    linarith
  have himage := hbound hxdist
  have hxvalue : affine_step x = 0 := by simp [affine_step, hxneg]
  have hzero_value : affine_step 0 = 1 := by simp [affine_step]
  rw [hxvalue, hzero_value, Real.dist_eq] at himage
  norm_num at himage

end

end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
