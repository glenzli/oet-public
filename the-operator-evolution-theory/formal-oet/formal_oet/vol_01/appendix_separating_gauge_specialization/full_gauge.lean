import formal_oet.vol_01.ch_03_operator_local_degeneracy.computational_fiber

namespace formal_oet.vol_01.appendix_separating_gauge_specialization

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-5ddb4141bb0d9204
全族复合距离：有限非空指标族全部分量的最大值。
此构造不要求族分离性；附加条件沿用 CH1 的 IsSeparating。
-/
def full_gauge_dist : X → X → ENNReal :=
  comp_pseudo_metric d (full_nonempty_finset : NonemptyFinset I)

/--
OET anchor: h-954b5b2b9076a08d
**命题（全族复合距离的开球与分离性）**
从族分离的附加假设推出全族复合距离的点分离性。
-/
theorem full_gauge_dist_eq_zero_iff
    (hd_self : ∀ i x, d i x x = 0)
    (hsep : IsSeparating d) (x y : X) :
    full_gauge_dist d x y = 0 ↔ x = y := by
  constructor
  · intro hxy
    apply hsep x y
    intro i
    have hall :=
      (comp_pseudo_metric_eq_zero_iff d
        (full_nonempty_finset : NonemptyFinset I) x y).mp hxy
    exact hall i (Finset.mem_univ i)
  · intro hxy
    subst y
    rw [full_gauge_dist, comp_pseudo_metric_eq_zero_iff]
    intro j _
    exact hd_self j x

/-- Internal metric part of the full-gauge specialization. -/
theorem full_gauge_extended_pseudo_metric
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    ExtendedPseudoMetric X bot (full_gauge_dist d) := by
  classical
  let i0 : I := Classical.choice ‹Nonempty I›
  refine
    { nonabsorbing := (hd i0).nonabsorbing
      dist_self := ?_
      symm := ?_
      triangle := ?_
      isolate_bot := ?_ }
  · intro x
    rw [full_gauge_dist, comp_pseudo_metric_eq_zero_iff]
    intro i _
    exact (hd i).dist_self x
  · intro x y
    simp only [full_gauge_dist, comp_pseudo_metric]
    apply Finset.sup_congr rfl
    intro i _
    exact (hd i).symm x y
  · intro x y z
    simp only [full_gauge_dist, comp_pseudo_metric]
    apply Finset.sup_le
    intro i hi
    calc
      d i x z ≤ d i x y + d i y z := (hd i).triangle x y z
      _ ≤ Finset.univ.sup (fun j => d j x y) +
          Finset.univ.sup (fun j => d j y z) :=
        add_le_add (Finset.le_sup (f := fun j => d j x y) hi)
          (Finset.le_sup (f := fun j => d j y z) hi)
  · intro x hx
    apply top_unique
    have hi : d i0 x bot = ⊤ := (hd i0).isolate_bot x hx
    rw [← hi]
    exact Finset.le_sup (f := fun j => d j x bot) (Finset.mem_univ i0)

/--
OET anchor: h-954b5b2b9076a08d
**命题（全族复合距离的开球与分离性）**
全族复合距离的开球是全部分量开球的交，不需要族分离假设。
Lean 中对全部 ENNReal 半径成立，包含正文使用的有限正半径。
-/
theorem full_gauge_ball (x : X) (r : ENNReal) :
    ball (full_gauge_dist d) x r = ⋂ i : I, ball (d i) x r := by
  ext y
  simp only [ball, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hy i
    exact lt_of_le_of_lt
      (Finset.le_sup (f := fun j => d j y x) (Finset.mem_univ i)) hy
  · intro hy
    simp only [full_gauge_dist, comp_pseudo_metric]
    by_cases hr : 0 < r
    · exact (Finset.sup_lt_iff hr).mpr (fun i _ => hy i)
    · have hr0 : r = 0 := bot_unique (not_lt.mp hr)
      subst r
      exact False.elim (not_lt_of_ge (zero_le _) (hy (Classical.choice ‹Nonempty I›)))

/--
OET anchor: h-954b5b2b9076a08d
**命题（全族复合距离的开球与分离性）**
在分离规范空间中汇总扩展度量性质与开球公式。
开球公式独立由 full_gauge_ball 给出，不使用族分离假设。
-/
theorem full_gauge_metric_and_ball
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (hsep : IsSeparating d) :
    (ExtendedPseudoMetric X bot (full_gauge_dist d)) ∧
    (∀ x y, full_gauge_dist d x y = 0 ↔ x = y) ∧
    (∀ x r,
      ball (full_gauge_dist d) x r = ⋂ i : I, ball (d i) x r) := by
  exact ⟨full_gauge_extended_pseudo_metric d hd,
    full_gauge_dist_eq_zero_iff d (fun i => (hd i).dist_self) hsep,
    full_gauge_ball d⟩

end

end formal_oet.vol_01.appendix_separating_gauge_specialization
