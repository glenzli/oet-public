import formal_oet.vol_01.exercise_solutions.foundation_examples

namespace formal_oet.vol_01.exercise_solutions.entropy_jump

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.exercise_solutions.foundation_examples

/-- `none` is the isolated point a; `some k` is a point in the cluster. -/
def cluster_distance {m : ℕ} (δ : ENNReal) (x y : Option (Fin m)) : ENNReal :=
  if x = y then 0 else if x = none ∨ y = none then 1 else δ

def distance {m : ℕ} (δ : ENNReal) := extend_distance (@cluster_distance m δ)
def domain (m : ℕ) : Set (Option (Option (Fin m))) := Set.range some

theorem cluster_le_one {m : ℕ} {δ : ENNReal} (hδ : δ < 1)
    (x y : Option (Fin m)) : cluster_distance δ x y ≤ 1 := by
  unfold cluster_distance
  split_ifs <;> simp_all [le_of_lt hδ]

/-- OET anchor: h-5e432018e992f2d3
The two-level distance is an extended pseudometric after adjoining bottom. -/
theorem distance_is_extended {m : ℕ} {δ : ENNReal} (hδ : δ < 1) :
    ExtendedPseudoMetric (Option (Option (Fin m))) none (@distance m δ) := by
  apply extend_distance_is_extended
  · intro x; simp [cluster_distance]
  · intro x y; simp [cluster_distance, eq_comm, or_comm]
  · intro x y z
    by_cases hxy : x = y
    · subst y; simp [cluster_distance]
    by_cases hyz : y = z
    · subst z; simp [cluster_distance]
    by_cases hxz : x = z
    · subst z; simp [cluster_distance]
    cases x <;> cases y <;> cases z <;> simp_all only [cluster_distance, Option.some.injEq, reduceCtorEq,
      not_false_eq_true, not_true_eq_false, ite_true, ite_false, or_self, or_true,
      or_false, self_le_add_left, self_le_add_right]
    · exact hδ.le.trans (by norm_num)

/-- OET anchor: h-5e432018e992f2d3
Positive cluster spacing separates every two distinct nonabsorbing points. -/
theorem cluster_positive {m : ℕ} {δ : ENNReal} (hδ : 0 < δ)
    {x y : Option (Fin m)} (hxy : x ≠ y) : 0 < cluster_distance δ x y := by
  simp only [cluster_distance, if_neg hxy]
  split_ifs <;> positivity

/-- OET anchor: h-5e432018e992f2d3
At and below the cluster spacing every point needs its own center. -/
theorem covering_fine {m : ℕ} {δ ε : ENNReal} (hδ : δ < 1)
    (hε : 0 < ε) (hεδ : ε ≤ δ) :
    covering_number (@distance m δ) ε (domain m) = (m + 1 : ℕ) := by
  have h := covering_number_eq_card_of_labels (@distance m δ) ε (domain m)
    (fun x => x.getD none) some (fun x => ⟨x, rfl⟩) (by simp)
  have hb : ∀ x ∈ domain m, ∀ c ∈ domain m,
      distance δ x c < ε ↔ x.getD none = c.getD none := by
    rintro _ ⟨x, rfl⟩ _ ⟨c, rfl⟩
    change cluster_distance δ x c < ε ↔ x = c
    by_cases h : x = c
    · simp [cluster_distance, h, hε]
    · simp only [cluster_distance, if_neg h]
      simp only [h, iff_false]
      split_ifs
      · exact not_lt_of_ge (hεδ.trans hδ.le)
      · exact not_lt_of_ge hεδ
  simpa using h hb

/-- OET anchor: h-5e432018e992f2d3
Between the two scales exactly two centers are necessary and sufficient. -/
theorem covering_middle {m : ℕ} (hm : 2 ≤ m) {δ ε : ENNReal}
    (hδ : 0 < δ) (hδε : δ < ε) (hε : ε ≤ 1) :
    covering_number (@distance m δ) ε (domain m) = 2 := by
  letI : NeZero m := ⟨by omega⟩
  let q : Option (Option (Fin m)) → Bool := fun x => (x.getD none).isSome
  let rep : Bool → Option (Option (Fin m)) :=
    fun b => some (if b then some 0 else none)
  have hr : ∀ y, rep y ∈ domain m := by intro y; exact ⟨_, rfl⟩
  have hq : ∀ y, q (rep y) = y := by intro y; cases y <;> rfl
  have hb : ∀ x ∈ domain m, ∀ c ∈ domain m, distance δ x c < ε ↔ q x = q c := by
    rintro _ ⟨x, rfl⟩ _ ⟨c, rfl⟩
    have hpos := hδ.trans hδε
    cases x <;> cases c <;>
      simp only [distance, extend_distance, cluster_distance, Option.some.injEq,
        reduceCtorEq, ite_true, ite_false, or_self, or_true, or_false, hpos,
        not_lt_of_ge hε, Option.getD_some, Option.isSome_none, Option.isSome_some,
        Bool.false_eq_true, Bool.true_eq_false, iff_true, q]
    split_ifs <;> assumption
  simpa using covering_number_eq_card_of_labels (@distance m δ) ε (domain m)
    q rep hr hq hb

/-- OET anchor: h-5e432018e992f2d3
Above the outer distance a single center covers the whole set. -/
theorem covering_coarse {m : ℕ} {δ ε : ENNReal} (hδ : δ < 1) (hε : 1 < ε) :
    covering_number (@distance m δ) ε (domain m) = 1 := by
  have hb : ∀ x ∈ domain m, ∀ c ∈ domain m, distance δ x c < ε ↔ () = () := by
    rintro _ ⟨x, rfl⟩ _ ⟨c, rfl⟩
    constructor
    · intro _; rfl
    · intro _; exact (cluster_le_one hδ x c).trans_lt hε
  simpa using covering_number_eq_card_of_labels (@distance m δ) ε (domain m)
    (fun _ => ()) (fun _ => some none) (fun _ => ⟨none, rfl⟩) (by simp) hb

/-- OET anchor: h-5e432018e992f2d3
The complete entropy profile, including both open-ball endpoints. -/
theorem entropy_profile {m : ℕ} (hm : 2 ≤ m) {δ ε : ENNReal}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    metric_entropy (@distance m δ) ε (domain m) =
      if ε ≤ δ then (Real.logb 2 (m + 1) : EReal) else
        if ε ≤ 1 then 1 else 0 := by
  unfold metric_entropy
  by_cases hfine : ε ≤ δ
  · rw [if_pos hfine, covering_fine hδ1 hε hfine]
    simp [log2_ereal, ENNReal.toReal_add]
  · rw [if_neg hfine]
    by_cases hmid : ε ≤ 1
    · rw [if_pos hmid, covering_middle hm hδ0 (lt_of_not_ge hfine) hmid]
      norm_num [log2_ereal, Real.logb_self_eq_one]
    · rw [if_neg hmid, covering_coarse hδ1 (lt_of_not_ge hmid)]
      simp [log2_ereal]

/-- OET anchor: h-5e432018e992f2d3
The entropy increment across the cluster threshold is exactly log₂(m+1)-1. -/
theorem entropy_jump_size {m : ℕ} (hm : 2 ≤ m) {δ ε : ENNReal}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδε : δ < ε) (hε1 : ε ≤ 1) :
    metric_entropy (@distance m δ) δ (domain m) -
      metric_entropy (@distance m δ) ε (domain m) =
        ((Real.logb 2 (m + 1) - 1 : ℝ) : EReal) := by
  rw [entropy_profile hm hδ0 hδ1 hδ0,
    entropy_profile hm hδ0 hδ1 (hδ0.trans hδε)]
  simp [not_le_of_gt hδε, hε1, EReal.coe_sub]

/-- OET anchor: h-5e432018e992f2d3
The jump sizes log₂(m+1)-1 have no bound independent of cluster size. -/
theorem entropy_jump_unbounded (M : ℝ) :
    ∃ m : ℕ, 2 ≤ m ∧ M < Real.logb 2 (m + 1) - 1 := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max (2 : ℝ) (2 ^ (M + 1) : ℝ))
  have hm2 : 2 ≤ m := by
    have : (2 : ℝ) < m := (le_max_left _ _).trans_lt hm
    exact_mod_cast (le_of_lt this)
  refine ⟨m, hm2, ?_⟩
  have hpow : (2 : ℝ) ^ (M + 1) < (m : ℝ) + 1 := by
    have := (le_max_right _ _).trans_lt hm
    linarith
  have hlog := (Real.lt_logb_iff_rpow_lt (b := (2 : ℝ)) (by norm_num)
    (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr hpow
  linarith

end formal_oet.vol_01.exercise_solutions.entropy_jump
