import formal_oet.vol_01.ch_05_operator_networks.operator_network
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
import formal_oet.vol_01.exercise_solutions.foundation_examples

namespace formal_oet.vol_01.exercise_solutions.network_path_lipschitz
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_02_operator_bounds
noncomputable section

def source : Set (Option ℝ)
  | none => False
  | some x => (-1 < x ∧ x < 0) ∨ (0 < x ∧ x < 1)

@[simp] theorem mem_source_none : (none : Option ℝ) ∉ source := by
  intro h
  exact h

@[simp] theorem mem_source_some (x : ℝ) :
    some x ∈ source ↔ (-1 < x ∧ x < 0) ∨ (0 < x ∧ x < 1) := Iff.rfl

def branch (x : Option ℝ) : Bool := if x.getD 0 < 0 then false else true

def node_op (b : Bool) : Operator (Option ℝ) none :=
  ⟨Option.map (fun _ => if b then (1 : ℝ) else 0), rfl⟩

/-- OET anchor: h-b3e92d181e7139bd
The two constant branches are a genuine finite operator network. -/
def network : FiniteOperatorNetwork (Option ℝ) none Bool where
  U := source
  bot_not_mem := mem_source_none
  node_fintype := inferInstance
  node_op := node_op
  node_dom_nonempty := fun b => ⟨some 0, by simp [dom, node_op]⟩
  entry := fun x => branch x.val
  entry_mem := by
    rintro ⟨x, hx⟩
    cases x with
    | none => exact False.elim hx
    | some x => simp [dom, node_op]
  choice := fun _ _ => .stop
  choice_next_mem := by intros; contradiction
  depth_bound := 1
  path_of := fun x => [branch x.val]
  path_terminal := fun _ => .stop rfl
  path_length_le_depth := by intro x; rfl
  node_reachable := by
    intro b
    cases b
    · refine ⟨⟨some (-1 / 2), by norm_num⟩, ?_⟩
      norm_num [branch]
    · refine ⟨⟨some (1 / 2), by norm_num⟩, ?_⟩
      norm_num [branch]

/-- The usual real distance, with the absorber at infinite distance. -/
def real_distance : Option ℝ → Option ℝ → ENNReal :=
  foundation_examples.extend_distance (fun x y : ℝ => ENNReal.ofReal |x - y|)

/-- OET anchor: h-b3e92d181e7139bd
The distance used in the exercise satisfies the extended gauge axioms. -/
theorem real_distance_valid : ExtendedPseudoMetric (Option ℝ) none real_distance := by
  apply foundation_examples.extend_distance_is_extended
  · intro x; simp
  · intro x y; simp [abs_sub_comm]
  · intro x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le x y z)

/-- OET anchor: h-b3e92d181e7139bd
The full absorbing extension of the piecewise-constant output. -/
theorem extensional_apply (x : ℝ) :
    network.extensional_operator.func (some x) =
      if (-1 < x ∧ x < 0) ∨ (0 < x ∧ x < 1) then
        some (if x < 0 then 0 else 1) else none := by
  by_cases hx : (-1 < x ∧ x < 0) ∨ (0 < x ∧ x < 1)
  · by_cases hn : x < 0 <;>
      simp [FiniteOperatorNetwork.extensional_operator, FiniteOperatorNetwork.eval,
        network, branch, node_op, chain_eval_nodes_core, hn, le_of_not_gt, not_le_of_gt]
  · simp [FiniteOperatorNetwork.extensional_operator, network, hx]

/-- OET anchor: h-b3e92d181e7139bd
The two singleton paths have exactly the given entrance intervals. -/
theorem path_domain (b : Bool) :
    network.path_domain [b] =
      {z | ∃ x : ℝ, z = some x ∧
        if b then 0 < x ∧ x < 1 else -1 < x ∧ x < 0} := by
  ext z
  cases z with
  | none => simp [FiniteOperatorNetwork.path_domain, network]
  | some x =>
    cases b
    · simp only [FiniteOperatorNetwork.path_domain, network, branch, Bool.if_true_right,
        Bool.or_false, List.cons.injEq, Bool.not_eq_eq_eq_not, Bool.not_false,
        decide_eq_true_eq, and_true, exists_prop, Set.mem_setOf_eq, mem_source_some,
        Option.getD_some, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
        exists_eq_left', and_congr_left_iff]
      intro hn
      constructor
      · rintro (h | h)
        · exact h.1
        · linarith
      · intro h; exact Or.inl ⟨h, hn⟩
    · simp only [FiniteOperatorNetwork.path_domain, network, branch, Bool.if_true_right,
        Bool.or_false, List.cons.injEq, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, not_lt, and_true, exists_prop, Set.mem_setOf_eq,
        mem_source_some, Option.getD_some, ↓reduceIte, Option.some.injEq, exists_eq_left']
      constructor
      · rintro ⟨h, hn⟩
        rcases h with h | h
        · exfalso; linarith
        · exact h
      · intro h; exact ⟨Or.inr h, le_of_lt h.1⟩

theorem reachable_path_singleton (p : network.ReachablePath) :
    ∃ b : Bool, p.nodes = [b] := by
  obtain ⟨z, hz, hp⟩ := p.nonempty_domain
  exact ⟨branch z, hp.symm⟩

/-- OET anchor: h-b3e92d181e7139bd
All same-path output distances vanish, giving the finite Lip bound zero. -/
theorem path_distance_zero (p : network.ReachablePath)
    {x y : Option ℝ} (hx : x ∈ network.path_domain p.nodes)
    (hy : y ∈ network.path_domain p.nodes) :
    real_distance ((network.path_chain p.nodes).func x)
      ((network.path_chain p.nodes).func y) = 0 := by
  obtain ⟨b, hb⟩ := reachable_path_singleton p
  rw [hb] at hx hy ⊢
  obtain ⟨x, rfl, hx⟩ := (Set.ext_iff.mp (path_domain b) x).mp hx
  obtain ⟨y, rfl, hy⟩ := (Set.ext_iff.mp (path_domain b) y).mp hy
  rw [network.path_chain_apply_eq_chain_eval_nodes,
    network.path_chain_apply_eq_chain_eval_nodes]
  simp [FiniteOperatorNetwork.chain_eval_nodes, chain_eval_nodes_core, network,
    node_op, real_distance, foundation_examples.extend_distance]

/-- OET anchor: h-b3e92d181e7139bd
No finite real Lip constant controls all source-domain pairs. -/
theorem no_finite_global_lip :
    ¬ ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ network.U, ∀ y ∈ network.U,
      real_distance (network.extensional_operator.func x)
        (network.extensional_operator.func y) ≤ ENNReal.ofReal L * real_distance x y := by
  rintro ⟨L, hL, h⟩
  let t : ℝ := 1 / (4 * (L + 1))
  have hden : 0 < 4 * (L + 1) := by positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have ht1 : t < 1 := by dsimp [t]; apply (div_lt_iff₀ hden).2; linarith
  have hx : some (-t) ∈ network.U := Or.inl ⟨by linarith, by linarith⟩
  have hy : some t ∈ network.U := Or.inr ⟨ht, ht1⟩
  have he := h (some (-t)) hx (some t) hy
  rw [extensional_apply, extensional_apply] at he
  have hx' : (-1 < -t ∧ -t < 0) ∨ (0 < -t ∧ -t < 1) := hx
  have hy' : (-1 < t ∧ t < 0) ∨ (0 < t ∧ t < 1) := hy
  simp only [if_pos hx', if_pos hy', if_pos (neg_neg_of_pos ht),
    if_neg (not_lt_of_ge (le_of_lt ht))] at he
  have hd : |-t - t| = 2 * t := by rw [abs_of_neg (by linarith)]; ring
  change ENNReal.ofReal |(0 : ℝ) - 1| ≤
    ENNReal.ofReal L * ENNReal.ofReal |-t - t| at he
  rw [hd, ← ENNReal.ofReal_mul hL] at he
  norm_num only [zero_sub, abs_neg, abs_one] at he
  have hr : (1 : ℝ) ≤ L * (2 * t) := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp he
  have hsmall : L * (2 * t) < 1 := by
    dsimp [t]
    rw [mul_one_div, ← mul_div_assoc]
    apply (div_lt_iff₀ hden).2
    nlinarith
  linarith

/-- OET anchor: h-b3e92d181e7139bd
Every path has the chapter's scalar Lip certificate with constant zero. -/
theorem path_scalar_lip (p : network.ReachablePath) :
    HasScalarLipBound (fun _ : Unit => real_distance) (network.path_chain p.nodes)
      (network.path_domain p.nodes) () () 0 := by
  refine ⟨network.path_domain_subset_path_chain_dom p, ?_⟩
  intro x hx y hy
  dsimp only
  rw [path_distance_zero p hx hy, zero_mul]

/-- OET anchor: h-b3e92d181e7139bd
There is no finite extended-valued scalar certificate on the entire source. -/
theorem no_finite_global_scalar_lip :
    ¬ ∃ c : ENNReal, c ≠ ⊤ ∧
      HasScalarLipBound (fun _ : Unit => real_distance) network.extensional_operator
        network.U () () c := by
  rintro ⟨c, hc, hbound⟩
  apply no_finite_global_lip
  refine ⟨c.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro x hx y hy
  simpa only [ENNReal.ofReal_toReal hc] using hbound.2 x hx y hy

end
end formal_oet.vol_01.exercise_solutions.network_path_lipschitz
