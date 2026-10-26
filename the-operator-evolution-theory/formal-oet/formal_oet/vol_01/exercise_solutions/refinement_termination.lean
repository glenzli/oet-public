import formal_oet.vol_01.ch_05_operator_networks.refinement_termination
import formal_oet.vol_01.ch_05_operator_networks.algebraic_refinement_construction

namespace formal_oet.vol_01.exercise_solutions.refinement_termination

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.refinement_termination
open NetworkObject

noncomputable section
variable {X : Type} {bot a : X}

/-- OET anchor: h-8570ea1bf1a8708b
A finite domain-splitting chain has at most its initial domain measure many steps.
The decreasing quantity is derived from the actual network refinement data. -/
theorem domain_refinement_step_bound
    {A : Type} (V : A → Type) (N : (s : A) → FiniteOperatorNetwork X bot (V s))
    (R : A → A → Prop)
    (hstep : ∀ s t, R s t → ∃ h : (N s).NodeDomainRefinement (N t),
      2 ≤ h.part_count)
    (hfinite : ∀ s v, ((N s).node_dom v).Finite)
    {s : A} {tail : List A} (hchain : RefinementChain R (s :: tail)) :
    tail.length ≤ nodeDomainMeasure (N s) := by
  have hdec : StrictlyDecreases R (fun s => nodeDomainMeasure (N s)) := by
    intro s t h
    obtain ⟨href, hproper⟩ := hstep s t h
    exact NodeDomainRefinement.nodeDomainMeasure_decreases href hproper (hfinite s)
  have h := refinement_chain_length_le_measure (R := R)
    (μ := fun s => nodeDomainMeasure (N s)) hdec hchain
  simpa using h

/-- Identity on one effective point, completed by the absorbing point elsewhere. -/
def singleton_identity (a : X) : Operator X bot :=
  restrict_operator id_operator {a}

@[simp] theorem singleton_identity_apply :
    (singleton_identity (bot := bot) a).func a = a := by
  simp [singleton_identity, restrict_operator, id_operator]

@[simp] theorem singleton_identity_dom (ha : a ≠ bot) :
    dom (singleton_identity (bot := bot) a) = {a} := by
  apply dom_restrict_operator_eq
  intro x hx
  have : x = a := hx
  subst x
  exact ha

private theorem singleton_identity_ne_bot (ha : a ≠ bot) :
    singleton_identity (bot := bot) a ≠ bot_operator := by
  intro h
  have := congrArg (fun f : Operator X bot => f.func a) h
  simp [ha, bot_operator] at this

private theorem restrict_singleton_identity :
    restrict_operator (singleton_identity (bot := bot) a) {a} = singleton_identity a := by
  apply Operator.ext
  funext x
  by_cases hx : x = a
  · subst x
    simp [restrict_operator]
  · simp [singleton_identity, restrict_operator, hx]

private theorem expanded_mem_inl
    {V : Type} {M : FiniteOperatorNetwork X bot V} {v w : V}
    (F : NodeFactorizationData M v) (p : List V) :
    Sum.inl w ∈ F.expand_path p ↔ w ∈ p := by
  classical
  induction p with
  | nil => simp [NodeFactorizationData.expand_path]
  | cons z p ih =>
    by_cases hz : z = v <;> simp [NodeFactorizationData.expand_path, hz, ih]

private theorem expanded_mem_inr
    {V : Type} {M : FiniteOperatorNetwork X bot V} {v : V}
    (F : NodeFactorizationData M v) (p : List V) :
    Sum.inr () ∈ F.expand_path p ↔ v ∈ p := by
  classical
  induction p with
  | nil => simp [NodeFactorizationData.expand_path]
  | cons z p ih =>
    by_cases hz : z = v
    · simp [NodeFactorizationData.expand_path, hz]
    · simp [NodeFactorizationData.expand_path, hz, ih, Ne.symm hz]

private theorem expanded_nodup
    {V : Type} {M : FiniteOperatorNetwork X bot V} {v : V}
    (F : NodeFactorizationData M v) (p : List V) (hp : p.Nodup) :
    (F.expand_path p).Nodup := by
  classical
  induction p with
  | nil => simp [NodeFactorizationData.expand_path]
  | cons z p ih =>
    have hznot := (List.nodup_cons.mp hp).1
    have hrest := ih hp.of_cons
    by_cases hz : z = v
    · subst z
      simp [NodeFactorizationData.expand_path, List.nodup_cons,
        expanded_mem_inl, expanded_mem_inr, hznot, hrest]
    · simp [NodeFactorizationData.expand_path, hz, List.nodup_cons,
        expanded_mem_inl, hznot, hrest]

private theorem expanded_nodup_length
    {V : Type} [DecidableEq V] {M : FiniteOperatorNetwork X bot V} {v : V}
    (F : NodeFactorizationData M v) (p : List V) (hp : p.Nodup) :
    (F.expand_path p).length = p.length + if v ∈ p then 1 else 0 := by
  classical
  induction p with
  | nil => simp [NodeFactorizationData.expand_path]
  | cons z p ih =>
    have hznot := (List.nodup_cons.mp hp).1
    have hrest := ih hp.of_cons
    by_cases hz : z = v
    · subst z
      simp [NodeFactorizationData.expand_path, hrest, hznot]
    · simp only [NodeFactorizationData.expand_path, hz, ↓reduceIte, List.length_cons,
        List.mem_cons, Ne.symm hz, false_or, hrest]
      omega

/-- Concrete finite networks whose every local operator is the same singleton identity.
All finite-network obligations remain in the actual `FiniteOperatorNetwork` value. -/
structure SingletonIdentityNetwork (X : Type) (bot a : X) where
  node_count : Nat
  network : FiniteOperatorNetwork X bot (Fin node_count)
  source_eq : network.U = {a}
  node_eq : ∀ v, network.node_op v = singleton_identity a
  path_nodup : ∀ x, (network.path_of x).Nodup

namespace SingletonIdentityNetwork
variable (ha : a ≠ bot) (N : SingletonIdentityNetwork X bot a)

def input : N.network.U := ⟨a, N.source_eq ▸ Set.mem_singleton a⟩

def target : Fin N.node_count := N.network.entry N.input

include ha in
@[simp] theorem local_domain (v : Fin N.node_count) :
    N.network.node_dom v = {a} := by
  rw [FiniteOperatorNetwork.node_dom_eq_dom, N.node_eq, singleton_identity_dom ha]

/-- OET anchor: h-8570ea1bf1a8708b
The two factors satisfy the actual algebraic-refinement hypotheses. -/
def factors_at (v : Fin N.node_count) : NodeFactorizationData N.network v where
  first := singleton_identity a
  second := singleton_identity a
  first_domain := by rw [N.local_domain ha, singleton_identity_dom ha]
  second_domain := by
    rw [N.local_domain ha, singleton_identity_dom ha]
    simp
  factorization := by
    intro x hx
    rw [N.local_domain ha] at hx
    have : x = a := hx
    subst x
    simp [N.node_eq]

/-- Select the entry node for the displayed infinite sequence. -/
def factors : NodeFactorizationData N.network N.target := N.factors_at ha N.target

private theorem factor_node_eq (v : Fin N.node_count ⊕ Unit) :
    (N.factors ha).node_op v = singleton_identity a := by
  classical
  cases v with
  | inl v =>
    by_cases hv : v = N.target
    · simp [NodeFactorizationData.node_op, hv, factors, factors_at, N.local_domain ha,
        restrict_singleton_identity]
    · simp [NodeFactorizationData.node_op, hv, N.node_eq]
  | inr v =>
    cases v
    simp [NodeFactorizationData.node_op, factors, factors_at, N.local_domain ha,
      singleton_identity_apply, restrict_singleton_identity]

/-- Split the entry identity into two identity factors and retain the constructed network. -/
def advance : SingletonIdentityNetwork X bot a where
  node_count := (N.factors ha).network.node_count
  network := (N.factors ha).network.standard_relabel
  source_eq := N.source_eq
  node_eq := by
    intro v
    change (N.factors ha).node_op _ = _
    exact N.factor_node_eq ha _
  path_nodup := by
    intro x
    change (List.map _ ((N.factors ha).network.path_of x)).Nodup
    apply List.Nodup.map (Equiv.injective _)
    apply List.Nodup.of_map (f := Subtype.val)
    rw [(N.factors ha).network_path_labels]
    exact expanded_nodup _ _ (N.path_nodup x)

/-- The step is the existing algebraic network construction with the displayed factors. -/
theorem advance_is_algebraic_construction :
    (N.advance ha).network = (N.factors ha).network.standard_relabel := rfl

/-- Each step preserves the global operator, including completion outside the source. -/
theorem advance_extensional_eq :
    (N.advance ha).network.extensional_operator = N.network.extensional_operator :=
  (N.factors ha).network.standard_relabel_preserves.2.1.trans
    (N.factors ha).network_extensional_eq

private theorem input_unique (x : N.network.U) : x = N.input := by
  apply Subtype.ext
  exact (Set.ext_iff.mp N.source_eq x.val).mp x.property

private theorem input_target_mem : N.target ∈ N.network.path_of N.input := by
  have hm : ∀ {v x p}, TerminalPathFrom N.network.node_op N.network.choice v x p → v ∈ p := by
    intro v x p hp
    cases hp <;> simp
  exact hm (N.network.path_terminal N.input)

/-- With no repeated labels the identity insertion adds exactly one occurrence. -/
theorem advance_path_length :
    ((N.advance ha).network.path_of (N.advance ha).input).length =
      (N.network.path_of N.input).length + 1 := by
  classical
  have hlength := congrArg List.length ((N.factors ha).network_path_labels N.input)
  simp only [List.length_map] at hlength
  have hexpand := expanded_nodup_length (N.factors ha) _ (N.path_nodup N.input)
  rw [if_pos N.input_target_mem] at hexpand
  simpa only [advance, FiniteOperatorNetwork.standard_relabel,
    FiniteOperatorNetwork.relabel_path_length] using hlength.trans hexpand

/-- The unique input visits every node once; therefore path length is actual node count. -/
theorem node_count_eq_path_length :
    N.network.node_count = (N.network.path_of N.input).length := by
  classical
  letI := N.network.node_fintype
  have hcover : (N.network.path_of N.input).toFinset = Finset.univ := by
    apply Finset.ext
    intro v
    simp only [Finset.mem_univ, iff_true, List.mem_toFinset]
    obtain ⟨x, hx⟩ := N.network.node_reachable v
    simpa only [N.input_unique x] using hx
  rw [← List.toFinset_card_of_nodup (N.path_nodup N.input), hcover]
  rfl

/-- The maximum over reachable paths is the length at the sole effective input. -/
theorem evaluation_depth_eq_path_length :
    N.network.evaluation_depth = (N.network.path_of N.input).length := by
  apply le_antisymm
  · apply N.network.evaluation_depth_le_of_input_lengths
    intro x
    rw [N.input_unique x]
  · exact N.network.input_path_length_le_evaluation_depth N.input

/-- Initial one-node identity network. -/
def initial : SingletonIdentityNetwork X bot a where
  node_count := (single_node_network (singleton_identity a)
    (singleton_identity_ne_bot ha)).node_count
  network := (single_node_network (singleton_identity a)
    (singleton_identity_ne_bot ha)).standard_relabel
  source_eq := singleton_identity_dom ha
  node_eq := by intro v; rfl
  path_nodup := by intro x; simp [FiniteOperatorNetwork.standard_relabel,
    FiniteOperatorNetwork.relabel, single_node_network]

/-- OET anchor: h-8570ea1bf1a8708b
Iterating actual admissible identity factorization gives an infinite sequence. -/
def sequence : Nat → SingletonIdentityNetwork X bot a
  | 0 => initial ha
  | n + 1 => (sequence n).advance ha

@[simp] theorem sequence_successor (n : Nat) :
    sequence ha (n + 1) = (sequence ha n).advance ha := rfl

/-- OET anchor: h-8570ea1bf1a8708b
Every member is a finite network on one effective input, with finite local domains. -/
theorem sequence_local_domains_finite (n : Nat) (v : Fin (sequence ha n).node_count) :
    ((sequence ha n).network.node_dom v).Finite := by
  rw [(sequence ha n).local_domain ha]
  exact Set.finite_singleton a

/-- OET anchor: h-8570ea1bf1a8708b
Every network in the sequence realizes exactly the same singleton identity. -/
theorem sequence_extensional_operator (n : Nat) :
    (sequence ha n).network.extensional_operator = singleton_identity a := by
  induction n with
  | zero =>
    exact (single_node_network (singleton_identity a)
      (singleton_identity_ne_bot ha)).standard_relabel_preserves.2.1.trans
      (single_node_network_extensional_operator_eq _ _)
  | succ n ih => exact ((sequence ha n).advance_extensional_eq ha).trans ih

/-- Path lengths in the actual networks grow strictly, so the construction never stabilizes. -/
theorem sequence_path_length_strict :
    StrictMono (fun n => ((sequence ha n).network.path_of (sequence ha n).input).length) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [sequence_successor, advance_path_length]
  omega

/-- After `m` identity refinements the actual path has `m + 1` occurrences. -/
theorem sequence_path_length (m : Nat) :
    ((sequence ha m).network.path_of (sequence ha m).input).length = m + 1 := by
  induction m with
  | zero => simp [sequence, initial, FiniteOperatorNetwork.standard_relabel,
      FiniteOperatorNetwork.relabel, single_node_network]
  | succ m ih =>
    rw [sequence_successor, advance_path_length, ih]

/-- OET anchor: h-8570ea1bf1a8708b
Actual node count and evaluation depth both grow to `m + 1`. -/
theorem sequence_size_and_depth (m : Nat) :
    (sequence ha m).network.node_count = m + 1 ∧
      (sequence ha m).network.evaluation_depth = m + 1 := by
  constructor
  · rw [(sequence ha m).node_count_eq_path_length, sequence_path_length]
  · rw [(sequence ha m).evaluation_depth_eq_path_length, sequence_path_length]

/-- OET anchor: h-8570ea1bf1a8708b
The domain measure is zero throughout the singleton identity construction. -/
theorem sequence_domain_measure (m : Nat) :
    nodeDomainMeasure (sequence ha m).network = 0 := by
  classical
  unfold nodeDomainMeasure
  simp [(sequence ha m).local_domain ha]

/-- OET anchor: h-8570ea1bf1a8708b
Even a ranking required to decrease only along the displayed sequence is impossible. -/
theorem no_sequence_decreasing_ranking :
    ¬ ∃ μ : SingletonIdentityNetwork X bot a → Nat,
      ∀ n, μ (sequence ha (n + 1)) < μ (sequence ha n) := by
  rintro ⟨μ, hμ⟩
  apply no_infinite_refinement_chain
    (R := fun m n : Nat => n = m + 1)
    (μ := fun n => μ (sequence ha n))
    (fun {m n} h => h ▸ hμ m)
  exact ⟨id, fun _ => rfl⟩

/-- OET anchor: h-8570ea1bf1a8708b
The additive local-operator rank condition would require an impossible inequality. -/
theorem identity_rank_cannot_decrease (rank : Operator X bot → Nat) :
    ¬ 2 * rank (singleton_identity a) < rank (singleton_identity a) := by omega

/-- No natural-valued ranking decreases on all these permitted identity refinements. -/
theorem no_decreasing_ranking :
    ¬ ∃ μ : SingletonIdentityNetwork X bot a → Nat,
      ∀ N, μ (N.advance ha) < μ N := by
  rintro ⟨μ, hμ⟩
  apply no_infinite_refinement_chain
    (R := fun N M : SingletonIdentityNetwork X bot a => M = N.advance ha)
    (μ := μ) (fun h => h ▸ hμ _)
  exact ⟨sequence ha, fun _ => rfl⟩

end SingletonIdentityNetwork
end
end formal_oet.vol_01.exercise_solutions.refinement_termination
