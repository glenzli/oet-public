import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_01_foundations.operator_space

namespace formal_oet.vol_01.exercise_solutions.foundation_examples

open formal_oet.vol_01.ch_01_foundations

/-- Extend a distance by one isolated absorbing point. -/
def extend_distance {A : Type} (d : A → A → ENNReal) :
    Option A → Option A → ENNReal
  | none, none => 0
  | some x, some y => d x y
  | _, _ => ⊤

theorem extend_distance_is_extended {A : Type} [Nonempty A]
    (d : A → A → ENNReal) (hself : ∀ x, d x x = 0)
    (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) :
    ExtendedPseudoMetric (Option A) none (extend_distance d) := by
  refine ⟨⟨some (Classical.choice ‹Nonempty A›), by simp⟩, ?_, ?_, ?_, ?_⟩
  · intro x; cases x <;> simp [extend_distance, hself]
  · intro x y; cases x <;> cases y <;> simp [extend_distance, hsymm]
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp [extend_distance, htri]
  · intro x hx; cases x <;> simp_all [extend_distance]

/-- Count internal covers when the open balls are exactly label classes. -/
theorem covering_number_eq_card_of_labels {X Y : Type} [Fintype Y]
    (d : X → X → ENNReal) (ε : ENNReal) (U : Set X)
    (q : X → Y) (rep : Y → X) (hrep : ∀ y, rep y ∈ U)
    (hqrep : ∀ y, q (rep y) = y)
    (hball : ∀ x ∈ U, ∀ c ∈ U, d x c < ε ↔ q x = q c) :
    covering_number d ε U = (Fintype.card Y : ENNReal) := by
  classical
  have hinj : Function.Injective rep := by
    intro x y h
    simpa [hqrep] using congrArg q h
  let centers := Finset.univ.image rep
  have hnet : InternalEpsilonNet d ε U centers := by
    constructor
    · intro c hc
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hc
      exact hrep y
    · intro x hx
      refine ⟨rep (q x), Finset.mem_image.mpr ⟨q x, Finset.mem_univ _, rfl⟩, ?_⟩
      exact (hball x hx _ (hrep _)).mpr (hqrep _).symm
  apply le_antisymm
  · have hcard : centers.card = Fintype.card Y := by
      exact (Finset.card_image_of_injective _ hinj).trans (Finset.card_univ)
    exact iInf_le_of_le centers (iInf_le_of_le hnet (by rw [hcard]))
  · apply le_iInf
    intro s
    apply le_iInf
    intro hs
    have hsub : (Finset.univ : Finset Y) ⊆ s.image q := by
      intro y _
      obtain ⟨c, hc, hd⟩ := hs.2 (rep y) (hrep y)
      have heq := (hball _ (hrep y) _ (hs.1 hc)).mp hd
      exact Finset.mem_image.mpr ⟨c, hc, (hqrep y ▸ heq).symm⟩
    have hcard : Fintype.card Y ≤ s.card := by
      exact (Finset.card_le_card hsub).trans (Finset.card_image_le)
    exact_mod_cast hcard

/-- Distance obtained from a binary readout. -/
def readout_distance {A : Type} (q : A → Bool) (x y : A) : ENNReal :=
  if q x = q y then 0 else 1

theorem readout_triangle {A : Type} (q : A → Bool) (x y z : A) :
    readout_distance q x z ≤ readout_distance q x y + readout_distance q y z := by
  unfold readout_distance
  split_ifs <;> simp_all

/-- The two readouts on a, b, c, represented by 0, 1, 2. -/
def readout (i : Bool) (x : Fin 3) : Bool :=
  if i then decide (x = 2) else decide (x = 1)

def component (i : Bool) := extend_distance (readout_distance (readout i))
def domain : Set (Option (Fin 3)) := Set.range some

/-- OET anchor: h-6f3c195f30ebebd6
Both component distances satisfy the extended gauge axioms. -/
theorem component_is_extended (i : Bool) :
    ExtendedPseudoMetric (Option (Fin 3)) none (component i) := by
  apply extend_distance_is_extended
  · intro x; simp [readout_distance]
  · intro x y; simp [readout_distance, eq_comm]
  · exact readout_triangle _

/-- OET anchor: h-6f3c195f30ebebd6
Each component has exactly two open unit-ball classes. -/
theorem component_covering (i : Bool) :
    covering_number (component i) 1 domain = 2 := by
  let q : Option (Fin 3) → Bool := fun x => readout i (x.getD 0)
  let rep : Bool → Option (Fin 3) :=
    fun b => some (if b then (if i then 2 else 1) else 0)
  have h := covering_number_eq_card_of_labels (component i) 1 domain q rep
  have hr : ∀ y, rep y ∈ domain := by intro y; exact ⟨_, rfl⟩
  have hq : ∀ y, q (rep y) = y := by
    intro y; cases i <;> cases y <;> decide
  have hb : ∀ x ∈ domain, ∀ c ∈ domain, component i x c < 1 ↔ q x = q c := by
    rintro _ ⟨x, rfl⟩ _ ⟨c, rfl⟩
    change (if readout i x = readout i c then (0 : ENNReal) else 1) < 1 ↔ _
    split_ifs <;> simp_all [q]
  simpa using h hr hq hb

/-- OET anchor: h-6f3c195f30ebebd6
The maximum of the two components separates all three points. -/
theorem joint_covering :
    covering_number (fun x y => max (component false x y) (component true x y))
      1 domain = 3 := by
  apply (covering_number_eq_card_of_labels _ 1 domain
    (fun x => x.getD 0) some (fun x => ⟨x, rfl⟩) (by simp) ?_).trans
      (by simp)
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  fin_cases x <;> fin_cases y <;>
    norm_num [component, extend_distance, readout_distance, readout, Fin.ext_iff]

/-- OET anchor: h-6f3c195f30ebebd6
The explicit maximum is the textbook subfamily pseudometric. -/
theorem joint_distance_eq_subfamily (x y : Option (Fin 3)) :
    subfamily_pseudometric component Set.univ x y =
      max (component false x y) (component true x y) := by
  simp [subfamily_pseudometric, iSup_subtype, iSup_bool_eq, max_comm]

/-- OET anchor: h-6f3c195f30ebebd6
Joint covering in the textbook subfamily notation. -/
theorem subfamily_covering :
    covering_number (subfamily_pseudometric component Set.univ) 1 domain = 3 := by
  have heq : subfamily_pseudometric component Set.univ =
      fun x y => max (component false x y) (component true x y) := by
    funext x y
    exact joint_distance_eq_subfamily x y
  rw [heq]
  exact joint_covering

/-- OET anchor: h-6f3c195f30ebebd6
The binary readouts attain exactly three of the four possible pairs. -/
theorem joint_readout_range :
    Set.range (fun x : Fin 3 => (readout false x, readout true x)) =
      {(false, false), (true, false), (false, true)} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩; fin_cases x <;> decide
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩

end formal_oet.vol_01.exercise_solutions.foundation_examples
