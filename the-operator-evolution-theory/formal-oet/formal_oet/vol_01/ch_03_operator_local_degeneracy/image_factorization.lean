import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators

variable {X I : Type} {bot : X}
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-6d303a1afa732703
**命题 #h-6d303a1afa732703（像值因子化与标量 Lip 界，等值点对集包含）**
`EqPairSetLe phi_a phi_b U` means that the equal-value pair set of `phi_a`
on `U` is contained in the equal-value pair set of `phi_b`.
-/
def EqPairSetLe (phi_a phi_b : Operator X bot) (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, phi_a.func x = phi_a.func y → phi_b.func x = phi_b.func y

/--
OET anchor: h-c21391963ef67ef0
**命题 #h-c21391963ef67ef0（零距商上的像值因子化，零测距点对集包含）**
`ZeroDistPairSetLe d phi_a phi_b U` is the componentwise zero-distance
pair-set inclusion on `U`.
-/
def ZeroDistPairSetLe (phi_a phi_b : Operator X bot) (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    (∀ j : I, d j (phi_a.func x) (phi_a.func y) = 0) →
      ∀ j : I, d j (phi_b.func x) (phi_b.func y) = 0

/--
OET anchor: h-c21391963ef67ef0
**命题 #h-c21391963ef67ef0（零距商上的像值因子化，像集分离性）**
The gauge family separates the image of `phi` on `U`.
-/
def ImageSeparating (phi : Operator X bot) (U : Set X) : Prop :=
  ∀ a ∈ operator_image phi U, ∀ b ∈ operator_image phi U,
    (∀ j : I, d j a b = 0) → a = b

/--
OET anchor: h-6d303a1afa732703
**命题 #h-6d303a1afa732703（像值因子化与标量 Lip 界）**
A point transform `T` satisfying `T ∘ phi_a = phi_b` on `U` forces equality
pair-set inclusion.
-/
theorem eq_pair_set_le_of_point_transform
    (phi_a phi_b : Operator X bot) (U : Set X) (T : X → X)
    (hT : ∀ x ∈ U, T (phi_a.func x) = phi_b.func x) :
    EqPairSetLe phi_a phi_b U := by
  intro x hx y hy hxy
  rw [← hT x hx, ← hT y hy, hxy]

/--
OET anchor: h-6d303a1afa732703
**命题 #h-6d303a1afa732703（像值因子化与标量 Lip 界）**
Under equal-value pair-set inclusion, a point transform can be chosen on the image
of `phi_a`; outside that image it is assigned `bot`.
-/
noncomputable def point_transform_from_eq_pair_set
    (phi_a phi_b : Operator X bot) (U : Set X)
    (_hpair : EqPairSetLe phi_a phi_b U) : X → X :=
  by
    classical
    exact fun y =>
      if hy : ∃ x : X, x ∈ U ∧ phi_a.func x = y then
        phi_b.func (Classical.choose hy)
      else
        bot

/--
OET anchor: h-6d303a1afa732703
**命题 #h-6d303a1afa732703（像值因子化与标量 Lip 界）**
The chosen transform realizes `phi_b` on every point of `U`.
-/
theorem point_transform_from_eq_pair_set_spec
    (phi_a phi_b : Operator X bot) (U : Set X)
    (hpair : EqPairSetLe phi_a phi_b U) :
    ∀ x ∈ U,
      point_transform_from_eq_pair_set phi_a phi_b U hpair (phi_a.func x) = phi_b.func x := by
  classical
  intro x hx
  unfold point_transform_from_eq_pair_set
  let hy : ∃ y : X, y ∈ U ∧ phi_a.func y = phi_a.func x := ⟨x, hx, rfl⟩
  have hspec := Classical.choose_spec hy
  rw [dif_pos hy]
  exact hpair (Classical.choose hy) hspec.1 x hx hspec.2

/--
OET anchor: h-6d303a1afa732703
**命题 #h-6d303a1afa732703（像值因子化与标量 Lip 界）**
Point transforms on the image exist exactly when equal-value pair sets are included.
-/
theorem point_transform_exists_iff_eq_pair_set_le
    (phi_a phi_b : Operator X bot) (U : Set X) :
    (∃ T : X → X, ∀ x ∈ U, T (phi_a.func x) = phi_b.func x) ↔
      EqPairSetLe phi_a phi_b U := by
  constructor
  · rintro ⟨T, hT⟩
    exact eq_pair_set_le_of_point_transform phi_a phi_b U T hT
  · intro hpair
    exact ⟨point_transform_from_eq_pair_set phi_a phi_b U hpair,
      point_transform_from_eq_pair_set_spec phi_a phi_b U hpair⟩

/--
OET anchor: h-6d303a1afa732703
**命题 #h-6d303a1afa732703（像值因子化与标量 Lip 界，共同域版本）**
Text-faithful point-transform criterion retaining the explicit common-domain
condition on `U`.
-/
theorem point_transform_exists_iff_eq_pair_set_le_on_common_domain
    (phi_a phi_b : Operator X bot) (U : Set X)
    (hdom_a : U ⊆ dom phi_a) (hdom_b : U ⊆ dom phi_b) :
    (∃ T : X → X, ∀ x ∈ U, T (phi_a.func x) = phi_b.func x) ↔
      EqPairSetLe phi_a phi_b U := by
  have _ := hdom_a
  have _ := hdom_b
  exact point_transform_exists_iff_eq_pair_set_le phi_a phi_b U

/--
If the zero-distance pair-set inclusion holds and the target image is separated
by the gauge family, then equal-value pair-set inclusion follows. This is a
local helper for the point/quotient distinction rather than a separately
numbered item in the text.
-/
theorem eq_pair_set_le_of_zero_dist_pair_set_le_and_image_separating
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi_a phi_b : Operator X bot) (U : Set X)
    (hpair_zero : ZeroDistPairSetLe d phi_a phi_b U)
    (hsep : ImageSeparating d phi_b U) :
    EqPairSetLe phi_a phi_b U := by
  intro x hx y hy hxy
  apply hsep (phi_b.func x) (Set.mem_image_of_mem phi_b.func hx)
    (phi_b.func y) (Set.mem_image_of_mem phi_b.func hy)
  apply hpair_zero x hx y hy
  intro j
  rw [hxy]
  exact (hd j).dist_self (phi_a.func y)

/--
If equal-value pair inclusion holds and the source image is separated, then
zero-distance pair inclusion follows. This is the reverse helper needed for
the point/quotient criterion comparison.
-/
theorem zero_dist_pair_set_le_of_eq_pair_set_le_and_image_separating
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi_a phi_b : Operator X bot) (U : Set X)
    (hpair_eq : EqPairSetLe phi_a phi_b U)
    (hsep : ImageSeparating d phi_a U) :
    ZeroDistPairSetLe d phi_a phi_b U := by
  intro x hx y hy hzero j
  have hxy : phi_a.func x = phi_a.func y :=
    hsep (phi_a.func x) (Set.mem_image_of_mem phi_a.func hx)
      (phi_a.func y) (Set.mem_image_of_mem phi_a.func hy) hzero
  have hab : phi_b.func x = phi_b.func y := hpair_eq x hx y hy hxy
  rw [hab]
  exact (hd j).dist_self (phi_b.func y)

/--
OET anchor: h-c21391963ef67ef0
**命题 #h-c21391963ef67ef0（零距商上的像值因子化，点值与商值判据一致）**
On an explicit common domain, the directional point-value and quotient-value
criteria agree when both the source and target images are separated.
-/
theorem eq_pair_set_le_iff_zero_dist_pair_set_le_of_images_separating
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi_a phi_b : Operator X bot) (U : Set X)
    (hdom_a : U ⊆ dom phi_a) (hdom_b : U ⊆ dom phi_b)
    (hsep_a : ImageSeparating d phi_a U)
    (hsep_b : ImageSeparating d phi_b U) :
    EqPairSetLe phi_a phi_b U ↔ ZeroDistPairSetLe d phi_a phi_b U := by
  have _ := hdom_a
  have _ := hdom_b
  constructor
  · intro hpair_eq
    exact zero_dist_pair_set_le_of_eq_pair_set_le_and_image_separating
      d hd phi_a phi_b U hpair_eq hsep_a
  · intro hpair_zero
    exact eq_pair_set_le_of_zero_dist_pair_set_le_and_image_separating
      d hd phi_a phi_b U hpair_zero hsep_b

/--
OET anchor: h-c21391963ef67ef0
**命题 #h-c21391963ef67ef0（零距商上的像值因子化，双向点值与商值判据一致）**
Under separation of both images, mutual equal-value inclusion agrees with
mutual zero-distance inclusion.
-/
theorem mutual_eq_pair_iff_mutual_zero_dist_pair_of_images_separating
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi_a phi_b : Operator X bot) (U : Set X)
    (hdom_a : U ⊆ dom phi_a) (hdom_b : U ⊆ dom phi_b)
    (hsep_a : ImageSeparating d phi_a U)
    (hsep_b : ImageSeparating d phi_b U) :
    (EqPairSetLe phi_a phi_b U ∧ EqPairSetLe phi_b phi_a U) ↔
      (ZeroDistPairSetLe d phi_a phi_b U ∧ ZeroDistPairSetLe d phi_b phi_a U) := by
  have hab := eq_pair_set_le_iff_zero_dist_pair_set_le_of_images_separating
    d hd phi_a phi_b U hdom_a hdom_b hsep_a hsep_b
  have hba := eq_pair_set_le_iff_zero_dist_pair_set_le_of_images_separating
    d hd phi_b phi_a U hdom_b hdom_a hsep_b hsep_a
  exact and_congr hab hba

/--
OET anchor: h-c21391963ef67ef0
**命题 #h-c21391963ef67ef0（零距商上的像值因子化）**
The zero-distance pair-set inclusion is precisely the well-definedness
condition for the formula `[phi_a x] ↦ [phi_b x]` on zero-distance quotient
classes.
-/
theorem zero_quotient_transform_well_defined
    (phi_a phi_b : Operator X bot) (U : Set X)
    (hpair_zero : ZeroDistPairSetLe d phi_a phi_b U) :
    ∀ x ∈ U, ∀ y ∈ U,
      (∀ j : I, d j (phi_a.func x) (phi_a.func y) = 0) →
        ∀ j : I, d j (phi_b.func x) (phi_b.func y) = 0 := by
  exact hpair_zero

/--
OET anchor: h-c21391963ef67ef0
**命题 #h-c21391963ef67ef0（零距商上的像值因子化，商像集）**
The componentwise zero-distance relation is a setoid on each operator image.
-/
def zero_image_setoid
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi : Operator X bot) (U : Set X) :
    Setoid { y : X // y ∈ operator_image phi U } where
  r a b := ∀ j : I, d j a.1 b.1 = 0
  iseqv := by
    exact ⟨
      (by
        intro a j
        exact (hd j).dist_self a.1),
      (by
        intro a b hab j
        rw [(hd j).symm]
        exact hab j),
      (by
        intro a b c hab hbc j
        have htri := (hd j).triangle a.1 b.1 c.1
        have hle : d j a.1 c.1 ≤ 0 := by
          simpa [hab j, hbc j] using htri
        exact le_antisymm hle (zero_le _))⟩

/--
OET anchor: h-c21391963ef67ef0
**命题 #h-c21391963ef67ef0（零距商上的像值因子化，商像集）**
The zero-distance quotient of an operator image.
-/
abbrev ZeroImageQuotient
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi : Operator X bot) (U : Set X) : Type :=
  Quotient (zero_image_setoid d hd phi U)

/--
OET anchor: h-c21391963ef67ef0
**命题 #h-c21391963ef67ef0（零距商上的像值因子化，商映射）**
Under zero-distance pair-set inclusion, the formula
`[phi_a x] ↦ [phi_b x]` defines an actual map between quotient image types.
-/
noncomputable def zero_quotient_transform
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi_a phi_b : Operator X bot) (U : Set X)
    (hpair_zero : ZeroDistPairSetLe d phi_a phi_b U) :
    ZeroImageQuotient d hd phi_a U → ZeroImageQuotient d hd phi_b U :=
  Quot.lift
    (fun a : { y : X // y ∈ operator_image phi_a U } =>
      let x := Classical.choose a.2
      let hx := Classical.choose_spec a.2
      Quotient.mk (zero_image_setoid d hd phi_b U)
        ⟨phi_b.func x, Set.mem_image_of_mem phi_b.func hx.1⟩)
    (by
      intro a b hab
      apply Quot.sound
      intro j
      let xa := Classical.choose a.2
      let xb := Classical.choose b.2
      have hxa := Classical.choose_spec a.2
      have hxb := Classical.choose_spec b.2
      apply hpair_zero xa hxa.1 xb hxb.1
      intro k
      calc
        d k (phi_a.func xa) (phi_a.func xb) = d k a.1 b.1 := by
          rw [hxa.2, hxb.2]
        _ = 0 := hab k)

/--
OET anchor: h-c21391963ef67ef0
**命题 #h-c21391963ef67ef0（零距商上的像值因子化，商映射公式）**
The quotient transform sends the class of `phi_a x` to the class of `phi_b x`.
-/
theorem zero_quotient_transform_spec
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi_a phi_b : Operator X bot) (U : Set X)
    (hpair_zero : ZeroDistPairSetLe d phi_a phi_b U)
    (x : X) (hx : x ∈ U) :
    zero_quotient_transform d hd phi_a phi_b U hpair_zero
        (Quotient.mk (zero_image_setoid d hd phi_a U)
          ⟨phi_a.func x, Set.mem_image_of_mem phi_a.func hx⟩) =
      Quotient.mk (zero_image_setoid d hd phi_b U)
        ⟨phi_b.func x, Set.mem_image_of_mem phi_b.func hx⟩ := by
  apply Quot.sound
  intro j
  let xa :=
    Classical.choose (show phi_a.func x ∈ operator_image phi_a U from
      Set.mem_image_of_mem phi_a.func hx)
  have hxa :=
    Classical.choose_spec (show phi_a.func x ∈ operator_image phi_a U from
      Set.mem_image_of_mem phi_a.func hx)
  apply hpair_zero xa hxa.1 x hx
  intro k
  rw [hxa.2]
  exact (hd k).dist_self (phi_a.func x)

/--
OET anchor: h-c21391963ef67ef0
The prescribed quotient-image map exists exactly when the zero-distance pair
set is included. Necessity uses equality of quotient classes, rather than
assuming pair-set inclusion as a certificate.
-/
theorem zero_quotient_transform_exists_iff
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi_a phi_b : Operator X bot) (U : Set X) :
    (∃ T : ZeroImageQuotient d hd phi_a U → ZeroImageQuotient d hd phi_b U,
      ∀ x (hx : x ∈ U),
        T (Quotient.mk (zero_image_setoid d hd phi_a U)
          ⟨phi_a.func x, Set.mem_image_of_mem phi_a.func hx⟩) =
        Quotient.mk (zero_image_setoid d hd phi_b U)
          ⟨phi_b.func x, Set.mem_image_of_mem phi_b.func hx⟩) ↔
      ZeroDistPairSetLe d phi_a phi_b U := by
  constructor
  · rintro ⟨T, hT⟩ x hx y hy hzero
    have hclasses :
        Quotient.mk (zero_image_setoid d hd phi_a U)
            ⟨phi_a.func x, Set.mem_image_of_mem phi_a.func hx⟩ =
          Quotient.mk (zero_image_setoid d hd phi_a U)
            ⟨phi_a.func y, Set.mem_image_of_mem phi_a.func hy⟩ :=
      Quotient.sound hzero
    have houtputs := congrArg T hclasses
    rw [hT x hx, hT y hy] at houtputs
    exact Quotient.exact houtputs
  · intro hpair
    exact ⟨zero_quotient_transform d hd phi_a phi_b U hpair,
      zero_quotient_transform_spec d hd phi_a phi_b U hpair⟩

/--
OET anchor: h-6d303a1afa732703
**命题 #h-6d303a1afa732703（像值因子化与标量 Lip 界，标量情形）**
In the scalar representative setting, a `K_A`-co-Lip operator `phi_a` and an
`L_B`-Lip operator `phi_b` make the point transform Lipschitz with coefficient
`K_A⁻¹ * L_B` on representative pairs.
-/
theorem point_transform_scalar_lip_bound_of_colip
    (dist : X → X → ENNReal)
    (phi_a phi_b : Operator X bot) (U : Set X) (T : X → X)
    (K_a L_b : ENNReal)
    (hK_ne_zero : K_a ≠ 0) (hK_ne_top : K_a ≠ ⊤)
    (hL_ne_top : L_b ≠ ⊤)
    (hdom_a : U ⊆ dom phi_a) (hdom_b : U ⊆ dom phi_b)
    (hT : ∀ x ∈ U, T (phi_a.func x) = phi_b.func x)
    (hcolip :
      ∀ x ∈ U, ∀ y ∈ U,
        K_a * dist x y ≤ dist (phi_a.func x) (phi_a.func y))
    (hL :
      ∀ x ∈ U, ∀ y ∈ U,
        dist (phi_b.func x) (phi_b.func y) ≤ L_b * dist x y) :
    ∀ x ∈ U, ∀ y ∈ U,
      dist (T (phi_a.func x)) (T (phi_a.func y)) ≤
        (K_a⁻¹ * L_b) * dist (phi_a.func x) (phi_a.func y) := by
  have _ := hL_ne_top
  have _ := hdom_a
  have _ := hdom_b
  intro x hx y hy
  have hbase := hcolip x hx y hy
  have hxy_le :
      dist x y ≤ K_a⁻¹ * dist (phi_a.func x) (phi_a.func y) :=
    (ENNReal.mul_le_iff_le_inv hK_ne_zero hK_ne_top).mp hbase
  calc
    dist (T (phi_a.func x)) (T (phi_a.func y))
        = dist (phi_b.func x) (phi_b.func y) := by rw [hT x hx, hT y hy]
    _ ≤ L_b * dist x y := hL x hx y hy
    _ ≤ L_b * (K_a⁻¹ * dist (phi_a.func x) (phi_a.func y)) :=
        by simpa [mul_comm] using mul_le_mul_right hxy_le L_b
    _ = (K_a⁻¹ * L_b) * dist (phi_a.func x) (phi_a.func y) := by
        ac_rfl

/--
OET anchor: h-6d303a1afa732703
**命题 #h-6d303a1afa732703（像值因子化与标量 Lip 界，双向因子化）**
Two point transforms exist in both directions exactly when the equal-value
pair sets are mutually included.
-/
theorem point_transform_both_directions_iff
    (phi_a phi_b : Operator X bot) (U : Set X)
    (hdom_a : U ⊆ dom phi_a) (hdom_b : U ⊆ dom phi_b) :
    ((∃ T_ab : X → X, ∀ x ∈ U, T_ab (phi_a.func x) = phi_b.func x) ∧
      (∃ T_ba : X → X, ∀ x ∈ U, T_ba (phi_b.func x) = phi_a.func x)) ↔
      EqPairSetLe phi_a phi_b U ∧ EqPairSetLe phi_b phi_a U := by
  have _ := hdom_a
  have _ := hdom_b
  rw [point_transform_exists_iff_eq_pair_set_le,
    point_transform_exists_iff_eq_pair_set_le]

/--
OET anchor: h-c21391963ef67ef0
**命题 #h-c21391963ef67ef0（零距商上的像值因子化，双向包含的逻辑形式）**
Mutual inclusion is equivalent to equality of the zero-distance pair predicates.
-/
theorem zero_dist_pair_set_mutual_iff
    (phi_a phi_b : Operator X bot) (U : Set X) :
    (ZeroDistPairSetLe d phi_a phi_b U ∧ ZeroDistPairSetLe d phi_b phi_a U) ↔
      ∀ x ∈ U, ∀ y ∈ U,
        ((∀ j : I, d j (phi_a.func x) (phi_a.func y) = 0) ↔
          ∀ j : I, d j (phi_b.func x) (phi_b.func y) = 0) := by
  constructor
  · rintro ⟨hab, hba⟩ x hx y hy
    exact ⟨fun hzero => hab x hx y hy hzero,
      fun hzero => hba x hx y hy hzero⟩
  · intro h
    constructor
    · intro x hx y hy hzero
      exact (h x hx y hy).1 hzero
    · intro x hx y hy hzero
      exact (h x hx y hy).2 hzero

/--
OET anchor: h-c21391963ef67ef0
Prescribed quotient transforms in both directions exist exactly when the two
zero-distance pair predicates agree on the common input set.
-/
theorem zero_quotient_transforms_both_directions_iff
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (phi_a phi_b : Operator X bot) (U : Set X) :
    ((∃ T : ZeroImageQuotient d hd phi_a U → ZeroImageQuotient d hd phi_b U,
      ∀ x (hx : x ∈ U),
        T (Quotient.mk (zero_image_setoid d hd phi_a U)
          ⟨phi_a.func x, Set.mem_image_of_mem phi_a.func hx⟩) =
        Quotient.mk (zero_image_setoid d hd phi_b U)
          ⟨phi_b.func x, Set.mem_image_of_mem phi_b.func hx⟩) ∧
      (∃ T : ZeroImageQuotient d hd phi_b U → ZeroImageQuotient d hd phi_a U,
      ∀ x (hx : x ∈ U),
        T (Quotient.mk (zero_image_setoid d hd phi_b U)
          ⟨phi_b.func x, Set.mem_image_of_mem phi_b.func hx⟩) =
        Quotient.mk (zero_image_setoid d hd phi_a U)
          ⟨phi_a.func x, Set.mem_image_of_mem phi_a.func hx⟩)) ↔
      ∀ x ∈ U, ∀ y ∈ U,
        ((∀ j : I, d j (phi_a.func x) (phi_a.func y) = 0) ↔
          ∀ j : I, d j (phi_b.func x) (phi_b.func y) = 0) := by
  rw [zero_quotient_transform_exists_iff, zero_quotient_transform_exists_iff]
  exact zero_dist_pair_set_mutual_iff d phi_a phi_b U

/--
**定义（零测距纤维预序）**
The zero-distance fiber preorder is zero-distance pair-set inclusion.
-/
def zero_dist_fiber_le (phi_a phi_b : Operator X bot) (U : Set X) : Prop :=
  ZeroDistPairSetLe d phi_a phi_b U

/--
**定义（零测距纤维预序）**
The zero-distance fiber preorder is reflexive.
-/
theorem zero_dist_fiber_refl (phi : Operator X bot) (U : Set X) :
    zero_dist_fiber_le d phi phi U := by
  intro x hx y hy hpair_zero
  exact hpair_zero

/--
**定义（零测距纤维预序）**
The zero-distance fiber preorder is transitive.
-/
theorem zero_dist_fiber_trans
    (phi_a phi_b phi_c : Operator X bot) (U : Set X)
    (hab : zero_dist_fiber_le d phi_a phi_b U)
    (hbc : zero_dist_fiber_le d phi_b phi_c U) :
    zero_dist_fiber_le d phi_a phi_c U := by
  intro x hx y hy hpair_zero
  exact hbc x hx y hy (hab x hx y hy hpair_zero)

/--
OET anchor: h-b99ec286d2be8e72
**注 #h-b99ec286d2be8e72（纤维包含的传递）**
Finite chains of zero-distance fiber inclusions compose by transitivity.
-/
theorem zero_dist_fiber_chain_monotone
    (phi : Nat → Operator X bot) (U : Set X) (m : Nat)
    (hstep : ∀ r : Nat, r < m → zero_dist_fiber_le d (phi r) (phi (r + 1)) U) :
    zero_dist_fiber_le d (phi 0) (phi m) U := by
  induction m with
  | zero =>
      exact zero_dist_fiber_refl d (phi 0) U
  | succ m ih =>
      exact zero_dist_fiber_trans d (phi 0) (phi m) (phi (m + 1)) U
        (ih (fun r hr => hstep r (Nat.lt_trans hr (Nat.lt_succ_self m))))
        (hstep m (Nat.lt_succ_self m))

/--
OET anchor: h-b99ec286d2be8e72
**注 #h-b99ec286d2be8e72（纤维包含的传递，任意子链）**
Every interval of a finite monotone fiber chain is monotone.
-/
theorem zero_dist_fiber_subchain_monotone
    (phi : Nat → Operator X bot) (U : Set X) (m a b : Nat)
    (hstep : ∀ r : Nat, r < m → zero_dist_fiber_le d (phi r) (phi (r + 1)) U)
    (hab : a ≤ b) (hbm : b ≤ m) :
    zero_dist_fiber_le d (phi a) (phi b) U := by
  have hchain := zero_dist_fiber_chain_monotone d
    (fun r => phi (a + r)) U (b - a)
    (by
      intro r hr
      simpa [Nat.add_assoc] using hstep (a + r) (by omega))
  simpa [Nat.add_sub_of_le hab] using hchain

/--
OET anchor: h-b99ec286d2be8e72
**注 #h-b99ec286d2be8e72（纤维包含的传递，真包含传播）**
If one step of a finite monotone fiber chain is strict, then the endpoint
inclusion is strict.
-/
theorem zero_dist_fiber_chain_strict_of_strict_step
    (phi : Nat → Operator X bot) (U : Set X) (m r : Nat)
    (hstep : ∀ s : Nat, s < m → zero_dist_fiber_le d (phi s) (phi (s + 1)) U)
    (hr_pos : 1 ≤ r) (hrm : r ≤ m)
    (hstrict :
      zero_dist_fiber_le d (phi (r - 1)) (phi r) U ∧
        ¬ zero_dist_fiber_le d (phi r) (phi (r - 1)) U) :
    zero_dist_fiber_le d (phi 0) (phi m) U ∧
      ¬ zero_dist_fiber_le d (phi m) (phi 0) U := by
  have hfull := zero_dist_fiber_chain_monotone d phi U m hstep
  refine ⟨hfull, ?_⟩
  intro hend_start
  have hstart_before : zero_dist_fiber_le d (phi 0) (phi (r - 1)) U :=
    zero_dist_fiber_subchain_monotone d phi U m 0 (r - 1) hstep
      (Nat.zero_le _) (by omega)
  have hafter_end : zero_dist_fiber_le d (phi r) (phi m) U :=
    zero_dist_fiber_subchain_monotone d phi U m r m hstep hrm le_rfl
  apply hstrict.2
  exact zero_dist_fiber_trans d (phi r) (phi m) (phi (r - 1)) U
    hafter_end
    (zero_dist_fiber_trans d (phi m) (phi 0) (phi (r - 1)) U
      hend_start hstart_before)

end formal_oet.vol_01.ch_03_operator_local_degeneracy
