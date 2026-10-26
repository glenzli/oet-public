import formal_oet.vol_01.ch_05_operator_networks.network_extensional_space

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations

universe u v w

variable {X : Type} {bot : X}

/--
OET anchor: h-f4f084a4606187ed
**定义（网络读出映射）**
A network profile is a selected readout from network objects to a value space.
-/
structure NetworkProfile (Net : Sort u) (P : Sort v) where
  read : Net → P

/--
OET path: vol-01-gauge-spaces-and-operators/05-operator-networks.md
**定义（网络读出映射）**
A parametrized profile records the readout parameter explicitly.
-/
structure ParametrizedNetworkProfile (Net : Sort u) (Param : Sort v) (P : Sort w) where
  read : Param → Net → P

/--
OET anchor: h-f4f084a4606187ed
**定义（规范网络读出）**
A gauge profile equips its value space with a finite family of extended
pseudometrics. The distance axioms are part of the definition; the readout
value space need not carry a distinguished absorbing point.
-/
structure GaugeNetworkProfile (Net : Sort u) (P : Sort v) (A : Type w)
    extends NetworkProfile Net P where
  dist : A → P → P → ENNReal
  finite_index : Fintype A
  dist_self : ∀ a p, dist a p p = 0
  dist_symm : ∀ a p q, dist a p q = dist a q p
  dist_triangle : ∀ a p q r, dist a p r ≤ dist a p q + dist a q r

/--
OET anchor: h-f4f084a4606187ed
**定义（算子读出映射）**
The operator readout is the basic network profile with value space
`X_op`.
-/
noncomputable def operator_profile :
    NetworkProfile (NetworkObject X bot) (Operator X bot) where
  read := NetworkObject.extensional_operator

/--
OET anchor: h-f4f084a4606187ed
**定义（外延不变读出）**
A profile is extensional-invariant when it is constant on operator-readout
fibers.
-/
def ExtensionalInvariantProfile
    {P : Sort v} (profile : NetworkProfile (NetworkObject X bot) P) : Prop :=
  ∀ N M : NetworkObject X bot,
    (operator_profile (X := X) (bot := bot)).read N =
      (operator_profile (X := X) (bot := bot)).read M →
    profile.read N = profile.read M

/--
OET anchor: h-f4f084a4606187ed
**定义（外延不变读出）**
The operator profile is extensional-invariant by definition.
-/
theorem operator_profile_extensional_invariant :
    ExtensionalInvariantProfile (operator_profile (X := X) (bot := bot)) := by
  intro N M h
  exact h

/--
OET anchor: h-f4f084a4606187ed
Restrict an existing readout to a subset of its domain. This operation is
separate from a readout originally defined only on that subset.
-/
def NetworkProfile.restrict {Net : Type u} {P : Sort v}
    (profile : NetworkProfile Net P) (A : Set Net) : NetworkProfile A P where
  read := fun N => profile.read N.val

/--
OET anchor: h-f4f084a4606187ed
**定义（子集上定义的外延不变读出）**
A profile defined only on A is constant on the operator-readout fibers inside A.
No value or extension outside A is required, and P need not be nonempty.
-/
def ExtensionalInvariantSubprofile
    {A : Set (NetworkObject X bot)} {P : Sort v}
    (profile : NetworkProfile A P) : Prop :=
  ∀ N M : A, N.val.extensional_operator = M.val.extensional_operator →
    profile.read N = profile.read M

/--
OET anchor: h-f4f084a4606187ed
**定义（对象子集上的外延不变读出）**
A readout is extensional-invariant on the specified collection of network
objects; no constancy outside that collection is required.
-/
def ExtensionalInvariantProfileOn
    {P : Sort v} (profile : NetworkProfile (NetworkObject X bot) P)
    (A : Set (NetworkObject X bot)) : Prop :=
  ∀ N ∈ A, ∀ M ∈ A,
    N.extensional_operator = M.extensional_operator → profile.read N = profile.read M

/--
OET anchor: h-f4f084a4606187ed
For a readout obtained by restricting a total profile, the subset-domain
formulation agrees exactly with the original on-subset API.
-/
theorem extensional_invariant_subprofile_restrict_iff_on
    {P : Sort v} (profile : NetworkProfile (NetworkObject X bot) P)
    (A : Set (NetworkObject X bot)) :
    ExtensionalInvariantSubprofile (profile.restrict A) ↔
      ExtensionalInvariantProfileOn profile A := by
  constructor
  · intro h N hN M hM heq
    exact h ⟨N, hN⟩ ⟨M, hM⟩ heq
  · intro h N M heq
    exact h N.val N.property M.val M.property heq

/-- The global definition is exactly the special case of the full object space. -/
theorem extensional_invariant_profile_iff_on_univ
    {P : Sort v} (profile : NetworkProfile (NetworkObject X bot) P) :
    ExtensionalInvariantProfile profile ↔ ExtensionalInvariantProfileOn profile Set.univ := by
  constructor
  · intro h N _ M _ heq
    exact h N M heq
  · intro h N M heq
    exact h N (Set.mem_univ N) M (Set.mem_univ M) heq

/-- Restricting the collection preserves extensional invariance. -/
theorem extensional_invariant_profile_on_mono
    {P : Sort v} {profile : NetworkProfile (NetworkObject X bot) P}
    {A B : Set (NetworkObject X bot)} (hAB : A ⊆ B)
    (h : ExtensionalInvariantProfileOn profile B) :
    ExtensionalInvariantProfileOn profile A := by
  intro N hN M hM heq
  exact h N (hAB hN) M (hAB hM) heq

end formal_oet.vol_01.ch_05_operator_networks
