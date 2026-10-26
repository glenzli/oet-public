import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/--
Source: vol-01-gauge-spaces-and-operators/02-operator-bounds.md,
分量通道（正文中的单输入分量上界说明）.
A scalar Lip bound on the restricted domain, from input component `i` to output component `j`.
-/
def HasScalarLipBound (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i j : I) (c : ENNReal) : Prop :=
  U ⊆ dom ϕ ∧
    ∀ x ∈ U, ∀ y ∈ U,
      d j (ϕ.func x) (ϕ.func y) ≤ c * d i x y

end formal_oet.vol_01.ch_02_operator_bounds
