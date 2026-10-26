import formal_oet.vol_01.ch_04_operator_chain_calculus.decomposition_core


namespace formal_oet.vol_01.ch_04_operator_chain_calculus

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy

open scoped BigOperators

variable {X I M : Type} {bot : X} [Fintype I]
local instance instDecidableEqIPiecewiseSynthesis : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

/--
OET anchor: h-e84832eedce36d68
**定义（定义域分划）**
有限族 `block m` 是 `U` 的分划。
-/
structure DomainPartition (U : Set X) (block : M → Set X) : Prop where
  index_finite : Finite M
  index_nonempty : Nonempty M
  nonempty : ∀ m : M, (block m).Nonempty
  disjoint : ∀ m n : M, m ≠ n → Disjoint (block m) (block n)
  covers : ∀ x : X, x ∈ U ↔ ∃ m : M, x ∈ block m

/--
OET anchor: h-e84832eedce36d68
**定义（分段算子）**
`ψ` 在每个分块 `block m` 上等于局域算子 `local m`，在 `U` 外为 `bot`。
-/
structure PiecewiseOperatorSpec
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (ψ : Operator X bot) : Prop where
  partition : DomainPartition U block
  local_domain : ∀ m : M, block m ⊆ dom (loc m)
  agrees : ∀ m : M, ∀ x ∈ block m, ψ.func x = (loc m).func x
  outside : ∀ x ∉ U, ψ.func x = bot

/-- A nonempty finite partition has a nonempty union. -/
theorem domain_partition_domain_nonempty
    (U : Set X) (block : M → Set X) (h : DomainPartition U block) :
    U.Nonempty := by
  letI : Nonempty M := h.index_nonempty
  let m : M := Classical.choice h.index_nonempty
  rcases h.nonempty m with ⟨x, hx⟩
  exact ⟨x, (h.covers x).mpr ⟨m, hx⟩⟩

/--
OET anchor: h-e84832eedce36d68
**定义（分段算子，实际构造）**
在分划域内选择唯一所属块，并使用该块的局域算子；域外取吸收元。
-/
noncomputable def piecewise_operator
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (hpartition : DomainPartition U block) : Operator X bot := by
  classical
  exact ⟨fun x => if hx : x ∈ U then
    (loc (Classical.choose ((hpartition.covers x).mp hx))).func x else bot, by
      dsimp only
      split
      · exact (loc _).preserves_bot
      · rfl⟩

/-- Disjointness makes the chosen block independent of the membership witness. -/
theorem piecewise_operator_apply_of_mem
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (hpartition : DomainPartition U block) (m : M) {x : X}
    (hx : x ∈ block m) :
    (piecewise_operator U block loc hpartition).func x = (loc m).func x := by
  classical
  have hxU : x ∈ U := (hpartition.covers x).mpr ⟨m, hx⟩
  have hchosen : Classical.choose ((hpartition.covers x).mp hxU) = m := by
    by_contra hne
    exact Set.disjoint_left.mp (hpartition.disjoint _ m hne)
      (Classical.choose_spec ((hpartition.covers x).mp hxU)) hx
  simp only [piecewise_operator, dif_pos hxU, hchosen]

/-- The constructed operator is absorbing outside the partition domain. -/
theorem piecewise_operator_apply_of_not_mem
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (hpartition : DomainPartition U block) {x : X} (hx : x ∉ U) :
    (piecewise_operator U block loc hpartition).func x = bot := by
  classical
  simp only [piecewise_operator, dif_neg hx]

/--
OET anchor: h-e84832eedce36d68
**定义（分段算子的良定义性）**
从分划和各块的局域定义域条件直接得到分段规格，无须预先给出算子。
-/
theorem piecewise_operator_spec
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (hpartition : DomainPartition U block)
    (hlocal : ∀ m : M, block m ⊆ dom (loc m)) :
    PiecewiseOperatorSpec U block loc (piecewise_operator U block loc hpartition) := by
  exact ⟨hpartition, hlocal,
    fun m _ hx => piecewise_operator_apply_of_mem U block loc hpartition m hx,
    fun _ hx => piecewise_operator_apply_of_not_mem U block loc hpartition hx⟩

/-- Block agreement and the exterior value determine the operator uniquely. -/
theorem piecewise_operator_unique
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (hpartition : DomainPartition U block) (ψ : Operator X bot)
    (hψ : PiecewiseOperatorSpec U block loc ψ) :
    ψ = piecewise_operator U block loc hpartition := by
  ext x
  by_cases hxU : x ∈ U
  · obtain ⟨m, hx⟩ := (hpartition.covers x).mp hxU
    rw [hψ.agrees m x hx, piecewise_operator_apply_of_mem U block loc hpartition m hx]
  · rw [hψ.outside x hxU, piecewise_operator_apply_of_not_mem U block loc hpartition hxU]

/-- A valid partition and local domains determine exactly one piecewise operator. -/
theorem exists_unique_piecewise_operator
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (hpartition : DomainPartition U block)
    (hlocal : ∀ m : M, block m ⊆ dom (loc m)) :
    ∃! ψ : Operator X bot, PiecewiseOperatorSpec U block loc ψ := by
  exact ⟨piecewise_operator U block loc hpartition,
    piecewise_operator_spec U block loc hpartition hlocal,
    fun ψ hψ => piecewise_operator_unique U block loc hpartition ψ hψ⟩

/-- The piecewise specification determines the operator domain. -/
theorem piecewise_operator_dom_eq
    (ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (loc : M → Operator X bot)
    (hψ : PiecewiseOperatorSpec U block loc ψ) :
    dom ψ = U := by
  ext x
  constructor
  · intro hx
    by_contra hxU
    exact hx (hψ.outside x hxU)
  · intro hxU
    rcases (hψ.partition.covers x).mp hxU with ⟨m, hxm⟩
    have hloc : (loc m).func x ≠ bot := hψ.local_domain m hxm
    dsimp [dom]
    rw [hψ.agrees m x hxm]
    exact hloc

/-- The actual construction has precisely the prescribed input domain. -/
theorem dom_piecewise_operator
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (hpartition : DomainPartition U block)
    (hlocal : ∀ m : M, block m ⊆ dom (loc m)) :
    dom (piecewise_operator U block loc hpartition) = U :=
  piecewise_operator_dom_eq _ U block loc
    (piecewise_operator_spec U block loc hpartition hlocal)

/-- The infimum of one Lip-matrix entry over all valid matrices. -/
noncomputable def lip_entry_inf
    (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  ⨅ L : I → I → ENNReal, ⨅ _hL : IsLipMatrix d ϕ U L, L i j

/-- The supremum of one co-Lip-matrix entry over all valid matrices. -/
noncomputable def colip_entry_sup
    (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  ⨆ K : I → I → ENNReal, ⨆ _hK : IsCoLipMatrix d ϕ U K, K i j

/--
OET anchor: h-5846008cae9ea67d
**命题 #h-5846008cae9ea67d（分段合成的全域证书比较界，Lip 证书的分块限制）**
全域 Lip 矩阵在每个分块上仍合法。
-/
theorem piecewise_lip_bound_restricts
    (ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (loc : M → Operator X bot) (m : M)
    (L : I → I → ENNReal)
    (hψ : PiecewiseOperatorSpec U block loc ψ)
    (hL : IsLipMatrix d ψ U L) :
    IsLipMatrix d (loc m) (block m) L := by
  exact piecewise_lip_restricts_to_piece d ψ (loc m) U (block m) L
    (fun x hx => (hψ.partition.covers x).mpr ⟨m, hx⟩)
    (fun x hx => hψ.agrees m x hx)
    hL

/--
OET anchor: h-5846008cae9ea67d
**命题 #h-5846008cae9ea67d（分段合成的全域证书比较界，co-Lip 证书的分块限制）**
全域 co-Lip 矩阵在每个非空分块上仍合法。
-/
theorem piecewise_colip_bound_restricts
    (ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (loc : M → Operator X bot) (m : M)
    (K : I → I → ENNReal)
    (hψ : PiecewiseOperatorSpec U block loc ψ)
    (hK : IsCoLipMatrix d ψ U K) :
    IsCoLipMatrix d (loc m) (block m) K := by
  exact piecewise_colip_restricts_to_piece d ψ (loc m) U (block m) K
    (hψ.partition.nonempty m)
    (fun x hx => (hψ.partition.covers x).mpr ⟨m, hx⟩)
    (fun x hx => hψ.agrees m x hx)
    hK

/--
OET anchor: h-5846008cae9ea67d
**命题 #h-5846008cae9ea67d（分段合成的全域证书比较界，全域 Lip 条目的下界）**
Every global Lip entry dominates the largest local entrywise infimum.
-/
theorem piecewise_global_lip_entry_lower_bound
    (ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (loc : M → Operator X bot) (L : I → I → ENNReal)
    (i j : I) (hψ : PiecewiseOperatorSpec U block loc ψ)
    (hL : IsLipMatrix d ψ U L) :
    (⨆ m : M, lip_entry_inf d (loc m) (block m) i j) ≤ L i j := by
  apply iSup_le
  intro m
  exact iInf_le_of_le L
    (iInf_le_of_le (piecewise_lip_bound_restricts d ψ U block loc m L hψ hL) le_rfl)

/--
OET anchor: h-5846008cae9ea67d
**命题 #h-5846008cae9ea67d（分段合成的全域证书比较界，全域 Lip 条目下确界的下界）**
The global entrywise infimum dominates the largest local entrywise infimum.
-/
theorem piecewise_global_lip_inf_lower_bound
    (ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (loc : M → Operator X bot) (i j : I)
    (hψ : PiecewiseOperatorSpec U block loc ψ) :
    (⨆ m : M, lip_entry_inf d (loc m) (block m) i j) ≤
      lip_entry_inf d ψ U i j := by
  unfold lip_entry_inf
  apply le_iInf
  intro L
  apply le_iInf
  intro hL
  exact piecewise_global_lip_entry_lower_bound d ψ U block loc L i j hψ hL

/--
OET anchor: h-5846008cae9ea67d
**命题 #h-5846008cae9ea67d（分段合成的全域证书比较界，全域 co-Lip 条目的上界）**
Every global co-Lip entry is bounded by the smallest local entrywise supremum.
-/
theorem piecewise_global_colip_entry_upper_bound
    (ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (loc : M → Operator X bot) (K : I → I → ENNReal)
    (i j : I) (hψ : PiecewiseOperatorSpec U block loc ψ)
    (hK : IsCoLipMatrix d ψ U K) :
    K i j ≤ (⨅ m : M, colip_entry_sup d (loc m) (block m) i j) := by
  apply le_iInf
  intro m
  exact le_iSup_of_le K
    (le_iSup_of_le (piecewise_colip_bound_restricts d ψ U block loc m K hψ hK) le_rfl)

/--
OET anchor: h-5846008cae9ea67d
**命题 #h-5846008cae9ea67d（分段合成的全域证书比较界，全域 co-Lip 条目上确界的上界）**
The global entrywise supremum is bounded by the smallest local entrywise supremum.
-/
theorem piecewise_global_colip_sup_upper_bound
    (ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (loc : M → Operator X bot) (i j : I)
    (hψ : PiecewiseOperatorSpec U block loc ψ) :
    colip_entry_sup d ψ U i j ≤
      (⨅ m : M, colip_entry_sup d (loc m) (block m) i j) := by
  unfold colip_entry_sup
  apply iSup_le
  intro K
  apply iSup_le
  intro hK
  exact piecewise_global_colip_entry_upper_bound d ψ U block loc K i j hψ hK

/--
OET anchor: h-5846008cae9ea67d
**命题 #h-5846008cae9ea67d（分段合成的全域证书比较界，跨分区识别下的 co-Lip 归零）**
A positive source distance identified by two different pieces forces the global
co-Lip entrywise supremum to zero.
-/
theorem piecewise_colip_sup_eq_zero_of_cross_identification
    (ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (loc : M → Operator X bot) (m n : M) (i j : I)
    (x y : X) (hψ : PiecewiseOperatorSpec U block loc ψ)
    (hmn : m ≠ n) (hx : x ∈ block m) (hy : y ∈ block n)
    (hd_pos : 0 < d i x y)
    (hzero : d j ((loc m).func x) ((loc n).func y) = 0) :
    colip_entry_sup d ψ U i j = 0 := by
  have _ := hmn
  apply le_antisymm
  · unfold colip_entry_sup
    apply iSup_le
    intro K
    apply iSup_le
    intro hK
    have hxU : x ∈ U := (hψ.partition.covers x).mpr ⟨m, hx⟩
    have hyU : y ∈ U := (hψ.partition.covers y).mpr ⟨n, hy⟩
    have hterm : K i j * d i x y ≤ ∑ l : I, K l j * d l x y :=
      Finset.single_le_sum
        (fun l _ => zero_le (K l j * d l x y)) (Finset.mem_univ i)
    have hsum : (∑ l : I, K l j * d l x y) ≤ 0 := by
      have hbound := hK.2.2 x hxU y hyU j
      rw [hψ.agrees m x hx, hψ.agrees n y hy, hzero] at hbound
      exact hbound
    have hmul : K i j * d i x y = 0 := le_antisymm (le_trans hterm hsum) (zero_le _)
    exact le_of_eq ((mul_eq_zero.mp hmul).resolve_right (ne_of_gt hd_pos))
  · exact zero_le _

/--
OET anchor: h-5846008cae9ea67d
**命题（分段合成的全域 Lip 比较界，从原始分划数据出发）**
同时给出实际构造的全域条目下确界及每个合法证书的下界。
-/
theorem constructed_piecewise_lip_comparison
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (hpartition : DomainPartition U block)
    (hlocal : ∀ m : M, block m ⊆ dom (loc m)) (i j : I) :
    (⨆ m : M, lip_entry_inf d (loc m) (block m) i j) ≤
        lip_entry_inf d (piecewise_operator U block loc hpartition) U i j ∧
      ∀ L : I → I → ENNReal,
        IsLipMatrix d (piecewise_operator U block loc hpartition) U L →
        (⨆ m : M, lip_entry_inf d (loc m) (block m) i j) ≤ L i j := by
  have hψ := piecewise_operator_spec U block loc hpartition hlocal
  exact ⟨piecewise_global_lip_inf_lower_bound d _ U block loc i j hψ,
    fun L hL => piecewise_global_lip_entry_lower_bound d _ U block loc L i j hψ hL⟩

/--
OET anchor: h-5846008cae9ea67d
**命题（分段合成的全域 co-Lip 比较界，从原始分划数据出发）**
同时给出实际构造的全域条目上确界及每个合法证书的上界。
-/
theorem constructed_piecewise_colip_comparison
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (hpartition : DomainPartition U block)
    (hlocal : ∀ m : M, block m ⊆ dom (loc m)) (i j : I) :
    colip_entry_sup d (piecewise_operator U block loc hpartition) U i j ≤
        (⨅ m : M, colip_entry_sup d (loc m) (block m) i j) ∧
      ∀ K : I → I → ENNReal,
        IsCoLipMatrix d (piecewise_operator U block loc hpartition) U K →
        K i j ≤ (⨅ m : M, colip_entry_sup d (loc m) (block m) i j) := by
  have hψ := piecewise_operator_spec U block loc hpartition hlocal
  exact ⟨piecewise_global_colip_sup_upper_bound d _ U block loc i j hψ,
    fun K hK => piecewise_global_colip_entry_upper_bound d _ U block loc K i j hψ hK⟩

/--
OET anchor: h-5846008cae9ea67d
**命题（跨分区识别下的 co-Lip 归零，从原始分划数据出发）**
不同块的局域输出零距而输入正距，迫使实际分段算子的该条目归零。
-/
theorem constructed_piecewise_colip_sup_eq_zero
    (U : Set X) (block : M → Set X) (loc : M → Operator X bot)
    (hpartition : DomainPartition U block)
    (hlocal : ∀ m : M, block m ⊆ dom (loc m))
    (m n : M) (i j : I) (x y : X)
    (hmn : m ≠ n) (hx : x ∈ block m) (hy : y ∈ block n)
    (hd_pos : 0 < d i x y)
    (hzero : d j ((loc m).func x) ((loc n).func y) = 0) :
    colip_entry_sup d (piecewise_operator U block loc hpartition) U i j = 0 :=
  piecewise_colip_sup_eq_zero_of_cross_identification d _ U block loc m n i j x y
    (piecewise_operator_spec U block loc hpartition hlocal) hmn hx hy hd_pos hzero

/--
**注（分区内继承）**
分区内，分段算子的 L/K 矩阵继承局域算子。
-/
theorem piecewise_interior_matrix_inheritance
    (ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (loc : M → Operator X bot) (m : M)
    (hψ : PiecewiseOperatorSpec U block loc ψ) :
    LocalEquivalent ψ (loc m) (block m) := by
  intro x hx
  exact hψ.agrees m x hx

/-- Internal domain and pointwise agreement for the synthesis of restrictions. -/
theorem piecewise_restricted_operator_domain_synthesis
    (ϕ ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (hU : U ⊆ dom ϕ)
    (hψ : PiecewiseOperatorSpec U block
      (fun m : M => restrict_operator ϕ (block m)) ψ) :
    DomainSynthesis ψ ϕ U := by
  refine ⟨?_, piecewise_operator_dom_eq ψ U block
    (fun m : M => restrict_operator ϕ (block m)) hψ, hU⟩
  intro x hx
  rcases (hψ.partition.covers x).mp hx with ⟨m, hxm⟩
  rw [hψ.agrees m x hxm, restrict_operator_apply_of_mem ϕ (block m) hxm]

/--
OET anchor: h-b4f65e22f18fce79
**推论 #h-b4f65e22f18fce79（域分解与合成恒等式）**
拼接同一算子在分划各块上的限制，恰好得到该算子在整个分划域上的限制。
-/
theorem piecewise_restricted_operator_eq_restrict
    (ϕ ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (hU : U ⊆ dom ϕ)
    (hψ : PiecewiseOperatorSpec U block
      (fun m : M => restrict_operator ϕ (block m)) ψ) :
    ψ = restrict_operator ϕ U := by
  have h_syn := piecewise_restricted_operator_domain_synthesis ϕ ψ U block hU hψ
  ext x
  by_cases hx : x ∈ U
  · rw [restrict_operator_apply_of_mem ϕ U hx]
    exact h_syn.1 x hx
  · rw [hψ.outside x hx, restrict_operator_apply_of_not_mem ϕ U hx]

/--
OET anchor: h-b4f65e22f18fce79
**推论 #h-b4f65e22f18fce79（域分解与合成恒等式）**
For the actual piecewise synthesis of the restrictions of `ϕ`, equality in the
operator monoid holds exactly when the synthesis domain is the full domain.
-/
theorem piecewise_restricted_operator_eq_iff
    (ϕ ψ : Operator X bot) (U : Set X) (block : M → Set X)
    (hU : U ⊆ dom ϕ)
    (hψ : PiecewiseOperatorSpec U block
      (fun m : M => restrict_operator ϕ (block m)) ψ) :
    ψ = ϕ ↔ U = dom ϕ :=
  domain_synthesis_eq_iff ψ ϕ U
    (piecewise_restricted_operator_domain_synthesis ϕ ψ U block hU hψ)

/-- The restrictions to partition blocks satisfy the required local domains. -/
theorem partition_restrictions_local_domain
    (ϕ : Operator X bot) (U : Set X) (block : M → Set X)
    (hpartition : DomainPartition U block) (hU : U ⊆ dom ϕ) :
    ∀ m : M, block m ⊆ dom (restrict_operator ϕ (block m)) := by
  intro m
  have hm : block m ⊆ dom ϕ :=
    fun x hx => hU ((hpartition.covers x).mpr ⟨m, hx⟩)
  rw [dom_restrict_operator_eq ϕ (block m) hm]

/--
OET anchor: h-b4f65e22f18fce79
**推论（域分解与合成恒等式，从原始分划数据出发）**
直接构造各块限制的分段算子，得到整个分划域上的限制。
-/
theorem constructed_piecewise_restrictions_eq_restrict
    (ϕ : Operator X bot) (U : Set X) (block : M → Set X)
    (hpartition : DomainPartition U block) (hU : U ⊆ dom ϕ) :
    piecewise_operator U block (fun m => restrict_operator ϕ (block m)) hpartition =
      restrict_operator ϕ U :=
  piecewise_restricted_operator_eq_restrict ϕ _ U block hU
    (piecewise_operator_spec U block _ hpartition
      (partition_restrictions_local_domain ϕ U block hpartition hU))

/--
OET anchor: h-b4f65e22f18fce79
**推论（域分解与合成恒等式，原算子的恢复条件）**
实际合成恢复原算子，当且仅当分划域是原算子的整个定义域。
-/
theorem constructed_piecewise_restrictions_eq_iff
    (ϕ : Operator X bot) (U : Set X) (block : M → Set X)
    (hpartition : DomainPartition U block) (hU : U ⊆ dom ϕ) :
    piecewise_operator U block (fun m => restrict_operator ϕ (block m)) hpartition = ϕ ↔
      U = dom ϕ :=
  piecewise_restricted_operator_eq_iff ϕ _ U block hU
    (piecewise_operator_spec U block _ hpartition
      (partition_restrictions_local_domain ϕ U block hpartition hU))

end

end formal_oet.vol_01.ch_04_operator_chain_calculus
