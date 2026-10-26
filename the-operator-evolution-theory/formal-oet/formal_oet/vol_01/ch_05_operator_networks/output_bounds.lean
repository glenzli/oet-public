import formal_oet.vol_01.ch_05_operator_networks.path_matrix
import formal_oet.vol_01.ch_03_operator_local_degeneracy.mapping_entropy


namespace formal_oet.vol_01.ch_05_operator_networks

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy

open scoped BigOperators

variable {X V I : Type} {bot : X}
variable [Fintype I]
local instance instDecidableEqIOutputBounds : DecidableEq I := Classical.decEq I
variable (d : I → X → X → ENNReal)

namespace FiniteOperatorNetwork

variable (N : FiniteOperatorNetwork X bot V)

/--
OET anchor: h-4b1389b158d2780e
**定义（路径输出片）**
一条可达路径域经过网络外延算子后的输出像集。
-/
def path_output_set (p : N.ReachablePath) : Set X :=
  N.extensional_operator.func '' N.path_domain p.nodes

set_option linter.unusedFintypeInType false in
/--
OET anchor: h-13da76fc7723fdef
**命题 #h-13da76fc7723fdef（输出覆盖数的路径分解上界，输出覆盖）**
网络输出像集被所有可达路径输出像集覆盖。
-/
theorem network_output_eq_iunion_path_outputs :
    N.extensional_operator.func '' N.U =
      (⋃ p : N.ReachablePath, N.path_output_set p) := by
  apply Set.Subset.antisymm
  · intro z hz
    rcases hz with ⟨x, hxU, rfl⟩
    let p : N.ReachablePath :=
      ⟨N.path_of ⟨x, hxU⟩, ⟨x, hxU, rfl⟩⟩
    exact Set.mem_iUnion.mpr
      ⟨p, x, ⟨hxU, rfl⟩, rfl⟩
  · intro z hz
    rcases Set.mem_iUnion.mp hz with ⟨p, x, hxPath, rfl⟩
    exact ⟨x, N.path_domain_subset_source hxPath, rfl⟩

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-13da76fc7723fdef
**命题 #h-13da76fc7723fdef（输出覆盖数的路径分解上界，覆盖数上界）**
在可达路径有限时，网络输出覆盖数由各路径输出覆盖数之和控制。
-/
theorem network_output_cover_bound (j : I) (ε : ENNReal) :
    cov_num d j ε (N.extensional_operator.func '' N.U) ≤
      ∑ p : N.ReachablePath, cov_num d j ε (N.path_output_set p) := by
  rw [N.network_output_eq_iunion_path_outputs]
  simpa [cov_num] using
    covering_number_i_union_finite_le (d j) ε
      (fun p : N.ReachablePath => N.path_output_set p)

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-13da76fc7723fdef
**命题 #h-13da76fc7723fdef（输出覆盖数的路径分解上界，路径输出标量 Lip 覆盖数变换）**
路径链在单分量上有有限正标量 Lip 上界时，路径输出覆盖数可拉回
路径域。
-/
theorem path_scalar_lip_cov_num_bound (φ : Operator X bot)
    (U : Set X) (j : I) (L ε : ENNReal)
    (hLip : HasScalarLipBound d φ U j j L)
    (hpos : 0 < L) (hne_top : L ≠ ⊤) :
    cov_num d j ε (φ.func '' U) ≤
      cov_num d j (ε / L) U := by
  have hcov :=
    lip_cov_num_bound_aux d φ U j j L (ε / L) hLip hpos hne_top
  have hmul : L * (ε / L) = ε :=
    ENNReal.mul_div_cancel'
      (fun h => False.elim ((ne_of_gt hpos) h))
      (fun h => False.elim (hne_top h))
  simpa [hmul] using hcov

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/--
OET anchor: h-13da76fc7723fdef
**命题 #h-13da76fc7723fdef（输出覆盖数的路径分解上界，零 Lip 路径输出项）**
若路径输出像在目标分量上直径为零，则任意正半径覆盖项至多为一。
-/
theorem zero_diameter_path_cov_num_le_one
    (A : Set X) (j : I) (ε : ENNReal)
    (hε : 0 < ε)
    (hzero : ∀ x ∈ A, ∀ y ∈ A, d j x y = 0) :
    cov_num d j ε A ≤ 1 := by
  classical
  by_cases hA : A.Nonempty
  · rcases hA with ⟨a, ha⟩
    have hnet : InternalEpsilonNet (d j) ε A {a} := by
      refine ⟨?_, ?_⟩
      · intro x hx
        have hxa : x = a := by simpa using hx
        simpa [hxa] using ha
      · intro x hx
        refine ⟨a, by simp, ?_⟩
        simpa [hzero x hx a ha] using hε
    calc
      cov_num d j ε A ≤ (({a} : Finset X).card : ENNReal) := by
        exact iInf_le_of_le {a} (iInf_le_of_le hnet le_rfl)
      _ = 1 := by simp
  · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A
    have hnet : InternalEpsilonNet (d j) ε (∅ : Set X) ∅ := by
      simp [InternalEpsilonNet]
    calc
      cov_num d j ε (∅ : Set X) ≤ ((∅ : Finset X).card : ENNReal) := by
        exact iInf_le_of_le ∅ (iInf_le_of_le hnet le_rfl)
      _ ≤ 1 := by simp

set_option linter.unusedFintypeInType false in
/--
OET anchor: h-13da76fc7723fdef
**命题 #h-13da76fc7723fdef（输出覆盖数的路径分解上界）**

正文两层结论的最终包装：先对全部可达路径求和，再把任一具有有限正标量 Lip
证书的路径输出项拉回其路径域。
-/
theorem network_output_path_decomposition_bound_textbook
    (j : I) (ε : ENNReal) (hε : 0 < ε) (hε_top : ε ≠ ⊤) :
    cov_num d j ε (N.extensional_operator.func '' N.U) ≤
        ∑ p : N.ReachablePath, cov_num d j ε (N.path_output_set p) ∧
      ∀ p : N.ReachablePath, ∀ L : ENNReal, 0 < L → L ≠ ⊤ →
        HasScalarLipBound d N.extensional_operator (N.path_domain p.nodes) j j L →
        cov_num d j ε (N.path_output_set p) ≤
          cov_num d j (ε / L) (N.path_domain p.nodes) := by
  have _ := hε
  have _ := hε_top
  constructor
  · exact N.network_output_cover_bound d j ε
  · intro p L hL hL_top hLip
    exact path_scalar_lip_cov_num_bound d N.extensional_operator
      (N.path_domain p.nodes) j L ε hLip hL hL_top

end FiniteOperatorNetwork

end

end formal_oet.vol_01.ch_05_operator_networks
