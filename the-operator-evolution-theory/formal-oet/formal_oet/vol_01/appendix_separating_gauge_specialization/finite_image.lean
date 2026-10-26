import formal_oet.vol_01.appendix_separating_gauge_specialization.full_gauge
import formal_oet.vol_01.ch_03_operator_local_degeneracy.annihilation_matrix
import Mathlib.Data.Set.Card

namespace formal_oet.vol_01.appendix_separating_gauge_specialization

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]
variable (d : I → X → X → ENNReal)

/-- OET anchor: h-f2de1cf0247fd557 推论（统一零化半径与有限像）的点对证明步骤。
严格低于统一全输出零化半径的点对具有相同像值；不要求半径上确界取到。 -/
theorem equal_of_lt_uniform_full_output_radius
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X) (r : ENNReal)
    (hradius : r ≤ metric_min_annihilation_radius
      (full_gauge_dist d) (full_gauge_dist d) φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hxy : full_gauge_dist d x y < r) : φ.func x = φ.func y := by
  have hmin : metric_min_annihilation_radius
      (full_gauge_dist d) (full_gauge_dist d) φ U ≤
      metric_annihilation_radius (full_gauge_dist d) (full_gauge_dist d) φ U y := by
    exact iInf_le_of_le y (iInf_le_of_le hy le_rfl)
  have hzero := output_zero_of_lt_metric_annihilation_radius
    (full_gauge_dist d) (full_gauge_dist d) φ U x y hx
    (lt_of_lt_of_le hxy (hradius.trans hmin))
  have hall := (comp_pseudo_metric_eq_zero_iff d
    (full_nonempty_finset : NonemptyFinset I) (φ.func x) (φ.func y)).mp hzero
  exact hsep (φ.func x) (φ.func y) (fun i => hall i (Finset.mem_univ i))

/-- 有限开球内覆盖在统一全输出零化条件下精确覆盖所有像值。 -/
theorem image_eq_image_of_uniform_full_output_radius
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X) (r : ENNReal)
    (hradius : r ≤ metric_min_annihilation_radius
      (full_gauge_dist d) (full_gauge_dist d) φ U)
    (S : Finset X) (hS : InternalEpsilonNet (full_gauge_dist d) r U S) :
    φ.func '' U = φ.func '' (S : Set X) := by
  apply Set.Subset.antisymm
  · rintro z ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := hS.2 x hx
    refine ⟨s, hs, ?_⟩
    exact (equal_of_lt_uniform_full_output_radius d hsep φ U r hradius
      hx (hS.1 hs) hxs).symm
  · exact Set.image_mono hS.1

/--
OET anchor: h-f2de1cf0247fd557 推论（统一零化半径与有限像）。
有限覆盖中心的像等于整个像，故像有限且其点数不超过中心数。
-/
theorem finite_image_of_uniform_full_output_radius
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X)
    (hU : U.Nonempty) (hdom : U ⊆ dom φ) (r : ENNReal)
    (hr : FinitePositiveRadius r)
    (hradius : r ≤ metric_min_annihilation_radius
      (full_gauge_dist d) (full_gauge_dist d) φ U)
    (S : Finset X) (hS : InternalEpsilonNet (full_gauge_dist d) r U S) :
    φ.func '' U = φ.func '' (S : Set X) ∧
      (φ.func '' U).Finite ∧ (φ.func '' U).ncard ≤ S.card := by
  -- These retain the textbook's domain and finite-positive-radius conventions.
  have _ := hU
  have _ := hdom
  have _ := hr
  have heq := image_eq_image_of_uniform_full_output_radius d hsep φ U r hradius S hS
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    exact S.finite_toSet.image φ.func
  · rw [heq]
    simpa using (Set.ncard_image_le (s := (S : Set X)) (f := φ.func) S.finite_toSet)

/--
OET anchor: h-f2de1cf0247fd557 推论（统一零化半径与有限像）的覆盖数界。
覆盖数有限时，选择最小有限内覆盖，得到像点数不超过输入覆盖数。
-/
theorem finite_image_card_le_covering_number
    (hsep : IsSeparating d) (φ : Operator X bot) (U : Set X)
    (hU : U.Nonempty) (hdom : U ⊆ dom φ) (r : ENNReal)
    (hr : FinitePositiveRadius r)
    (hradius : r ≤ metric_min_annihilation_radius
      (full_gauge_dist d) (full_gauge_dist d) φ U)
    (hfinite : covering_number (full_gauge_dist d) r U < ⊤) :
    (φ.func '' U).Finite ∧
      ((φ.func '' U).ncard : ENNReal) ≤ covering_number (full_gauge_dist d) r U := by
  have hex : ∃ S : Finset X, InternalEpsilonNet (full_gauge_dist d) r U S := by
    by_contra hn
    exact (ne_of_lt hfinite)
      ((covering_number_eq_top_iff (full_gauge_dist d) r U).mpr hn)
  obtain ⟨S, hS, hcard, _⟩ := covering_number_attained (full_gauge_dist d) r U hex
  obtain ⟨_, himage, hbound⟩ :=
    finite_image_of_uniform_full_output_radius d hsep φ U hU hdom r hr hradius S hS
  refine ⟨himage, ?_⟩
  rw [hcard]
  exact_mod_cast hbound

end

end formal_oet.vol_01.appendix_separating_gauge_specialization
