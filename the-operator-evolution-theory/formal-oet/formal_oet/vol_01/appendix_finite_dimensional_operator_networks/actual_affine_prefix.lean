import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.actual_affine_geometry
import formal_oet.vol_01.appendix_finite_dimensional_operator_networks.cover_and_morphology

namespace formal_oet.vol_01.appendix_finite_dimensional_operator_networks
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_01.ch_05_operator_networks.FiniteOperatorNetwork
open formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
noncomputable section
attribute [local instance] Classical.propDecidable
variable {n : ℕ} [NeZero n]

/--
Compatibility helper: the zero radius and threshold classification of an affine last-node
operator on its actual open occurrence domain. `hQ` identifies that domain in
coordinates; it is not an ambient cover or a prefix-composite domain.
-/
theorem actual_affine_prefix_radius_readout {V : Type}
    (N : FiniteOperatorNetwork (CoordinatePoint n Set.univ) none V) (q : N.PrefixOccurrence)
    (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n) (b : CoordinateVector n)
    (Q : Set (CoordinateVector n))
    (hQ : prefix_occurrence_input_domain N q = coordinate_model_set Set.univ Q)
    (ho : IsOpen Q)
    (hF : ∀ x ∈ Q, (prefix_occurrence_local_operator N q).func (full_coordinate_point x) =
      full_coordinate_point (coordinate_affine_map T b x))
    (σ : ScaleFamily (CoordinatePoint n Set.univ) (Fin n))
    (τs τr : ENNReal) (hτr : 0 < τr) (i j : Fin n) :
    prefix_zero_radius coordinate_dist N q i j = (if coordinate_linear_row T j = 0 then ⊤ else 0) ∧
    prefix_threshold_readout coordinate_dist N σ τs τr q i j =
      (decide (σ i (prefix_occurrence_input_domain N q) < τs),
        decide (coordinate_linear_row T j = 0)) := by
  classical
  have hn : Q.Nonempty := by
    obtain ⟨x, hx⟩ := prefix_occurrence_input_domain_nonempty N q
    rw [hQ] at hx
    rcases hx with ⟨a, ha, _⟩
    exact ⟨a.val, ha⟩
  have hr : prefix_zero_radius coordinate_dist N q i j =
      if coordinate_linear_row T j = 0 then ⊤ else 0 := by
    unfold prefix_zero_radius
    rw [hQ]
    exact affine_min_radius_on_open_set _ T b Q hn ho hF i j
  refine ⟨hr, ?_⟩
  change (decide (σ i (prefix_occurrence_input_domain N q) < τs),
    decide (τr ≤ prefix_zero_radius coordinate_dist N q i j)) = _
  rw [hr]
  by_cases hrow : coordinate_linear_row T j = 0 <;> simp [hrow, not_le.mpr hτr]

/-- OET anchor: h-e4b8f2d657424bba
The last-node affine map is restricted to the actual nonempty convex occurrence
domain. Its row vanishes on the available directions exactly in the infinite
radius case, including occurrences with empty ambient interior. -/
theorem actual_affine_prefix_convex_radius_readout {V : Type}
    (N : FiniteOperatorNetwork (CoordinatePoint n Set.univ) none V) (q : N.PrefixOccurrence)
    (T : CoordinateVector n →ₗ[ℝ] CoordinateVector n) (b : CoordinateVector n)
    (Q : Set (CoordinateVector n))
    (hQ : prefix_occurrence_input_domain N q = coordinate_model_set Set.univ Q)
    (hconv : Convex ℝ Q)
    (hF : ∀ x ∈ Q, (prefix_occurrence_local_operator N q).func (full_coordinate_point x) =
      full_coordinate_point (coordinate_affine_map T b x))
    (σ : ScaleFamily (CoordinatePoint n Set.univ) (Fin n))
    (τs τr : ENNReal) (hτr : 0 < τr) (i j : Fin n) :
    prefix_zero_radius coordinate_dist N q i j = (if (coordinate_linear_row T j).domRestrict (direction_span Q) = 0 then ⊤ else 0) ∧
    prefix_threshold_readout coordinate_dist N σ τs τr q i j =
      (decide (σ i (prefix_occurrence_input_domain N q) < τs),
        decide ((coordinate_linear_row T j).domRestrict (direction_span Q) = 0)) := by
  classical
  have hn : Q.Nonempty := by
    obtain ⟨x, hx⟩ := prefix_occurrence_input_domain_nonempty N q
    rw [hQ] at hx
    rcases hx with ⟨a, ha, _⟩
    exact ⟨a.val, ha⟩
  have hr : prefix_zero_radius coordinate_dist N q i j =
      if (coordinate_linear_row T j).domRestrict (direction_span Q) = 0 then ⊤ else 0 := by
    unfold prefix_zero_radius
    rw [hQ]
    exact affine_min_radius_on_convex_set _ T b Q hn hconv hF i j
  refine ⟨hr, ?_⟩
  change (decide (σ i (prefix_occurrence_input_domain N q) < τs),
    decide (τr ≤ prefix_zero_radius coordinate_dist N q i j)) = _
  rw [hr]
  by_cases hrow : (coordinate_linear_row T j).domRestrict (direction_span Q) = 0 <;> simp [hrow, not_le.mpr hτr]

/-- OET anchor: h-e4b8f2d657424bba
This bridge derives the actual-domain identification, convexity and local affine
formula from the network data. The threshold readout is written `\operatorname{Type}_q(i,j)`
in the text. None is a separately assumed radius conclusion. -/
theorem actual_affine_prefix_direction_readout {V : Type}
    (N : FiniteOperatorNetwork (CoordinatePoint n Set.univ) none V)
    (F : V → CoordinateVector n →ᵃ[ℝ] CoordinateVector n)
    (hF : AffineNodeRealization N F)
    (hentry : ∀ v, IsAffineCell (real_locus (N.entry_domain v)))
    (hedge : ∀ v w, IsAffineCell (real_locus (N.edge_domain v w)))
    (q : N.PrefixOccurrence)
    (σ : ScaleFamily (CoordinatePoint n Set.univ) (Fin n))
    (τs τr : ENNReal) (hτr : 0 < τr) (i j : Fin n) :
    let D := real_locus (N.prefix_input_domain q.nodes)
    let T := (F (prefix_occurrence_last N q)).linear
    prefix_zero_radius coordinate_dist N q i j =
      (if (coordinate_linear_row T j).domRestrict (direction_span D) = 0 then ⊤ else 0) ∧
    prefix_threshold_readout coordinate_dist N σ τs τr q i j =
      (decide (σ i (prefix_occurrence_input_domain N q) < τs),
        decide ((coordinate_linear_row T j).domRestrict (direction_span D) = 0)) := by
  dsimp only
  let D := real_locus (N.prefix_input_domain q.nodes)
  let v := prefix_occurrence_last N q
  have hQ : prefix_occurrence_input_domain N q = coordinate_model_set Set.univ D := by
    ext x
    cases x with
    | none =>
      constructor
      · intro hx
        have hh := actual_prefix_input_subset_node_domain N q hx
        exact (hh ((N.node_op v).preserves_bot)).elim
      · rintro ⟨a, _, h⟩; cases h
    | some a =>
      constructor
      · intro hx
        exact ⟨a, (mem_real_locus _ a).mpr hx, rfl⟩
      · rintro ⟨b, hb, h⟩
        have hab : b = a := Option.some.inj h.symm
        subst b
        exact (mem_real_locus _ a).mp hb
  have hlocal : ∀ x ∈ D, (prefix_occurrence_local_operator N q).func (full_coordinate_point x) =
      full_coordinate_point (coordinate_affine_map (F v).linear (F v 0) x) := by
    intro x hx
    let a : (Set.univ : Set (CoordinateVector n)) := ⟨x, Set.mem_univ _⟩
    have ha : some a ∈ N.prefix_input_domain q.nodes := (mem_real_locus _ a).mp hx
    obtain ⟨b, hb, hval⟩ := hF v a (actual_prefix_input_subset_node_domain N q ha)
    change (N.node_op v).func (some a) = _
    rw [hb]
    congr 1
    apply Subtype.ext
    exact hval.trans (congrFun (F v).decomp x)
  exact actual_affine_prefix_convex_radius_readout N q (F v).linear (F v 0) D hQ
    (actual_prefix_input_domain_convex_nonempty N F hF hentry hedge q).1 hlocal σ τs τr hτr i j

end
end formal_oet.vol_01.appendix_finite_dimensional_operator_networks
