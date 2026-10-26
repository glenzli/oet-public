import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.coordinate_fiber_bridge
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.jacobi_coordinate_bridge
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.norm_ball_bridge
import formal_oet.vol_01.appendix_finite_dimensional_coordinate_model.fibers_and_derivatives

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.appendix_separating_gauge_specialization
noncomputable section
variable {n : ℕ} [NeZero n]

theorem coordinate_sup_distance_eq_norm (x y : CoordinateVector n) :
    coordinate_sup_distance x y = ENNReal.ofReal ‖x - y‖ := by
  simp only [coordinate_sup_distance]
  rw [Pi.norm_def, ENNReal.ofReal_coe_nnreal, ENNReal.coe_finset_sup]
  congr 1
  funext i
  simp [ENNReal.coe_nnreal_eq, Real.norm_eq_abs]

def full_coordinate_point (x : CoordinateVector n) : CoordinatePoint n Set.univ :=
  some ⟨x, Set.mem_univ x⟩

def full_model_operator (F : CoordinateVector n → CoordinateVector n)
    (Q : Set (CoordinateVector n)) :=
  coordinate_model_operator Set.univ Q F (fun _ _ => Set.mem_univ _)

def full_model_radius (F : CoordinateVector n → CoordinateVector n)
    (Q : Set (CoordinateVector n)) (y : CoordinateVector n) : ENNReal :=
  full_output_annihilation_radius coordinate_dist (full_model_operator F Q)
    coordinate_full_dist (coordinate_model_set Set.univ Q) (full_coordinate_point y)

def coordinate_model_radius (F : CoordinateVector n → CoordinateVector n)
    (Q : Set (CoordinateVector n)) (i j : Fin n) (y : CoordinateVector n) : ENNReal :=
  annihilation_radius coordinate_dist (full_model_operator F Q) i
    (singleton_nonempty_finset j) (coordinate_model_set Set.univ Q) (full_coordinate_point y)

theorem full_model_radius_eq (F : CoordinateVector n → CoordinateVector n)
    (Q : Set (CoordinateVector n)) (y : CoordinateVector n) (hy : y ∈ Q) :
    full_model_radius F Q y = exact_constancy_radius coordinate_sup_distance F Q y := by
  let Q' : Set (Set.univ : Set (CoordinateVector n)) := Subtype.val ⁻¹' Q
  have hS : some '' Q' = coordinate_model_set Set.univ Q := by
    ext x; simp [Q', coordinate_model_set, eq_comm]
  have hd : some '' Q' ⊆ dom (full_model_operator F Q) := by
    rw [hS, full_model_operator, coordinate_model_operator_dom]
  unfold full_model_radius full_coordinate_point
  rw [← hS]
  erw [full_coordinate_annihilation_radius_level_set _ Q' hd ⟨y, Set.mem_univ y⟩ hy]
  unfold exact_constancy_radius
  apply iSup_congr
  intro r
  apply iSup_congr
  intro hr
  apply iSup_congr_Prop ?_ (by intros; rfl)
  constructor
  · intro h x hx hxy
    have hh := h ⟨x, Set.mem_univ x⟩ hx hxy
    simpa [full_model_operator, coordinate_model_operator, coordinate_readout, hx, hy] using hh
  · intro h x hx hxy
    have hh := h x.val hx hxy
    have hx' : x.val ∈ Q := hx
    simpa [full_model_operator, coordinate_model_operator, coordinate_readout, hx', hy] using hh

theorem coordinate_model_radius_eq (F : CoordinateVector n → CoordinateVector n)
    (Q : Set (CoordinateVector n)) (i j : Fin n) (y : CoordinateVector n) (hy : y ∈ Q) :
    coordinate_model_radius F Q i j y =
      exact_constancy_radius (fun x y => ENNReal.ofReal |x i - y i|)
        (fun x => F x j) Q y := by
  let Q' : Set (Set.univ : Set (CoordinateVector n)) := Subtype.val ⁻¹' Q
  have hS : some '' Q' = coordinate_model_set Set.univ Q := by
    ext x; simp [Q', coordinate_model_set, eq_comm]
  have hd : some '' Q' ⊆ dom (full_model_operator F Q) := by
    rw [hS, full_model_operator, coordinate_model_operator_dom]
  unfold coordinate_model_radius full_coordinate_point
  rw [← hS]
  erw [coordinate_annihilation_radius_level_set _ Q' hd i j ⟨y, Set.mem_univ y⟩ hy]
  unfold exact_constancy_radius
  apply iSup_congr
  intro r
  apply iSup_congr
  intro hr
  apply iSup_congr_Prop ?_ (by intros; rfl)
  constructor
  · intro h x hx hxy
    have hh := h ⟨x, Set.mem_univ x⟩ hx hxy
    simpa [full_model_operator, coordinate_model_operator, coordinate_readout, hx, hy] using hh
  · intro h x hx hxy
    have hh := h x.val hx hxy
    have hx' : x.val ∈ Q := hx
    simpa [full_model_operator, coordinate_model_operator, coordinate_readout, hx', hy] using hh

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
