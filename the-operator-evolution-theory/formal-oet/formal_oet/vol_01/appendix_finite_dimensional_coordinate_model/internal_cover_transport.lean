import formal_oet.vol_01.ch_01_foundations.metric_entropy

namespace formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
open formal_oet.vol_01.ch_01_foundations
noncomputable section

/-- Internal covering numbers are preserved by a distance-preserving map on the
set being covered. Both directions construct internal centers; no general
monotonicity under set inclusion is used. -/
theorem internal_cover_image_eq {X Y : Type} (d : X → X → ENNReal)
    (e : Y → Y → ENNReal) (f : X → Y) (S : Set X) (ε : ENNReal)
    (hd : ∀ x ∈ S, ∀ y ∈ S, e (f x) (f y) = d x y) :
    covering_number e ε (f '' S) = covering_number d ε S := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro s
    apply le_iInf
    intro hnet
    have hnet' : InternalEpsilonNet e ε (f '' S) (s.image f) := by
      constructor
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨x, hnet.1 hx, rfl⟩
      · rintro _ ⟨x, hx, rfl⟩
        obtain ⟨c, hc, hxc⟩ := hnet.2 x hx
        exact ⟨f c, Finset.mem_image.mpr ⟨c, hc, rfl⟩, by rw [hd x hx c (hnet.1 hc)]; exact hxc⟩
    exact (iInf_le_of_le (s.image f) (iInf_le_of_le hnet' le_rfl)).trans
      (by exact_mod_cast Finset.card_image_le)
  · apply le_iInf
    intro s
    apply le_iInf
    intro hnet
    let lift (c : {c // c ∈ s}) : X := (hnet.1 c.property).choose
    have hlift (c : {c // c ∈ s}) : lift c ∈ S ∧ f (lift c) = c.val :=
      (hnet.1 c.property).choose_spec
    let t := Finset.univ.image lift
    have hnet' : InternalEpsilonNet d ε S t := by
      constructor
      · intro x hx
        obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hx
        exact (hlift c).1
      · intro x hx
        obtain ⟨c, hc, hxc⟩ := hnet.2 (f x) ⟨x, hx, rfl⟩
        refine ⟨lift ⟨c, hc⟩, Finset.mem_image.mpr ⟨⟨c, hc⟩, Finset.mem_univ _, rfl⟩, ?_⟩
        rw [← hd x hx _ (hlift ⟨c, hc⟩).1, (hlift ⟨c, hc⟩).2]
        exact hxc
    have hcard : t.card ≤ s.card := by
      simpa using (Finset.card_image_le : t.card ≤ (Finset.univ : Finset {c // c ∈ s}).card)
    exact (iInf_le_of_le t (iInf_le_of_le hnet' le_rfl)).trans (by exact_mod_cast hcard)

end
end formal_oet.vol_01.appendix_finite_dimensional_coordinate_model
