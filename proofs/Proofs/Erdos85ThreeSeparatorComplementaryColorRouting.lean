import Proofs.Erdos85ThreeSeparatorDesignStarInjection

/-!
# Complementary color routing through a three-separator

The B39 injection preserves more than incidence.  At a residual overlap,
the two residual centers use two distinct separator colors and the image
edge in the exceptional K-star uses the unique third color.  The same
three-color fact describes the remaining residual route at a P-fiber.
These are B40a and B40b.
-/

open Finset

namespace Erdos85

noncomputable section

/-- Two distinct colors in a three-element separator have a unique
complementary color. -/
theorem existsUnique_complementaryColor_of_threeSeparator
    {V : Type*} [DecidableEq V]
    (W : Finset V) (w₁ w₂ : V)
    (hWcard : W.card = 3)
    (hw₁ : w₁ ∈ W) (hw₂ : w₂ ∈ W) (hne : w₁ ≠ w₂) :
    ∃! w₃, w₃ ∈ W \ {w₁, w₂} := by
  have hpairSub : {w₁, w₂} ⊆ W := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact hw₁
    · exact hw₂
  have hpairCard : ({w₁, w₂} : Finset V).card = 2 := by
    simp [hne]
  have hcard : (W \ {w₁, w₂}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hpairSub, hWcard, hpairCard]
  obtain ⟨w₃, hw₃⟩ := Finset.card_eq_one.mp hcard
  refine ⟨w₃, ?_, ?_⟩
  · rw [hw₃]
    exact Finset.mem_singleton_self w₃
  · intro w hw
    rw [hw₃] at hw
    exact Finset.mem_singleton.mp hw

/-- Exact complement form: three routed, pairwise-distinct colors exhaust
the separator, so the third route is precisely the complementary color. -/
theorem complementaryColor_sdiff_eq_singleton
    {V : Type*} [DecidableEq V]
    (W : Finset V) (w₁ w₂ w₃ : V)
    (hWcard : W.card = 3)
    (hw₁ : w₁ ∈ W) (hw₂ : w₂ ∈ W) (hw₃ : w₃ ∈ W)
    (h12 : w₁ ≠ w₂) (h13 : w₁ ≠ w₃) (h23 : w₂ ≠ w₃) :
    W \ {w₁, w₂} = {w₃} := by
  obtain ⟨u, hu, huUnique⟩ :=
    existsUnique_complementaryColor_of_threeSeparator W w₁ w₂
      hWcard hw₁ hw₂ h12
  have hw₃mem : w₃ ∈ W \ {w₁, w₂} := by
    simp [hw₃, h13.symm, h23.symm]
  have hw₃u : w₃ = u := huUnique w₃ hw₃mem
  subst u
  ext w
  constructor
  · intro hw
    exact Finset.mem_singleton.mpr (huUnique w hw)
  · intro hw
    exact Finset.mem_singleton.mp hw ▸ hu

/-- B40a: the color on the K-star image of a residual-overlap edge is the
unique color complementary to the two endpoint-wing colors. -/
theorem residualOverlap_Kstar_color_is_complementary
    {V : Type*} [DecidableEq V]
    (W : Finset V) (rColor₁ rColor₂ kColor : V)
    (hWcard : W.card = 3)
    (hr₁ : rColor₁ ∈ W) (hr₂ : rColor₂ ∈ W) (hk : kColor ∈ W)
    (h12 : rColor₁ ≠ rColor₂)
    (h1k : rColor₁ ≠ kColor) (h2k : rColor₂ ≠ kColor) :
    W \ {rColor₁, rColor₂} = {kColor} := by
  exact complementaryColor_sdiff_eq_singleton W rColor₁ rColor₂ kColor
    hWcard hr₁ hr₂ hk h12 h1k h2k

/-- B40b: after the two colors incident with a P-center are used, the
remaining residual center has exactly the complementary third color. -/
theorem Pfiber_remaining_R_color_is_complementary
    {V : Type*} [DecidableEq V]
    (W : Finset V) (incident₁ incident₂ remaining : V)
    (hWcard : W.card = 3)
    (hi₁ : incident₁ ∈ W) (hi₂ : incident₂ ∈ W)
    (hr : remaining ∈ W)
    (h12 : incident₁ ≠ incident₂)
    (h1r : incident₁ ≠ remaining) (h2r : incident₂ ≠ remaining) :
    W \ {incident₁, incident₂} = {remaining} := by
  exact complementaryColor_sdiff_eq_singleton W incident₁ incident₂ remaining
    hWcard hi₁ hi₂ hr h12 h1r h2r

end


end Erdos85


#print axioms Erdos85.existsUnique_complementaryColor_of_threeSeparator
#print axioms Erdos85.complementaryColor_sdiff_eq_singleton
#print axioms Erdos85.residualOverlap_Kstar_color_is_complementary
#print axioms Erdos85.Pfiber_remaining_R_color_is_complementary
