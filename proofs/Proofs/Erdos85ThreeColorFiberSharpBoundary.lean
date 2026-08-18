import Proofs.Erdos85NearTwinNoRainbowSaturation

/-! # Sharp boundary for three color fibers -/

namespace Erdos85

/-- Four objects distributed among three colors with fiber capacity two
either double two colors, or have the sharp `2+1+1` profile. -/
theorem threeColor_two_doubles_or_two_one_one
    {C : Type*} [DecidableEq C]
    (palette : Finset C) (f : C → ℕ)
    (hcard : palette.card = 3)
    (hcap : ∀ c ∈ palette, f c ≤ 2)
    (hmass : 4 ≤ ∑ c ∈ palette, f c) :
    (∃ a ∈ palette, ∃ b ∈ palette, a ≠ b ∧ f a = 2 ∧ f b = 2) ∨
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        palette = {a, b, c} ∧ f a = 2 ∧ f b = 1 ∧ f c = 1 ∧
        ∑ d ∈ palette, f d = 4 := by
  obtain ⟨a, b, c, hab, hac, hbc, hpalette⟩ :=
    Finset.card_eq_three.mp hcard
  subst palette
  have ha : f a ≤ 2 := hcap a (by simp)
  have hb : f b ≤ 2 := hcap b (by simp)
  have hc : f c ≤ 2 := hcap c (by simp)
  have hsum : 4 ≤ f a + f b + f c := by
    simpa [hab, hac, hbc, Nat.add_assoc] using hmass
  by_cases habTwo : f a = 2 ∧ f b = 2
  · left
    exact ⟨a, by simp, b, by simp, hab, habTwo.1, habTwo.2⟩
  by_cases hacTwo : f a = 2 ∧ f c = 2
  · left
    exact ⟨a, by simp, c, by simp, hac, hacTwo.1, hacTwo.2⟩
  by_cases hbcTwo : f b = 2 ∧ f c = 2
  · left
    exact ⟨b, by simp, c, by simp, hbc, hbcTwo.1, hbcTwo.2⟩
  right
  have hone :
      (f a = 2 ∧ f b = 1 ∧ f c = 1) ∨
      (f b = 2 ∧ f a = 1 ∧ f c = 1) ∨
      (f c = 2 ∧ f a = 1 ∧ f b = 1) := by
    omega
  rcases hone with h | h | h
  · have hmass4 : ∑ d ∈ ({a, b, c} : Finset C), f d = 4 := by
      simp [hab, hac, hbc, h]
    exact ⟨a, b, c, hab, hac, hbc, rfl,
      h.1, h.2.1, h.2.2, hmass4⟩
  · have hpal : ({a, b, c} : Finset C) = {b, a, c} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
    have hmass4 : ∑ d ∈ ({a, b, c} : Finset C), f d = 4 := by
      simp [hab, hac, hbc, h]
    exact ⟨b, a, c, hab.symm, hbc, hac, hpal,
      h.1, h.2.1, h.2.2, hmass4⟩
  · have hpal : ({a, b, c} : Finset C) = {c, a, b} := by
      ext z
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
    have hmass4 : ∑ d ∈ ({a, b, c} : Finset C), f d = 4 := by
      simp [hab, hac, hbc, h]
    exact ⟨c, a, b, hac.symm, hbc.symm, hab, hpal,
      h.1, h.2.1, h.2.2, hmass4⟩

/-- Fiberwise form used by owner-color censuses: a set of mass at least four
mapping to three colors, with every color used at most twice, has either two
doubled colors or the exact `2+1+1` boundary. -/
theorem threeColor_fibers_two_doubles_or_two_one_one
    {R C : Type*} [DecidableEq R] [DecidableEq C]
    (E : Finset R) (color : R → C) (palette : Finset C)
    (hpalette : palette.card = 3)
    (hmass : 4 ≤ E.card)
    (hmap : Set.MapsTo color E palette)
    (hcap : ∀ c ∈ palette,
      (E.filter fun r => color r = c).card ≤ 2) :
    (∃ a ∈ palette, ∃ b ∈ palette, a ≠ b ∧
      (E.filter fun r => color r = a).card = 2 ∧
      (E.filter fun r => color r = b).card = 2) ∨
      ∃ a b c, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
        palette = {a, b, c} ∧
        (E.filter fun r => color r = a).card = 2 ∧
        (E.filter fun r => color r = b).card = 1 ∧
        (E.filter fun r => color r = c).card = 1 ∧ E.card = 4 := by
  let f := fun c => (E.filter fun r => color r = c).card
  have hdecomp : E.card = ∑ c ∈ palette, f c :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hmass' : 4 ≤ ∑ c ∈ palette, f c := by omega
  rcases threeColor_two_doubles_or_two_one_one
      palette f hpalette (by simpa [f] using hcap) hmass' with h | h
  · left
    simpa [f] using h
  · rcases h with ⟨a, b, c, hab, hac, hbc, hp, ha, hb, hc, hsum⟩
    right
    refine ⟨a, b, c, hab, hac, hbc, hp, ?_, ?_, ?_, ?_⟩
    · simpa [f] using ha
    · simpa [f] using hb
    · simpa [f] using hc
    · omega

end Erdos85
