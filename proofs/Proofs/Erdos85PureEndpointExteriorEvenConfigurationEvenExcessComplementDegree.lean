import Proofs.Erdos85PureEndpointExteriorMinimalCircuitEulerian

/-!
# Missing-partner degrees in an even-excess circuit

Two generic lemmas isolate the mechanism for the even larger-circuit branch.
Every point of a selected row has another selected row through it; linearity
makes those partners distinct, giving internal degree at least the uniform
row size.  If the total circuit size is `m+2s` and internal degree is even,
the complementary missing-partner degree is odd and at most `2s-1`.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- In a linear pointwise-even configuration, a selected `m`-uniform row
meets at least `m` other selected rows. -/
theorem linear_evenConfiguration_uniform_le_internalMeeting
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (Inc : α → β → Prop) [DecidableRel Inc]
    (T : Finset α) (L : Finset β) (p : α) (m : ℕ)
    (hp : p ∈ T)
    (huniform : (L.filter fun l => Inc p l).card = m)
    (heven : ∀ l ∈ L, Even ((T.filter fun q => Inc q l).card))
    (hlinear : ∀ q ∈ T.erase p, ∀ l ∈ L, ∀ l' ∈ L,
      Inc p l → Inc q l → Inc p l' → Inc q l' → l = l') :
    m ≤ ((T.erase p).filter fun q =>
      (L.filter fun l => Inc p l ∧ Inc q l).Nonempty).card := by
  classical
  let B := L.filter fun l => Inc p l
  let M := (T.erase p).filter fun q =>
    (L.filter fun l => Inc p l ∧ Inc q l).Nonempty
  have hexists : ∀ l : {l // l ∈ B}, ∃ q,
      q ∈ T.erase p ∧ Inc q l.1 := by
    intro l
    have hlData := Finset.mem_filter.mp l.2
    let fiber := T.filter fun q => Inc q l.1
    have hpFiber : p ∈ fiber :=
      Finset.mem_filter.mpr ⟨hp, hlData.2⟩
    have hfiberEven : Even fiber.card := heven l.1 hlData.1
    have hfiberPos : 0 < fiber.card := Finset.card_pos.mpr ⟨p, hpFiber⟩
    have hfiberTwo : 2 ≤ fiber.card := by
      obtain ⟨k, hk⟩ := hfiberEven
      omega
    have herasePos : 0 < (fiber.erase p).card := by
      rw [Finset.card_erase_of_mem hpFiber]
      omega
    obtain ⟨q, hq⟩ := Finset.card_pos.mp herasePos
    have hqData := Finset.mem_erase.mp hq
    exact ⟨q, Finset.mem_erase.mpr
      ⟨hqData.1, (Finset.mem_filter.mp hqData.2).1⟩,
        (Finset.mem_filter.mp hqData.2).2⟩
  let f : {l // l ∈ B} → {q // q ∈ M} := fun l =>
    let q := Classical.choose (hexists l)
    ⟨q, Finset.mem_filter.mpr ⟨
      (Classical.choose_spec (hexists l)).1,
      ⟨l.1, Finset.mem_filter.mpr ⟨
        (Finset.mem_filter.mp l.2).1,
        ⟨(Finset.mem_filter.mp l.2).2,
          (Classical.choose_spec (hexists l)).2⟩⟩⟩⟩⟩
  have hfval : ∀ l : {l // l ∈ B},
      Inc (f l).1 l.1 := by
    intro l
    exact (Classical.choose_spec (hexists l)).2
  have hfinj : Function.Injective f := by
    intro l l' hll'
    apply Subtype.ext
    have hqmem : (f l).1 ∈ T.erase p :=
      (Finset.mem_filter.mp (f l).2).1
    have hlData := Finset.mem_filter.mp l.2
    have hl'Data := Finset.mem_filter.mp l'.2
    have hfval' : Inc (f l).1 l'.1 := by
      have := hfval l'
      rw [← hll'] at this
      exact this
    exact hlinear (f l).1 hqmem l.1 hlData.1 l'.1 hl'Data.1
      hlData.2 (hfval l) hl'Data.2 hfval'
  have hcardSub := Fintype.card_le_of_injective f hfinj
  simpa only [Fintype.card_coe, B, M, huniform] using hcardSub

/-- Arithmetic form of the even-excess complement law. -/
theorem evenExcess_missingDegree_odd_le
    (m s t internal missing : ℕ)
    (hs : 0 < s)
    (ht : t = m + 2 * s)
    (hpart : internal + missing = t - 1)
    (hm : Even m) (hi : Even internal)
    (hlower : m ≤ internal) :
    Odd missing ∧ missing ≤ 2 * s - 1 := by
  obtain ⟨a, ha⟩ := hm
  obtain ⟨b, hb⟩ := hi
  have htpos : 0 < t := by omega
  refine ⟨⟨a + s - b - 1, by omega⟩, ?_⟩
  omega

end

end Erdos85

#print axioms Erdos85.linear_evenConfiguration_uniform_le_internalMeeting
#print axioms Erdos85.evenExcess_missingDegree_odd_le
