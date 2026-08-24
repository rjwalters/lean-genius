import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEquality

/-!
# Row-partner coordinates in an equality circuit

The equality proof contains a stronger local coordinatization: after fixing a
row, its points biject with all other rows, each point being sent to its unique
partner row.  This file exposes that structure as a reusable theorem.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- In a linear `m`-uniform equality circuit, the points of any fixed row
bijection with the other `m` rows through incidence. -/
theorem linear_evenConfiguration_eq_succ_partnerBijection
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (m : ℕ)
    (hcard : ∀ a ∈ T, (B a).card = m)
    (hlinear : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      ((B a) ∩ (B b)).card ≤ 1)
    (heven : ∀ y : β, Even ((T.filter fun a => y ∈ B a).card))
    (hTcard : T.card = m + 1) :
    ∀ a ∈ T,
      ∃ f : {y // y ∈ B a} → {b // b ∈ T.erase a},
        Function.Bijective f ∧ ∀ y, y.1 ∈ B (f y).1 := by
  classical
  have hpartners : ∀ a ∈ T, ∀ y ∈ B a,
      ∃ b, b ∈ T.erase a ∧ y ∈ B b := by
    intro a haT y hyB
    let I := T.filter fun b => y ∈ B b
    have haI : a ∈ I := Finset.mem_filter.mpr ⟨haT, hyB⟩
    have hpos : 0 < I.card := Finset.card_pos.mpr ⟨a, haI⟩
    have hIy : Even I.card := by simpa [I] using heven y
    have htwo : 2 ≤ I.card := by
      rcases hIy with ⟨k, hk⟩
      omega
    have herase : (I.erase a).card = I.card - 1 :=
      Finset.card_erase_of_mem haI
    have hne : (I.erase a).Nonempty := by
      apply Finset.card_pos.mp
      rw [herase]
      omega
    obtain ⟨b, hb⟩ := hne
    have hbData := Finset.mem_erase.mp hb
    have hbI := Finset.mem_filter.mp hbData.2
    exact ⟨b, Finset.mem_erase.mpr ⟨hbData.1, hbI.1⟩, hbI.2⟩
  intro a haT
  let f : {y // y ∈ B a} → {b // b ∈ T.erase a} := fun y =>
    ⟨((hpartners a haT y.1 y.2).choose),
      (hpartners a haT y.1 y.2).choose_spec.1⟩
  have hfmem : ∀ y : {y // y ∈ B a}, y.1 ∈ B (f y).1 := by
    intro y
    exact (hpartners a haT y.1 y.2).choose_spec.2
  have hfinj : Function.Injective f := by
    intro y z hyz
    apply Subtype.ext
    have hfT : (f y).1 ∈ T := Finset.mem_of_mem_erase (f y).2
    have hfa : (f y).1 ≠ a := Finset.ne_of_mem_erase (f y).2
    apply Finset.card_le_one.mp
      (hlinear a haT (f y).1 hfT hfa.symm)
    · exact Finset.mem_inter.mpr ⟨y.2, hfmem y⟩
    · exact Finset.mem_inter.mpr ⟨z.2, hyz ▸ hfmem z⟩
  have hdom : Fintype.card {y // y ∈ B a} = m := by
    rw [Fintype.card_coe, hcard a haT]
  have hcod : Fintype.card {b // b ∈ T.erase a} = m := by
    rw [Fintype.card_coe, Finset.card_erase_of_mem haT, hTcard]
    omega
  have hfsurj : Function.Surjective f := by
    exact (Fintype.bijective_iff_injective_and_card f).2
      ⟨hfinj, hdom.trans hcod.symm⟩ |>.2
  exact ⟨f, ⟨hfinj, hfsurj⟩, hfmem⟩

end

end Erdos85

#print axioms Erdos85.linear_evenConfiguration_eq_succ_partnerBijection
