import Proofs.Erdos85PureEndpointExteriorIncidenceKernel

/-!
# Equality rigidity for a linear even configuration

The lower bound `|T| ≥ m+1` for a nonempty even configuration is rigid at
equality.  Every point of a row must be paired with a different row, and the
resulting injection is a bijection.  Hence all row pairs meet, and every used
point has configuration degree exactly two.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Equality case for the circuit-girth bound in a linear uniform set
system. -/
theorem linear_evenConfiguration_eq_succ_rigidity
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (m : ℕ)
    (hcard : ∀ a ∈ T, (B a).card = m)
    (hlinear : ∀ a ∈ T, ∀ b ∈ T, a ≠ b →
      ((B a) ∩ (B b)).card ≤ 1)
    (heven : ∀ y : β, Even ((T.filter fun a => y ∈ B a).card))
    (hTcard : T.card = m + 1) :
    (∀ a ∈ T, ∀ b ∈ T, a ≠ b → ((B a) ∩ (B b)).card = 1) ∧
    ∀ y : β, (T.filter fun a => y ∈ B a).Nonempty →
      (T.filter fun a => y ∈ B a).card = 2 := by
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
  have hlocal : ∀ a ∈ T,
      ∃ f : {y // y ∈ B a} → {b // b ∈ T.erase a},
        Function.Bijective f ∧
        ∀ y, y.1 ∈ B (f y).1 := by
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
      have hfT : (f y).1 ∈ T :=
        Finset.mem_of_mem_erase (f y).2
      have hfa : (f y).1 ≠ a := Finset.ne_of_mem_erase (f y).2
      apply Finset.card_le_one.mp
        (hlinear a haT (f y).1 hfT hfa.symm)
      · exact Finset.mem_inter.mpr ⟨y.2, hfmem y⟩
      · exact Finset.mem_inter.mpr
          ⟨z.2, hyz ▸ hfmem z⟩
    have hdom : Fintype.card {y // y ∈ B a} = m := by
      rw [Fintype.card_coe, hcard a haT]
    have hcod : Fintype.card {b // b ∈ T.erase a} = m := by
      rw [Fintype.card_coe, Finset.card_erase_of_mem haT, hTcard]
      omega
    have hfsurj : Function.Surjective f := by
      exact (Fintype.bijective_iff_injective_and_card f).2
        ⟨hfinj, hdom.trans hcod.symm⟩ |>.2
    exact ⟨f, ⟨hfinj, hfsurj⟩, hfmem⟩
  constructor
  · intro a haT b hbT hab
    obtain ⟨f, _hfBij, hfmem⟩ := hlocal a haT
    let b' : {b // b ∈ T.erase a} :=
      ⟨b, Finset.mem_erase.mpr ⟨hab.symm, hbT⟩⟩
    obtain ⟨y, hy⟩ := _hfBij.2 b'
    apply Nat.le_antisymm (hlinear a haT b hbT hab)
    apply Finset.card_pos.mpr
    refine ⟨y.1, Finset.mem_inter.mpr ⟨y.2, ?_⟩⟩
    have hyval : (f y).1 = b := congrArg Subtype.val hy
    simpa [hyval] using hfmem y
  · intro y hyI
    let I := T.filter fun a => y ∈ B a
    obtain ⟨a, haI⟩ := hyI
    have haT := (Finset.mem_filter.mp haI).1
    have hay := (Finset.mem_filter.mp haI).2
    obtain ⟨f, hfBij, hfmem⟩ := hlocal a haT
    let ya : {z // z ∈ B a} := ⟨y, hay⟩
    have hsub : I ⊆ {a, (f ya).1} := by
      intro b hbI
      have hbData := Finset.mem_filter.mp hbI
      by_cases hba : b = a
      · simp [hba]
      · let b' : {b // b ∈ T.erase a} :=
          ⟨b, Finset.mem_erase.mpr ⟨hba, hbData.1⟩⟩
        obtain ⟨z, hz⟩ := hfBij.2 b'
        have hzy : z.1 = y := by
          apply Finset.card_le_one.mp
            (hlinear a haT b hbData.1 (Ne.symm hba))
          · exact Finset.mem_inter.mpr
              ⟨z.2, by
                have hzval : (f z).1 = b := congrArg Subtype.val hz
                simpa [hzval] using hfmem z⟩
          · exact Finset.mem_inter.mpr ⟨hay, hbData.2⟩
        have hbf : b = (f ya).1 := by
          have hza : z = ya := Subtype.ext hzy
          have hzval : (f z).1 = b := congrArg Subtype.val hz
          calc
            b = (f z).1 := hzval.symm
            _ = (f ya).1 := by rw [hza]
        simp [hbf]
    have hle : I.card ≤ 2 := by
      apply (Finset.card_le_card hsub).trans
      calc
        ({a, (f ya).1} : Finset α).card ≤ ({(f ya).1} : Finset α).card + 1 :=
          by simpa using Finset.card_insert_le a ({(f ya).1} : Finset α)
        _ = 2 := by simp
    have hpos : 0 < I.card := Finset.card_pos.mpr ⟨a, haI⟩
    have hIy : Even I.card := by simpa [I] using heven y
    rcases hIy with ⟨k, hk⟩
    change I.card = 2
    omega

end

end Erdos85

#print axioms Erdos85.linear_evenConfiguration_eq_succ_rigidity
