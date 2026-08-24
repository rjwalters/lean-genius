import Mathlib

/-!
# Parity of a finite fixed-point-free involution

This is the counting kernel for the Baer broken fiber.  A canonical pairing
makes its domain even; subtracting that domain from an even neighbor star
then leaves an even completion fiber.
-/

namespace Erdos85

/-- A finite set preserved by a fixed-point-free involution has even
cardinality. -/
theorem even_card_of_closed_fixedPointFree_involution
    {V : Type*} [DecidableEq V] (mate : V → V) (S : Finset V)
    (hclosed : ∀ x ∈ S, mate x ∈ S)
    (hinvol : ∀ x ∈ S, mate (mate x) = x)
    (hfree : ∀ x ∈ S, mate x ≠ x) :
    Even S.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
      by_cases hS : S = ∅
      · simp [hS]
      obtain ⟨x, hxS⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      let y := mate x
      have hyS : y ∈ S := hclosed x hxS
      have hyx : y ≠ x := hfree x hxS
      let R := (S.erase x).erase y
      have hRsub : R ⊂ S := by
        rw [Finset.ssubset_iff_subset_ne]
        constructor
        · exact (Finset.erase_subset y (S.erase x)).trans
            (Finset.erase_subset x S)
        · intro hEq
          have hxR : x ∈ R := hEq ▸ hxS
          exact (Finset.mem_erase.mp
            (Finset.mem_erase.mp hxR).2).1 rfl
      have hRclosed : ∀ z ∈ R, mate z ∈ R := by
        intro z hzR
        have hzErase := Finset.mem_erase.mp hzR
        have hzErase' := Finset.mem_erase.mp hzErase.2
        have hzy : z ≠ y := hzErase.1
        have hzx : z ≠ x := hzErase'.1
        have hzS : z ∈ S := hzErase'.2
        have hmS := hclosed z hzS
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hmS⟩⟩
        · intro hmzy
          have := congrArg mate hmzy
          rw [hinvol z hzS, show mate y = x from hinvol x hxS] at this
          exact hzx this
        · intro hmzx
          have := congrArg mate hmzx
          rw [hinvol z hzS] at this
          exact hzy this
      have hRinvol : ∀ z ∈ R, mate (mate z) = z := by
        intro z hzR
        exact hinvol z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzR))
      have hRfree : ∀ z ∈ R, mate z ≠ z := by
        intro z hzR
        exact hfree z (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzR))
      obtain ⟨k, hk⟩ := ih R hRsub hRclosed hRinvol hRfree
      have hcardX : (S.erase x).card + 1 = S.card :=
        Finset.card_erase_add_one hxS
      have hyErase : y ∈ S.erase x :=
        Finset.mem_erase.mpr ⟨hyx, hyS⟩
      have hcardY : R.card + 1 = (S.erase x).card := by
        exact Finset.card_erase_add_one hyErase
      refine ⟨k + 1, ?_⟩
      omega

#print axioms even_card_of_closed_fixedPointFree_involution

end Erdos85
