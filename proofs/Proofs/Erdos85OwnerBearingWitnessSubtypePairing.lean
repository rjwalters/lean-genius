import Proofs.Erdos85DisjointFiberInvolutionGluing

/-!
# Owner-bearing witness subtype pairing

The owner-adapted normal form `(73rnz_cjibbb)` prescribes one relay before
pairing the remaining ordinary broken-T endpoints.  This file gives the
finite extension lemma needed for that construction.
-/

namespace Erdos85

noncomputable section

/-- Extend the prescribed pair `x ↔ y` by an arbitrary pairing of a
disjoint even residual fiber. -/
theorem exists_mate_with_prescribed_pair_and_even_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (x y : V) (R : Finset V) (hxy : x ≠ y)
    (hxR : x ∉ R) (hyR : y ∉ R) (hevenR : Even R.card) :
    ∃ mate : V → V,
      mate x = y ∧ mate y = x ∧
      (∀ v ∈ R, mate v ∈ R) ∧
      (∀ v ∈ insert x (insert y R), mate (mate v) = v) ∧
      (∀ v ∈ insert x (insert y R), mate v ≠ v) := by
  let P : Finset V := {x, y}
  let swap : V → V := fun v => if v = x then y else x
  have hdisjoint : Disjoint P R := by
    apply Finset.disjoint_left.mpr
    intro v hvP hvR
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hvP
    rcases hvP with rfl | rfl
    · exact hxR hvR
    · exact hyR hvR
  have hswapClosed : ∀ v, v ∈ P → swap v ∈ P := by
    intro v hv
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
    rcases hv with rfl | rfl
    · simp [swap]
    · simp [swap, hxy]
  have hswapInvol : ∀ v, v ∈ P → swap (swap v) = v := by
    intro v hv
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [swap, hxy]
    · simp [swap, hxy]
  have hswapFree : ∀ v, v ∈ P → swap v ≠ v := by
    intro v hv
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simpa [swap] using hxy.symm
    · simpa [swap, hxy.symm] using hxy
  obtain ⟨mate, hOnP, _hclosedP, hclosedR, hinvol, hfree⟩ :=
    exists_gluedMate_of_involution_of_even_disjoint
      P R hdisjoint swap hswapClosed hswapInvol hswapFree hevenR
  refine ⟨mate, ?_, ?_, hclosedR, ?_, ?_⟩
  · simpa [P, swap] using hOnP x (by simp [P])
  · simpa [P, swap, hxy.symm] using hOnP y (by simp [P])
  · simpa [P] using hinvol
  · simpa [P] using hfree

/-- **Owner-bearing subtype normal form (`73rnz_cjibbb`).**  A singleton
leaf pairs to the unique full endpoint when it exists; if the full fiber is
empty, it pairs to an ordinary endpoint.  All unused ordinary endpoints are
paired internally. -/
theorem exists_ownerBearing_witnessSubtype_mate
    {V : Type*} [Fintype V] [DecidableEq V]
    (leaf full ordinary : Finset V)
    (hLF : Disjoint leaf full) (hLO : Disjoint leaf ordinary)
    (hFO : Disjoint full ordinary)
    (hleaf : leaf.card = 1) (hfull : full.card ≤ 1)
    (heven : Even (leaf.card + full.card + ordinary.card)) :
    ∃ mate : V → V,
      (∀ l ∈ leaf,
        (full.card = 1 → mate l ∈ full) ∧
        (full.card = 0 → mate l ∈ ordinary)) ∧
      (∀ o ∈ ordinary, mate o ∈ ordinary ∪ leaf) ∧
      (∀ v ∈ leaf ∪ full ∪ ordinary, mate (mate v) = v) ∧
      (∀ v ∈ leaf ∪ full ∪ ordinary, mate v ≠ v) := by
  obtain ⟨l, hleafEq⟩ := Finset.card_eq_one.mp hleaf
  have hfullCases : full.card = 0 ∨ full.card = 1 := by omega
  rcases hfullCases with hfullZero | hfullOne
  · have hordOdd : Odd ordinary.card := by
      obtain ⟨k, hk⟩ := heven
      refine ⟨k - 1, ?_⟩
      omega
    have hordNonempty : ordinary.Nonempty := by
      apply Finset.card_pos.mp
      obtain ⟨k, hk⟩ := hordOdd
      omega
    obtain ⟨o, hoOrd⟩ := hordNonempty
    let R := ordinary.erase o
    have hevenR : Even R.card := by
      obtain ⟨k, hk⟩ := hordOdd
      refine ⟨k, ?_⟩
      rw [Finset.card_erase_of_mem hoOrd]
      omega
    have hlo : l ≠ o := by
      intro h
      subst o
      exact Finset.disjoint_left.mp hLO (by simp [hleafEq]) hoOrd
    obtain ⟨mate, hmateL, hmateO, hclosedR, hinvol, hfree⟩ :=
      exists_mate_with_prescribed_pair_and_even_residual
        l o R hlo
          (by
            intro hlR
            exact Finset.disjoint_left.mp hLO (by simp [hleafEq])
              ((Finset.mem_erase.mp hlR).2))
          (by simp [R]) hevenR
    refine ⟨mate, ?_, ?_, ?_, ?_⟩
    · intro l' hl'
      have hl'eq : l' = l := by simpa [hleafEq] using hl'
      subst l'
      exact ⟨by intro h; omega, by intro _; simpa [hmateL] using hoOrd⟩
    · intro v hv
      by_cases hvo : v = o
      · subst v
        exact Finset.mem_union.mpr (Or.inr (by simpa [hleafEq, hmateO]))
      · have hvR : v ∈ R := Finset.mem_erase.mpr ⟨hvo, hv⟩
        exact Finset.mem_union.mpr (Or.inl
          ((Finset.mem_erase.mp (hclosedR v hvR)).2))
    · intro v hv
      have hfullEmpty : full = ∅ := Finset.card_eq_zero.mp hfullZero
      have hOrdDecomp : insert o R = ordinary := by
        exact Finset.insert_erase hoOrd
      have hsupport : leaf ∪ full ∪ ordinary = insert l (insert o R) := by
        rw [hleafEq, hfullEmpty, Finset.union_empty, hOrdDecomp]
        simp
      exact hinvol v (by rwa [← hsupport])
    · intro v hv
      have hfullEmpty : full = ∅ := Finset.card_eq_zero.mp hfullZero
      have hOrdDecomp : insert o R = ordinary := by
        exact Finset.insert_erase hoOrd
      have hsupport : leaf ∪ full ∪ ordinary = insert l (insert o R) := by
        rw [hleafEq, hfullEmpty, Finset.union_empty, hOrdDecomp]
        simp
      exact hfree v (by rwa [← hsupport])
  · obtain ⟨f, hfullEq⟩ := Finset.card_eq_one.mp hfullOne
    have hevenOrd : Even ordinary.card := by
      obtain ⟨k, hk⟩ := heven
      refine ⟨k - 1, ?_⟩
      omega
    have hlf : l ≠ f := by
      intro hEq
      have hlmem : l ∈ leaf := by simp [hleafEq]
      have hfmem : f ∈ full := by simp [hfullEq]
      exact Finset.disjoint_left.mp hLF hlmem (hEq.symm ▸ hfmem)
    have hlO : l ∉ ordinary := fun h =>
      Finset.disjoint_left.mp hLO (by simp [hleafEq]) h
    have hfO : f ∉ ordinary := fun h =>
      Finset.disjoint_left.mp hFO (by simp [hfullEq]) h
    obtain ⟨mate, hmateL, _hmateF, hclosedO, hinvol, hfree⟩ :=
      exists_mate_with_prescribed_pair_and_even_residual
        l f ordinary hlf hlO hfO hevenOrd
    refine ⟨mate, ?_, ?_, ?_, ?_⟩
    · intro l' hl'
      have hl'eq : l' = l := by simpa [hleafEq] using hl'
      subst l'
      exact ⟨by intro _; simpa [hfullEq, hmateL], by intro h; omega⟩
    · intro o ho
      exact Finset.mem_union.mpr (Or.inl (hclosedO o ho))
    · intro v hv
      have hsupport : leaf ∪ full ∪ ordinary = insert l (insert f ordinary) := by
        rw [hleafEq, hfullEq]
        simp
      exact hinvol v (by rwa [← hsupport])
    · intro v hv
      have hsupport : leaf ∪ full ∪ ordinary = insert l (insert f ordinary) := by
        rw [hleafEq, hfullEq]
        simp
      exact hfree v (by rwa [← hsupport])

end

end Erdos85

#print axioms Erdos85.exists_mate_with_prescribed_pair_and_even_residual
#print axioms Erdos85.exists_ownerBearing_witnessSubtype_mate
