import Proofs.Erdos85EvenFinsetInvolutionPairing

/-!
# Extending a partial pairing by one prescribed pair

The Baer relay construction needs each even neighbor star paired, with one
owner-determined pair fixed in advance.  Once the remaining vertices have an
involutive fixed-point-free mate, this file supplies the generic extension.
-/

namespace Erdos85

variable {V : Type*} [DecidableEq V]

/-- Override a mate map so that `a` and `b` are paired with one another. -/
def prescribePair (mate : V → V) (a b : V) (x : V) : V :=
  if x = a then b else if x = b then a else mate x

@[simp] theorem prescribePair_left (mate : V → V) (a b : V) :
    prescribePair mate a b a = b := by
  simp [prescribePair]

@[simp] theorem prescribePair_right (mate : V → V) (a b : V) :
    prescribePair mate a b b = a := by
  simp [prescribePair]

/-- A pairing of the complement of `{a,b}` extends to a pairing of `S` which
uses the prescribed pair `a ↔ b`. -/
theorem prescribePair_spec
    (S : Finset V) (mate : V → V) (a b : V)
    (hab : a ≠ b) (haS : a ∈ S) (hbS : b ∈ S)
    (hclosed : ∀ x ∈ S, x ≠ a → x ≠ b →
      mate x ∈ S ∧ mate x ≠ a ∧ mate x ≠ b)
    (hinvol : ∀ x ∈ S, x ≠ a → x ≠ b → mate (mate x) = x)
    (hfree : ∀ x ∈ S, x ≠ a → x ≠ b → mate x ≠ x) :
    prescribePair mate a b a = b ∧
    prescribePair mate a b b = a ∧
    (∀ x ∈ S, prescribePair mate a b x ∈ S) ∧
    (∀ x ∈ S,
      prescribePair mate a b (prescribePair mate a b x) = x) ∧
    ∀ x ∈ S, prescribePair mate a b x ≠ x := by
  refine ⟨by simp, by simp, ?_, ?_, ?_⟩
  · intro x hxS
    by_cases hxa : x = a
    · simpa [hxa] using hbS
    by_cases hxb : x = b
    · simpa [hxb, hab] using haS
    simpa [prescribePair, hxa, hxb] using
      (hclosed x hxS hxa hxb).1
  · intro x hxS
    by_cases hxa : x = a
    · subst x
      simp
    by_cases hxb : x = b
    · subst x
      simp
    have hm := hclosed x hxS hxa hxb
    simp [prescribePair, hxa, hxb, hm.2.1, hm.2.2,
      hinvol x hxS hxa hxb]
  · intro x hxS
    by_cases hxa : x = a
    · subst x
      simpa using hab.symm
    by_cases hxb : x = b
    · subst x
      simp [hab]
    simpa [prescribePair, hxa, hxb] using hfree x hxS hxa hxb

/-- Every even finite set admits a fixed-point-free involution containing any
prescribed pair of distinct members. -/
theorem exists_mate_of_even_finset_with_prescribed_pair
    [Fintype V] (S : Finset V) (a b : V)
    (heven : Even S.card) (hab : a ≠ b) (haS : a ∈ S) (hbS : b ∈ S) :
    ∃ mate : V → V,
      mate a = b ∧ mate b = a ∧
      (∀ x, x ∈ S → mate x ∈ S) ∧
      (∀ x, x ∈ S → mate (mate x) = x) ∧
      (∀ x, x ∈ S → mate x ≠ x) ∧
      ∀ x, x ∉ S → mate x = x := by
  let R := (S.erase a).erase b
  have hbR : b ∈ S.erase a := Finset.mem_erase.mpr ⟨hab.symm, hbS⟩
  have hcardA : (S.erase a).card = S.card - 1 :=
    Finset.card_erase_of_mem haS
  have hcardB : R.card = (S.erase a).card - 1 := by
    exact Finset.card_erase_of_mem hbR
  obtain ⟨k, hk⟩ := heven
  have hevenR : Even R.card := by
    refine ⟨k - 1, ?_⟩
    omega
  obtain ⟨base, hbaseClosed, hbaseInvol, hbaseFree, hbaseOutside⟩ :=
    exists_mate_of_even_finset R hevenR
  have hclosed : ∀ x ∈ S, x ≠ a → x ≠ b →
      base x ∈ S ∧ base x ≠ a ∧ base x ≠ b := by
    intro x hxS hxa hxb
    have hxR : x ∈ R := by simp [R, hxS, hxa, hxb]
    have hmR := hbaseClosed x hxR
    have hm := Finset.mem_erase.mp hmR
    have hm' := Finset.mem_erase.mp hm.2
    exact ⟨hm'.2, hm'.1, hm.1⟩
  have hspec := prescribePair_spec S base a b hab haS hbS hclosed
    (fun x hxS hxa hxb =>
      hbaseInvol x (by simp [R, hxS, hxa, hxb]))
    (fun x hxS hxa hxb =>
      hbaseFree x (by simp [R, hxS, hxa, hxb]))
  refine ⟨prescribePair base a b, hspec.1, hspec.2.1,
    hspec.2.2.1, hspec.2.2.2.1, hspec.2.2.2.2, ?_⟩
  intro x hxS
  have hxa : x ≠ a := fun h => hxS (h ▸ haS)
  have hxb : x ≠ b := fun h => hxS (h ▸ hbS)
  have hxR : x ∉ R := by
    intro hxR
    exact hxS (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hxR))
  simp [prescribePair, hxa, hxb, hbaseOutside x hxR]

#print axioms prescribePair_spec
#print axioms exists_mate_of_even_finset_with_prescribed_pair

end Erdos85
