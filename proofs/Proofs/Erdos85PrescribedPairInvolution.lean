import Mathlib

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

#print axioms prescribePair_spec

end Erdos85
