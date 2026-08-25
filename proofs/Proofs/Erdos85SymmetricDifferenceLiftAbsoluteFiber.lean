import Proofs.Erdos85SymmetricDifferenceDiagonal

/-!
# The absolute fibre in a symmetric difference lift

The coefficient-grid construction lifts an array `φ` to a relation on pairs:

`(a,b) ~ (c,d) ↔ d = b + φ a c`.

The abstract diagonal theorem shows that a symmetric characteristic-two
difference array necessarily has one zero diagonal entry.  This file records
the graph-facing consequence: the lifted relation is reflexive on exactly one
entire fibre, and therefore cannot be loopless.
-/

namespace Erdos85

/-- The relation on the coefficient grid lifted from a difference array. -/
def symmetricDifferenceLift
    {ι G : Type*} [AddCommGroup G]
    (φ : ι → ι → G) (x y : ι × G) : Prop :=
  y.2 = x.2 + φ x.1 y.1

/-- A symmetric characteristic-two difference lift has exactly one absolute
first coordinate: its self-related vertices are one full coefficient fibre. -/
theorem symmetricDifferenceLift_absolute_fiber
    {ι G : Type*} [Fintype ι] [Fintype G] [AddCommGroup G]
    (hcard : Fintype.card ι = Fintype.card G)
    (φ : ι → ι → G)
    (hsymm : ∀ a b, φ a b = φ b a)
    (hcharTwo : ∀ x : G, x + x = 0)
    (hrow : ∀ ⦃a b : ι⦄, a ≠ b →
      Function.Injective (fun c => φ a c - φ b c)) :
    ∃ a,
      (∀ b, symmetricDifferenceLift φ (a, b) (a, b)) ∧
      ∀ x, symmetricDifferenceLift φ x x ↔ x.1 = a := by
  obtain ⟨a, ha⟩ := exists_diagonal_eq_zero_of_symmetricDifference
    hcard φ hsymm hcharTwo hrow
  have hinj : Function.Injective (fun i => φ i i) :=
    symmetricDifference_diagonal_injective φ hsymm hcharTwo hrow
  refine ⟨a, ?_, ?_⟩
  · intro b
    simp [symmetricDifferenceLift, ha]
  · intro x
    constructor
    · intro hx
      have hxzero : φ x.1 x.1 = 0 := by
        simpa [symmetricDifferenceLift] using hx
      exact hinj (hxzero.trans ha.symm)
    · intro hx
      subst hx
      simp [symmetricDifferenceLift, ha]

end Erdos85

#print axioms Erdos85.symmetricDifferenceLift_absolute_fiber
