import Mathlib

/-!
# Diagonals of symmetric difference matrices in characteristic two

The elementary observation here is the abstract obstruction behind the
self-indexed-polarity coefficient model.  If every difference of two rows is
injective and the coefficient array is symmetric, then in an exponent-two
group the diagonal entries are themselves injective.  For equally-sized
finite index and coefficient types, the diagonal therefore takes every value,
including zero.
-/

namespace Erdos85

theorem symmetricDifference_diagonal_injective
    {ι G : Type*} [AddCommGroup G]
    (φ : ι → ι → G)
    (hsymm : ∀ a b, φ a b = φ b a)
    (hcharTwo : ∀ x : G, x + x = 0)
    (hrow : ∀ ⦃a b : ι⦄, a ≠ b →
      Function.Injective (fun c => φ a c - φ b c)) :
    Function.Injective (fun a => φ a a) := by
  intro a b hab
  change φ a a = φ b b at hab
  by_contra hne
  have hvalues := hrow hne (show
      φ a a - φ b a = φ a b - φ b b by
    rw [hsymm b a]
    have hneg (x : G) : -x = x := by
      exact (eq_neg_of_add_eq_zero_left (hcharTwo x)).symm
    simp only [sub_eq_add_neg, hneg, hab]
    exact add_comm _ _)
  exact hne hvalues

theorem exists_diagonal_eq_zero_of_symmetricDifference
    {ι G : Type*} [Fintype ι] [Fintype G] [AddCommGroup G]
    (hcard : Fintype.card ι = Fintype.card G)
    (φ : ι → ι → G)
    (hsymm : ∀ a b, φ a b = φ b a)
    (hcharTwo : ∀ x : G, x + x = 0)
    (hrow : ∀ ⦃a b : ι⦄, a ≠ b →
      Function.Injective (fun c => φ a c - φ b c)) :
    ∃ a, φ a a = 0 := by
  have hinj : Function.Injective (fun a => φ a a) :=
    symmetricDifference_diagonal_injective φ hsymm hcharTwo hrow
  have hbij : Function.Bijective (fun a => φ a a) :=
    (Fintype.bijective_iff_injective_and_card (fun a => φ a a)).2 ⟨hinj, hcard⟩
  have hsurj : Function.Surjective (fun a => φ a a) := hbij.2
  exact hsurj 0

end Erdos85

#print axioms Erdos85.symmetricDifference_diagonal_injective
#print axioms Erdos85.exists_diagonal_eq_zero_of_symmetricDifference
