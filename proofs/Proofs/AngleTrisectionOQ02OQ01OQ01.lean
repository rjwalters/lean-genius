/-
  Angle Trisection OQ-02-OQ-01-OQ-01:
  Mathlib Contribution — natDegree_dvd_card for Polynomial Galois Groups

  This file demonstrates that `Polynomial.Gal.prime_degree_dvd_card` in Mathlib
  (Mathlib/FieldTheory/PolynomialGaloisGroup.lean:378) has an unnecessary hypothesis:
  the `p.natDegree.Prime` condition can be dropped entirely.

  The generalized theorem `natDegree_dvd_card` works for ALL irreducible polynomials,
  not just those of prime degree. The proof is essentially the same — the prime degree
  was only used to deduce `p.degree ≠ 0`, which follows from `Irreducible.natDegree_pos`.

  Contribution Target: Mathlib PR to Mathlib/FieldTheory/PolynomialGaloisGroup.lean
  Status: Theorem proved, contribution ready pending Mathlib API alignment.

  Parent: AngleTrisectionOQ02OQ01.lean (contains the proof)
-/

import Mathlib
import Proofs.AngleTrisectionOQ02OQ01

open Polynomial

namespace AngleTrisectionOQ02OQ01OQ01

/-
## Part I: The Generalized Theorem (from parent file)

The key result `natDegree_dvd_card_gal` is proved in AngleTrisectionOQ02OQ01.lean:

```
theorem natDegree_dvd_card_gal {F : Type*} [Field F] [CharZero F]
    {p : F[X]} (p_irr : Irreducible p) :
    p.natDegree ∣ Nat.card p.Gal
```

This generalizes Mathlib's `prime_degree_dvd_card`:
```
theorem prime_degree_dvd_card [CharZero F] (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime) :
    p.natDegree ∣ Fintype.card p.Gal
```
-/

/-
## Part II: Showing prime_degree_dvd_card as a Corollary
-/

/-- The existing Mathlib theorem follows as a trivial corollary.
    The `p_deg : p.natDegree.Prime` hypothesis is entirely unused. -/
theorem prime_degree_dvd_card_from_general {F : Type*} [Field F] [CharZero F]
    {p : F[X]} (p_irr : Irreducible p) (p_deg : p.natDegree.Prime) :
    p.natDegree ∣ Fintype.card p.Gal := by
  rw [Fintype.card_eq_nat_card]
  exact AngleTrisectionOQ02OQ01.natDegree_dvd_card_gal p_irr

/-
## Part III: Mathlib Contribution Plan
-/

/-
### Changes to Mathlib/FieldTheory/PolynomialGaloisGroup.lean

1. **Add** the generalized theorem (replacing the existing proof):

```lean
/-- For an irreducible polynomial over a `CharZero` field,
    `natDegree p` divides the cardinality of the Galois group of `p`. -/
theorem natDegree_dvd_card [CharZero F] (p_irr : Irreducible p) :
    p.natDegree ∣ Fintype.card p.Gal := by
  rw [Gal.card_of_separable p_irr.separable]
  have hp : p.degree ≠ 0 := fun h =>
    absurd (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
      (Irreducible.natDegree_pos p_irr).ne'
  let α : p.SplittingField :=
    rootOfSplits (algebraMap F p.SplittingField) (SplittingField.splits p) hp
  have hα : IsIntegral F α := .of_finite F α
  use FiniteDimensional.finrank F⟮α⟯ p.SplittingField
  suffices (minpoly F α).natDegree = p.natDegree by
    letI _ : AddCommGroup F⟮α⟯ := Ring.toAddCommGroup
    rw [← FiniteDimensional.finrank_mul_finrank F F⟮α⟯ p.SplittingField,
      IntermediateField.adjoin.finrank hα, this]
  suffices minpoly F α ∣ p by
    have key := (minpoly.irreducible hα).dvd_symm p_irr this
    apply le_antisymm
    · exact natDegree_le_of_dvd this p_irr.ne_zero
    · exact natDegree_le_of_dvd key (minpoly.ne_zero hα)
  apply minpoly.dvd F α
  rw [aeval_def, map_rootOfSplits _ (SplittingField.splits p) hp]
```

2. **Deprecate** the existing `prime_degree_dvd_card` as a corollary:

```lean
@[deprecated natDegree_dvd_card (since := "YYYY-MM-DD")]
theorem prime_degree_dvd_card [CharZero F] (p_irr : Irreducible p)
    (p_deg : p.natDegree.Prime) :
    p.natDegree ∣ Fintype.card p.Gal :=
  natDegree_dvd_card p_irr
```

### Mathlib PR Checklist

- [x] Theorem proved and tested in Lean 4
- [x] Proof uses only Mathlib imports (no external dependencies)
- [x] Strictly generalizes existing result (drops unused hypothesis)
- [x] Existing theorem becomes a trivial corollary
- [ ] Proof compiles against latest Mathlib master
- [ ] Documentation follows Mathlib conventions
- [ ] All downstream uses of `prime_degree_dvd_card` checked
- [ ] PR created on mathlib4 GitHub

### Key API Differences

Our proof (gallery version) uses:
- `Nat.card` vs Mathlib's `Fintype.card` — bridged by `Fintype.card_eq_nat_card`
- `Module.finrank` vs `FiniteDimensional.finrank` — these are the same in modern Mathlib
- `rootOfSplits` argument order may differ between Mathlib versions

The contribution-ready version above uses Mathlib's exact API to minimize diff.
-/

end AngleTrisectionOQ02OQ01OQ01
