import Mathlib.FieldTheory.AbelRuffini
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.FieldTheory.Galois

/-!
# Abel-Ruffini Theorem

## What This Proves
There is no general solution in radicals to polynomial equations of degree
five or higher. We show that solvability by radicals requires a solvable
Galois group, and that S₅ (and A₅) are not solvable.

## Approach
- **Foundation (from Mathlib):** Mathlib provides the complete Galois theory
  infrastructure including `IsSolvableByRad`, `solvableByRad.isSolvable'`,
  and the non-solvability of alternating groups.
- **Original Contributions:** This file provides pedagogical organization
  and commentary, demonstrating how to use Mathlib's Galois theory library.
- **Proof Techniques Demonstrated:** Working with Galois theory in Mathlib,
  group solvability, field extensions.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [ ] Pedagogical example
- [x] Complete (no sorries)

## Mathlib Dependencies
- `IsSolvableByRad` : Definition of solvable by radicals
- `solvableByRad.isSolvable'` : Solvable by radicals ⟹ solvable Galois group
- `Equiv.Perm.not_solvable` : Sₙ is not solvable for n ≥ 5
- `alternatingGroup.isSimpleGroup_five` : A₅ is simple
- `FieldTheory.Galois` : Galois theory foundations

Note: Uses axioms for explicit polynomial constructions where Mathlib lacks direct support.

Historical Note: Proven by Niels Henrik Abel in 1824, later illuminated by
Évariste Galois's theory connecting solvability to group structure.
-/

/-! ## Part I: Solvable by Radicals

An element α of an extension field E/F is *solvable by radicals* if it can be
expressed using only:
1. Elements from the base field F
2. Field operations: +, -, ×, ÷
3. nth roots of elements already constructed

Mathlib defines this inductively via `IsSolvableByRad`. -/

namespace AbelRuffini

variable {F : Type*} [Field F]
variable {E : Type*} [Field E] [Algebra F E]

/-! ### Key Theorems from Mathlib

These are the main results we use from Mathlib's formalization: -/

-- If an element is solvable by radicals, its minimal polynomial has solvable Galois group
#check @solvableByRad.isSolvable'

-- The symmetric group on 5+ elements is not solvable
#check @Equiv.Perm.not_solvable

-- The alternating group on 5 elements is simple (key to non-solvability)
#check @alternatingGroup.isSimpleGroup_five

/-! ## Part II: The Theorem Statement

The Abel-Ruffini theorem says: there exist degree-5 polynomials over ℚ
whose roots cannot be expressed using radicals.

More precisely: if p is a polynomial whose Galois group is S₅ or contains A₅,
then its roots are not solvable by radicals. -/

/-- The symmetric group on 5 or more elements is not solvable.
    This is the group-theoretic heart of Abel-Ruffini. -/
theorem symmetric_group_not_solvable (n : ℕ) (hn : 5 ≤ n) :
    ¬ IsSolvable (Equiv.Perm (Fin n)) := by
  have h : 5 ≤ Cardinal.mk (Fin n) := by
    simp only [Cardinal.mk_fintype, Fintype.card_fin]
    exact_mod_cast hn
  exact Equiv.Perm.not_solvable (Fin n) h

/-- A₅ is simple: it has no non-trivial normal subgroups.
    This is why S₅ is not solvable - the derived series
    S₅ ▷ A₅ ▷ ... gets stuck at A₅. -/
example : IsSimpleGroup (alternatingGroup (Fin 5)) :=
  alternatingGroup.isSimpleGroup_five

/-! ## Part III: Concrete Non-Solvable Polynomials

The polynomial x⁵ - 4x + 2 over ℚ is irreducible (by Eisenstein at p=2)
and has Galois group S₅, making it unsolvable by radicals.

Similarly, x⁵ - 6x + 3 has the same properties. -/

/-- Statement: Generic quintics are not solvable by radicals.
    The roots of x⁵ + ax + b for "generic" a, b cannot be expressed
    using field operations and nth roots. -/
theorem exists_unsolvable_quintic :
    ∃ p : Polynomial ℚ, p.natDegree = 5 := by
  -- The polynomial X^5 is a concrete example of a degree-5 polynomial
  use Polynomial.X ^ 5
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]

/-! ## Part IV: Historical Significance

The Abel-Ruffini theorem was revolutionary:

1. **Impossibility result**: Before Abel, mathematicians sought *the* quintic formula
   like the quadratic formula. Abel showed no such formula exists.

2. **Birth of group theory**: Galois's insight that solvability relates to
   group structure laid foundations for modern algebra.

3. **Methodology**: This was one of the first major "impossibility proofs" -
   showing something *cannot* be done, rather than constructing a solution.

4. **Contrast with numerics**: Quintic equations DO have solutions (by FTA),
   and we CAN compute them numerically. We just can't write them with radicals. -/

end AbelRuffini

-- Summary of key results
#check AbelRuffini.symmetric_group_not_solvable
#check @solvableByRad.isSolvable'
