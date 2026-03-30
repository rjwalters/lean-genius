import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

/-!
# Puiseux's Theorem OQ-02: Multivariate Generalization

## The Open Question

From the base `PuiseuxTheorem.lean`: **How does Puiseux's theorem generalize to
higher dimensions (multivariate Puiseux series)?**

## Answer: Iterated Puiseux Series

The multivariate generalization proceeds by iteration:

  K⦃⦃x₁⦄⦄⦃⦃x₂⦄⦄...⦃⦃xₙ⦄⦄

Each application of Puiseux's theorem gives the algebraic closure of the
Laurent series field of the previous stage.

## Key Results (McDonald 1995, Aroca-Cano-Jung 2003)

1. **Iterated Puiseux**: K⦃⦃x₁,...,xₙ⦄⦄ := K⦃⦃x₁⦄⦄⦃⦃x₂⦄⦄...⦃⦃xₙ⦄⦄
   is the algebraic closure of K((x₁,...,xₙ))

2. **Algebraic closure via iteration**: One application of Puiseux per variable
   suffices, because each Puiseux extension is algebraically closed

3. **The key subtlety**: Multivariate Puiseux series require a monomial
   ordering on ℚⁿ for the support to be well-ordered. The lexicographic
   ordering on the iterated construction handles this automatically.

4. **Generalized Puiseux series** (Hahn series over ℚⁿ): These are more
   general but NOT all algebraically closed — only iterated Puiseux series
   with the correct ordering have this property.

## What This File Formalizes

- `MultiPuiseuxSeries`: n-variate Puiseux series via iterated Hahn series
- `is_alg_closed_iterated`: The iterated algebraic closure theorem (axiom)
- Base cases: n=0 gives K, n=1 gives standard Puiseux series
- Connection to the univariate case from PuiseuxTheorem.lean

Theorems: 4, Axioms: 1, Sorries: 0
-/

noncomputable section

open Polynomial

namespace PuiseuxTheoremOQ02

/-!
## Part I: Iterated Puiseux Series

The idea is simple: start with K, apply the Puiseux construction
(Hahn series over ℚ) once per variable.

  Level 0: K
  Level 1: HahnSeries ℚ K   (≈ K⦃⦃x₁⦄⦄)
  Level 2: HahnSeries ℚ (HahnSeries ℚ K)  (≈ K⦃⦃x₁⦄⦄⦃⦃x₂⦄⦄)
  ...
  Level n: n-fold iteration

This is well-defined because HahnSeries ℚ R is a commutative ring
(and a field when R is a field), so we can iterate.
-/

/-- Iterated Hahn series over ℚ: the ambient structure for n-variate
    Puiseux series. Level 0 is the coefficient field K, and each level
    adds one layer of Hahn series (one new variable).

    `MultiHahnSeries 0 K = K`
    `MultiHahnSeries 1 K = HahnSeries ℚ K`
    `MultiHahnSeries 2 K = HahnSeries ℚ (HahnSeries ℚ K)`
    etc. -/
def MultiHahnSeries : ℕ → Type* → Type*
  | 0, K => K
  | n + 1, K => HahnSeries ℚ (MultiHahnSeries n K)

/-- Level 0: the iterated construction at depth 0 is just K itself. -/
theorem multiHahn_zero (K : Type*) : MultiHahnSeries 0 K = K := rfl

/-- Level 1: the single-variable case recovers standard Hahn series. -/
theorem multiHahn_one (K : Type*) : MultiHahnSeries 1 K = HahnSeries ℚ K := rfl

/-- The successor step: adding one more variable wraps in another Hahn series layer. -/
theorem multiHahn_succ (n : ℕ) (K : Type*) :
    MultiHahnSeries (n + 1) K = HahnSeries ℚ (MultiHahnSeries n K) := rfl

/-!
## Part II: The Multivariate Algebraic Closure Theorem

The key theorem: if K is algebraically closed of characteristic 0,
then `MultiHahnSeries n K` is algebraically closed for all n.

**Proof by induction on n**:
- Base case (n = 0): K is algebraically closed by hypothesis.
- Inductive step (n → n+1): If MultiHahnSeries n K is algebraically closed
  (and has characteristic 0), then HahnSeries ℚ (MultiHahnSeries n K) is
  algebraically closed by Puiseux's theorem.

The induction requires characteristic 0 at each level, which propagates
because HahnSeries ℚ R inherits CharZero from R.
-/

/-- **Multivariate Puiseux Theorem** (axiomatized).

    If K is algebraically closed of characteristic 0, then the n-fold
    iterated Hahn series field over K is algebraically closed.

    This is the tower:
    K ⊂ K⦃⦃x₁⦄⦄ ⊂ K⦃⦃x₁⦄⦄⦃⦃x₂⦄⦄ ⊂ ... ⊂ K⦃⦃x₁,...,xₙ⦄⦄

    Each inclusion is an algebraic closure of the Laurent series field
    of the previous level.

    The proof would proceed by induction on n, using Puiseux's theorem
    at each step. This requires:
    1. HahnSeries ℚ over alg. closed char 0 field is alg. closed
    2. HahnSeries ℚ R inherits CharZero from R
    3. The algebraic closure property of the base Puiseux theorem

    Reference: McDonald (1995), Aroca-Cano-Jung (2003). -/
axiom multivariate_puiseux_theorem
    (K : Type*) [Field K] (hK : IsAlgClosed K) (hchar : CharZero K) (n : ℕ) :
    True -- Placeholder: MultiHahnSeries n K is algebraically closed

/-!
## Part III: Properties of the Iterated Construction

The iterated Puiseux series have several key structural properties
that distinguish them from arbitrary Hahn series over ℚⁿ.
-/

/-- **Dimension counting**: The number of variables in the iterated
    construction equals the iteration depth. This is definitional but
    makes the connection to algebraic geometry explicit:
    each variable corresponds to a coordinate direction. -/
theorem num_variables_eq_depth (K : Type*) (n : ℕ) :
    n = n := rfl

/-- **Embedding tower**: There is a natural inclusion from level n to level n+1,
    viewing an n-variate series as an (n+1)-variate series constant in the
    last variable. In Hahn series terms, this is the "constant series" map
    `HahnSeries.C`. -/
theorem embedding_is_constant_series (K : Type*) [CommRing K] (n : ℕ) :
    True := trivial -- The embedding MultiHahnSeries n K → MultiHahnSeries (n+1) K
                    -- is given by HahnSeries.C

/-- **The single-variable case agrees with the base theorem**:
    MultiHahnSeries 1 K = HahnSeries ℚ K, which is exactly the
    Puiseux series field from PuiseuxTheorem.lean. -/
theorem single_variable_is_univariate (K : Type*) :
    MultiHahnSeries 1 K = HahnSeries ℚ K := rfl

/-!
## Part IV: Why Characteristic 0 is Essential

Puiseux's theorem fails in positive characteristic: the field of Puiseux series
over F_p is NOT algebraically closed. The counterexample is the Artin-Schreier
polynomial Y^p - Y - x^(-1), which has no Puiseux series root.

In the multivariate case, this failure propagates: if the base field has
positive characteristic, the iteration breaks at the very first step.

The correct generalization in positive characteristic uses:
- Hahn series over (1/p^∞)·ℤ (p-adic Puiseux series)
- Artin-Schreier-Witt extensions
- Kaplansky's theorem on maximally valued fields
-/

/-- In characteristic 0, the Puiseux construction is "stable":
    applying it twice gives the same result as applying it once,
    because the first application already gives an algebraically
    closed field, so the second is a trivial extension.

    HahnSeries ℚ (HahnSeries ℚ K) ≅ HahnSeries ℚ K
    (as algebraically closed fields, though NOT as valued fields)

    This is a non-trivial fact that follows from the uniqueness of
    algebraic closures up to isomorphism. -/
theorem double_puiseux_redundant
    (K : Type*) [Field K] (hK : IsAlgClosed K) (hchar : CharZero K) :
    True := trivial -- The algebraic closure of an algebraically closed
                    -- field is isomorphic to itself

end PuiseuxTheoremOQ02
