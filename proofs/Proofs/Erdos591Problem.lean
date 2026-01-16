/-
Erdős Problem #591: Ordinal Ramsey Theory for ω^(ω²)

Let α = ω^(ω²). Is it true that in any red/blue coloring of the edges
of the complete graph K_α, there is either a red K_α or a blue K_3?

**Status**: OPEN (Prize: $250)

**Background**:
- Specker (1957) proved this holds for α = ω² but fails for α = ω^n when 3 ≤ n < ω
- Chang proved it holds for α = ω^ω (see Problem 590)
- The case α = ω^(ω²) remains open

This is an ordinal partition relation problem, written in arrow notation as:
  ω^(ω²) → (ω^(ω²), 3)²

Reference: https://erdosproblems.com/591
Sources: [Sp57] Specker, Teilmengen von Mengen mit Relationen (1957)
         [Er82e], [Er87] Erdős collections
-/

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Ordinal.Exponential

open Ordinal

namespace Erdos591

/-!
## Ordinal Ramsey Theory Background

Ramsey theory studies when structure must appear in sufficiently large systems.
The classical Ramsey theorem says: for any 2-coloring of edges of a sufficiently
large complete graph, there exists a monochromatic clique of prescribed size.

**Ordinal Ramsey theory** extends this to infinite ordinals. The question is:
for which ordinals α does every 2-coloring of K_α contain either a
monochromatic K_α (of the first color) or a K_n (of the second color)?

The arrow notation α → (α, n)² means: for any 2-coloring of pairs from α,
there exists either a subset of order type α with all pairs of color 1,
or a subset of size n with all pairs of color 2.
-/

/--
The ordinal Ramsey property α → (α, n)²: every 2-coloring of pairs from α
contains either a monochromatic subset of order type α (color 1) or
a monochromatic subset of size n (color 2).

This is axiomatized as a predicate on ordinals. The formal definition
involves coloring functions on the type of pairs, order embeddings,
and finite subsets - details beyond our current scope.
-/
axiom OrdinalRamseyProperty (α : Ordinal.{0}) (n : ℕ) : Prop

/-!
## Known Results

The following results establish the boundary of what we know:
-/

/--
Specker's theorem (1957): The ordinal Ramsey property holds for α = ω².
That is, ω² → (ω², 3)².

Specker showed that any 2-coloring of pairs from ω² must contain either
a red copy of ω² or a blue triangle.
-/
axiom specker_omega_squared :
    OrdinalRamseyProperty (ω ^ 2) 3

/--
Specker also showed the property FAILS for α = ω^n when 3 ≤ n < ω.
There exist colorings of K_{ω^n} with no red K_{ω^n} and no blue K_3.

This is surprising: larger ordinals can actually have WORSE Ramsey properties!
The gap between ω² (works) and ω³ (fails) is remarkable.
-/
axiom specker_omega_power_n_fails (n : ℕ) (hn : 3 ≤ n) :
    ¬ OrdinalRamseyProperty (ω ^ n) 3

/--
Chang's theorem: The property holds for α = ω^ω.
This is Erdős Problem 590.

Despite ω³, ω⁴, ... all failing, the limit ordinal ω^ω works again!
-/
axiom chang_omega_omega :
    OrdinalRamseyProperty (ω ^ ω) 3

/-!
## The Open Problem

The question for α = ω^(ω²) lies between the known cases.
We have:
- ω² works (Specker)
- ω^n fails for finite n ≥ 3 (Specker)
- ω^ω works (Chang)
- ω^(ω²) = ? (This problem)

The pattern is tantalizing but incomplete. Does the property hold
for all ordinals of the form ω^β where β is a limit ordinal?
-/

/--
**OPEN PROBLEM (Erdős Problem #591, Prize: $250)**:

Does the ordinal Ramsey property hold for α = ω^(ω²)?
That is, does ω^(ω²) → (ω^(ω²), 3)² ?

The answer is unknown as of 2024.
-/
def erdos_591_conjecture : Prop :=
  OrdinalRamseyProperty (ω ^ (ω ^ 2)) 3

/--
Note: The conjecture `erdos_591_conjecture` is OPEN.
Erdős offered $250 for its resolution.
-/
theorem erdos_591_is_open : True := trivial

/-!
## The Ordinal Hierarchy

To understand the problem, we need to understand the ordinals involved.
The ordinal ω is the order type of the natural numbers.
-/

/--
ω² = ω · ω is the order type of ℕ × ℕ under lexicographic ordering.
It looks like ω copies of ω arranged in sequence:
  0, 1, 2, ..., ω, ω+1, ω+2, ..., ω·2, ω·2+1, ...
-/
theorem omega_squared_eq_mul : ω ^ 2 = ω * ω := pow_two ω

/--
ω³ = ω · ω · ω is even larger - ω copies of ω².
-/
theorem omega_cubed_eq : ω ^ 3 = ω * ω * ω := by
  rw [pow_succ, pow_two]

/--
ω^ω is the supremum of all ω^n for finite n.
It's the first ordinal that cannot be reached by finite exponentiation from ω.
-/
theorem omega_to_omega_positive : 0 < ω ^ ω := by
  apply Ordinal.opow_pos
  exact Ordinal.omega0_pos

/--
ω^(ω²) = ω^(ω·ω) is vastly larger than ω^ω.
It's ω^ω · ω^ω · ... (ω times), then that whole thing ω times, etc.
-/
theorem omega_omega_squared_positive : 0 < ω ^ (ω ^ 2) := by
  apply Ordinal.opow_pos
  exact Ordinal.omega0_pos

/--
ω^(ω²) is expressed in terms of ordinal exponentiation.
-/
theorem omega_omega_squared_form : ω ^ (ω ^ 2) = ω ^ (ω * ω) := by
  rw [pow_two]

/-!
## Understanding the Pattern

The Ramsey property α → (α, 3)² exhibits a surprising pattern:

| Ordinal α | Property holds? | Reference |
|-----------|----------------|-----------|
| ω         | Yes            | Trivial   |
| ω²        | Yes            | Specker   |
| ω³        | No             | Specker   |
| ω⁴        | No             | Specker   |
| ...       | No             | Specker   |
| ω^n (n≥3) | No             | Specker   |
| ω^ω       | Yes            | Chang     |
| ω^(ω²)    | ?              | OPEN      |

The pattern suggests that "limit" ordinal exponents (like ω, ω²) might
restore the Ramsey property that fails for successor ordinal exponents.
-/

end Erdos591
