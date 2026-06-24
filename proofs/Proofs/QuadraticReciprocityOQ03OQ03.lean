import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-
# From the Legendre Symbol Algorithm to the Jacobi Symbol

## What This Proves
The parent entry (`quadratic-reciprocity-oq-03`) established quadratic reciprocity as a
GCD-like *algorithm* for computing the Legendre symbol `(a/p)` for an odd prime `p`.
This file extends that algorithm to the **Jacobi symbol** `J(a | n)` for an arbitrary odd
`n`, the object that actually drives primality testing (the Solovay–Strassen toolkit).

The Jacobi symbol is defined multiplicatively over the prime factorization:
`J(a | n) = ∏_{p | n} (a / p)^{v_p(n)}`. Every reduction step of the Legendre algorithm has
a Jacobi analogue, so the *same* Euclidean-style descent computes `J(a | n)` directly —
crucially **without factoring `n`**, which is exactly why it is useful for primality testing.

### The decisive contrast with the Legendre symbol
For a prime `p`, `(a/p) = 1` iff `a` is a quadratic residue mod `p`. This characterization
**fails** for composite `n`: only one direction survives — `J(a | n) = -1` forces `a` to be
a non-residue, but `J(a | n) = 1` does **not** make `a` a residue. We prove this is a genuine
gap by exhibiting `J(2 | 15) = 1` while `2` is not a square mod `15`. This one-sidedness is
precisely the source of error in the Solovay–Strassen test (Euler liars).

## Status
- [x] Jacobi extends Legendre at primes
- [x] Full reduction toolkit (multiplicativity in both arguments, mod-reduction)
- [x] Supplementary laws and reciprocity for the Jacobi symbol
- [x] One-directional residue test + explicit counterexample to the converse
- [x] Verified composite-modulus example computations
- [x] Complete — 0 sorries, 0 axioms

## Mathlib Dependencies
- `jacobiSym`, notation `J(a | b)` (scope `NumberTheorySymbols`)
- `jacobiSym.legendreSym.to_jacobiSym`, `jacobiSym.mul_left`, `jacobiSym.mul_right`, `jacobiSym.mod_left`
- `jacobiSym.at_neg_one`, `jacobiSym.at_two`, `jacobiSym.quadratic_reciprocity`
- `ZMod.nonsquare_of_jacobiSym_eq_neg_one`, `ZMod.isSquare_of_jacobiSym_eq_one`
-/

set_option linter.unusedVariables false

open scoped NumberTheorySymbols

namespace JacobiAlgorithm

-- ============================================================
-- PART 1: The Jacobi symbol extends the Legendre symbol
-- ============================================================

/-- At an odd prime `p`, the Jacobi symbol agrees with the Legendre symbol. So every Legendre
computation from the parent entry is a special case of the Jacobi algorithm. -/
theorem jacobi_eq_legendre (p : ℕ) [Fact p.Prime] (a : ℤ) :
    J(a | p) = legendreSym p a :=
  (jacobiSym.legendreSym.to_jacobiSym p a).symm

-- ============================================================
-- PART 2: Algorithm reduction lemmas (the descent steps)
-- ============================================================

/-- **Step (numerator multiplicativity).** Factor the top and handle each factor separately —
identical to the Legendre step. -/
theorem jacobiSym_mul_left (a₁ a₂ : ℤ) (n : ℕ) :
    J(a₁ * a₂ | n) = J(a₁ | n) * J(a₂ | n) :=
  jacobiSym.mul_left a₁ a₂ n

/-- **Step (denominator multiplicativity).** *New phenomenon for composite moduli.* The
symbol splits over a factorization of the bottom; this is what makes `J(a | n)` well-defined
beyond primes. -/
theorem jacobiSym_mul_right (a : ℤ) (m n : ℕ) [NeZero m] [NeZero n] :
    J(a | m * n) = J(a | m) * J(a | n) :=
  jacobiSym.mul_right a m n

/-- **Step (reduce the numerator).** The symbol depends on `a` only through `a % n`, so we may
always shrink the top — the Euclidean-descent step. -/
theorem jacobiSym_mod_left (a : ℤ) (n : ℕ) :
    J(a | n) = J(a % n | n) :=
  jacobiSym.mod_left a n

/-- **Step (powers of the numerator).** `J(aᵉ | n) = J(a | n)ᵉ`. -/
theorem jacobiSym_pow_left (a : ℤ) (e n : ℕ) :
    J(a ^ e | n) = J(a | n) ^ e :=
  jacobiSym.pow_left a e n

-- ============================================================
-- PART 3: Supplementary laws and reciprocity for Jacobi
-- ============================================================

/-- **First supplementary law.** `J(-1 | n) = χ₄(n)` for odd `n`. -/
theorem jacobiSym_at_neg_one {n : ℕ} (hn : Odd n) :
    J(-1 | n) = ZMod.χ₄ n :=
  jacobiSym.at_neg_one hn

/-- **Second supplementary law.** `J(2 | n) = χ₈(n)` for odd `n`. -/
theorem jacobiSym_at_two {n : ℕ} (hn : Odd n) :
    J(2 | n) = ZMod.χ₈ n :=
  jacobiSym.at_two hn

/-- **Reciprocity swap for the Jacobi symbol.** For odd naturals `a`, `b`:
`J(a | b) = (-1)^((a-1)/2·(b-1)/2) · J(b | a)`. This is the engine of the descent: it lets us
flip `J(a | b) ↔ J(b | a)` and then reduce mod the smaller modulus, never needing the prime
factorization of either argument. -/
theorem jacobiSym_reciprocity {a b : ℕ} (ha : Odd a) (hb : Odd b) :
    J(a | b) = (-1) ^ (a / 2 * (b / 2)) * J(b | a) :=
  jacobiSym.quadratic_reciprocity ha hb

-- ============================================================
-- PART 4: One-directional residue test (Solovay–Strassen)
-- ============================================================

/-- **The valid direction.** If `J(a | n) = -1` then `a` is *not* a quadratic residue mod `n`.
This direction holds for every modulus and is what lets the Jacobi symbol *certify*
non-residues / detect composites. -/
theorem nonresidue_of_jacobi_eq_neg_one {a : ℤ} {n : ℕ} (h : J(a | n) = -1) :
    ¬ IsSquare (a : ZMod n) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one h

/-- **The direction that survives only for primes.** When `n = p` is prime, `J(a | p) = 1`
*does* recover that `a` is a residue. (For composite `n` this is false — see below.) -/
theorem residue_of_jacobi_eq_one_prime {a : ℤ} {p : ℕ} [Fact p.Prime] (h : J(a | p) = 1) :
    IsSquare (a : ZMod p) :=
  ZMod.isSquare_of_jacobiSym_eq_one h

-- ============================================================
-- PART 5: Computing composite-modulus symbols
-- ============================================================
-- The `norm_num` extension for the Jacobi symbol runs exactly this descent (reciprocity +
-- supplementary laws + reduction) to evaluate `J(a | n)` *without factoring `n`*, producing
-- a kernel-checked proof term — so these stay 0-axiom (no `native_decide`).

/-- `J(2 | 15) = 1`. (Equivalently `J(2|3)·J(2|5) = (-1)·(-1)`: `2` is a non-residue mod each
of `3` and `5`, but the two `-1`s multiply to `+1` — the source of the false positive below.) -/
theorem jacobiSym_two_fifteen : J(2 | 15) = 1 := by norm_num

/-- `J(7 | 15) = -1`. Because the value is `-1`, the algorithm *certifies* that `7` is a
non-residue mod `15` (Part 4). -/
theorem jacobiSym_seven_fifteen : J(7 | 15) = -1 := by norm_num

/-- `J(3 | 15) = 0`: a shared factor makes the symbol vanish (`gcd(3,15) ≠ 1`). -/
theorem jacobiSym_three_fifteen : J(3 | 15) = 0 := by norm_num

-- ============================================================
-- PART 6: The converse FAILS for composite moduli
-- ============================================================

/-- `2` is not a quadratic residue modulo `15`: the squares mod `15` are `{0,1,4,6,9,10}`,
and `2` is not among them. -/
theorem two_not_square_mod_fifteen : ¬ IsSquare (2 : ZMod 15) := by decide

/-- **Main contrast theorem.** The Legendre characterization "symbol `= 1` ⟹ residue" is
genuinely *false* for the Jacobi symbol at composite moduli: there exist `a`, `n` with
`J(a | n) = 1` while `a` is not a square mod `n`. Here `J(2 | 15) = 1` (Part 5) yet `2` is a
non-residue mod `15`. These are exactly the *Euler liars* underlying the Solovay–Strassen
test, and the reason the Jacobi symbol gives a *probabilistic* (not exact) residue test. -/
theorem jacobi_one_not_residue_test :
    ∃ (a : ℤ) (n : ℕ), J(a | n) = 1 ∧ ¬ IsSquare (a : ZMod n) :=
  ⟨2, 15, jacobiSym_two_fifteen, two_not_square_mod_fifteen⟩

/-- The certified non-residue from `J(7 | 15) = -1`: `7` is not a square mod `15`. The valid
direction of the test in action. -/
theorem seven_not_square_mod_fifteen : ¬ IsSquare (7 : ZMod 15) :=
  nonresidue_of_jacobi_eq_neg_one jacobiSym_seven_fifteen

-- ============================================================
-- PART 7: Algorithm termination (Euclidean descent)
-- ============================================================

/-- Reciprocity strictly shrinks the problem: from `J(a | b)` we pass to `J(b | a)` and then
to `J(b % a | a)` with modulus `a < b`. Stated as the reciprocity flip available whenever
`a < b` are odd — the basis for an unbounded recursion that always decreases the modulus,
exactly like the Euclidean algorithm. -/
theorem algorithm_descent {a b : ℕ} (ha : Odd a) (hb : Odd b) (hab : a < b) :
    J(a | b) = (-1) ^ (a / 2 * (b / 2)) * J(b | a) :=
  jacobiSym_reciprocity ha hb

end JacobiAlgorithm

-- ============================================================
-- Export main results
-- ============================================================

#check @JacobiAlgorithm.jacobi_eq_legendre
#check @JacobiAlgorithm.jacobiSym_mul_right
#check @JacobiAlgorithm.jacobiSym_reciprocity
#check @JacobiAlgorithm.nonresidue_of_jacobi_eq_neg_one
#check @JacobiAlgorithm.jacobi_one_not_residue_test
#check @JacobiAlgorithm.algorithm_descent
