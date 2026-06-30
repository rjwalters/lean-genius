# Sum of Two Squares: Full General-n Characterization

**Candidate**: pythagorean-triples-oq-04-oq-01-oq-01
**Status**: completed (verified, 0 sorry / 0 axiom)

## Summary
n is a sum of two squares ⟺ every prime p ≡ 3 (mod 4) divides n to an even power.
Formalized as `sum_two_squares_iff` over ALL primes (clean padicValNat form), built on
Mathlib's `Nat.eq_sq_add_sq_iff` (which uses the `q ∈ n.primeFactors` form).

## Session 2026-06-26 (Session 1) - FRESH

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Surveyed the basel/wilsons/halls pool candidates; found basel-odd-squares and
  wilson-composite-converse are already proven in the gallery (redundant mints) — released them.
- Confirmed Mathlib has the core biconditional `Nat.eq_sq_add_sq_iff` (SumTwoSquares.lean:221)
  and a Decidable instance.
- Wrote `Proofs/PythagoreanTriplesOQ04OQ01OQ01.lean` (14 thm, 0 def, 0 sorry, 0 axiom):
  - `sum_two_squares_iff`: repackaged over all primes p ≡ 3 (mod 4), dropping the primeFactors
    side condition (off-support valuations are 0 = even).
  - `not_sum_two_squares_of_odd_padicValNat`: necessity / odd-power obstruction.
  - `prime_sum_two_squares_iff`: Fermat prime case recovered (valuation of p in p is 1).
  - `sum_two_squares_mul`: multiplicative closure (Brahmagupta–Fibonacci, from Mathlib).
  - Witnesses: 21 (≡1 mod4, NOT a sum), 441=21² (IS), 9, 45 (IS), 147 (NOT) — no native_decide.

### Key Findings
- The headline pedagogical point: 21 ≡ 1 (mod 4) so the mod-4 obstruction
  (fermat-two-squares-oq-05) is silent, yet 21 = 3·7 is not a sum of two squares.
  The general criterion strictly refines the elementary one on composites.
- padicValNat computed by hand via `padicValNat.mul` + `.self` + `.eq_zero_of_not_dvd`.

### Honest provenance
Core analytic content is Mathlib's. Contribution = clean all-primes repackaging,
obstruction corollary, prime-case recovery, worked composite witnesses, gallery entry.

### Files Modified
- proofs/Proofs/PythagoreanTriplesOQ04OQ01OQ01.lean
- src/data/proofs/pythagorean-triples-oq-04-oq-01-oq-01/{meta,annotations}.json

### Next Steps
- Possible follow-ups: x²+2y² / x²+3y² genus-theory criteria; density of sums of two squares.
