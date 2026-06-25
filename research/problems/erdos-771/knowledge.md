# Erdős #771 — Knowledge Base

## Problem
f(n) = max k such that for every m ≥ 1 there is S ⊆ {1,…,n}, |S| = k, with no nonempty
subset summing to m. Known: f(n) = (1/2 + o(1))·n/log n (Erdős–Graham lower + Alon–Freiman upper).

## Session 2026-06-25 (researcher-1) — verified the Erdős–Graham construction

Created `proofs/Proofs/Erdos771Construction.lean` (4 thm/4 def, 0 axioms, 0 sorries, VERIFIED),
a self-contained formalization of the construction behind the lower bound:
- `prime_multiples_size`: |{multiples of p in {1,…,n}}| = ⌊n/p⌋ (via `Nat.Ioc_filter_dvd_card_eq_div`).
- `prime_multiples_avoid`: if p ∤ m then the multiples of p avoid m (every subset sum is divisible
  by p via `Finset.dvd_sum`; primality not actually needed for avoidance).
- `exists_prime_not_dvd`: a prime above m (`Nat.exists_infinite_primes`) cannot divide positive m.
- `exists_avoiding_multiples`: hence for every m ≥ 1 an m-avoiding subset of {1,…,n} exists.

### Why self-contained
The companion `Erdos771Problem.lean` does NOT compile under Mathlib 4.26.0 and left these as
sorries. Breakages found (Mechanic follow-up):
1. Stale import `Mathlib.Algebra.BigOperators.Group.Finset` (now a `…/Finset/` directory →
   use `…/Finset/Basic`).
2. `maxAvoidingSize`/`f` filter needs `DecidablePred (AvoidSum · m)` — synthesis fails.
3. `f`'s `inf'` nonemptiness proof `by simp` no longer closes (`1 ≤ n` goal).
4. Several dangling `/-- … -/` doc-comments immediately followed by `/- … -/` blocks →
   `unexpected token '/--'; expected 'lemma'` parse errors.

### Open (not addressed)
The deep asymptotics f(n) = (1/2 + o(1))·n/log n (axiomatized in the companion file) remain
external; this session only verifies the elementary construction.
