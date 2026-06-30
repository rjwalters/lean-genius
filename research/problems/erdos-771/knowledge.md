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

## Session 2026-06-25 (researcher-9) — quantitative bound via Bertrand

Extended `Erdos771Construction.lean` (now 6 thm/4 def, 0 axioms, 0 sorries, VERIFIED) with a
quantitative strengthening of `exists_avoiding_multiples`:
- `prime_gt_not_dvd`: a prime `p > m ≥ 1` cannot divide `m` (else `p ≤ m` by `Nat.le_of_dvd`).
- `exists_avoiding_multiples_quantitative`: via Bertrand's postulate
  (`Nat.exists_prime_lt_and_le_two_mul`), for every `m ≥ 1` there is a prime `m < p ≤ 2m`,
  giving an `m`-avoiding subset of `{1,…,n}` of size `⌊n/p⌋ ≥ ⌊n/(2m)⌋`. Size bound via
  `Nat.div_le_div_left hp2m hp.pos` (Nat division is antitone in the denominator).

### Why this matters
The bare existence used *some* prime `> m`, possibly enormous (least prime ∤ `m = lcm{2,…,t}`
grows with `t`), so `⌊n/p⌋` could be tiny. Bertrand pins the prime to within a factor of two
of `m`, turning existence into an explicit size lower bound.

### Still open
The per-m bound `⌊n/(2m)⌋` weakens as `m` grows; the n/log n lower bound needs a
uniform-over-all-m argument (primes near log n) not formalized here. Asymptotics remain external.

### Gotchas
- Docker down → offline typecheck with `LAKE_UNSAFE=1 elan run leanprover/lean4:v4.26.0 lake env
  lean Proofs/Erdos771Construction.lean`. Main repo's shared `.lake` had a CORRUPT
  `Mathlib/Data/Nat/Bits.olean.private` (invalid header) → typechecked in a sibling worktree
  (`r8-picard`) with an intact Mathlib build instead.
- `Nat.div_le_div_left (h : a ≤ b) (hpos : 0 < a) : k / b ≤ k / a` — args are the *smaller*
  denominator's `≤` and positivity.
