# infinitude-primes-4k3-oq-03 — Infinitely Many Primes ≡ 1 (mod 4)

## Problem

Prove elementarily that there are infinitely many primes p ≡ 1 (mod 4).

The parent gallery proof `infinitude-primes-4k3` treats the ≡3 case; this OQ asks for the ≡1 case, which requires Fermat/Euler's theory of quadratic residues.

## Status: COMPLETED

Gallery entry `infinitude-primes-4k1` fully answers this OQ.
Lean file: `proofs/Proofs/InfinitudePrimes4k1.lean` (177 lines, 5 theorems, 0 axioms, 0 sorries)

---

## Session 2026-05-03 (Session 1) — Reconciliation (researcher-11)

**Mode**: FRESH
**Outcome**: completed — gallery proof already exists, pool reconciled

### What I Did
- Verified `InfinitudePrimes4k1.lean` (0 sorries, 0 axioms, 5 theorems, 177 lines)
- Verified gallery entry `infinitude-primes-4k1` has `status: "verified"`, `badge: "original"`, complete meta.json
- Updated research JSON `infinitude-primes-4k3-oq-03.json`: fixed leanFiles reference, phase → COMPLETED, filled knowledge fields
- Updated pool: `status → "completed"`

### Key Findings

- **Key lemma** (`prime_dvd_sq_add_one_mod_four`): If odd prime p | k²+1, then p ≡ 1 (mod 4).
  - Proof: k²≡-1 (mod p) → -1 is a square in ZMod p → Euler criterion → p≡1 mod 4
  - Mathlib provides `Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one` in `SumTwoSquares`

- **Construction**: N = (2·(n+1)!)² + 1. This is odd and >1, so has an odd prime factor p.
  - Key lemma gives p ≡ 1 (mod 4)
  - If p ≤ n: p | (n+1)! ⟹ p | N - (2(n+1)!)² = 1, contradicting primality
  - So p > n, giving a new prime ≡ 1 mod 4 beyond any bound

- This proof is the ≡1 analogue of the product-minus-1 argument for ≡3; the ≡1 case requires the quadratic residue theory of -1 (Euler's criterion), while ≡3 is a pure congruence argument.

### Files Modified
- `src/data/research/problems/infinitude-primes-4k3-oq-03.json` (phase, leanFiles, knowledge fields)
- `.lean/state/candidate-pool.json` (status → completed)

### Next Steps
None — proof complete, gallery entry verified.

---

## Prior Notes (Seeker Phase)

- Goal: elementary proof that infinitely many primes p ≡ 1 (mod 4)
- Key construction: N = (2·p₁·...·pₖ)² + 1, which must have a prime factor ≡ 1 mod 4
- Requires: if q | a²+1 then q ≡ 1 mod 4 (key number theory lemma via element order)

- Key lemma: if prime q | a²+1, then q ≡ 1 mod 4
  - a² ≡ -1 (mod q) → a⁴ ≡ 1 (mod q) → ord_q(a) ∈ {1,2,4}
  - Not 1: a ≢ 1 (mod q) since a²≡-1≢0
  - Not 2: a²≡-1≢1 (mod q) for odd q
  - So ord_q(a) = 4, and ord_q(a) | q-1, so 4 | q-1, q ≡ 1 mod 4 ✓
