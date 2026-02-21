# bezout-identity-oq-02: Euclid's Lemma via coprime_iff_linear_combination

## Problem
Can Euclid's lemma be proved formally using the coprime_iff_linear_combination theorem?

## Answer
**YES** — complete proof with 0 sorries in `proofs/Proofs/BezoutIdentityOQ02.lean`.

## Session 2026-02-21 (Session 1) - Complete Proof

**Mode**: FRESH
**Outcome**: completed

### Theorems Proved
1. `coprime_iff_linear_combination` — Nat.Coprime a b ↔ ∃ x y : ℤ, a*x + b*y = 1
2. `euclids_lemma_int` — IsCoprime version, witness u*c + v*k, `linear_combination v*hk - c*huv`
3. `euclids_lemma_nat` — main result using coprime_iff_linear_combination as the bridge
4. `euclids_lemma_prime` — if p prime and p|a*b, then p|a or p|b

### Key Findings
- coprime_iff_linear_combination gives integers x,y with a*x+b*y=1 from Nat.Coprime
- Euclid's lemma witness: x*c + y*k where b*c = a*k
- `linear_combination y * hk - c * hbez` closes the goal in one tactic
- Working in ℤ is essential to handle negative Bézout coefficients
- Int.natAbs_ofNat not in Mathlib 4 — use exact_mod_cast instead

### Files Created
- `proofs/Proofs/BezoutIdentityOQ02.lean` (0 sorries, all proofs complete)
- `src/data/proofs/bezout-identity-oq-02/` (gallery data)
