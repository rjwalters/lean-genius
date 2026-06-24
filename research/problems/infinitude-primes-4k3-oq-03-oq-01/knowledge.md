# infinitude-primes-4k3-oq-03-oq-01

**Problem**: Infinitely many primes ≡ 1 (mod 3) via the cyclotomic Φ₃ Euclid-style argument.

**Status**: COMPLETED — verified, 0 axioms, 0 sorries.

## Summary

Proved `infinitely_many_primes_1_mod_3 : ∀ n, ∃ p, Nat.Prime p ∧ p > n ∧ p % 3 = 1`
by the cyclotomic Euclid construction `N = Φ₃(3·(n+1)!) = (3·(n+1)!)² + 3·(n+1)! + 1`.
File: `proofs/Proofs/InfinitudePrimes4k3OQ03OQ01.lean` (165 lines, 4 theorems).

## Session 2026-06-23 (Session 1) — FRESH

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Mirrored the architecture of the sibling `InfinitudePrimes4k1.lean` (≡ 1 mod 4 via Φ₄ = x²+1),
  adapting it to Φ₃ = x²+x+1 with the multiplicative-order argument made explicit.
- Key lemma `prime_dvd_phi3_mod_three`: prime p ≠ 3 dividing m²+m+1 ⟹ p ≡ 1 (mod 3).
  Proof: cast to ℤ/p, `linear_combination ((m)-1)*h0` gives m³ = 1; `orderOf_dvd_of_pow_eq_one`
  bounds order by 3; order 1 forces p = 3 (excluded); `ZMod.orderOf_dvd_card_sub_one` gives 3 ∣ p−1.
- Main construction uses m = 3·(n+1)! so 3 ∣ m (forces coprime factor ≠ 3) and (n+1)! ∣ m (forces p > n).
- Built on host (docker down): `LAKE_UNSAFE=1 lake build` with `ulimit -v`, 112 s, mathlib cached.
- `#print axioms`: only propext, Classical.choice, Quot.sound → verified/0-axiom.

### Key Findings
- The factorization (x−1)(x²+x+1) = x³−1 is the entire "cyclotomic" content; in Lean it is a single
  `linear_combination`. The order argument is identical to the Φ₄ case at d=4 vs d=3.
- `ZMod.orderOf_dvd_card_sub_one {a ≠ 0} : orderOf a ∣ p − 1` is the clean Fermat-in-order-form lemma
  (Mathlib.FieldTheory.Finite.Basic), avoiding manual `pow_card_sub_one_eq_one` + `orderOf_dvd_of_pow_eq_one`.
- `ZMod.natCast_zmod_eq_zero_iff_dvd` is deprecated (since 2025-06-30) → use `ZMod.natCast_eq_zero_iff`.

### Files Modified
- proofs/Proofs/InfinitudePrimes4k3OQ03OQ01.lean (new)
- src/data/proofs/infinitude-primes-4k3-oq-03-oq-01/{meta.json, annotations.json} (new)

### Next Steps (follow-up open questions)
- Generalize to a uniform Lean theorem: primes dividing Φ_d(k) with p ∤ d are ≡ 1 (mod d), subsuming
  d = 3 (this file) and d = 4 (InfinitudePrimes4k1) under one cyclotomic argument.
- Formalize the complementary ≡ 2 (mod 3) class via the elementary product argument.
