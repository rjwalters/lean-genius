# Problem: Mersenne Prime Distribution (LPW Conjecture)
**ID**: perfect-numbers-oq-03
**Phase**: COMPLETED
**Status**: All provable sorries eliminated; LPW conjecture remains open

## Problem Statement

**Formal**: #{p ≤ N : p prime, 2^p-1 prime} ~ (e^γ / log 2) · log log N

**Tractability**: The LPW conjecture is wide open. However, supporting theorems are provable.

## Session 2026-04-13 (Session 2) — Prove Mersenne Necessity + Factor Congruence

**Mode**: FRESH (RICH knowledge, priority)
**Outcome**: completed — all 3 sorries proved

### What I Did

1. **mersenne_prime_exp_prime** (Mersenne necessity): Rewrote the broken proof skeleton.
   - Handle n=0,1 via `rcases n with _ | _ | _` + `simp [M]`/`norm_num [M]`
   - For n≥2, not prime: `Nat.exists_prime_and_dvd` gives prime factor a
   - Show a < n: if a = n then n is prime, contradicting hypothesis
   - `mersenne_dvd_of_dvd ha_dvd` gives M(a)|M(n)
   - 1 < M(a): since a prime (a≥2), 2^a≥4, M(a)=2^a-1≥3
   - M(a) < M(n): `Nat.pow_lt_pow_right` + omega
   - Contradiction via `hM.eq_one_or_self_of_dvd` + omega

2. **factor_cong_one_mod_p** (q|2^p-1 → p|q-1):
   - Show (2:ZMod q)≠0: q|2 would mean q=2 (by le_antisymm), but 2|2^p and 2|(2^p-(2^p-1))=1, contradiction
   - Convert q|2^p-1 to (2:ZMod q)^p=1: via `Nat.cast_sub hp1`, `Nat.cast_pow`, `Nat.cast_ofNat`, `Nat.cast_one`, `sub_eq_zero.mp`
   - orderOf(2:ZMod q)|p via `orderOf_dvd_of_pow_eq_one`
   - p prime → orderOf=1 or p
   - orderOf=1: `orderOf_eq_one_iff` gives (2:ZMod q)=1, then (1:ZMod q)=2-1=1-1=0, contradicts `one_ne_zero`
   - orderOf=p: Fermat `ZMod.pow_card_sub_one_eq_one` gives (2:ZMod q)^(q-1)=1, so orderOf|q-1

3. Fixed `mersennePrimeCount` definition bug (`.card.filter` → `.filter(...).card`)

### Key Findings
- `orderOf_eq_one_iff` exists in Mathlib4 (confirmed from InverseGaloisA5.lean usage)
- `ZMod.pow_card_sub_one_eq_one` is the Fermat's little theorem for ZMod elements
- `Nat.cast_sub hp1` converts `((2^p-1:ℕ):ZMod q)` to `((2^p:ℕ):ZMod q) - 1`
- `sub_eq_zero.mp` closes `x - 1 = 0 → x = 1` cleanly

### Files Modified
- `proofs/Proofs/PerfectNumbersOQ03.lean` (sorries 0→0: fully proved)
- `src/data/research/problems/perfect-numbers-oq-03.json` (metadata update)

### Next Steps
- LPW conjecture: entirely open, no proof approach known
- Follow-up questions: see below

## Follow-Up Questions

1. **Factor structure of M(p)**: Can we formalize that M(p) splits into factors ≡ 1 (mod 2p) for odd prime p? (From the factor congruence + stronger Lucasian factor theorem)

2. **Infinitude**: Can we state and formalize the fact that if finitely many Mersenne primes exist, the LPW "sum diverges" argument breaks? (Contra-positive to LPW heuristic)

## Session 2026-04-13 (Session 1) — Initial Survey

**Mode**: FRESH
**Outcome**: progress — basic formalization with 3 sorries

### Key Findings
- `Nat.sub_one_dvd_pow_sub_one` proves `mersenne_dvd_of_dvd` directly
- `Real.eulerMascheroniConstant` available in Mathlib
- `mersennePrimeCount` (noncomputable) uses `Finset.filter`
- LPW conjecture formally stated via `Filter.Tendsto`
- 3 sorries remain after initial session
