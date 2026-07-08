# Erdős #1093 — OQ-02: Is d(284,28)=9 the maximal deficiency?

## Summary

**Parent:** Erdős #1093 (deficiency of binomial coefficients, Erdős–Lacampagne–Selfridge).
For `n ≥ 2k`, when `C(n,k)` has no prime factor `≤ k`, the *deficiency* is the number
of `0 ≤ i < k` with `n − i` being `k`-smooth. The current record is
`deficiency(C(284,28)) = 9`.

**OQ-02:** Is `9` the maximum possible deficiency over all admissible `(n,k)`,
or do higher values occur? (The universal upper-bound direction is open.)

## Status: OPEN (universal bound); existence half machine-verified.

---

## Session 2026-07-08 (Session 1) — Record admissibility + reduction

**Mode:** FRESH
**Outcome:** progress

### What I Did
- Selected erdos-1093-oq-02 (concrete, computable record value; parent infrastructure exists).
- Discovered the parent `Erdos1093Problem.lean` was **broken on main** — `omega` at
  L173 (`isKSmooth_one`) lacked `p.Prime`'s `two_le`. Repaired with
  `hp.one_lt.ne'` on `Nat.dvd_one.mp hd`. Parent now builds (3058 jobs).
- Wrote companion `Erdos1093ProblemOQ02.lean` (0 sorry, 0 axiom declarations).

### Key Findings
- The parent's `deficiency_284_28 = 9` does **not** by itself exhibit a valid
  deficiency example: the `deficiency` count is defined unconditionally, but the
  ELS problem additionally requires `C(n,k)` to have no prime factor `≤ k`. That
  admissibility check was never done. It only needs primes `≤ k` (Kummer not
  required): `C(284,28)` is a ~110-bit bignum, so `native_decide` computes it and
  tests divisibility by primes `≤ 28` instantly ⇒ `noSmallPrimeFactors_284_28`.
- The maximality question splits: **existence half** = finite verification
  (attained at `(284,28)`); **universal half** = genuinely open (unbounded `n,k`,
  cannot enumerate). `maximalDeficiencyIs_nine_iff_upperBound` reduces the whole
  conjecture to exactly the universal bound.
- Trivial bound `deficiency ≤ k` ⇒ any counterexample needs `k ≥ 10`
  (`deficiency_le_nine_of_k_le_nine`).
- Explicit certificate: the 9 smooth indices are `{4,8,9,11,12,14,18,20,24}`,
  i.e. `280,276,275,273,272,270,266,264,260` are the 28-smooth values.

### Files Modified
- `proofs/Proofs/Erdos1093Problem.lean` (1-line repair)
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (new, verified)
- `src/data/research/problems/erdos-1093-oq-02.json` (new)

### Next Steps
- Attack the universal bound for small `k ≥ 10`: the ELS bound `n ≪ 2^k√k`
  gives a finite per-`k` range, but the parent axiom `els_upper_bound`'s constant
  is not effective — an explicit constant would make each fixed-`k` slice decidable.
- Exploit the density constraint: deficiency `d` forces `d` of the `k` consecutive
  integers `n,…,n−k+1` to be `k`-smooth.
- Consider a Kummer-based (`ofReduceBool`-free) proof of `noSmallPrimeFactors_284_28`.
