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

## Session 2026-07-08 (Session 2) — Density bound + sharpened reduction

**Mode:** REVISIT (MODERATE knowledge tier, highest available)
**Outcome:** progress

### What I Did
- Added the first **non-trivial upper bound** on the deficiency to the OQ-02
  file (Section V), all `ofReduceBool`-free (no `native_decide`):
  - `smooth_contributor_not_prime` — every smooth contributor `n−i` (`i<k`,
    `n≥2k`) is composite: it exceeds `k`, and a `k`-smooth number `>k` cannot be
    prime (`isKSmooth_prime_iff`).
  - `deficiency_le_nonprime_count` — weak form: `deficiency ≤ #{i<k : ¬(n−i).Prime}`
    (smooth filter ⊆ non-prime filter).
  - `deficiency_add_prime_count_le` — **sharp density bound**:
    `deficiency n k + #{i<k : (n−i).Prime} ≤ k`.
- Added `maximalDeficiencyIs_nine_iff_kGe10` (Section VI): the conjecture is
  equivalent to the open statement quantified only over `k ≥ 10` (small `k`
  discharged by the trivial bound). Strictly sharper than
  `maximalDeficiencyIs_nine_iff_upperBound`.
- Built clean: `Proofs.Erdos1093ProblemOQ02` (3059 jobs), 0 sorry, 0 new axioms.

### Key Findings
- **Primes in the window contribute nothing.** The `k` consecutive integers
  `n, …, n−k+1` all exceed `k` (admissible ⇒ `n ≥ 2k`), and a prime is
  `k`-smooth iff `≤ k`. So the trivial `deficiency ≤ k` upgrades to
  `deficiency ≤ k − (#primes in window)` — the first genuine upper bound here.
- **Reframes the open core.** A hypothetical deficiency `> 9` at `k ≥ 10` needs a
  length-`k` run of consecutive integers with `< k−9` primes: an exceptionally
  prime-poor window. This is exactly the density input the ELS bound
  (`els_upper_bound`, `n ≪ 2^k√k`) formalizes.

### Files Modified
- `proofs/Proofs/Erdos1093ProblemOQ02.lean` (Sections V–VI, +~75 lines, verified)
- `src/data/research/problems/erdos-1093-oq-02.json` (knowledge)

### Next Steps
- Quantify: combine `deficiency + #primes ≤ k` with a prime-count lower bound on
  `[n−k+1, n]` (Brun–Titchmarsh) to force `k`-dependent upper bounds for `k ≥ 10`.
- Attempt `k = 10, 11, 12` slices via the composite-contributor structure plus
  the `p ∤ C(n,k)` admissibility constraint.

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

## Session 2026-07-08 (Session 2, researcher-1) — Section VII: prime-window caps deficiency

**Mode:** DEEP DIVE (RICH problem, look-outward from mature state)
**Outcome:** progress (2 new ofReduceBool-free theorems)

### What I Did
Extended the sharp density bound `deficiency + #primes-in-window ≤ k`
(`deficiency_add_prime_count_le`) with its effective/extreme consequences:
- `deficiency_lt_k_of_prime_in_window`: a single prime `n-i` (`i<k`) in the
  window forces `deficiency n k < k` (one prime certificate suffices — effective).
- `window_primefree_of_deficiency_eq_k`: the trivial-max case `deficiency n k = k`
  forces a prime gap of length ≥ k (no window value is prime). Structural reason
  record deficiencies are hard: they demand prime-poor windows (the ELS density
  phenomenon).

Both proved by pulling `#primes ≥ 1` (`Finset.one_le_card.mpr ⟨i,_⟩`) into the
sharp bound and closing with `omega`. No native_decide, no new axioms.

### Verification
Built clean (3059 jobs). File now 19 theorems, 0 sorries, 0 axiom declarations.
native_decide (⇒ ofReduceBool) still used ONLY by the 3 record facts
(deficiency_284_28 [parent], noSmallPrimeFactors_284_28, smooth_indices_284_28);
all structural results (Sections I,III–VII) are ofReduceBool-free.

### Assessment / Frontier
The open core (universal upper bound `deficiency ≤ 9` for all admissible pairs,
k ≥ 10) is genuinely blocked on analytic NT: it needs an *effective* ELS/Brun–
Titchmarsh short-interval prime-count bound, absent from Mathlib v4.26. The parent
axiom `els_upper_bound` has a non-effective constant, so even fixed-k slices aren't
decidable. Elementary structural theory here is near its frontier.

### Next Steps (if revisited)
- ofReduceBool-free proof of `noSmallPrimeFactors_284_28` via Kummer/Legendre digit
  sums (Mathlib `Nat.Prime.factorization_choose`), per-prime for p∈{2,3,5,7,11,13,17,19,23};
  only partial (record count/smooth_indices still need native_decide).
- The universal bound needs effective analytic NT — BLOCKED until Mathlib has it.
