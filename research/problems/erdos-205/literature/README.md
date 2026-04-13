# Literature: erdos-205

Key references for Erdős Problem #205 (Powers of 2 plus numbers with few prime factors).

## Primary References

1. **Erdős, Paul** (1950). "On integers of the form 2^k + p and some related problems."
   *Summa Brasiliensis Mathematicae* 2, pp. 113–123.
   — Introduced covering systems; showed positive density of odd integers ≠ 2^k + prime.

2. **Romanoff, N. P.** (1934). "Über einige Sätze der additiven Zahlentheorie."
   *Mathematische Annalen* 109, pp. 668–678.
   — Proved positive density of integers = 2^k + prime.

3. **Hardy, G. H.; Ramanujan, S.** (1917). "The normal number of prime factors of a number n."
   *Quarterly Journal of Mathematics* 48, pp. 76–92.
   — Proved average Ω(n) ≈ log log n; motivates the threshold in the conjecture.

4. **Erdős, Paul; Kac, Mark** (1940). "The Gaussian law of errors in the theory of additive
   number theoretic functions." *American Journal of Mathematics* 62, pp. 738–742.
   — Proved Ω(n) is asymptotically Gaussian around log log n.

5. **Crocker, R.** (1971). "On a sum of a prime and two powers of two."
   *Pacific Journal of Mathematics* 36, pp. 103–107.
   — Extended covering systems: infinitely many odd n ≠ 2^a + 2^b + prime.

6. **Barreto-Leeham** (2026). Unpublished/Preprint.
   — Disproved Erdős #205: counterexamples where all remainders have Ω >> log log.

## Mathlib Modules Used

- `Mathlib.Data.Nat.Factors` — primeFactorsList, Nat.perm_primeFactorsList_mul
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — Real.log_le_log, log monotonicity
- `Mathlib.Order.Finset` — Finset.inf'_le (key for remainder_achieves_min)

## Lean Source

- `proofs/Proofs/Erdos205Problem.lean` — 444 lines, 6 axioms, 0 sorries, 44 theorems
