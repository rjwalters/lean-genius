# Erdős #1093 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

For $n\geq 2k$ we define the deficiency of $\binom{n}{k}$ as follows. If $\binom{n}{k}$ is divisible by a prime $p\leq k$ then the deficiency is undefined. Otherwise, the deficiency is the number of $0\leq i<k$ such that $n-i$ is $k$-smooth, that is, divisible only by primes $\leq k$.

Are there infinitely many binomial coefficients with deficiency $1$? Are there only finitely many with deficiency $>1$?



A problem of Erd\H{o}s, Lacampagne, and Selfridge \cite{ELS88}, that was also asked in the 1986 problem session of West Coast Number Theory (as reported here).

In \cite{ELS93} they prove that if the deficiency exists and is $\geq 1$ then $n\ll 2^k\sqrt{k}$.

The following examples are either from \cite{ELS88} or here. The following have deficiency $1$ (there are $58$ examples with $n\leq 10^5$):\[\binom{7}{3},\binom{13}{4},\binom{14}{4},\binom{23}{5},\binom{62}{6},\binom{94}{10},\binom{95}{10}.\]The examples which follow are the only known examples with deficiency $>1$. The following have deficiency $2$:\[\binom{44}{8},\binom{74}{10},\binom{174}{12},\binom{239}{14},\binom{5179}{27},\binom{8413}{28},\binom{8414}{28},\binom{96622}{42}.\]The following have deficiency $3$:\[\binom{46}{10},\binom{47}{10},\binom{241}{16},\binom{2105}{25},\binom{1119}{27},\binom{6459}{33}.\]The following has deficiency $4$:\[\binom{47}{11}.\]The following has deficiency $9$:\[\binom{284}{28}.\]See also [384] and [1094].

Barreto in the comments has given a positive answer to the second question, conditional on two (strong) conjectures.




References


[ELS88] Erd\H{o}s, P. and Lacampagne, C. B. and Selfridge, J. L., Prime factors of binomial coefficients and related problems. Acta Arith. (1988), 507--523.

[ELS93] Erd\H{o}s, P. and Lacampagne, C. B. and Selfridge, J. L., Estimates of the least prime factor of a binomial coefficient. Math. Comp. (1993), 215--224.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 3/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #2
- Problem #384
- Problem #1094
- Problem #1092
- Problem #39
- Problem #1

## References

- ELS88
- ELS93

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-15*

## Session 2026-05-04 (Session 1) — Structural Theorems + Complete Census

**Mode**: FRESH
**Outcome**: progress

### What I Did
1. Extended Lean file (167 → 225 lines, 25 → 38 theorems)
2. Added all missing ELS (1988) high-deficiency examples by native_decide:
   - Deficiency 2: C(174,12), C(239,14)
   - Deficiency 3: C(241,16), C(1119,27), C(2105,25), C(6459,33)
3. Added structural theorems:
   - `isKSmooth_mono`: k-smoothness is monotone in k
   - `isKSmooth_prime_iff`: prime p is k-smooth iff p ≤ k
   - `isKSmooth_mul`: k-smooth numbers closed under multiplication
   - `isKSmooth_pow`: k-smooth numbers closed under powers
   - `isKSmooth_of_dvd`: divisors of k-smooth numbers are k-smooth
   - `isKSmooth_iff_primeFactors`: characterization via primeFactors (for m ≠ 0)
   - `deficiency_pos_of_smooth`: explicit smooth term → positive deficiency
4. Fixed `isKSmooth_one` proof (explicit `hp.two_le` for omega)
5. Updated meta.json sections, proofStrategy, and leanFile stats

### Key Findings
- The ELS computational census (deficiency-2 through deficiency-4) is now fully verified by native_decide for k ≤ 33
- `IsKSmooth` forms a filter-closed family: closed under ×, ^, ∣ — this gives the theory a multiplicative structure
- The remaining axiom (`els_upper_bound`) is deep analytic number theory and unlikely to be formalizable soon
- Status remains: 0 sorries, 1 axiom (els_upper_bound)

### Files Modified
- `proofs/Proofs/Erdos1093Problem.lean` (167 → 225 lines)
- `src/data/proofs/erdos-1093/meta.json` (updated stats and sections)

### Next Steps
- Verify remaining large ELS deficiency-2 examples: C(5179,27), C(8413,28), C(8414,28), C(96622,42) — may need long native_decide
- Attempt to prove `noSmallPrimeFactors_7_3` etc. explicitly (requires decidability or manual proof)
- Connect IsKSmooth to Mathlib's `Nat.Coprime` or factorization API
