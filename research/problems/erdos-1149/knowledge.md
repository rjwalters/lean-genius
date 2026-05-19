# Erdős #1149 — Knowledge Base

## Problem Statement

For non-integer α > 0, the natural density of {n ≥ 1 : gcd(n, ⌊n^α⌋) = 1} equals 6/π².

$$
\lim_{N \to \infty} \frac{|\{n \leq N : \gcd(n, \lfloor n^\alpha \rfloor) = 1\}|}{N} = \frac{6}{\pi^2}.
$$

## Status

**Erdős Database Status**: SOLVED (Bergelson–Richter 2017)

**Lean Formalization**: 0 sorries, 1 axiom
- `bergelson_richter` — main theorem (deep ergodic theory).

(`random_coprime_density` was previously axiomatized but was proved in PR #15578 via Möbius+Tannery.)

**Tractability Score**: 6/10
**Aristotle Suitable**: Companion file (`Erdos1149Aristotle.lean`) is 0-sorry; no further candidates.

## Tags

- erdos
- number-theory
- coprimality
- asymptotic-density
- floor-function
- ergodic-theory
- zeta-function

## Key Mathematical Facts

- 6/π² = 1/ζ(2) = ∏_p(1 − 1/p²) (Euler product, Cesàro 1881).
- Integer α: gcd(n, n^k) = n, so density = 0; the non-integer hypothesis is essential.
- Bergelson–Richter (2017) used multiplicative-function theory along polynomial sequences and ergodic averaging to prove the density 6/π² for non-integer α > 0.
- Möbius detection: ∑_{d ∣ gcd(a,b)} μ(d) = [gcd(a,b) = 1] (proved as `moebius_sum_divisors_eq`).
- Counting identity (open in Lean): C(N) := |{(a,b) ∈ [1,N]² : gcd(a,b) = 1}| = ∑_{d=1}^N μ(d) ⌊N/d⌋² (follows from `moebius_sum_divisors_eq` + `card_multiples` + `pairs_with_common_factor`, all proved).

## Path-to-Proof for `random_coprime_density` (HISTORICAL — now proved)

This subgoal was completed in PR #15578. The actual proof reuses the Möbius infrastructure listed below and delegates the analytic crux (Möbius–Tannery interchange) to `BaselProblemOQ04OQ03.coprime_pair_density_limit`, rather than re-deriving it inline.

Infrastructure preserved in `Erdos1149Problem.lean`:

1. `moebius_sum_divisors_eq`: ∑_{d ∣ n} μ(d) = [n = 1] (Dirichlet identity μ * ζ = ε).
2. `card_multiples`: |{a ∈ [1,N] : d ∣ a}| = ⌊N/d⌋.
3. `pairs_with_common_factor`: for prime p, |{(a,b) : p ∣ gcd(a,b)}| = ⌊N/p⌋².

Historical step-by-step plan (the path that was actually followed):

- **Step A** (counting identity): `countCoprimePairs N = ∑_{d=1}^N μ(d) * (⌊N/d⌋)²`. Uses `moebius_sum_divisors_eq` plus a sum-swap on (a,b,d) with d ∣ gcd(a,b).
- **Step B** (asymptotic interchange — Möbius–Tannery): `(1/N²) ∑_{d=1}^N μ(d) ⌊N/d⌋² → ∑_{d=1}^∞ μ(d)/d²`. Imported from `BaselProblemOQ04OQ03.coprime_pair_density_limit` to avoid re-proving Tannery.
- **Step C** (closed-form sum): `∑_{d=1}^∞ μ(d)/d² = 1/ζ(2) = 6/π²`. Mathlib's `hasSum_zeta_two` plus `ArithmeticFunction.moebius_mul_coe_zeta`.

Final realised cost: a single theorem in the main file (`random_coprime_density`, line 162) bridging Set/Finset cardinality back to the `BaselProblemOQ04OQ03` density limit, plus light infrastructure already in place. The hard analytic step lives in the Basel companion slug.

## Bergelson–Richter Axiom

`bergelson_richter` is the main 2017 theorem. The proof in the literature uses:
- Equidistribution of ⌊n^α⌋ mod m for non-integer α (Vinogradov-style estimates).
- Multiplicative-function-along-polynomial-sequences machinery from ergodic theory.
- The Bergelson–Host–Kra structure theorem and nilfactor analysis.

These ingredients are far from Mathlib. Leaving this axiom in place is the right judgment.

## Related Problems

- Problem #2000, #83, #888, #2, #39, #1 — broader Erdős coprimality / density problems.

## References

- Bergelson, V., & Richter, F. K. (2017). Multiplicative richness of additively large sets in Z^d. *Journal d'Analyse Mathématique*.
- Erdős, P. (1969 / 1983). *Some problems on number theory*. Marseille.
- Euler, L. (1748). *Introductio in analysin infinitorum*.
- Cesàro / Sylvester (1881): coprime probability 6/π².

## Sessions

- 2026-03-11 (researcher-5): Initial formalization, 16 theorems, 2 axioms.
- 2026-03-13: Möbius inversion infrastructure (`moebius_sum_divisors_eq`, `card_multiples`, `pairs_with_common_factor`).
- 2026-03-24: Gallery integration polished; registry marks slug COMPLETED + graduated.
- 2026-04-27 (researcher-8): JSON metadata reconciled (sorryCount 1→0 for Aristotle file, line counts corrected, problemStatement and knownResults populated). Documented concrete path-to-proof for `random_coprime_density` axiom.
- PR #15578: Axiom-elimination ACT — `random_coprime_density` proved via Möbius+Tannery (delegating asymptotic interchange to `BaselProblemOQ04OQ03.coprime_pair_density_limit`). Main file axiom count 2→1. The remaining axiom (`bergelson_richter`) is retained by design.
- 2026-05-17 (researcher-9, S4 STATE-SYNC): Doc-only sync — corrected `problem.md` counts (320→335 lines, 17→18 theorems, 2→1 axioms), updated `knowledge.md` axiom listing (`random_coprime_density` is now a proved theorem, not an axiom), and updated `state.md` from ACT→COMPLETED. Gallery `meta.json` was already canonical. No Lean source touched.

---

*Last updated: 2026-05-17*
