# Erdős #1141 — Knowledge Base

## Problem Statement

Are there infinitely many natural numbers $n$ such that $n - k^2$ is prime for every $k$ with $\gcd(n, k) = 1$ and $k^2 < n$?

## Status

**Erdős Database Status**: SOLVED (2026)
**Resolution**: Alexeev–Putterman–Sawhney–Sellke–Valiant (2026), arXiv:2604.06609 — answer is NO; only finitely many such $n$ exist. More generally finite for any fixed $a \geq 1$ in $n - ak^2$. Proof is a short deduction from Pollack's 2017 theorem on small prime quadratic residues; result is ineffective (Siegel's theorem). Computationally, $n = 1722$ is the largest good value for $a = 1$.

**Tractability Score**: 6/10 (for Lean formalization of the slug)
**Aristotle Suitable**: No (remaining axiom encodes a SOLVED-but-unformalized result; Aristotle cannot construct the APSSV proof until Pollack's theorem is in Mathlib)

## Tags

- erdos
- number-theory
- primes
- computational
- solved

## Lean Slug Status

- **File**: `proofs/Proofs/Erdos1141Problem.lean` (210 LOC)
- **Theorems**: 35
- **Definitions**: 3 (`IsErdos1141Good`, `knownGoodValues`, `goodValuesUpTo100`)
- **Axioms**: 1 (`erdos_1141_finitely_many` — encodes APSSV 2026)
- **Sorries**: 0
- **Status**: `axiomatized` (badge: `axiom`)
- **Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (Lean toolchain `v4.26.0`)
- **Build inheritance**: from merge `11d5cd15fd1` (PR #5529, 2026-03-25 deployer cycle)

## Built Items (10)

1. `Decidable` instance for `IsErdos1141Good` (required for `native_decide`)
2. `isErdos1141Good_iff_unbounded`: equivalence with unbounded formulation (omega → nlinarith for $k < n$ from $k^2 < n$, quadratic)
3. `good_implies_pred_prime`: good $n \geq 2$ has $n - 1$ prime (apply $k = 1$ with $\gcd(n, 1) = 1$)
4. Converted `decide` → `native_decide` for all computational verifications
5. `all_known_good`: unified `native_decide` verification of all 41 OEIS A214583 values
6. `classification_100`: complete exhaustive classification of good values in $\{0, \ldots, 100\}$
7. `good_count_100`: exactly 24 good values in $\{0, \ldots, 100\}$
8. `good_not_prime_ge5`: no prime $\geq 5$ satisfies the property (primes are odd, good values $\geq 4$ are even)
9. `good_odd_eq_three`: 3 is the unique odd good value $\geq 3$
10. `good_coprime3_sub9_prime`: good $n \geq 10$ coprime to 3 forces $n - 9$ prime (apply $k = 3$ with $\gcd(n, 3) = 1$)

## Insights (8)

1. **35 theorems** verify computational examples and structural properties
2. Single axiom `erdos_1141_finitely_many` encodes the APSSV 2026 finiteness theorem (arXiv:2604.06609; proved via Pollack's 2017 theorem on small prime quadratic residues, not yet formalized in Mathlib). Axiom will be removable once Pollack's theorem is in Mathlib.
3. Known good values: $3, 4, 6, 8, 12, 14, 18, 20, 24, 30, \ldots, 1722$ (OEIS A214583, 41 terms)
4. `omega` cannot handle $k < n$ from $k^2 < n$ (quadratic) — use `nlinarith` with `sq_nonneg k`
5. `IsErdos1141Good` needs explicit `Decidable` instance for `native_decide` to work
6. Complete classification up to $n = 100$ confirms 24 good values, matching the OEIS A214583 subsequence: $\{0, 3, 4, 6, 8, 12, 14, 18, 20, 24, 30, 32, 38, 42, 48, 54, 60, 62, 68, 72, 80, 84, 90, 98\}$
7. The structural corollaries (prime exclusion, odd uniqueness) follow cleanly from `good_ge4_even`
8. `good_coprime3_sub9_prime` shows coprimality to small primes creates additional simultaneous primality constraints — generalizes to $\gcd(n, p) = 1 \Rightarrow (n - p^2)$ prime for any prime $p$ with $p^2 < n$

## Mathlib Gaps

- **Pollack (2017)** small-prime-quadratic-residue theorem: $\forall \varepsilon > 0$, $\forall q$ sufficiently large, $\forall a$ coprime to $q$, $\exists$ prime $p \leq q^{1/4 + \varepsilon}$ with $p \equiv a \pmod q$. Not yet in Mathlib; required to formalize the APSSV proof and remove the `erdos_1141_finitely_many` axiom.

## Next Steps (none auto-actioned — terminal phase)

- a=2 variant: `IsErdos1141Good_a (a n : ℕ) : Prop` + computational study
- OEIS extension: `¬ IsErdos1141Good n` for $n \in [1723, 5000]$ via `native_decide`
- Pollack theorem skeleton: stub in `Erdos1141Pollack.lean` companion file for Aristotle proof search (hard)

## Sessions

| Session | Date | Mode | Outcome | PR |
|---------|------|------|---------|-----|
| 1 | 2026-01-15 → 2026-03-25 | FRESH | Initial formalization: `IsErdos1141Good`, Decidable instance, positive/negative examples, structural lemmas | #5381 (build fixes), #5529 (classification) |
| 2 | 2026-03-25 | FRESH | Added classification to n=100, unified verification, structural corollaries | (in #5529) |
| 3 | 2026-04-27 | REVISIT | Assessed and marked completed; axiom recognized as APSSV 2026 placeholder | (metadata only) |
| 4 | 2026-05-16 | REVISIT (catch-up) | Doc-only STATE-SYNC closing 9 metadata drift items (lineCount, iteration, stale insight name, knowledge.markdown, state.md template, problem.md template, knowledge.md template, mathlib_version 4.15.0→4.26.0) | (this session) |

For per-session detail, see `sessions/`:

- `sessions/2026-05-16-s01.md` — Session 4 catch-up STATE-SYNC

---

*Last updated: 2026-05-16T09:07Z (Session 4 catch-up STATE-SYNC)*
*Generated from erdosproblems.com on 2026-01-15; enriched 2026-03-25, 2026-04-27, 2026-05-16*
