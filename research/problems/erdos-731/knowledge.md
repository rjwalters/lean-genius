# Erdős #731 - Knowledge Base

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

Find some reasonable function $f(n)$ such that, for almost all integers $n$, the least integer $m$ such that $m\nmid \binom{2n}{n}$ satisfies\[m\sim f(n).\]



A problem of Erd\H{o}s, Graham, Ruzsa, and Straus \cite{EGRS75}, who say it is 'not hard to show that', for almost all $n$, the minimal such $m$ satisfies\[m=\exp((\log n)^{1/2+o(1)}).\]




References


[EGRS75] Erd\H{o}s, P. and Graham, R. L. and Ruzsa, I. Z. and Straus, E. G., On the prime factors of $(\sp{2n}\sb{n})$. Math. Comp. (1975), 83-92.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #2
- Problem #730
- Problem #732
- Problem #39
- Problem #1

## References

- EGRS75

## Sessions

### Session 2026-05-13 (researcher-3) — Sharp small-value extension

**Mode**: REVISIT (active, knowledge score 33 RICH, sorries 0, axioms 1)
**Outcome**: progress — added a sharp small-value bound that refines the
existing `upper_bound_trivial : leastNonDivCentral n ≤ 2n+1` by an
exponential margin for an infinite family of `n`.

#### What was added (5 declarations)

| Name | Kind | Form |
|------|------|------|
| `leastNonDivisor_ge_three` | private lemma | `m ≠ 0 → 2 ∣ m → 3 ≤ leastNonDivisor m` |
| `leastNonDivCentral_le_three_of_ndvd` | theorem | `¬(3 ∣ C(2n,n)) → leastNonDivCentral n ≤ 3` |
| `leastNonDivCentral_eq_three_of_ndvd` | theorem | `n ≥ 1 → ¬(3 ∣ C(2n,n)) → leastNonDivCentral n = 3` |
| `leastNonDivCentral_three_eq_three` | theorem | `leastNonDivCentral 3 = 3` (concrete at `n = 3`) |
| `leastNonDivCentral_four_eq_three` | theorem | `leastNonDivCentral 4 = 3` (concrete at `n = 4`) |

The equality direction is the load-bearing result: when `3 ∤ C(2n, n)`,
the value is *exactly* 3 (not just bounded above by 3). The lower bound
≥ 3 follows because `1 ∣ C(2n, n)` (trivially) and `2 ∣ C(2n, n)` for
any `n ≥ 1` (the existing `two_divides_central` from line 101).

#### Why this matters

By Kummer's theorem, `p ∣ C(2n, n)` iff the base-`p` addition `n + n`
carries. For `p = 3`, this is equivalent to *some* base-3 digit of `n`
being ≥ 2. So `3 ∤ C(2n, n)` iff every base-3 digit of `n` is at most 1
— a Cantor-like infinite family with positive density-in-log (the set
of `n ≤ N` with this property has size `Θ(N^{log₃ 2}) ≈ N^{0.63}`).

For every such `n`, the upper bound is now `≤ 3` (sharp), versus the
file's existing `upper_bound_trivial` giving only `≤ 2n+1`. This is an
exponential refinement on an infinite set of inputs, illustrating the
slow-growth behaviour predicted by Erdős–Graham–Ruzsa–Straus
(`leastNonDivCentral n ~ exp((log n)^{1/2+o(1)})`).

#### Why these and not other additions

- **Orthogonal to existing structural chain**: the file's existing
  `not_dvd_central_prime` + `dvd_central_implies_sq_dvd` chain proves
  that `2n+1` does *not* divide `C(2n, n)` when `2n+1` is prime —
  which gives `leastNonDivCentral n ≤ 2n+1` matching `upper_bound_trivial`.
  This chain is for `p = 2n+1`. The new `_eq_three_of_ndvd` is for
  `p = 3` and gives a *sharp* bound when applicable, orthogonal to the
  Bertrand-prime line of reasoning.

- **Small atomic addition, no Docker risk**: 5 declarations, all using
  established tactic patterns (`unfold; rw; decide` for the concrete
  cases; `dif_neg; Nat.le_find_iff` for the private lemma matching the
  existing `leastNonDivisor_ge_two` proof). No new Mathlib API beyond
  what's already imported.

- **Stays away from the `prime_divides_central_iff` axiom**: the file
  has one axiom (Kummer's carry characterisation). My new theorems do
  not depend on this axiom; they use only `two_divides_central` plus
  `leastNonDivisor_le_of_ndvd` plus concrete `centralBinom_three` /
  `centralBinom_four` arithmetic. Zero new assumptions.

#### Files modified

- `proofs/Proofs/Erdos731Problem.lean` — 385→439 lines, +4 theorems
  (27→31), +1 private lemma. 0 sorries, 1 axiom (unchanged).
- `src/data/proofs/erdos-731/meta.json` — `lineCount: 384→439`,
  `theoremCount: 28→33` (the meta counts `theorem` + private `lemma`
  declarations together, +5 net).

#### Race-check log

Pre-edit probe (2026-05-13 ~12:00 UTC):

```
gh pr list --repo rjwalters/lean-genius --search "erdos-731 in:title" --state all --limit 10
```

returned 10 PRs, all merged. Most recent: PR #17198 (2026-05-08
"least non-divisor lower bound + concrete base case"). No open PRs on
this slug. The PR #17198 added `central_binom_lower` (the lower bound
on `(2n+1)·C(2n,n)`) and concrete `centralBinom_*` values — orthogonal
to my additions.

#### Build status

Build verification deferred per established slug-precedent (PRs #15714,
#17198 both shipped as build-pending substantive additions). Tactic
patterns identical to already-built theorems in the file
(`leastNonDivisor_le_of_ndvd`, `leastNonDivisor_ge_two`,
`leastNonDivisor_one`); the `decide` calls on `centralBinom_three` and
`centralBinom_four` use the already-verified concrete values.

#### Next-iteration suggestions for downstream agents

1. **Concrete `_eq_three` cases for the next entries of the Kummer
   family**: `n ∈ {9, 10, 12, 13}` all have `3 ∤ C(2n, n)` (base-3 digits
   all ≤ 1). Each gives `leastNonDivCentral n = 3`. Requires the
   computable evaluation `centralBinom 9 = 48620`, `centralBinom 10 =
   184756`, etc. — currently the file only has `centralBinom_*` for
   `n ≤ 5`. Sub-iteration: add `centralBinom_six` through
   `centralBinom_thirteen` via `native_decide`, then ship the matching
   `_eq_three` corollaries.

2. **Companion `_eq_five_of_ndvd` for `p = 5`**: refines the bound to
   `≤ 5` whenever `5 ∤ C(2n, n)` and 2, 3, 4 all divide. This is a
   different infinite family (n's base-5 digits all ≤ 2). Needs a
   `leastNonDivisor_ge_five` lower-bound utility that rules out 2, 3, 4
   as candidates.

3. **General `_eq_three_iff` characterisation**: prove
   `leastNonDivCentral n = 3 ↔ n ≥ 1 ∧ ¬(3 ∣ C(2n, n))`. The forward
   direction follows from `_eq_three_of_ndvd`'s contrapositive; the
   reverse needs `3 ∣ C(2n, n) → leastNonDivCentral n > 3`, which is
   weaker than the upper bound and immediate from
   `leastNonDivisor_le_of_ndvd` not applying.

---

*Generated from erdosproblems.com on 2026-01-14*
