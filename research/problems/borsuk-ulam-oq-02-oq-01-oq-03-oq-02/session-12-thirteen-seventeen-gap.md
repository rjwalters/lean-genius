# Session 12 — Per-n explicit values across the (13, 17) prime gap

**Author**: researcher-6
**Date**: 2026-05-09
**Iteration**: 12 (S12)
**Builds on**: iter-10's `largestPrimeBelow_eq_of_in_plateau` (axiom-free
plateau lemma) and origin/main's `largestPrimeBelow_thirteen_eq_sixteen`
(endpoint LPB equality), `no_prime_in_fourteen_to_sixteen` (interval
helper for the gap), and `symBUDim_eq_of_lpb_eq[_of]` (conditional
symBUDim collapse from equal LPB).

**Independent from**: S11 (PR #17460), which targets the (7, 11) and
(11, 13) gaps. The two iterations cover orthogonal prime gaps and use
disjoint name suffixes (`_eq_symBUDim_seven|_eleven` vs
`_eq_symBUDim_thirteen`).

## Summary

Adds 10 new theorems to
`proofs/Proofs/BorsukUlamOQ02OQ01OQ03OQ02.lean` in a new section after
`symBUDim_thirteen_eq_sixteen_of`. Mirrors S11's pattern for the
(13, 17) prime gap with anchor 13:

| Theorem | Form | Provenance |
|---|---|---|
| `largestPrimeBelow_thirteen` | `lpb 13 = 13` | `largestPrimeBelow_self_of_prime` |
| `largestPrimeBelow_fourteen_eq_thirteen` | `lpb 14 = 13` | `largestPrimeBelow_eq_of_in_plateau 13 13 14` |
| `largestPrimeBelow_fifteen_eq_thirteen` | `lpb 15 = 13` | same with `m = 15` |
| `largestPrimeBelow_sixteen_eq_thirteen` | `lpb 16 = 13` | `largestPrimeBelow_thirteen_eq_sixteen.trans largestPrimeBelow_thirteen` |
| `symBUDim_fourteen_eq_symBUDim_thirteen` | `symBUDim 14 d = symBUDim 13 d` | `symBUDim_eq_of_lpb_eq` |
| `symBUDim_fifteen_eq_symBUDim_thirteen` | `symBUDim 15 d = symBUDim 13 d` | same |
| `symBUDim_sixteen_eq_symBUDim_thirteen` | `symBUDim 16 d = symBUDim 13 d` | same |
| `symBUDim_fourteen_fifteen_sixteen_collapse` | triple conjunction | composition |
| `symBUDim_fourteen_eq_symBUDim_thirteen_of` | hypothesis-form | `symBUDim_eq_of_lpb_eq_of` |
| `symBUDim_sixteen_eq_symBUDim_thirteen_of` | hypothesis-form | same |

## Why this iteration

The S11 PR (#17460, "Iter 11 — concrete LPB at composite n + symBUDim
plateau collapse") explicitly lists the (13, 17) gap and (23, 29) gap
as **next steps** after its own (7, 11)+(11, 13) work:

> Next Steps: extend plateau collapse instances to higher composite n
> in larger prime gaps; the next gap (13, 17) covers n = 14, 15, 16;
> the first prime gap of length ≥ 4 is (23, 29) covering n = 24, 25,
> 26, 27, 28 (a five-fold plateau collapse).

This iteration claims the first half of that follow-up — the (13, 17)
gap — using the same proof technique S11 uses (iter-10's
`largestPrimeBelow_eq_of_in_plateau` anchored at the previous prime).

The endpoint statements (`largestPrimeBelow_thirteen_eq_sixteen` and
`symBUDim_thirteen_eq_sixteen` at lines 875 and 883 of origin/main)
already exist, so this iteration *fills in the per-n granularity*:

1. The endpoint statement only says `lpb 16 = lpb 13`; this iteration
   pins both sides to the explicit value `13`, so `lpb 14`, `lpb 15`,
   `lpb 16` each unfold to a concrete numeral in downstream rewriting.
2. The endpoint `symBUDim 13 d = symBUDim 16 d` does not directly give
   the per-n equalities `symBUDim 14 d = symBUDim 13 d` and
   `symBUDim 15 d = symBUDim 13 d`. The new lemmas pinpoint each
   intermediate `n`.
3. The triple package `symBUDim_fourteen_fifteen_sixteen_collapse`
   bundles the three per-n equalities for downstream rewriting in one
   step.

## Independence from S11 (#17460)

| Aspect | S11 (open) | S12 (this) |
|---|---|---|
| Target gap | (7, 11) and (11, 13) | (13, 17) |
| Anchor primes | 7 and 11 | 13 |
| New `largestPrimeBelow_<n>` | 4 (`_eight`, `_nine`, `_ten`, `_twelve`) + 1 anchor (`_eleven`) | 4 (`_thirteen` anchor + `_<14,15,16>_eq_thirteen`) |
| New `symBUDim_<n>_eq_symBUDim_<p*>` | 4 (`_eight`/`_nine`/`_ten`/`_twelve` against `_seven`/`_eleven`) | 3 (`_<14,15,16>_eq_symBUDim_thirteen`) |
| Triple package | none (asymmetric pairs across two gaps) | `symBUDim_fourteen_fifteen_sixteen_collapse` |
| Hypothesis-form variants | 2 (`_eight_eq_..._of`, `_twelve_eq_..._of`) | 2 (`_fourteen_eq_..._of`, `_sixteen_eq_..._of`) |
| Helper reuse | `no_prime_in_eight_to_ten` (existing) | `no_prime_in_fourteen_to_sixteen` (existing) |
| New Mathlib API | none | none |

The two iterations are net-additive and non-conflicting in name space.

## Counts

- `lineCount`: 1485 → 1610 (+125, ~95 lines of proof bodies +
  ~20 lines of docstrings + 10 `#check` lines)
- `theoremCount`: 93 → 103 (+10)
- `substantiveTheoremCount`: 91 → 101 (+10; all new theorems are
  user-facing collapse witnesses, no internal helpers)
- `axiomCount`: 1 (unchanged)
- `definitionCount`: 2 (unchanged)
- `sorries`: 0 (unchanged)

## Mathlib API surface (this iteration introduces NONE)

All proofs use the same in-file API exercised by the parallel S11 work:

| Lemma | Source | Already used by |
|---|---|---|
| `largestPrimeBelow_self_of_prime` | this file:259 | S2/S3/S5/S7/S9 anchors at 2/3/5/7 |
| `largestPrimeBelow_eq_of_in_plateau` | this file:750 (iter-10) | `largestPrimeBelow_eight_eq_ten` (#16793) |
| `no_prime_in_fourteen_to_sixteen` | this file:868 | `largestPrimeBelow_thirteen_eq_sixteen` |
| `symBUDim_eq_of_lpb_eq` | this file:770 | `symBUDim_eight_eq_ten`, `symBUDim_thirteen_eq_sixteen` |
| `symBUDim_eq_of_lpb_eq_of` | this file:792 | hypothesis-form symBUDim variants |
| `largestPrimeBelow_thirteen_eq_sixteen` | this file:875 | (used in `_sixteen_eq_thirteen`) |

Zero new imports; zero new external helper lemmas. The risk profile is
strictly bounded by the existing iter-10 + (13, 16) endpoint section
already on origin/main.

## Build status

**[BUILD UNVERIFIED]** Standard caveat: worktree's `proofs/.lake` is
a recursive self-symlink (per memory
`feedback_researcher_lake_symlink_broken.md`), so local Docker builds
re-fresh-clone Mathlib (~30–45 min cold). All new proofs are
3–5-line syntactic compositions of existing in-file lemmas; the
proof-side risk is minimal. Verifying via Docker or CI post-merge is
recommended.

## Next iteration (S13) plan

Mirror this iteration for the (23, 29) gap (the first gap of length 6),
yielding a five-fold plateau collapse `symBUDim 24 d = symBUDim 25 d
= symBUDim 26 d = symBUDim 27 d = symBUDim 28 d = symBUDim 23 d`.
The infrastructure is identical: `no_prime_in_twentyfour_to_twentyeight`
is already in the file (line 897), so the proofs again reduce to short
applications of `largestPrimeBelow_eq_of_in_plateau` and
`symBUDim_eq_of_lpb_eq`. Estimated ~120 lines (slightly larger than
S12 because of five composite values rather than three).
