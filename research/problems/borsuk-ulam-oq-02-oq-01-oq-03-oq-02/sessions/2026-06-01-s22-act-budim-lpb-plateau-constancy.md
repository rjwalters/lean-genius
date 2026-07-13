# S22 ACT — `buDim ∘ largestPrimeBelow` constancy on prime-gap plateaus (PART XXVI)

**Author:** researcher-1
**Timestamp:** 2026-06-01 ~04:30 UTC
**Phase:** Iter 21 ACT — third constancy axis on `buDim ∘ lpb`, axiom-free
**Iteration:** 21 (post Iter 20 S21 doc-only build re-verify, 2026-05-31)

## TL;DR

Adds a new **PART XXVI** to
`proofs/Proofs/BorsukUlamOQ02OQ01OQ03OQ02.lean` containing 5 new
**axiom-free** theorems:

| Theorem | Status | Statement |
|---|---|---|
| `buDim_largestPrime_const_in_no_prime_range` | axiom-free | no prime in `(n, m]` ⇒ `buDim (lpb n) d = buDim (lpb m) d` for all `d` |
| `buDim_lpb_seven_eq_buDim_lpb_ten`  | axiom-free | `buDim (lpb 7) d = buDim (lpb 10) d` |
| `buDim_seven_eq_buDim_lpb_ten`      | axiom-free | `buDim 7 d = buDim (lpb 10) d` |
| `buDim_lpb_eight_eq_buDim_lpb_ten`  | axiom-free | `buDim (lpb 8) d = buDim (lpb 10) d` |
| `buDim_lpb_nine_eq_buDim_lpb_ten`   | axiom-free | `buDim (lpb 9) d = buDim (lpb 10) d` |

No new axioms.  No sorries.  Lean file goes from 1885 → 1995 lines and
(per `grep -c "^theorem "`) 115 → 120 theorems.

## Motivation

Iter 19 S20 ACT (PART XXV) added concrete `lpb 8 = lpb 9 = lpb 10 = 7`
axiom-free and lifted the iter-17 plateau-collapse machinery to a 4-step
conditional run `symBUDim 7 d = symBUDim 10 d`.  That equality was
conditional on the file's axiom `symBUDim_eq_largestPrime` because the
plateau-collapse machinery flowed through `symBUDim` — the level at which
the conjecture acts.

The new PART XXVI observes that the **`buDim ∘ lpb` side** of the same
chain is **axiom-free**: equality `lpb n = lpb m` (a *purely structural*
fact, no Yang-Borsuk involved) is enough to conclude `buDim (lpb n) d =
buDim (lpb m) d` by simple congruence on the prime argument.  This is the
structurally-most-primitive form of the iter-19 conditional, and it is
the fact that the conjecture *transports* into the `symBUDim` statement.

### The three constancy axes

The file now has three orthogonal constancy facts for the
`buDim ∘ largestPrimeBelow` family:

| Axis | Location | Conditions | Restriction |
|---|---|---|---|
| Even-`d` constancy in `n` | PART XXIV (iter 17) | parent's `buDim_prime` | even `d` only, **but** unrestricted in `n` (any `n, m ≥ 2`) |
| Plateau constancy at all `d` (this part) | PART XXVI (iter 21) | structural congruence on `lpb` | all `d`, **but** restricted to no-prime-in-gap pairs |
| Conditional plateau on `symBUDim` | PART XVI/XXV (iter 10/19) | needs `symBUDim_eq_largestPrime` | all `d` and no-prime-in-gap pairs; conjecture lifts `buDim` ⇒ `symBUDim` |

The first two are **axiom-free** and complementary: even-`d` constancy
holds across *every* `n, m ≥ 2` (parent's cyclic Yang-Borsuk pins the
value to `2k − 1`), whereas plateau constancy at every `d` (including
odd) requires the no-prime-in-gap condition.  The third axis is the
conjecture's lift: under `symBUDim_eq_largestPrime`, the structural
plateau constancy on `buDim ∘ lpb` transports to constancy on `symBUDim`
at every `d`.

## What is NEW vs already-existing infrastructure

- The general statement `buDim_largestPrime_const_in_no_prime_range`
  is a one-line rewrite proof over PART XVI's
  `largestPrimeBelow_const_in_no_prime_range`.  It is *not* a deep
  theorem — it is the named packaging of the structural fact that
  was already implicit.  But the packaging matters: it makes the
  third constancy axis explicit and citable from downstream code, and
  it documents the axiom-free / conditional distinction across the
  three axes side by side.
- The concrete instances `buDim_lpb_{seven|eight|nine}_eq_buDim_lpb_ten`
  are the `buDim`-side **axiom-free** analogue of iter-19's
  conditional `symBUDim_seven_eq_ten`.  They use only iter-19's
  axiom-free `largestPrimeBelow_{eight|nine|ten}_eq_seven` plus the
  iter-21 general theorem.
- `buDim_seven_eq_buDim_lpb_ten` exposes the prime witness on the
  left side (via `largestPrimeBelow_seven`), giving the cleanest
  `buDim 7 d = buDim (lpb 10) d` form that downstream code is most
  likely to want.

## What is NOT done (intentionally)

- **No parent-side axiom addition.**  The proposed parent-side
  `buDim_prime_odd` axiom (Iter 18 S18 PREP) remains deferred for the
  reasons documented in iter 20: it would unify the odd-`d` value to
  `d − 1` for every prime and trivialise the conjecture's
  `largestPrimeBelow`-content (PARTS VI-XX become decorative).
- **No symBUDim-side biconditional.**  Still pending; needs
  `symBUDim_cyc` injectivity-across-primes infrastructure not currently
  axiomatized.
- **No Bertrand-window monotonicity concrete-pair instances.**  The
  iter-16 Path Forward item 2 follow-up is not exercised here —
  PART XXVI focuses on the plateau-constancy axis, which complements
  iter-16's monotonicity content without overlapping.

## Files changed

```
proofs/Proofs/BorsukUlamOQ02OQ01OQ03OQ02.lean    +110 lines (1885 → 1995)
src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/meta.json    metadata sync
research/problems/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/state.md   iter-21 entry
research/problems/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/sessions/2026-06-01-s22-act-budim-lpb-plateau-constancy.md (this file)
```

Net additions: 5 axiom-free theorems, +110 lines on the Lean side.

## Build verification

`./proofs/scripts/docker-build.sh Proofs.BorsukUlamOQ02OQ01OQ03OQ02` — see
PR description for the verification status at submission time.  Per memory
`[G9 qualifier masks real bugs — ALWAYS Docker-verify]`, this session
ran the Docker build *before* opening the PR.

## Counts delta

- lineCount: 1885 → 1995 (+110)
- theoremCount (grep `^theorem `): 115 → 120 (+5)
- substantiveTheoremCount: 113 → 118 (+5)  *(meta.json mirror updated)*
- axiomCount: 1 (unchanged)
- definitionCount: 2 (unchanged)
- sorries: 0 (unchanged)

## Next actions (post-Iter 21)

Unchanged from iter 20:
1. (a) Iter 18 PR (2): parent `buDim_prime_odd` axiom + PART XXVII closure
   — multi-week, content-collapse caveat still applies.
2. (c) symBUDim-side biconditional — still pending.
3. (d) Bertrand-window monotonicity concrete-pair instances — incremental;
   gauge value before committing.
4. (e) NEW — Apply PART XXVI's general
   `buDim_largestPrime_const_in_no_prime_range` to the other dyadic
   gaps catalogued in iter 11/12/13:
   - `(13, 17)` — gap of size 4, would give `buDim 13 d = buDim (lpb 16) d`
   - `(23, 29)` — gap of size 6, `buDim 23 d = buDim (lpb 28) d`
   - `(89, 97)` — gap of size 8, `buDim 89 d = buDim (lpb 96) d`
   Each is a one-line application of the general theorem with the
   matching `no_prime_in_*` lemma already in scope.  Incremental.
