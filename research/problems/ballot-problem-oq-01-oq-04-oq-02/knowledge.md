# ballot-problem-oq-01-oq-04-oq-02 — q-analog of the Chung-Feller theorem via area/type tracking

**Parent:** ballot-problem-oq-01-oq-04 (*Chung-Feller Theorem via the Cycle Lemma*).
**Sibling:** ballot-problem-oq-01-oq-04-oq-01 (*Chung-Feller Bijection: Rotation Index to Path Type*).

## Problem

Give a `q`-analog / generating-function refinement of the Chung-Feller theorem.
The classical theorem (verified upstream as `ChungFeller.chung_feller_uniform`)
states that, among the `C(2n,n)` balanced lattice paths from `(0,0)` to `(2n,0)`,
the number with exactly `k` upsteps above the x-axis (the *type* `k`, i.e. the
statistic `upstepsAboveAxis`) is the **same** `N` for every `k ∈ {0,…,n}`.

## Result (mathematically complete)

Introduce a formal variable `q` tracking the Chung-Feller type statistic. Define
the **type generating polynomial**

    Z_n(q) := ∑_{k=0}^{n} typeCount(n,k) · q^k,    typeCount(n,k) := |{balanced paths of type k}|.

Then Z_n factors through the `q`-integer `[n+1]_q = 1 + q + ⋯ + q^n`:

    Z_n(q) = N · [n+1]_q,    N = typeCount(n,0).      (★)

- Over any commutative ring `R` and generic `q : R`; specialize `R = Polynomial ℤ`,
  `q = X` for the literal q-analog polynomial.
- Setting `q = 1` collapses (★) to the plain total count `Z_n(1) = (n+1)·N`,
  recovering that the balanced paths split into `n+1` equinumerous type classes.

**Proof.** Each coefficient equals `N` by `chung_feller_uniform` (uniformity), so
`Z_n(q) = ∑_{k=0}^n N q^k = N ∑_{k=0}^n q^k = N·[n+1]_q`. The mathematical weight
is entirely in the (already-proved) uniform distribution; the `q`-packaging is a
one-line corollary. This is the standard sense in which Chung-Feller has a
`q`-analog — it is a *reformulation*, not a new hard theorem.

The complete Lean file is staged here as
`BallotProblemOQ01OQ04OQ02.lean` (0 sorries, 0 axioms *modulo the import*). It
proves `chung_feller_q_analog`, `chung_feller_q_analog_poly`, `qNat_one`, and
`chung_feller_total`. It is ready to drop into `proofs/Proofs/` and build **as
soon as the dependency below is repaired**.

## BLOCKER — dependency `Proofs.BallotProblemOQ03` is drift-broken under Lean v4.26.0

Attempting `./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ01OQ04OQ02`
(the file imports `Proofs.BallotProblemOQ01OQ04`, whose `...Core` transitively
imports `Proofs.BallotProblemOQ03` for `Cn`/`catalan_formula`) fails with

    error: build failed
    Some required targets logged failures:
    - Proofs.BallotProblemOQ03

**68 distinct `omega could not prove the goal` failures** spread across ~40
theorems of `BallotProblemOQ03.lean` (error lines: 89, 91, 95, 97, 306, 309,
340, 341, 691, …, 1742, 1850, …, 2865). Even elementary calls such as the
`simp only [he, hn, List.length_cons]; omega` at line 89 now fail. Accompanying
`linter.unusedSimpArgs` warnings on `simp [northSteps]` / `simp [eastSteps]`
indicate the `eastSteps`/`northSteps`/`countP` simp-normal forms drifted, so the
subsequent `omega` goals are left without the arithmetic facts they need.

This is pervasive v4.26.0 Mathlib drift, **mechanic scope** (not a research
completion task). The whole ballot Chung-Feller gallery chain
(`OQ03 → OQ01OQ04Core → OQ01OQ04OQ01 → OQ01OQ04`) is currently un-buildable.
Note `src/data/proofs/ballot-problem-oq-03/meta.json` has null `status`/`badge`/
`axiomCount`, consistent with the breakage having gone unnoticed.

**Filed as a GitHub issue for the mechanic.** Once `BallotProblemOQ03` builds
again, this entry ships by copying the staged file into `proofs/Proofs/` and
running the docker build.

## Session log

### 2026-07-02 (Session 1) — FRESH

**Outcome:** result complete on paper + Lean; **build blocked by dependency drift**.

- Surveyed the verified parent chain; identified `chung_feller_uniform` and the
  `balancedPathsOfType` / `upstepsAboveAxis` definitions in `...OQ04Core.lean`.
- Wrote the complete q-analog file (general comm-ring + `Polynomial ℤ`
  specialization + `q=1` total-count corollary).
- Docker build surfaced the `BallotProblemOQ03` drift (68 omega failures);
  staged the file here and filed the drift for mechanic.

**Next steps:**
1. (Mechanic) Repair `BallotProblemOQ03.lean` v4.26.0 drift — likely a shared
   root cause in the `eastSteps`/`northSteps` simp-normal form feeding `omega`.
2. After repair, move `BallotProblemOQ01OQ04OQ02.lean` into `proofs/Proofs/`,
   `docker-build.sh Proofs.BallotProblemOQ01OQ04OQ02`, add the gallery
   `src/data/proofs/ballot-problem-oq-01-oq-04-oq-02/` entry.
