# Research State: ehrhart-cube-proven-oq-03

## Current State

**Phase**: S1 OBSERVE
**Path**: full
**Since**: 2026-05-12T20:55Z
**Last Updated**: 2026-05-12 (Session 1 researcher-12)
**Iteration**: 1

## Session 1 — S1 OBSERVE: Barvinok algorithm gallery-gap survey (researcher-12, 2026-05-12)

**Mode.** ANALYSIS-ONLY (no `.lean` edits).

**Outcome.** Workspace created.  Slug retargeted to a **concrete
gallery gap**: the existing `ehrhart-cube-proven*` family is entirely
identity-type (cube formula, h*-vector, recursions, Eulerian numbers).
None of them address **algorithmic / generating-function** lattice
point counting.  Barvinok-1994 fills exactly that gap.

**Key findings.**

1. **Gap confirmed.**  The four existing entries
   (`ehrhart-cube-proven`, `ehrhart-cube-proven-oq-01`,
   `ehrhart-cube-proven-oq-02`, `ehrhart-cube-proven-oq-04`) prove
   *identities* and *recursions* about `#([0,1]ᵈ ∩ (1/n)ℤᵈ)` and its
   Eulerian h*-vector.  None state Barvinok's theorem; none introduce
   the short rational generating function `f(P; x)`.

2. **Mathlib v4.26.0 has Ehrhart theory** in
   `Mathlib.Combinatorics.Polytope.Ehrhart` and rational-function /
   power-series infrastructure (`RatFunc`, `MvPowerSeries`,
   `MvPolynomial.aeval`).  It does **NOT** have signed simplicial-cone
   decomposition or polytime-complexity statements.  Barvinok's
   algorithm itself must be **axiomatised** (or stated as an
   un-implemented `def`/`theorem` with the polytime claim as an
   axiom) for the gallery entry.

3. **Tractable corollary**: `f([0,n]ᵈ; x) = ∏ᵢ (1 − xᵢⁿ⁺¹) / (1 − xᵢ)`,
   the short rational generating function for the unit-cube dilation.
   This is *first-principles provable* via geometric series and acts
   as a sanity-test corollary linking OQ-03 to the verified parent
   `ehrhart-cube-proven`.

4. **Naming**: file `Proofs/EhrhartCubeProvenOQ03.lean`, gallery dir
   `src/data/proofs/ehrhart-cube-proven-oq-03/`.  Consistent with the
   sibling-naming convention used by OQ-01, OQ-02, OQ-04.

**Files modified (this PR).**
* `research/problems/ehrhart-cube-proven-oq-03/problem.md` — new (anchor doc).
* `research/problems/ehrhart-cube-proven-oq-03/knowledge.md` — new (Mathlib survey + 3-tier strategy).
* `research/problems/ehrhart-cube-proven-oq-03/state.md` — new (this file).
* `research/problems/ehrhart-cube-proven-oq-03/sessions/2026-05-12-s01.md` — new (session log).
* `src/data/research/problems/ehrhart-cube-proven-oq-03.json` — new (index entry, iteration 1).

**Build status.** No `.lean` changes; no build attempted.  Parent
`Proofs/EhrhartCubeProven.lean` and siblings
`Proofs/EhrhartCubeProvenOQ04.lean` both build clean on `origin/main`.

## Next Action (S2 ACT)

S2.1 — Probe Mathlib v4.26.0 generating-function API:

```bash
# In Docker (NEVER use direct lake build):
./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ03Probe
```

with `Proofs/EhrhartCubeProvenOQ03Probe.lean` importing
`Mathlib.Combinatorics.Polytope.Ehrhart`,
`Mathlib.Algebra.MvPolynomial.Basic`,
`Mathlib.FieldTheory.RatFunc.Basic`,
`Mathlib.RingTheory.PowerSeries.Basic`, and `#check`-ing candidate
identifiers (`@MvPolynomial`, `@RatFunc`, `@MvPowerSeries`,
`@Polynomial.geom_series_def`).

S2.2 — Implement `Proofs/EhrhartCubeProvenOQ03.lean`:

- `def ShortRationalGenFn` — short rational generating function as a
  finite signed sum.
- `axiom barvinok_polytime` — Barvinok's polynomial-time bound (the
  algorithm's existence is the axiomatised core).
- `theorem cube_generating_fn_factored` — first-principles
  `f([0,n]ᵈ; x) = ∏ᵢ (1 − xᵢⁿ⁺¹) / (1 − xᵢ)`.
- `theorem cube_count_eval_at_one` — bridge to `(n+1)ᵈ` via `x → 1`
  specialisation, importing `EhrhartCubeProven`.

S2.3 — Gallery entry `src/data/proofs/ehrhart-cube-proven-oq-03/meta.json`
with `status: axiomatized`, `badge: axiom`, `axiomCount: 1` (the
`barvinok_polytime` axiom).

## Decision Log

- **2026-05-12 S1**: Decision to introduce Barvinok via an
  axiomatised polytime statement + first-principles provable
  generating-function corollary.  Reason: Mathlib has no complexity
  class infrastructure, so the polytime claim cannot be formalised
  without major preliminaries.  The generating-function side is
  algebra-only and tractable.

- **2026-05-12 S1**: Decision NOT to attempt the signed-cone
  decomposition in S2.  Reason: even the 2-D case requires
  continued-fraction-style descent in a context Mathlib doesn't
  directly support.  Defer to a stretch S3 or future OQ.
