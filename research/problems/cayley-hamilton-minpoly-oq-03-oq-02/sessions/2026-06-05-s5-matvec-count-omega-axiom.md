# S5 ACT — Matvec-count bound + axiomatized Layer 3 ω placeholder

**Researcher:** researcher-1
**Date:** 2026-06-05
**Phase:** ACT
**Iteration:** 5
**Build verified:** ✅ `./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonMinpolyOQ03OQ02` — 3062/3062 jobs, 0 errors (8.0 s of compile after Mathlib cache warm-up).

## Goal

Per S4 state.md, ship two complementary follow-ups, each ~20-40 LOC, single Docker build:

1. **Matvec-count bound.** A theorem bounding the number of squared-Krylov factors needed to assemble `M^j`.
2. **Layer 3 axiomatized placeholder.** Add `ω` axioms with bounds, formalising the open-mathematics dependency.

## What shipped

`proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean` extended from 228 → ~333 LOC, 9 → 11 theorems, 0 → 3 axioms.

### Layer 2.5 — Factor-count bound (1 helper + 1 theorem)

* **`length_le_twoPow_sum`** (private helper).
  For any `L : List ℕ`, `L.length ≤ (L.map (fun i => 2 ^ i)).sum`.
  Proof: induction on `L`; the cons case uses `Nat.one_le_two_pow` and
  `omega` to absorb the `1 ≤ 2 ^ a` slack into the length bound.

* **`squareKrylovProd_factor_count_le`** (main).
  `j.bitIndices.length ≤ j` — the number of squared-Krylov factors
  needed to assemble `M^j` is bounded by `j` itself. Proof: combine
  `Nat.twoPowSum_bitIndices` (the binary-expansion identity) with the
  helper, then `omega` closes.

Combined with `squareKrylovProd_eq_pow` (S3) and `squareKrylovProd_mulVec`
(S4), this gives a *quantitative* matrix-multiplication count for the
Keller–Gehrig assembly step: `popcount(j) - 1` matrix products plus
`⌈log₂ j⌉ + 1` squarings to materialise the sequence `T_0, …, T_{⌈log₂ j⌉}`.

The sharper bound `j.bitIndices.length ≤ Nat.size j` (≤ `⌈log₂ (j+1)⌉`)
is left for future Mathlib API exploration; the `≤ j` bound is the
elementary, immediately verifiable version.

### Layer 3 — Axiomatized ω placeholder (3 axioms + 1 theorem)

* **`axiom omegaMM : ℝ`** — the matrix-multiplication exponent ω, an opaque real constant.
* **`axiom omegaMM_two_le : (2 : ℝ) ≤ omegaMM`** — folklore lower bound (must read n² entries).
* **`axiom omegaMM_lt_three : omegaMM < (3 : ℝ)`** — Strassen (1969) upper bound `ω ≤ log₂ 7 < 3`.
* **`omegaMM_mem_Ico`** — sanity-check conjunction `2 ≤ ω < 3`, derived from the two axioms.

The full operation-count statement (Keller–Gehrig recovers `μ_M` in
`O(n^ω)` field operations) is *deferred*: a complete Lean formulation
requires (a) a complexity monad and (b) a fast-matmul oracle, neither
of which Mathlib provides. This session ships the algebraic and
exponent-bound axioms; the operation-count claim itself is left for
a future S6+ iteration once the relevant Mathlib infrastructure lands.

## Status update

* **File:** `proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean`
* **Lines:** 228 → ~333 (≈ +105 LOC, mostly docstrings)
* **Theorems:** 9 → 11 (3 Layer 1 + 4 Layer 2 matrix + 2 Layer 2 vector
  + 1 Layer 2.5 factor-count + 1 Layer 3 ω-bounds sanity)
* **Helpers:** 1 → 2 (`prod_pow_of_list`, `length_le_twoPow_sum`)
* **Sorries:** 0 (unchanged)
* **Axioms:** 0 → **3** (`omegaMM`, `omegaMM_two_le`, `omegaMM_lt_three`)
* **Build:** 3062/3062 jobs clean (Docker, mathlib v4.26.0 / lean v4.26.0)

**Axiom-integrity policy.** Per CLAUDE.md, the file now carries
assumptions and its gallery `meta.json` (when opened in S6) must use
`status = "axiomatized"`, `badge = "axiom"`, with the assumptions field
naming `omegaMM` + its bound axioms.

## Build log

```
./proofs/scripts/docker-build.sh Proofs.CayleyHamiltonMinpolyOQ03OQ02
...
✔ [3062/3062] Built Proofs.CayleyHamiltonMinpolyOQ03OQ02 (8.0s)
Build completed successfully (3062 jobs).

=== Build succeeded ===
```

## Next action (S6)

The "natural S6" is the gallery promotion outlined in the S2 plan:
open `src/data/proofs/cayley-hamilton-minpoly-oq-03-oq-02/meta.json`
with `status = "axiomatized"`, `badge = "axiom"`, listing the three
`omegaMM` axioms in the assumptions field. The file now contains 11
theorems demonstrating the structural and correctness layers and the
factor-count bound; an honest gallery presentation can cover all 11
theorems + the 3 Layer 3 axioms as the formal statement of the
Keller–Gehrig algorithm "up to ω".

Alternatively, S6 could pursue the sharper bound `j.bitIndices.length
≤ Nat.size j` (or `≤ Nat.log2 j + 1`), which is the asymptotically
correct popcount bound, once the appropriate Mathlib API is identified.

## Reflection

The S5 split between a *combinatorial* matvec-count bound and an
*opaque ω axiom* was the right shape: the first is fully verified, the
second is the honest minimum commitment to talk about ω at all. The
operation-count claim itself (which would require both a complexity
monad and the ω axiom together) cannot be stated cleanly today, so the
file makes the dependence explicit by axiomatising what's missing
rather than overclaiming with a sorry or a vague `True` placeholder.

The 3-axiom Layer 3 is the smallest possible commitment consistent
with the project's axiom-integrity policy: each axiom is named, has
a citation in its docstring, and carries a tight bound. Future work
to add a complexity monad would only need to define an
operation-count predicate and connect it to `omegaMM`; no axiom in
this file would need revising.
