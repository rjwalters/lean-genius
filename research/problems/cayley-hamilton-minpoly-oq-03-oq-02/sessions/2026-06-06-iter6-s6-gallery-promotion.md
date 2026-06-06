# S6 — Gallery promotion

**Researcher:** researcher-3
**Date:** 2026-06-06
**Iteration:** 6
**Phase:** ACT

## Goal

Open the gallery entry for `cayley-hamilton-minpoly-oq-03-oq-02` now that the
Lean file `CayleyHamiltonMinpolyOQ03OQ02.lean` is at S5 completion (333 LOC,
11 theorems, 0 sorries, 3 axioms — all build-verified by researcher-1 on
2026-06-05).

## Action

Created `src/data/proofs/cayley-hamilton-minpoly-oq-03-oq-02/meta.json`
mirroring the parent OQ-03 schema with the following fields specialised
to this entry's axiomatized status:

* `status: "axiomatized"` and `badge: "axiom"` (per the assumption-status
  rules in CLAUDE.md — never overclaim `verified` when axioms encode
  mathematical content).
* `axiomCount: 3` — the three Layer 3 ω axioms (`omegaMM`, `omegaMM_two_le`,
  `omegaMM_lt_three`).
* `assumptions` field naming each axiom, with its mathematical
  justification (folklore lower bound, Strassen 1969 upper bound) and an
  explicit statement that the full operation-count theorem is deferred
  pending Mathlib growing a complexity monad and fast-matmul oracle.
* `theoremCount: 11`, `definitionCount: 2`, `lineCount: 333` — matching
  the Lean file.
* Five `sections` covering Layer 1 (structural), Layer 2 (matrix-level
  correctness), Layer 2 (vector-level corollaries), Layer 2.5 (factor-count
  bound), and Layer 3 (axiomatized ω placeholder), each with line-range,
  summary, and mathematical context.
* `overview.historicalContext` traces Keller-Gehrig 1985 → Giesbrecht 1995
  → Storjohann 2000, with numerical breakeven analysis at n = 64
  (Strassen vs naive vs CW-Williams).
* `overview.keyInsights` covers the structural-vs-quantitative split, the
  binary-expansion skeleton, the powers-of-single-matrix commutativity, the
  minimum-honest Layer 3 commitment, and the numerical-breakeven caveat.
* `conclusion.openQuestions` enumerates four follow-ups: Mathlib
  complexity-monad design, sharper popcount bound, Giesbrecht/Storjohann
  $O(n^\omega)$ refinement, and Strassen formalisation.
* `references` cite Keller-Gehrig 1985, Strassen 1969, Giesbrecht 1995,
  Storjohann 2000, Williams-Xu-Xu-Zhou 2024, von zur Gathen & Gerhard 2013,
  and Mathlib's `Data.Nat.BitIndices`.
* `crossReferences` link to the parent (OQ-03), sibling (OQ-03-OQ-01), and
  foundational (`cayley-hamilton-minpoly`) entries.

## Build verification

* `python3 -c "import json; json.load(...)"` — valid JSON.
* `pnpm annotations:build` — entry processed without errors.
* `pnpm research:build` — entry registered, no validation errors.
* `grep src/data/proofs/data-manifest.json` confirms entry hash:
  `meta: 419c79cf, ann: "", src: 6543659a`.
* `grep src/data/proofs/listings.json` confirms entry in gallery listings:
  `status: "axiomatized"`, `badge: "axiom"`, `sorries: 0`,
  `annotationCount: 0`.

## What's left

* Optional: `annotations.json` for inline highlights. Deferred — the
  meta.json `sections` already cover the per-section content; annotations
  add visual emphasis within the Lean source which the structural content
  here doesn't urgently need.
* Sharper factor-count bound `popcount(j) ≤ Nat.size j` — still deferred
  pending appropriate Mathlib `Nat.bitIndices` length API.
* Full operation-count theorem — still blocked on Mathlib complexity-monad.

## Decision

S6 closes Layers 1 + 2 + 2.5 + axiomatized Layer 3 as an `axiomatized`
gallery entry. The structural and correctness content is fully verified;
the quantitative complexity claim is explicitly axiomatic. This is the
right shape: it commits to the bare-minimum honest claim today while
leaving room for a future complexity-monad PR to slot in without
revising any axioms.

The problem can be marked `completed` in the research pool — the
structural side is done, and Layer 3 work is gated on Mathlib upstream
infrastructure that does not yet exist (and which is out of scope for a
single-problem research iteration).
