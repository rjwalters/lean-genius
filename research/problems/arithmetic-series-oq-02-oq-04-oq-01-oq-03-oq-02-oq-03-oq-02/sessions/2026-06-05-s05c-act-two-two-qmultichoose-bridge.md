# S5c ACT — (2, 2) Interior Bridge to `qMultichoose`

**Date**: 2026-06-05
**Author**: researcher-1
**Phase**: ACT (Lean diff, Docker-verified)
**Iteration**: 13 (S1 OBSERVE + 5 PREPs + S2/S3/S4/S6/S5/S5b/S5c ACT)
**Mode**: ACT — Lean diff, Docker-verified 7745/7745 jobs.

## Outcome

Added 1 theorem (~25 LOC including doc + section heading) to
`proofs/Proofs/ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean`.
Discharges the **S5c ACT scope** flagged in the previous state.md as
"add a parent-side `qMultichoose q 2 2 = qNumber q 3` lemma first" —
turns out the parent already has `qMultichoose_two_left q k :
qMultichoose q 2 k = qNumber q (k + 1)`, which evaluates to
`qMultichoose q 2 2 = qNumber q 3` at `k = 2` without any new
parent-side helper. The bridge is therefore a one-line composition.

## What landed

### `qtMultichoose_two_two_eq_qMultichoose` (Section X, headline)

```lean
theorem qtMultichoose_two_two_eq_qMultichoose (q t : R)
    (htq : (1 : R) - q ^ 2 * t ≠ 0) (hq : (1 - q : R) ≠ 0) :
    qtMultichoose q t 2 2 = qMultichoose q 2 2 := by
  rw [qtMultichoose_two_two_eq_qNumber q t htq hq, ← qMultichoose_two_left q 2]
```

Bridges the unique non-trivial polynomial-sub-lattice interior point
`(n, k) = (2, 2)` directly to the parent gallery's named object
`qMultichoose q 2 2`, under the same two Path A guards as the S5 ACT
`qtMultichoose_two_two_eq_qNumber`.

## Mathematical content

Pure composition iteration, like S5b ACT. The proof composes:

1. `qtMultichoose_two_two_eq_qNumber q t htq hq` (S5 ACT):
   `qtMultichoose q t 2 2 = qNumber q 3`
2. `qMultichoose_two_left q 2` (parent), instantiated at `k = 2`:
   `qMultichoose q 2 2 = qNumber q (2 + 1) = qNumber q 3`

The novelty is once again the **naming**: gallery integration (S7) can
now reference `qMultichoose q 2 2` as the canonical interior reference,
matching the polynomial style of the parent gallery entry's
`meta.json` rather than the rational Macdonald form `(1 - q^3) / (1 - q)`
or the intermediate `qNumber q 3`.

## Significance

**Closes the bridge chain for the entire polynomial sub-lattice.**

Before S5c ACT, the polynomial-sub-lattice characterization
`{k ≤ 1} ∪ {(2, 2)}` had four direct bridges to parent named objects
(S5b ACT) for the `k ≤ 1` slice but **no** direct bridge for the
`(2, 2)` interior point — only the intermediate `qNumber` bridge from
S5 ACT. The (2, 2) point was the visible gap.

After S5c ACT, every point in the sub-lattice is formally equated to a
parent-side named object:

| Sub-lattice point | Bridge to parent | Source |
|---|---|---|
| `(N, 0)` | `qtBinom q t N 0 = qBinom q N 0 = 1` | S5b ACT |
| `(N, 1)` | `qtBinom q t N 1 = qBinom q N 1` (under `1 - q ≠ 0`) | S5b ACT |
| `(n, 0)` mc | `qtMultichoose q t n 0 = qMultichoose q n 0 = 1` | S5b ACT |
| `(n, 1)` mc | `qtMultichoose q t n 1 = qMultichoose q n 1` (under `1 - q ≠ 0`) | S5b ACT |
| **`(2, 2)`** mc | **`qtMultichoose q t 2 2 = qMultichoose q 2 2`** (under `1 - q^2 t ≠ 0` and `1 - q ≠ 0`) | **S5c ACT (this iteration)** |

The polynomial-sub-lattice characterisation is now **complete at the
named-object level**.

## Counts after S5c ACT

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02.lean` | **~510** | **18** | 0 | 2 | 0 |

(Up from ~480 LOC / 17 theorems at end of S5b ACT.)

## Build status

**Docker-verified clean**:
`./proofs/scripts/docker-build.sh Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02`
→ `✔ [7745/7745] Built Proofs.ArithmeticSeriesOQ02OQ04OQ01OQ03OQ02OQ03OQ02 (153s)`
→ `=== Build succeeded ===`.
Mathlib v4.26.0.

## Remaining work

- **S7 ACT (gallery JSON integration)**: with the polynomial-sub-lattice
  bridge chain now complete at the named-object level, gallery
  `meta.json` can quote `qMultichoose q 2 2` (via S5c ACT) and
  `qMultichoose q n 1` (via S5b ACT) as the canonical references for
  the polynomial-sub-lattice values. The gallery entry will be
  `status: "axiomatized"` (not `verified`) since the positive
  `at_one_one` recovery still requires Path C migration. ~1 session;
  doc-only.

- **Path C (`RatFunc`) migration**: still the canonical route to the
  positive `qtMultichoose 1 1 n k = Nat.multichoose n k` recovery.
  ~80–120 LOC, multi-session.

- **S6 ACT (Macdonald axiomatised, optional)**: principal-specialization
  identity. Unchanged from prior state.

## Honesty

This iteration is a **pure composition** of two existing theorems
(`qtMultichoose_two_two_eq_qNumber` + parent's `qMultichoose_two_left`).
The mathematical content is one rewrite step. The value is the
**naming**: the sub-lattice bridge chain is now complete at the named
parent-object level, which simplifies downstream (gallery,
peer-reviewer, mechanic) references. The (2, 2) `qNumber` bridge was
already in S5 ACT; S5c ACT just lifts it to `qMultichoose`.

No new mathematical insight; no new technique; no new axiom. The
contribution is a closing piece to a polynomial-sub-lattice puzzle that
S5b ACT left at 80% complete.
