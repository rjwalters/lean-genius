# S17 STATE-SYNC — numeric correction + registry catch-up (researcher-2, 2026-06-13)

## Context

Docker daemon is **down** (2026-06-13), so build-dependent ACT (the (⟹)
Cramer paste, which carries the four documented `linear_combination` failure
modes) cannot be verified. This iteration is therefore deliberately
**build-free**: a correctness fix plus a registry sync, no Lean edit.

## What this iteration found

The S11-era `state.md` / JSON registry was stale relative to `origin/main`.
Two Lean PRs had merged without updating the registry:

1. **S7b ACT (#22967)** — reinstated the two numeric sanity lemmas via
   `Matrix.det_succ_row_zero` + `Matrix.det_fin_three`:
   - `concyclicityDetCoords_unit_circle = 0`
   - `concyclicityDetCoords_off_circle = -6`

2. **easy-direction ACT (#22917)** — proved `concyclic_implies_concyclicityDet_zero`
   **unconditionally** (concyclic ⟹ Δ = 0), via the explicit kernel vector
   `(1, -2O₀, -2O₁, O₀²+O₁²-r²)` and `Matrix.exists_mulVec_eq_zero_iff`. This
   discharges the **(⟸) half** of the headline iff; only the (⟹) Cramer
   direction is genuinely open now.

Plus S15 (`norm_sub_sq_coord`, `signed_inner_product_to_scalar(_coord)`) and
S16 (`coord_of_smul_diff`) which the S11 ledger predates. The file is now
**265 LOC, 1 sorry, 0 axioms** on `origin/main`.

## Correctness fix (the substantive win)

`knowledge.md` line 145 (S1 OBSERVE, 2026-05-12) claimed that moving the
fourth point off the unit circle to `(0, -2)` gives `Δ = -8`. **This is
wrong.** The correct value is `Δ = -6`.

Hand verification (points `(1,0), (0,1), (-1,0), (0,-2)`; matrix rows
`[x²+y², x, y, 1]`):

```
| 1  1  0  1 |     R2-R1, R3-R1, R4-R1     | 1  1  0  1 |
| 1  0  1  1 |   ───────────────────────>  | 0 -1  1  0 |
| 1 -1  0  1 |   (det unchanged)           | 0 -2  0  0 |
| 4  0 -2  1 |                             | 3 -1 -2  0 |
```

Expand along column 4: only row 1 is nonzero there (entry 1, cofactor sign
`(-1)^(1+4) = -1`). The surviving 3×3 minor

```
| 0 -1  1 |
| 0 -2  0 |   = 3 · det| -1  1 | = 3·(0+2) = 6
| 3 -1 -2 |            | -2  0 |
```

so `Δ = 1 · (-1) · 6 = -6`. This matches the **machine-checked** merged lemma
`concyclicityDetCoords_off_circle` (#22967), which proves
`concyclicityDetCoords 1 0 0 1 (-1) 0 0 (-2) = -6`. The file itself already
carried a comment flagging -8 as a slip; the knowledge base had not been
corrected.

## Files touched (no Lean edit)

- `research/problems/.../knowledge.md` — `Δ = -8` → `Δ = -6` with a derivation
  + machine-check note.
- `research/problems/.../state.md` — S17 STATE-SYNC header, updated Lean-status
  snapshot (111 → 265 LOC; new decl table), fixed two historical `-8` mentions.
- `src/data/research/problems/...json` — `currentState` (phase/since/iteration
  17/focus/blockers/nextAction), `knowledge.progressSummary`, `lastUpdatedAt`.
- this session log.

## Next action (when Docker recovers)

S18 ACT: (a) wire `concyclic_implies_concyclicityDet_zero` into the (⟸) branch
of `concyclicityDet_eq_zero_iff_concyclic`; (b) replace the `(hNonCollinear :
True)` placeholder with the algebraic 2×2 non-collinearity (S3 PREP Choice 1b);
(c) discharge the (⟹) direction via `Matrix.cramer` (S3 ACT, ~80 LOC). All
build-dependent — do not blind-ship during the outage.
