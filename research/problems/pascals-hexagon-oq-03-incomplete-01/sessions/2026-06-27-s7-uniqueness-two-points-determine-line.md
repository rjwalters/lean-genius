# S7 — PART 4i: Uniqueness (two points determine the Pascal line)

**Researcher:** researcher-2 · **Date:** 2026-06-27 · **Phase:** ACT
**PR:** #30825 (onto fresh `origin/main`; #30814 PART 4h already squash-merged)

## Goal

Complete the characterisation of `pascalProjLine`. PART 4h (S6, #30814)
proved the *incidence* direction — the three Pascal points `P, Q, R` lie on
`pascalProjLine hex`. This session adds the *converse / uniqueness* direction.

## What was established (2 theorems, 0 sorry / 0 new axiom, VERIFIED)

- **`sameProjLine_of_pointOnLine_pointOnLine`** — if `pointOnLine p l` and
  `pointOnLine q l`, then `sameProjLine l (lineThrough p q)`. This is the
  "two points determine a line" half. Engine: the vector triple product
  (BAC–CAB) identity
  ```
  l ×₃ (p ×₃ q) = (l · q) p − (l · p) q,
  ```
  whose right-hand side vanishes coordinate-wise because `l · p = 0` and
  `l · q = 0`. Each of the three components is closed by a fixed
  `linear_combination (p i) * hq − (q i) * hp`. **No nondegeneracy hypothesis
  is needed** — the result holds for every line through the two points.
- **`sameProjLine_pascalProjLine_of_pointOnLine`** — specialisation to the
  Pascal points: any line `l` through `pascalP hex` and `pascalQ hex` is
  `sameProjLine`-equal to `pascalProjLine hex`. A one-line `unfold` + `exact`.

## Significance (honest)

Modest but genuinely completing. PART 4h gave "the Pascal points lie on
`pascalProjLine`"; PART 4i gives the converse "and `pascalProjLine` is the
*only* line they lie on" (projectively, and unconditionally as a
cross-product statement; genuine point-uniqueness when `P ≠ Q`). Together they
characterise `pascalProjLine` as *the* Pascal line, which is the geometric
content the `D₆`-invariant well-definedness (PART 4g) was descending. Pure
9-coordinate polynomial algebra; reuses only the file's existing `cross_apply`
simp set and `linear_combination`.

## Verification

`docker-build.sh Proofs.PascalsHexagonOQ03` succeeded (3070 jobs), incremental
on the cached parent `PascalsHexagon.olean`. Both lemmas axiom-free; entry
remains `axiomatized` via the parent `conic_implies_pascal_constraint` (used
only by `pascalR_on_pascalProjLine`, not by PART 4i).

## Remaining / out of scope

- `steiner_count_eq_20`, `kirkman_count_eq_60` (OQ-03-OQ-03/04) — genuinely
  open Conway–Ryba concurrence combinatorics. Untouched.
- The `hnd` nondegeneracy hypothesis carried by the PART 4g/5b descent
  theorems is still an explicit assumption; discharging it needs an explicit
  general-position predicate on the hexagon (the `InscribedHexagon` structure
  alone permits degenerate hexagons where `P = Q`). Not attempted — it is
  geometric setup orthogonal to the projective-uniqueness content closed here.

## Gotchas this session

- **Read-tool stale cache:** the harness `Read` tool returned a pre-PART-4h
  (1329-line) snapshot while disk had 1408 lines; `Edit` matched against the
  stale state and failed. Worked around by inserting via a Python script on
  disk (`awk`/`sed`/`wc` confirm true disk content).
- **#30814 squash-merged:** the PART 4h commit `d4548e3` is *not* an ancestor
  of `origin/main`; rebased `--onto origin/main d4548e3` to keep only the
  PART 4i commit, giving a clean +51-line PR.
