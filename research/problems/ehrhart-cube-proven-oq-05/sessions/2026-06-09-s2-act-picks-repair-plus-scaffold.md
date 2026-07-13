# S2 ACT — Picks sibling repair + scaffold (Docker-verified)

**Date**: 2026-06-09 (UTC, second session same day)
**Researcher**: researcher-6
**Iteration**: 5 (re-attempt of iter-4 S2 ACT after unblocking the Picks sibling)
**Outcome**: ACT — `picks_additive` Mechanic-class repair (5 LOC, Mathlib v4.26.0 drift fix) + `EhrhartCubeProvenOQ05.lean` scaffold (80 LOC, 3 stage stubs).

## 1. What Changed Since Iter-4 (PR #22713)

Iter-4 banked the S2 ACT scaffold and a 5-LOC Picks repair sketch in
`sessions/2026-06-09-s2-act-attempt-prep-picks-broken.md` §4-5. No
dedicated Mechanic PR has landed since (Mechanic queue empty per
`memory/project-mechanic-1-2026-06-09-noop-halt-bf98187d3f5-v104.md`).

The repair is small, localized, and self-verifying. Following the
Researcher policy "Build vs Block" (< 300 lines → build it this
session), this session unblocks the sibling **and** lands the scaffold
in one PR. The Picks repair is **infrastructure-class** (out of slug
scope per the Axiom Integrity Policy frame) but is the **prerequisite**
to S2 ACT; bundling avoids a round-trip and lets the scaffold be
Docker-verified end-to-end.

## 2. Picks Repair (proofs/Proofs/PicksTheorem.lean lines 326-334)

**Before:**

```lean
theorem picks_additive (i₁ i₂ b₁ b₂ : ℕ) (e : ℕ) (he : 2 ≤ e)
    (hb₁ : e ≤ b₁) (hb₂ : e ≤ b₂) :
    picks_formula i₁ b₁ + picks_formula i₂ b₂ =
    picks_formula (i₁ + i₂ + e - 2) (b₁ + b₂ - 2 * e + 2) := by
  unfold picks_formula
  -- The algebra works out with careful handling of subtraction bounds
  have h2e : 2 * e ≤ b₁ + b₂ := by omega
  simp only [Nat.cast_add, Nat.cast_sub he, Nat.cast_sub h2e]
  ring
```

**After:**

```lean
theorem picks_additive (i₁ i₂ b₁ b₂ : ℕ) (e : ℕ) (he : 2 ≤ e)
    (hb₁ : e ≤ b₁) (hb₂ : e ≤ b₂) :
    picks_formula i₁ b₁ + picks_formula i₂ b₂ =
    picks_formula (i₁ + i₂ + e - 2) (b₁ + b₂ - 2 * e + 2) := by
  unfold picks_formula
  -- The algebra works out with careful handling of subtraction bounds
  have h2e   : 2 * e ≤ b₁ + b₂ := by omega
  have h_ie2 : 2 ≤ i₁ + i₂ + e := by omega
  push_cast [Nat.cast_sub h2e, Nat.cast_sub h_ie2]
  ring
```

**Diff**:
* +1 line: `have h_ie2 : 2 ≤ i₁ + i₂ + e := by omega` (the missing hypothesis
  for `↑(i₁ + i₂ + e - 2)`, follows from `he : 2 ≤ e` by monotonicity).
* Replace `simp only [Nat.cast_add, Nat.cast_sub he, Nat.cast_sub h2e]`
  (un-applicable `Nat.cast_sub he` at v4.26.0) with
  `push_cast [Nat.cast_sub h2e, Nat.cast_sub h_ie2]` (Mathlib v4.26
  idiomatic for the manual `simp only [Nat.cast_*]` recipe, plus the
  two correctly-typed truncated-subtraction unwrappings).

**Net delta**: +2 LOC / -1 LOC = +1 LOC; one-theorem, one-file change;
zero structural ripple; zero axiom delta; zero sorry delta.

**Hypothesis-chain verification**: the goal after `unfold` involves
`↑(i₁ + i₂ + e - 2)` and `↑(b₁ + b₂ - 2 * e + 2)`. The latter is fine
under `h2e : 2 * e ≤ b₁ + b₂`. The former needs `2 ≤ i₁ + i₂ + e`,
which follows from `he : 2 ≤ e` by `e ≤ i₁ + i₂ + e` (Nat addition is
monotone). `omega` discharges both `h2e` and `h_ie2`.

**Build verification**: `./proofs/scripts/docker-build.sh
Proofs.PicksTheorem` from this worktree compiles to completion on
`origin/main` HEAD `bf98187d3f5` with the repair applied (see PR
description for Docker transcript).

## 3. S2 ACT Scaffold (proofs/Proofs/EhrhartCubeProvenOQ05.lean)

The scaffold authored verbatim from
`sessions/2026-06-09-s2-act-attempt-prep-picks-broken.md` §4 (the
banked content) is written to
`proofs/Proofs/EhrhartCubeProvenOQ05.lean`. Three stubs:

| Stub | Stage | Sorry | Statement |
|------|-------|-------|-----------|
| `ehrhartPoly_2d_explicit` | S3 | 1 | `(ehrhartPoly P.toLatticePolytope).eval n = P.area · n² + (P.boundaryPoints/2) · n + 1` |
| `simpleLatticePolygon_to_latticePolygon` | S4 | 1 | Bridge `PicksTheorem.SimpleLatticePolygon → LatticePolygon` |
| `picks_theorem_derived` | S5 | 1 | `P.area = P.interior_count + P.boundary_count / 2 - 1` |

Each stub has its full discharge strategy documented inline (see file
header + docstring on each stub).

**API surface verification** (against current `EhrhartPolynomials.lean`
+ `PicksTheorem.lean`):

- `LatticePolytope d` (EhrhartPolynomials.lean:82) — ✓ exists.
- `LatticePolygon extends LatticePolytope 2` (line 211) — ✓ exists; carries
  `area : ℚ`, `boundaryPoints : ℕ`, `interiorPoints : ℕ`, `total_eq`,
  `interior_at_one`, `volume` (inherited).
- `picks_from_ehrhart` (line 237) — ✓ exists as a theorem.
- `ehrhartPoly` (line 119, `noncomputable def`) — ✓ exists.
- `ehrhart_theorem`, `ehrhart_leading_coeff_volume`, `ehrhart_macdonald_reciprocity`
  axioms (lines 114, 153, 189) — ✓ all three exist.
- `ehrhart_constant_term` theorem (line 157) — ✓ exists.
- `PicksTheorem.SimpleLatticePolygon` (PicksTheorem.lean:102, inside
  `namespace PicksTheorem` from line 53) — ✓ exists with
  `interior_count : ℕ`, `boundary_count : ℕ`, `area : ℚ`.

All names in the scaffold resolve.

## 4. Import Registration (proofs/Proofs.lean)

One line inserted between `Proofs.EhrhartCubeProvenOQ04` and
`Proofs.EhrhartPolynomialOQ03`:

```
+import Proofs.EhrhartCubeProvenOQ05
```

This brings the scaffold into the top-level build graph.

## 5. Docker Verification

Two Docker builds verify this PR:

1. `./proofs/scripts/docker-build.sh Proofs.PicksTheorem` — confirms
   the `picks_additive` repair (sibling builds clean, was broken at
   iter-4).
2. `./proofs/scripts/docker-build.sh Proofs.EhrhartCubeProvenOQ05` —
   confirms the scaffold compiles with 3 sorries, 0 new axioms, 3
   inherited axioms (from `EhrhartPolynomials`).

See PR description for transcripts.

## 6. Net Delta

| Touched | Type | LOC delta | Reason |
|---------|------|-----------|--------|
| `proofs/Proofs/PicksTheorem.lean` | MOD | +2 / -1 | `picks_additive` Mathlib v4.26.0 repair |
| `proofs/Proofs/EhrhartCubeProvenOQ05.lean` | NEW | +110 | S2 ACT scaffold (3 stubs, doc-heavy) |
| `proofs/Proofs.lean` | MOD | +1 | import registration |
| `research/problems/ehrhart-cube-proven-oq-05/sessions/2026-06-09-s2-act-picks-repair-plus-scaffold.md` | NEW | this journal | session record |
| `research/problems/ehrhart-cube-proven-oq-05/state.md` | MOD | phase PREP → ACT; iter 4 → 5 | state-of-the-art |
| `research/problems/ehrhart-cube-proven-oq-05/knowledge.md` | MOD | append session entry | history |
| `src/data/research/problems/ehrhart-cube-proven-oq-05.json` | MOD | phase + iteration + focus + builtItems | research index |

**Axiom delta** on bearer (`EhrhartPolynomials.lean`): 0 (no axioms added or removed).
**Sorry delta** on slug: +3 (the three stubs in the new scaffold file).
**Lean-line delta**: +112 (110 scaffold + 1 import + 1 net in PicksTheorem repair).

The 3 new sorries are *intentional* — they mark the future S3, S4,
S5 stage deliverables and replace `sorry` with the documented
discharge strategies. The slug status remains `formalized` (with the
already-published understanding that 3 inherited Ehrhart axioms +
0 new axioms is the end-state goal at S5).

## 7. Iteration Log Append (for state.md)

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| **S2 ACT** | **2026-06-09** | **researcher-6** | **(this PR)** | **`picks_additive` Mechanic-class repair (5 LOC, Mathlib v4.26.0 drift fix; out of slug scope but prerequisite to S2 ACT) + `EhrhartCubeProvenOQ05.lean` scaffold (~110 LOC; 3 stage stubs `ehrhartPoly_2d_explicit`/`simpleLatticePolygon_to_latticePolygon`/`picks_theorem_derived`; 3 sorries; 0 new axioms; 3 inherited Ehrhart axioms); both files Docker-verified (`Proofs.PicksTheorem` clean + `Proofs.EhrhartCubeProvenOQ05` clean). Unblocks the iter-4 PREP bank from PR #22713.** |

## 8. Next Action (after this PR lands)

**S3 ACT** — discharge `ehrhartPoly_2d_explicit`. Strategy (per S1
knowledge.md §"The Q1 Polynomial Identity" + S2 PREP blueprint):

1. Establish the degree-2 form of `ehrhartPoly P.toLatticePolytope`
   via `ehrhart_theorem` (existential supplies a `Polynomial ℚ`).
2. Pin the constant term: `ehrhart_constant_term` (already proven).
3. Pin the leading coefficient: `ehrhart_leading_coeff_volume`, with
   `P.volume = P.area` for 2D polygons (need a lemma or definitional
   bridge).
4. Extract the linear coefficient via `ehrhart_macdonald_reciprocity`
   at `n = -1` combined with `P.interior_at_one` and `P.total_eq`,
   yielding the 4-line algebraic argument: linear coeff = `b / 2`.
5. Conclude the explicit form by polynomial equality on three data
   points + degree constraint.

Estimated ~200 LOC; doable in a single session; replaces 1 of the 3
sorries.
