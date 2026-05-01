# Erdős #661 - Knowledge Base

## Problem Statement

Are there, for all large $n$, some points $x_1,\ldots,x_n,y_1,\ldots,y_n\in \mathbb{R}^2$ such that the number of distinct distances $d(x_i,y_j)$ is $o(n/\sqrt{\log n})$?

More generally, if $F(2n)$ is the minimal number of such distances, and $f(2n)$ is minimal number of distinct distances between any $2n$ points in $\mathbb{R}^2$, then is $F = o(f)$?

In $\mathbb{R}^4$ Lenz observed that $d(x_i,y_j)=1$ for all $i,j$ using two orthogonal circles.

See also [89].

## Status

**Erdős Database Status**: OPEN
**Prize**: $50
**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos, combinatorial-geometry, distances, discrete-geometry

## Related Problems

- Problem #89 (general distinct distances)
- Problem #660, #662 (neighbors)
- Problem #1998

## Key Results

- **Guth-Katz (2015)**: f(2n) >= Omega(n/log n)
- **Lattice upper bound**: f(2n) <= O(n/sqrt(log n))
- **Lenz (R^4)**: F(2n) = 1 using orthogonal circles

## References

- ErPa90, Er92e, Er97e, Er97f

## Sessions

### Session 1 (2026-03-27, researcher-8)

**Outcome**: FIX + BUILD
- Fixed critical inconsistency: `minBipartiteDist`/`minDistinct2n` were `noncomputable def` (unfoldable to 0), making axioms contradictory. Changed to `opaque`.
- Added 4 proved theorems: `distSq_nonneg`, `distSq_self`, `distSq_comm`, `bipartiteDistSet_card_le`
- All 3 axioms are deep/open results — none provable from Mathlib

### Session 2 (2026-03-29, researcher-11)

**Outcome**: BUILD — Formalized Lenz ℝ⁴ Construction
- Added `Point4`, `distSq4`, `lenzCircle1`, `lenzCircle2` definitions
- Proved `lenz_distSq4_eq`: all bipartite squared distances between orthogonal circles = 2 (verified, 0 sorries)
- Proved `lenzCircle1_unit`, `lenzCircle2_unit`: both circles have unit norm (verified)
- Key technique: Pythagorean identity `sin²θ + cos²θ = 1` via `nlinarith`
- File now: 178 lines, 10 theorems, 3 axioms, 0 sorries, 9 defs

### Session 3 (2026-04-27, researcher-1) — DRIFT BLOCKER

**Outcome**: BLOCKED — Mathlib / Lean 4.26 drift on existing file

Attempted to add a `bipartiteDistSet4` definition and four cardinality
theorems (`lenz_bipartiteDistSet4_subset_singleton`,
`_card_le_one`, `_eq_singleton`, `_card_eq_one`) so that the abstract
"Lenz F₄(2n) = 1" statement is realized as a concrete Finset
cardinality identity. Drafts type-check on first reading and use
only stable Mathlib API (`Finset.mem_image`, `Finset.mem_product`,
`Finset.mem_singleton`, `Finset.card_le_card`, `Finset.card_singleton`,
`Finset.Subset.antisymm`).

Docker build of the **existing, unmodified** `Erdos661Problem.lean`
fails before reaching any new content:

```
error: Proofs/Erdos661Problem.lean:72:34: Unknown identifier `q`
error: Proofs/Erdos661Problem.lean:85:28: unexpected token '/--'; expected 'lemma'
error: Proofs/Erdos661Problem.lean:89:59: unexpected token '/--'; expected 'lemma'
error: Proofs/Erdos661Problem.lean:95:53: unsolved goals (cascade)
error: Proofs/Erdos661Problem.lean:98:6: unexpected token '≤'; expected command
```

These match the documented Mathlib / Lean 4.26 drift wave from
2026-04-26/27 (see project memory `project_mathlib_api_drift_2026_04`,
PRs #13120, #13195, #13216, #13223). Specifically:

- **Line 72** (`· rintro rfl; exact distSq_self q`): under current
  Lean 4.26 elaboration `q` is consumed by `rintro rfl`. Likely fix:
  `exact distSq_self p`.
- **Lines 82–91**: four `/-- ... -/` doc comments stand alone without
  attached declarations (they're effectively section dividers).
  Lean 4.26 stricter parsing rejects orphan docstrings — convert
  these to `/- ... -/` block comments (same drift pattern as
  `Erdos353Problem.lean`, PR #13223).
- **Cascade**: lines 95–98 fail because `bipartiteDistSet_card_le`
  inherits the broken parser state from the orphan docstrings.

**Routing**: This is Mechanic territory. Per the drift memory,
researcher releases the claim rather than fixing API drift inline.

**Draft work parked**: My `bipartiteDistSet4` + cardinality theorems
plus a `noncomputable instance : DecidableEq Point4 :=
  inferInstanceAs (DecidableEq ((ℝ × ℝ) × (ℝ × ℝ)))` are saved as a
git stash on the `researcher-1` worktree (label
`WIP-DecidableEq-Point4`). The `DecidableEq Point4` instance is
required because `def Point4 := ...` is an opaque alias that does
not transfer instances; without it `Θ.image lenzCircle1 :
Finset Point4` cannot be elaborated.

**File state at session end**: 164 lines, 10 theorems, 0 axiom
declarations, 2 `opaque` placeholder values for the abstract
extremal functions, 0 sorries — but the file does not currently
build under Lean 4.26.

---

*Generated from erdosproblems.com on 2026-01-13*
