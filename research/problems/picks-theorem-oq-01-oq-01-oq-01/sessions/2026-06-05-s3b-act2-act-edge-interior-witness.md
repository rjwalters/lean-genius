# S3b-act-2 ACT — Case (a) witness for `exists_nonvertex_lattice_point`

**Date**: 2026-06-05
**Agent**: researcher-1
**Phase**: ACT (Lean code shipped + Docker-verified)
**Status**: Implements S3b-act-2 PREP (#22311, 2026-06-04). Docker GREEN
verified by S4 STATE-SYNC (#22016, 2026-06-02).

---

## What shipped

`proofs/Proofs/PicksTheoremOQ01OQ01OQ01.lean`: **721 → 858 LOC** (+137).
3058 Docker jobs clean at v4.26.0; file remains 0 sorries, 0 axioms.

New section IX (S3b-act-2):

| Item | Kind | Purpose |
|---|---|---|
| `LatticeTriangle.vEdgeStart` | def `Fin 3 → ℤ × ℤ` | Start vertex of edge `i` |
| `LatticeTriangle.vEdgeEnd` | def `Fin 3 → ℤ × ℤ` | End vertex of edge `i` |
| `LatticeTriangle.edgeGCD_eq_Int_gcd` | lemma | Bridges `edgeGCD` (over `Nat.gcd ∘ natAbs`) to `Int.gcd` of signed differences |
| `LatticeTriangle.OnStrictEdgeInterior` | def `Prop` | Membership in the edge interior (on the segment, ≠ endpoints) |
| `exists_nonvertex_lattice_point_of_edgeGCD_ge_two` | theorem | **Case (a) witness**: edge with `gcd ≥ 2` has a strict-interior lattice point |

---

## The witness

For edge `i` with `edgeGCD i ≥ 2`, set `g = Int.gcd dx dy` (where
`(dx, dy) = vEdgeEnd i - vEdgeStart i`). The witness is

```
p := (vEdgeStart i).fst + dx / g,  (vEdgeStart i).snd + dy / g
   -- i.e. the parameter-k=1 point of the gcd parametrisation
```

Three obligations:

1. **`p ∈ latticeSegmentPoints (vEdgeStart i) (vEdgeEnd i)`** —
   `Finset.mem_image.mpr ⟨1, _, _⟩` with `1 ∈ Finset.range (g+1)` from `g ≥ 2`.
2. **`p ≠ vEdgeStart i`** — equality of x-components forces `dx/g = 0`;
   combined with the y-component and `g ∣ Δ`, this gives `dx = dy = 0`,
   forcing `g = Int.gcd 0 0 = 0`, contradicting `g ≥ 2`.
3. **`p ≠ vEdgeEnd i`** — equality forces `dx/g = dx` and `dy/g = dy`.
   Multiply by `g` (using `g ∣ Δ`) to get `dx · g = dx`, i.e.
   `dx · (g - 1) = 0`. With `g ≥ 2` and `mul_eq_zero`, conclude `dx = 0`
   (and symmetrically `dy = 0`), then `g = 0`, ⊥.

---

## Departures from the PREP paste

**`edgeGCD_eq_Int_gcd` extracted as a top-level lemma.** The PREP inlined
the bridge with a `simp only [edgeDelta, vEdgeStart, vEdgeEnd, ...] <;>
rfl` chain inside the main proof. I extracted it as a named lemma
(`fin_cases i <;> rfl`) for clarity and to reuse if Case (b) or
follow-ups need the same identity. Trivial proof — `Int.gcd a b =
Nat.gcd a.natAbs b.natAbs` is the definition; `edgeDelta i` is defined
to use the same `natAbs` of the same signed differences as `vEdgeStart/End`.

**`Finset.mem_range.mpr (by omega)` split into two sub-goals.** The
direct `refine Finset.mem_image.mpr ⟨1, Finset.mem_range.mpr (by omega),
?_⟩` failed in the initial attempt because after `unfold
latticeSegmentPoints`, the inner `let g_inner := Int.gcd dx dy` is not
folded back to the outer `set g := Int.gcd dx dy` from omega's point
of view. omega saw the goal as `1 < (some Int.gcd) + 1` with no
hypothesis on the inner term.

Fix: use a `show 1 ∈ Finset.range (g + 1)` to bridge the
definitional gap, then `Finset.mem_range.mpr (by omega)`. The `show` is
accepted by Lean's defeq checker (the inner `let` and outer `set` are
zeta-equal), so the goal is reformulated using `g`, and omega gets
`hg : 2 ≤ g` plus goal `1 < g + 1`, which it handles trivially.

The second hole (the function-value equation) is shipped via an
explicit `show ... = ...` followed by `simp` to handle `1 * x = x`.

---

## Build verification

```
$ ./proofs/scripts/docker-build.sh Proofs.PicksTheoremOQ01OQ01OQ01
...
✔ [3058/3058] Built Proofs.PicksTheoremOQ01OQ01OQ01 (10s)
Build completed successfully (3058 jobs).
=== Build succeeded ===
```

Docker daemon was GREEN (S4 STATE-SYNC confirmed 2026-06-02 → reconfirmed
2026-06-05 at job start). No infra blockers.

---

## Bearer audit (Mathlib v4.26.0, pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

Final bearer set used (subset of PREP's 7-bearer table):

| Bearer | Path | Purpose |
|---|---|---|
| `Int.gcd_dvd_left` | `Mathlib/Data/Int/GCD.lean` | `(g : ℤ) ∣ dx` (witness ≠ v, ≠ w) |
| `Int.gcd_dvd_right` | `Mathlib/Data/Int/GCD.lean` | `(g : ℤ) ∣ dy` (witness ≠ v, ≠ w) |
| `Int.ediv_mul_cancel` | core Lean `Init/Data/Int/DivMod` | `(dx/g) * g = dx` from `g ∣ dx` |
| `Finset.mem_image` | `Mathlib/Data/Finset/Image.lean` | Membership in `latticeSegmentPoints` |
| `Finset.mem_range` | `Mathlib/Data/Finset/Range.lean` | `1 ∈ range (g + 1) ↔ 1 < g + 1` |
| `mul_eq_zero` | `Mathlib/Algebra/Ring/Defs.lean` | `dx · (g - 1) = 0 → dx = 0 ∨ g = 1` |

Two bearers from the PREP table were **not** needed in the final proof:

- `Int.natAbs_sub_comm` — the `edgeGCD_eq_Int_gcd` lemma closes by pure
  `rfl` after `fin_cases`, with no orientation flip required. The PREP
  conjectured a sign-flip in edge 2; in fact `edgeDelta 2` is already
  defined as `(v1 - v3)`, matching `vEdgeStart 2 → vEdgeEnd 2 = v3 → v1`
  so `dx = v1.1 - v3.1`. Direct `rfl`. No sub-comm needed.

NO v4.26.0 risk realised. All bearers pin-stable since v4.0.

---

## What this unlocks

The remaining hard step toward
`exists_nonvertex_lattice_point` is **Case (b)** (Minkowski-style
interior witness for primitive lattice triangles with `twiceArea ≥ 2`).
Once Case (b) lands, the combined statement
`∀ T (h : ¬ T.IsTrivial), ∃ p ≠ T.v1 ∧ p ≠ T.v2 ∧ p ≠ T.v3, ...`
follows by:

- If some `edgeGCD i ≥ 2`: use Case (a) (this PR).
- Else all `edgeGCD i = 1` (i.e. `T` is primitive on every edge):
  use Case (b) on the strict triangle interior.

S3b PREP §4.1.b recommends approach **(b.ii)** (Euclidean-algorithm-on-
edge-vectors) as the preferred non-circular route to Case (b).

---

## Files modified

- `proofs/Proofs/PicksTheoremOQ01OQ01OQ01.lean` (+137 LOC, 721 → 858)
- `research/problems/picks-theorem-oq-01-oq-01-oq-01/sessions/2026-06-05-s3b-act2-act-edge-interior-witness.md` (this report)
- `research/problems/picks-theorem-oq-01-oq-01-oq-01/state.md` (Phase + iter increment)
- `research/problems/picks-theorem-oq-01-oq-01-oq-01/knowledge.md` (S3b-act-2 ACT entry)

## Phase head transition

S3b-act-2 PREP (#22311, 2026-06-04, paste-ready code) →
**S3b-act-2 ACT (this PR, code shipped + Docker-verified)** →
S3b-act-3 next picker (Case (b) primitive-triangle interior witness via
Euclidean-algorithm-on-edge-vectors, S3b PREP §4.1.b approach (b.ii),
~50–100 LOC estimated). After Case (b), the combined
`exists_nonvertex_lattice_point` statement is one short corollary away.
