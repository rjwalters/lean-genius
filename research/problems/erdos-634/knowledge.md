# Erdős #634 — Triangle Dissection into Congruent Pieces

Status: gallery entry present (`Erdos634Problem.lean`), status `axiomatized`.
The general classification of (T, R, N) is OPEN ($25 prize).

## Session (researcher-6, 2026-07-09): soundness repair of the base entry

The shipped entry `Erdos634Problem.lean` was **logically inconsistent** — it
could derive `False` two independent ways. Both fixed in PR #36318.

1. **Area-only `IsDissectable` contradicted Beeson.** Dissectability was defined
   by area balance alone (`∑ pieceᵢ.area = T.area`). The companion
   `Erdos634AreaCollapse.lean` (merged, PR #35219, 0-axiom) proves this holds for
   *every* `n ≥ 1` (n equilateral pieces of side `1/√n`). Hence `IsDissectable 7`
   is provable, contradicting the axiom `¬IsDissectable 7`.
   **Fix:** added an abstract `axiom Tiles (T) (n) (pieces) : Prop`
   (covering + interior-disjointness) and made
   `IsDissectable n := ∃ T D, IsCongruentDissection T n D ∧ Tiles T n D.pieces`.
   The `Tiles` conjunct blocks the trivial equal-area witness, so Beeson's
   negatives are now consistent. `Tiles` stays abstract because Mathlib has no
   polygonal-tiling API.

2. **`congruent_implies_similar` was a `sorry` on a FALSE statement.** `Congruent`
   is on the unordered side multiset, but `Similar` was order-pinned
   (`T₂.a = k·T₁.a ∧ …`), which congruence does not imply (`(3,4,5)` vs `(4,3,5)`).
   **Fix:** restated `Similar` on the unordered multiset (faithful, relabelling-
   invariant); the theorem is now a real 1-liner
   `⟨1, one_pos, by simpa only [Congruent, one_mul] using h.symm⟩`.

Counts after: axioms 3→4, sorries 6→5 (the 5 remaining are the genuine reptiling
constructions `squares/two/three/six/sum`, blocked only on a Mathlib tiling API).

### Verification note
File elaborated cleanly: a Docker build reached
`[7743/7743] Building Proofs.Erdos634Problem (2.5s)` with zero type errors.
A fully green olean write was not obtainable this session (host Docker containerd
I/O errors + intermittent Mathlib-cache corruption / SIGBUS-135 under fleet load —
pure infrastructure, never type/math errors).

### Remaining / next directions
- The real open frontier is a **non-abstract `Tiles`**: a Mathlib polygonal-tiling
  API (covering + interior-disjoint measurable pieces). The `-oq-02` covering line
  (`Erdos634MedialCoveringOQ02.lean`) is the concrete-covering seed.
- Mathematically #634 itself (classification of achievable N) is open; `n=19` is
  the smallest unknown; `4k+3` prime conjecture (excluding 3).

## Session (researcher-3, 2026-07-09): interior-disjointness of the medial subdivision (corner pieces)

New file `Erdos634MedialDisjointOQ02.lean` — VERIFIED, clean Docker build
`[7744/7744] Built Proofs.Erdos634MedialDisjointOQ02 (5.5s)`, 0 axioms / 0 sorries.

Supplies the *interior-disjointness* complement of the covering line
(`Erdos634MedialCoveringOQ02` proved the covering half of oq-02). Over a
**non-degenerate** triangle (`LinearIndependent ℝ ![B - A, C - A]`, the two edge
vectors at `A` independent), the three **corner** medial pieces meet pairwise in
exactly one point — the midpoint of their shared side — hence have disjoint
interiors:

- `bary_unique` — barycentric coordinates unique in a non-degenerate triangle.
  Derived directly from `LinearIndependent.pair_iff` (no `AffineIndependent`
  API): from `a•A+b•B+c•C = a'•A+b'•B+c'•C` with unit sums, substitute
  `a=1-b-c`, then `linear_combination (norm := module) h` yields
  `(b-b')•(B-A)+(c-c')•(C-A)=0`, and pair_iff pins the coefficients.
- `pieceA_inter_pieceB = {midpoint A B}`, `pieceB_inter_pieceC = {midpoint B C}`,
  `pieceA_inter_pieceC = {midpoint C A}`. Proof recipe: expand each point's two
  triHull representations into `A B C`-barycentric form via the same
  `simp only [midpoint_eq_smul_add, invOf_eq_inv]; module` idiom as the covering
  file's `piece*_subset`; apply `bary_unique`; the resulting linear system forces
  the two apex coordinates to `1/2` (all discharged by `linarith`), pinning the
  point to the shared midpoint.

Reuses `triHull` from `Erdos634MedialCoveringOQ02` (imported), so results compose
with the covering statements.

### Still open on the oq-02 tiling frontier
- Interior-disjointness of each corner piece against the **central** piece (they
  meet in a shared *edge*, a `triHull` of two midpoints — a segment, not a point).
- The measure/area accounting to upgrade covering + interior-disjointness to a
  fully quantitative tiling (needs a Mathlib area/measure-of-triangle input).
