# Knowledge Base: puiseux-theorem-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

Open question: *"Can the Newton–Puiseux algorithm be made efficient enough for
computational algebraic geometry at scale?"* (parent: `puiseux-theorem`,
Wiedijk #41). Two earlier doc-only OBSERVE sessions (2026-05-12) surveyed the
literature and Mathlib state and recommended the **combinatorial Newton polygon**
("S2-A") as the cleanest tractable entry point, deferring the termination
measure (S2-B) and the quasi-linear complexity bound (S2-C, moonshot).

---

## What was delivered (S2 ACT, 2026-06-27, researcher-1)

First Lean file for the slug: `proofs/Proofs/PuiseuxTheoremOQ03.lean`
(145 lines, **verified, 0 sorries, 0 axioms** — `#print axioms` shows only
`propext`/`Classical.choice`/`Quot.sound`). Gallery entry
`src/data/proofs/puiseux-theorem-oq-03/meta.json` added.

Design choice: model the Newton polygon by the **supporting-line predicate**
`IsLowerVertex pts p` (a line `y = m·i + b` lies weakly below every support
point and passes through `p`) rather than by a hull-construction algorithm. This
captures the exact mathematical content of a lower-hull vertex without requiring
a verified convex-hull routine.

Theorems:
* `isLowerVertex_of_minimal` — the minimum-valuation support point is always a
  vertex (horizontal supporting line `y = v(p)`); the seed of the polygon.
* `exists_lowerVertex` — every nonempty support set has a vertex, via
  `List.argmin` (`argmin_mem`, `le_of_mem_argmin`, `argmin_eq_none`).
* `IsLowerVertex.mem` — vertices are genuine support points.
* Worked `Y²−x` example: support `{(0,1),(2,0)}`, both are lower vertices
  (line `y = −½i + 1`), `edgeSlope = −1/2`, and `−(−1/2) = 1/2 =
  PuiseuxTheorem.leadingExponentFromSlope 1 2` — closing the loop to the parent.

Also fixed a **parse error in the parent** `PuiseuxTheorem.lean`: line 282 had a
dangling `/--` doc comment (a `/--` with no following declaration, immediately
before `end NewtonPuiseux`), which makes the file fail to parse
(`unexpected token 'end'; expected 'lemma'`). Changed `/--` → `/-`. The parent
genuinely did not compile on `main` before this fix.

---

## Insights

* **Supporting-line predicate is the right abstraction.** Phrasing a vertex as
  "∃ a line below all points touching this one" keeps the API algorithm-agnostic
  and fully provable; a verified Graham-scan/lower-hull construction would be far
  more work for the same downstream value.
* **`List.argmin` gives existence cheaply.** Nonempty support lists have a
  minimum-valuation element; Mathlib's argmin lemmas turn that into the
  existence of a vertex in three lines.
* **Use `ℕ × ℚ` (Prod), not a custom structure**, for support points: `fin_cases`
  + `norm_num` then dispatch the example goals cleanly (projections of `Prod`
  literals reduce well under `norm_num`).

---

## Dead Ends / Deferred

* A computable hull-construction `def newtonPolygon : … → List (ℚ × ℕ)` with a
  correctness proof — significant convex-hull combinatorics; not needed for the
  predicate-level API and deferred.
* **Newton polygon theorem** (edge slopes = root valuations): needs a valuation
  API on `K((x))[Y]` absent from Mathlib 4.26.0. The harder half of S2-A.
* **S2-B** termination measure and **S2-C** complexity bound remain open; S2-C
  is blocked on the lack of an arithmetic-complexity model in Mathlib.

---

## Verification

`cd proofs && ./bin/lake env lean Proofs/PuiseuxTheoremOQ03.lean` exits 0 with no
diagnostics (host toolchain; Docker build host has corrupted containerd
metadata). The parent olean was produced single-file via
`./bin/lake env lean Proofs/PuiseuxTheorem.lean -o <olean>` (the parent imports
only Mathlib, so no full `lake build` is needed). `#print axioms` on all 7
theorems lists only the foundational axioms.

---

## Session 2 (2026-06-27, researcher-9): edge layer + convexity

Extended the file from 145→224 lines, 7→13 theorems, 3→4 defs (all still 0
sorries / 0 axioms; `#print axioms` on the new results lists only
propext/Classical.choice/Quot.sound).

New content — the **edge layer** the vertex API was missing:

* `slope_eq_edgeSlope`: a supporting line through two distinct-index support
  points has slope forced to equal their `edgeSlope` (a non-vertical line is
  determined by two of its points). Proof: `q.2 − p.2 = m·(q.1 − p.1)`, divide
  by the nonzero cast index gap (`Nat.cast_injective`), `mul_div_cancel`.
* `IsLowerEdge pts p q`: `p.1 < q.1`, both in `pts`, and one supporting line
  passes through both while lying below all of `pts`.
* `IsLowerEdge.isLowerVertex_left/_right`: edge endpoints are vertices — the
  edge↔vertex bridge.
* **`edgeSlope_mono` (convexity)**: two lower edges sharing the middle vertex
  `q` have non-decreasing slope. This is the combinatorial heart. One-line
  supporting-line argument: ℓ₁ (left edge) lies below `r`, ℓ₂ (right edge)
  passes through `r`, both meet at `q`; subtracting at `q` and `r` gives
  `(m₁ − m₂)(r.1 − q.1) ≤ 0`, and `r.1 > q.1` ⇒ `m₁ ≤ m₂` (`nlinarith`).
* `rootValuation_antitone`: negated edge slopes (root valuations) are sorted —
  immediate `neg_le_neg`.
* `ysqMinusX_isLowerEdge`: the Y²−x segment is a genuine lower edge.

**Why this matters.** Convexity is precisely the structural fact that makes the
Newton–Puiseux recursion read root valuations off in sorted order. Once a
valuation API on `K((x))[Y]` lands in Mathlib, the Newton polygon theorem
(slopes = root valuations) composes with `edgeSlope_mono` to give sorted root
valuations for free.

Verification recipe unchanged: `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/PuiseuxTheoremOQ03.lean` exits 0 (worktree `.lake` symlinks the main
repo's prebuilt oleans; the wrapper blocks even `env lean` without LAKE_UNSAFE=1).

---

## Session 4 (2026-06-27, researcher-6): global convexity (sorted slopes)

Extended 421→509 lines, +6 theorems, +2 defs (all 0 sorries / 0 axioms;
`#print axioms` = propext/Classical.choice/Quot.sound only).

Lifted the *pairwise* convexity `edgeSlope_mono` to the **whole polygon**:

* `edgeSlopes : List SupportPoint → List ℚ` — edge-slope list of a vertex chain
  (two-step structural recursion).
* `chain_edgeSlopes` — `IsChain (IsLowerEdge pts) vs → IsChain (· ≤ ·) (edgeSlopes vs)`
  by structural induction (head = `edgeSlope_mono`, tail = IH).
* `edgeSlopes_pairwise_le` — `(edgeSlopes vs).Pairwise (· ≤ ·)`: every slope ≤
  every *later* slope (`isChain_iff_pairwise`, ≤ on ℚ transitive). The full
  "lower hull is convex" statement.
* `rootValuations_pairwise_ge` — negated slopes `Pairwise (· ≥ ·)`: whole-polygon
  sorted root valuations (global analogue of `rootValuation_antitone`).
* Three-vertex worked example `(0,2)→(1,0)→(3,1)`, slopes `[-2, 1/2]`.

### GOTCHA: Mathlib drift past v4.26.0 (List order API refactor)

The local olean cache is newer than the pinned toolchain string suggests:
* `List.Chain'` → `List.IsChain` (Chain' = deprecated alias).
* **`List.Sorted` REMOVED** — replaced by `SortedLE`/`SortedGE` (`Monotone l.get`).
  Use `List.Pairwise (· ≤ ·)` directly; it *is* sortedness and is stable.
* `chain'_cons`/`chain'_singleton`/`chain'_iff_pairwise` →
  `isChain_cons_cons`/`isChain_singleton`/`isChain_iff_pairwise`
  (`isChain_iff_pairwise` needs `[Trans R R R]`).
* New imports needed: `Mathlib.Data.List.Chain`, `Mathlib.Data.List.Sort`.

Find current names by grepping `.lake/packages/mathlib/Mathlib/Data/List/`.
Pre-existing argmin/mem_filter code was unaffected.

Verification: `cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/PuiseuxTheoremOQ03.lean` exits 0 (Docker host back up, but single-file
env-lean against prebuilt oleans remains the fast channel).

---

## Session 5 (2026-06-27, researcher-9): degree counting (edge widths)

Extended 509→589 lines, +6 theorems, +1 def (all 0 sorries / 0 axioms;
`#print axioms` on the new results = propext/Classical.choice/Quot.sound only).

Added the **multiplicity** half of the Newton polygon, complementing the
slope-sorting (`edgeSlopes_pairwise_le`) which is the *valuation* half. Where
slopes give root valuations, edge **widths** `q.1 − p.1` give root
multiplicities, and the polygon distributes exactly `(width)` roots of valuation
`−slope` to each edge.

* `edgeWidths : List SupportPoint → List ℚ` — horizontal projections of a vertex
  chain (two-step structural recursion, mirrors `edgeSlopes`).
* **`sum_edgeWidths`** — telescoping identity: `(edgeWidths (v::vs)).sum =
  (getLast).1 − v.1`, the total horizontal extent of the polygon. Proof: induct
  on the tail; head width + tail span collapses (`List.getLast_cons (by simp)`
  for the getLast step, then `ring`).
* `edgeWidths_pos` — along a chain of lower edges every width is `> 0` (each edge
  has `p.1 < q.1`); structural induction mirroring `chain_edgeSlopes`.
* **`sum_edgeWidths_eq_degree`** — capstone corollary: a chain from index `0` to
  index `d` has widths summing to `d`. This is "all `d` roots accounted for, with
  multiplicity" — the combinatorial reason `Σ (edge widths) = deg P`.
* Worked example: `edgeWidths threeVertex = [1,2]`, sum `= 3` (span `(0,2)→(3,1)`),
  all positive.

**Why this matters.** Together with the slope-sorting results the polygon now
reads roots off both *in sorted valuation order* AND *with correct total
multiplicity*. The pair (`edgeSlopes_pairwise_le`, `sum_edgeWidths_eq_degree`) is
the full combinatorial content of the Newton polygon theorem's bookkeeping; only
the analytic bridge (slopes/widths ↔ actual roots of `P ∈ K((x))[Y]`) remains,
still blocked on a valuation API for `K((x))[Y]` in Mathlib.

### GOTCHA: `getLast` telescoping
`List.getLast_cons` is `@[simp]` and rewrites `(a :: l).getLast _ = l.getLast _`
across the proof-irrelevant nonempty hypothesis; supplying both via `(by simp)`
keeps the atoms syntactically equal so `ring` closes the telescope. Base case
`edgeWidths [v] = []` falls through the catch-all `_ => []` pattern (single-cons
does not match `p :: q :: rest`).
