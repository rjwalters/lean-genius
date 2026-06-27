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
