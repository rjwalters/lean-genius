# Erdős #660 — Distinct Distances in Convex Polyhedra

**Status:** OPEN (formalized scaffold; main conjecture remains a `sorry`)
**Lean file:** `proofs/Proofs/Erdos660Problem.lean` (registered in `Proofs.lean`)
**Companions:** `Erdos660Aristotle.lean` (0 sorries), `Erdos660ProblemAristotle.lean`

## Problem

For the vertices $x_1,\dots,x_n \in \mathbb{R}^3$ of a convex polyhedron, are there at
least $(1-o(1))\cdot n/2$ distinct pairwise distances? This is the 3D analogue of
Altman's 1963 result ($\ge \lfloor n/2\rfloor$ for convex polygons in $\mathbb{R}^2$).
The 3D case is open; even a weaker linear bound $\Omega(n)$ is open.

## Proof State

The main conjecture and the named classical results are genuinely OPEN/HARD and
stay axiomatized as `sorry`:
- `erdos_660_conjecture` — OPEN (the problem itself)
- `linear_lower_bound_conjecture` — OPEN (weaker form)
- `altman_convex_polygon_distances` — known (Altman 1963), HARD to formalize
- `guth_katz_distinct_distances` — known (Guth–Katz 2015), HARD to formalize
- 5 Platonic-solid construction theorems — require explicit coordinates plus
  `IsConvexPolyhedronVertices` (extreme points of the convex hull), HARD

## Sessions

### Session 2026-06-19 (s01) — FRESH

**Mode:** FRESH. **Outcome:** progress (1 sorry eliminated, 6 verified theorems added).

**What I did**
- Step 0 (preamble): inspected the Aristotle companions. `Erdos660Aristotle.lean`
  already proves (0 sorries) the supporting lemmas, including `trivial_lower_bound`
  over its own local `dist`-based definitions in namespace `Erdos660.Aristotle`.
- Integrated that work into the main registered file by porting the proofs to the
  main file's `euclideanDist`-wrapped `pairwiseDistances`/`distinctDistances`:
  - `trivial_lower_bound` — replaced the `sorry` with a real proof
    (`Finset.one_lt_card` → a positive distance lies in the filtered image →
    `Finset.card_pos`).
  - Added a **Verified base cases** subsection (all machine-checked):
    `pairwiseDistances_empty`, `distinctDistances_empty`,
    `pairwiseDistances_singleton`, `distinctDistances_singleton`,
    `two_point_one_distance` (exactly one distance for a 2-point set),
    `distinctDistances_mono` (monotone under adding vertices).

**Build verification**
- Docker build GREEN (`./proofs/scripts/docker-build.sh Proofs.Erdos660Problem`):
  `Build completed successfully (7743 jobs)`, exactly 9 `sorry` warnings, 0 errors.

**Key findings**
- The companion lemmas are stated over a *separate* `dist`-based definition, so the
  main file gained nothing from them until ported through the `euclideanDist` def.
  `euclideanDist p q := dist p q` is definitionally `dist`, so `simp [euclideanDist]`
  (and `rfl` on image witnesses) bridges the two.
- **Gotcha:** `pairwiseDistances` images over `S.product S` (a `Finset.product`).
  `simp only [..., Finset.mem_product]` does NOT fire on the membership produced by
  `Finset.mem_image` (linter flags it "unused"), so anonymous-constructor witnesses
  `⟨(p,q), ⟨hp, hq⟩, rfl⟩` fail: "expected type `Quot.lift … (S.product S).val` is
  not an inductive type". Fix: build/destruct product membership *explicitly* with
  `Finset.mem_product.mpr ⟨hp, hq⟩` / `Finset.mem_product.mp hab`, keeping only
  `Finset.mem_image` in the `simp only` set. This bit both `trivial_lower_bound`
  and `two_point_one_distance`.
- `distinctDistances_mono` is the one genuinely *structural* fact here: any lower
  bound for the conjecture must be consistent with monotonicity under vertex
  addition. The empty/singleton/two-point cases pin the base of the count.

**Files modified**
- `proofs/Proofs/Erdos660Problem.lean` (theoremCount 10→16, sorries 10→9)
- `src/data/proofs/erdos-660/meta.json` (counts; status stays `formalized`)

**Next steps**
- The Platonic-solid construction theorems are the next tractable targets, but each
  needs an explicit vertex set in `EuclideanSpace ℝ (Fin 3)` *and* a proof of
  `IsConvexPolyhedronVertices` (extreme points of the hull) — non-trivial in Lean.
  Octahedron $\{\pm e_i\}$ is the most approachable (2 distances: edge $\sqrt2$,
  diagonal $2$); could be submitted to Aristotle.
- Main conjecture stays OPEN — do not submit to Aristotle.
