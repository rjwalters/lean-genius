# de Gua's Theorem (pythagorean-theorem-oq-06)

## Problem Summary

Formalize **de Gua's theorem**, the 3-D analogue of the Pythagorean theorem:
for a *trirectangular tetrahedron* `O A B C` (three mutually perpendicular edges
meeting at vertex `O`), the squared area of the face `ABC` opposite `O` equals
the sum of the squared areas of the three right-angle faces:

  Area(ABC)² = Area(OAB)² + Area(OBC)² + Area(OCA)².

## Status: COMPLETE (build-pending verification)

Proof written in `proofs/Proofs/DeGuaTheorem.lean` — **0 sorries, 0 axioms**.

## Approach (verified sound)

Work in ℝ³ as `Fin 3 → ℝ` with the standard squared-area formula
`Area(PQR)² = ¼‖(Q−P)×(R−P)‖²`. Writing the perpendicular edges as
`u = A−O, v = B−O, w = C−O`, the hypotenuse-face edges are `v−u, w−u` and

  (v−u)×(w−u) = u×v + v×w + w×u.

Expanding the squared norm produces the three leg-face terms plus a cross-term
`2[(u×v)·(v×w) + (v×w)·(w×u) + (w×u)·(u×v)]`. By Binet–Cauchy,
`(a×b)·(c×d) = (a·c)(b·d) − (a·d)(b·c)`, each cross term is a combination of
pairwise dot products that vanishes under the orthogonality hypotheses
`u·v = v·w = w·u = 0`. The residual polynomial identity is discharged by
`linear_combination` with explicit coefficients.

### Key built items
- `de_gua_core` (edge-vector form): `crossSq (v-u) (w-u) = crossSq u v + crossSq v w + crossSq w u` under mutual orthogonality. Closed by `linear_combination`.
- `de_gua` (vertex form): full statement for tetrahedron `O A B C`, reduced to `de_gua_core` via `B−A = (B−O)−(A−O)`.
- `de_gua_axis_aligned` (canonical model, legs `a,b,c` on the axes): pure `ring`.

### Verification note
The `linear_combination` coefficients were verified numerically over 10⁵ random
integer samples (both the general orthogonal identity and the axis-aligned
special case) before formalizing — the algebra is exact, so the only residual
risk is Lean elaboration mechanics (def unfolding / `simp only` of `crossSq`,
`dot`, `Pi.sub_apply`).

## Mathlib gaps
None blocking. Used only `Mathlib.Tactic` (`linear_combination`, `ring`). Defined
`dot`/`crossSq`/`areaSq` locally in coordinates to keep the proof self-contained
and avoid `Matrix`/`Fin` indexing fragility.

## Next steps
1. Build-verify `Proofs.DeGuaTheorem` (Docker), then register in `Proofs.lean`.
2. Add gallery data under `src/data/proofs/de-gua-theorem/` (or `pythagorean-theorem-oq-06`).
3. Optional follow-up: n-simplex generalization (Conant/Beeler) — squared
   "volume" of the hypotenuse facet equals sum of squared facet volumes; or the
   sharp-boundary question (de Gua fails without mutual orthogonality — quantify
   the defect via the surviving cross term).

## Sessions

### Session 2026-06-16 (Session 1) — FRESH

**Mode**: FRESH
**Outcome**: complete (build-pending)

#### What I Did
- Claimed `pythagorean-theorem-oq-06`; confirmed de Gua not yet in gallery or Mathlib.
- Derived the proof via cross-product expansion + Binet–Cauchy; numerically verified the `linear_combination` coefficients over 10⁵ samples.
- Wrote `proofs/Proofs/DeGuaTheorem.lean` (3 theorems, 0 sorry / 0 axiom).
- Launched Docker build of `Proofs.DeGuaTheorem` under the dual-blackout conditions (Aristotle 404; host `proofs/.lake` self-symlink) — cache volume + oleans confirmed accessible inside the container.

#### Key Findings
- The dangling `.lake` symlink does **not** block: Docker mounts the cache volume at `/workspace/proofs/.lake/build` and Mathlib oleans are present; lake re-clones only the Mathlib *source* (packages dir not volume-mounted).
- de Gua reduces cleanly to a single polynomial identity; no heavy geometry infrastructure needed.

#### Files Modified
- `proofs/Proofs/DeGuaTheorem.lean` (new)
- `research/problems/pythagorean-theorem-oq-06/knowledge.md`, `state.md`
- `src/data/research/problems/pythagorean-theorem-oq-06.json`

#### Next Steps
Build-verify, register in `Proofs.lean`, add gallery data.
