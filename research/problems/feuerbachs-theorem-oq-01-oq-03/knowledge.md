# Feuerbach via Inversive Geometry (feuerbachs-theorem-oq-01-oq-03)

**Open question**: Can Feuerbach's tangency configuration be understood via
inversive geometry centered at the Feuerbach point?

## Summary

The Lean proof source already exists and is complete: `proofs/Proofs/FeuerbachsTheoremOQ01OQ03.lean`
(287 lines, **0 sorries, 0 axioms** in source) builds an inversive-geometry
framework and answers the OQ affirmatively. However, the slug had no research
bookkeeping and no gallery `meta.json`, and the research tracker still listed it
as `available`. This session is an ORIENT survey reconciling that state.

## What the existing proof establishes

Working in `Point := ℝ × ℝ` with `dot`/`normSq` and an inversion map
`invert r P = (r²/normSq P) • P`:

1. **Inversion basics** — `invert_normSq`, `invert_involution` (φ_r is an
   involution off the origin), `dot_invert_self`.
2. **Circle-to-line** (`invert_circle_to_line`): a circle through the origin
   O, i.e. `|P|² = 2(P·C)`, maps under φ_r to the line `φ_r(P)·C = r²/2`;
   converse `line_to_circle`.
3. **Parallel lines** (`invert_parallel_lines`): two origin-circles with
   collinear centers C₁=λ₁e, C₂=λ₂e map to the parallel lines
   `Q·e = r²/(2λ₁)` and `Q·e = r²/(2λ₂)`.
4. **Feuerbach collinearity** (`feuerbach_centers_collinear`): the Feuerbach
   point F, incenter I, and nine-point center N are collinear
   (`incenter_feuerbach_dir`, `ninepoint_feuerbach_dir`,
   `feuerbachPoint_coords`).
5. **Framework assembly** (`feuerbach_inversive_framework`).

This is the inversive-geometry reading the OQ asks for: tangency of the incircle
and nine-point circle becomes "two circles through O map to parallel lines"
under inversion centered at the tangency (Feuerbach) point.

## Status assessment (2026-06-13)

| Aspect | State |
|--------|-------|
| Lean source | Complete on origin/main: 0 sorries, 0 axioms |
| Docker build verification | **UNCONFIRMED** — no gallery `meta.json` records a `verified` status, and the file's last commit is an unrelated audit batch (#22746), not a build. Docker is down (verification blackout), so cannot confirm now. |
| Gallery integration | **MISSING** — no `src/data/proofs/feuerbachs-theorem-oq-01-oq-03/` directory. |
| Research tracker | Was `available` (stale) — corrected to `in-progress` to reflect that source exists but integration/verification is pending. |

## Next steps (post-Docker)

1. `./proofs/scripts/docker-build.sh Proofs.FeuerbachsTheoremOQ01OQ03` to confirm
   the source compiles against current Mathlib.
2. If it builds clean: create `src/data/proofs/feuerbachs-theorem-oq-01-oq-03/meta.json`
   (status `verified`, badge `original`, 0 sorries, 0 axioms) so the proof
   surfaces in the gallery; then flip tracker status to `completed`.
3. If it fails on Mathlib drift: repair, otherwise the inversive framework is
   mathematically complete and the fix should be mechanical.

## References

- Lean: `proofs/Proofs/FeuerbachsTheoremOQ01OQ03.lean`, depends on `Proofs.FeuerbachsTheoremDefs`
- Parent: `src/data/proofs/feuerbachs-theorem-oq-01/`
- Gallery: Feuerbach's theorem family (`feuerbachs-theorem`, `-oq-01`, `-oq-02`, `-oq-05`)
