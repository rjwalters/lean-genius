# Knowledge: knights-tour-oblique-oq-01-oq-02

## Result (researcher-9, 2026-06-26) — SOLVED, build-verification in progress

Rectangular generalization of the square-board oblique lower bound
(`knights-tour-oblique-oq-01`, `four_oblique_corners`).

**Theorem `four_oblique_corners_rect`**: every closed knight's tour on an m×n
board with m, n ≥ 5 has ≥ 4 oblique (>90°) turns, one forced at each corner.

### Approach
Reparameterize `SquareN n = Fin n × Fin n` as `SquareMN m n = Fin m × Fin n`,
and `n·n` as `m·n`. The entire square-case proof transports verbatim:
- corner degree 2 (each corner has exactly 2 knight neighbours), row bound m and
  column bound n act independently → squareness unused;
- entry/exit dot product at each corner is the constant −4 < 0 (aspect-ratio
  independent; the n−1 / m−1 coordinates cancel in the move-vector differences);
- closed tour visits all m·n squares; cyclic predecessor/successor of a corner
  index are its two (distinct, by nodup) neighbours → `corner_forces_oblique`.

5 corner-geometry lemma groups + tour-coverage + main theorem. 0 sorries, 0 axioms.
562 lines. File: `proofs/Proofs/KnightsTourObliqueOQ01OQ02.lean`,
namespace `KnightsTourObliqueRect`.

### Build status — VERIFIED (2026-06-26, researcher-9 cont.)
Docker build now completes green (3060 jobs, only cosmetic `unusedSimpArgs` /
`unnecessarySeqFocus` lint warnings, 0 errors). Entry is genuinely `verified`.

**Bug fixed before it built:** the original draft's `four_oblique_corners_rect`
proof claimed verification but did NOT compile. Three `omega` calls in the
wrap-around index lemma `hpn` failed because `omega` cannot reason about the
nonlinear product `m * n` — the in-scope `hpos : 0 < m * n` was too weak to rule
out `m * n = 2` (needed to show the cyclic predecessor and successor of an index
are distinct). Fix: add `have hbig : 25 ≤ m * n := by have := Nat.mul_le_mul hm hn; omega`
to the main theorem context, giving `omega` the linear fact it needs. Lesson:
`omega` treats `m * n` as an atom — any bound on a product must be supplied as an
explicit hypothesis.

### Key insight for the gallery
The oblique lower bound of 4 is a CORNER phenomenon, independent of board shape —
this separates the shape-independent floor (4) from the genuinely shape-dependent
open questions (exact minimum, uniqueness, full distribution).

### Follow-ups (depth guard: slug has 2 `-oq-` segments, under cap 3)
- Long thin boards (m=5, n→∞): does the minimum stay 4 or grow?
- Do degree-3/4 boundary (non-corner) cells force additional oblique turns?
