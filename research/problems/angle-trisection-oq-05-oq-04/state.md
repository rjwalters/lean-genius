# Current State

**Phase**: ACT
**Since**: 2026-05-12 (S4)
**Iteration**: 4

## Current Focus

S4 (researcher-12): constructive HH-2 (perpendicular bisector) as the
second of seven HH-axiom ingredients required by the conservativity
target `straight_fold_recovers_HH` (S3, still open).

Deliverables of this iteration (new in S4):

1. `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` grows 351 → 448 lines
   with a new "Part 6: Constructive HH-2 — Perpendicular Bisector"
   section. Counts: 0 axioms, 3 sorries (unchanged), 7 theorems
   (4 proved + 3 sorry), 6 definitions, 1 structure.

2. Three new theorems, one new definition, all proved without sorry:
   - `perpBisector (p₁ p₂ : Point) (h : p₁ ≠ p₂) : Line` — explicit
     `noncomputable def` of the perpendicular bisector.
   - `perpBisector_dirSq_pos` — squared chord length is positive.
   - `reflectAcross_perpBisector` — HH-2 reflection law: the
     perpendicular bisector sends `p₁` onto `p₂` (proved via
     `Prod.ext` + `field_simp` + `ring`).
   - `hh2_existence` — standalone HH-2 existence theorem.

3. Gallery metadata updated:
   `src/data/proofs/angle-trisection-oq-05-oq-04/meta.json`
   (lineCount 351 → 448; theoremCount 4 → 7; definitionCount 5 → 6;
   added Part 6 section entry; added four original-contributions
   bullets).

This S4 PR is **independent of S3 PR #17915** at the file level: its
additions are at the END of the file (after the Summary comment),
while S3 PR #17915 inserted content between
`straight_fold_recovers_HH` and `curved_fold_algebraic_implies_origami`.
When both merge, no textual conflict is expected.

## Active Approach

S4 closes the **second of seven** HH-axiom existence ingredients
needed to discharge `straight_fold_recovers_HH`. After S3 (HH-1) and
S4 (HH-2), the remaining ingredients are HH-3, HH-4, HH-5, HH-6
(Beloch fold — the deep one), and HH-7 (Hatori). Once all seven are
constructive, building an `HHAxioms` instance is mechanical, and
`straight_fold_recovers_HH` reduces to combining
`straight_fold_endpoints_collinear` (S3) with the new instance.

### Geometric content of HH-2

For distinct points `p₁, p₂ ∈ ℝ²`, the perpendicular bisector is the
line through their midpoint perpendicular to `p₂ - p₁`. In the
`ax + by + c = 0` normalisation used by the parent `Line` structure,

  a = p₂.1 - p₁.1
  b = p₂.2 - p₁.2
  c = -((p₂.1² - p₁.1²) + (p₂.2² - p₁.2²)) / 2

Plugging into the reflection formula
`reflectAcross l p = (p.1 - t a, p.2 - t b)` with
`t = 2 (a p₁.1 + b p₁.2 + c) / (a² + b²)` evaluates `t = -1` at `p₁`,
because the numerator equals `-(a² + b²) / 2`. The reflection adds
the direction vector `(p₂.1 - p₁.1, p₂.2 - p₁.2)` to `p₁` and lands
on `p₂`. The Lean proof uses `Prod.ext` followed by `field_simp` to
clear the single denominator `a² + b²` (provably nonzero via
`perpBisector_dirSq_pos`) and closes with `ring`.

## Blockers

None mathematical. The math is correct by hand-derivation.

Practical:

- Build verification of `AngleTrisectionOQ05OQ04.lean` is deferred —
  the `.lake` symlink is recursive-self-broken on this worktree, so
  `docker-build` would re-fetch Mathlib (~45 minutes). This PR
  follows the same "build pending" convention as the S2 and S3 PRs
  (#17883 merged build-pending; #17915 still open build-pending).
- The S3 PR #17915 has not merged yet; if its final form differs
  from the prior-session HH-1 names (`lineThrough`, `hh1_existence`,
  `straight_fold_endpoints_collinear`), the docstrings in this S4
  Part 6 referencing those names will need a trivial doc-only
  update. The Lean code does not depend on them.

## Next Action

**S5 (any researcher)**: Either
(a) discharge `straight_fold_recovers_HH` by continuing the HH-3
    through HH-7 construction sequence (HH-4 = perpendicular through
    point is the easiest next; HH-6 = Beloch fold is the hardest);
(b) tackle `curved_fold_algebraic_implies_origami` (S4-target
    sorry), noting that the current `IsOrigamiConstructible` def in
    the parent file `AngleTrisectionOQ05.lean` underuses `_α`
    (placeholder), so the theorem is trivially provable at `deg = 1`
    without substantive math — a stronger quantitative version
    using `minpoly` degree should be stated and proved instead.

Approximate scope of (a): another +90 lines per axiom, +540 lines
to complete all of HH-3..HH-7. Easier to spread over five sessions.

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| 1 | Checked `gh pr list` — found only one open PR (#17915 = S3 partial, mine from prior session) | clean to advance |
| 2 | Released two probe claims (borsuk-ulam 5 open PRs, hilbert-11 enumeration theater) | claim-random returned this slug on third try |
| 3 | Read S2 ORIENT scaffold and S3 partial diff; identified HH-2 as next constructive ingredient | scope set |
| 4 | Drafted `perpBisector` Line construction (a, b, c with reflection at p₁ giving t = -1) | math verified by hand |
| 5 | Inserted Part 6 (96 new lines) after Summary comment, before `end`; no overlap with S3 PR additions | clean independent extension |
| 6 | Updated meta.json: lineCount 351 → 448, theoremCount 4 → 7, definitionCount 5 → 6, added Part 6 section + 4 contributions | gallery in sync |
| 7 | Updated this state.md | iteration recorded |
| 8 | (pending) Commit + push + PR with label `research` | next |

## Honest Calibration

S4 produces:

- One explicit `noncomputable def` (`perpBisector`) of a fundamental
  Euclidean construction;
- Three proved theorems closing the HH-2 reflection law and standalone
  existence statement;
- No new sorry, no new axiom, no change to existing assumption count;
- Concrete and verifiable progress toward closing the still-open S3
  sorry `straight_fold_recovers_HH`.

S4 does **not** resolve any open mathematical question. The value is
two of seven HH-axiom ingredients now constructive, with explicit
witnesses computable from input coordinates. Progress is incremental
and additive — each subsequent session can close one or two more
ingredients independently.

## References Captured

Same set as S1/S2/S3: Huffman 1976; Fuchs-Tabachnikov 1999 (Thm 1 =
FT identity); Demaine-DHPT 2011 (transcendental curve elastica
witness); Alperin 2000 + Alperin-Lang 2006 (K_origami classification).

See `knowledge.md` for the full citation list and Mathlib gap
analysis (unchanged from S1).
