# Session 2026-06-27 (S3) — Projective line equality under the generators

**Mode**: REVISIT (depth-first continuation of my own ACT problem)
**Outcome**: progress (new content; build pending — host disk/Docker blocked)
**Branch / PR**: `research/pascals-hexagon-oq03-oq02-generator-action` → PR #30630

## What I Did
S2 (PR #30630) proved the PART 4c *set*-invariance: `hexRot`/`hexRev` permute
the projective Pascal triple `{[P],[Q],[R]}`. S2's stated "Next Action 2" was to
upgrade this to literal equality of the spanned `ProjLine`. I did exactly that —
added **PART 4d** to `proofs/Proofs/PascalsHexagonOQ03.lean`:

- `sameProjLine l m := crossProduct l m = 0` — parallelism = "same projective
  line up to nonzero scalar" for homogeneous line-vectors.
- `sameProjLine_refl`, `sameProjLine_neg_right`, `sameProjLine_smul_right`.
- `cross_cross_eq_det_smul : (P ×₃ Q) ×₃ (Q ×₃ R) = det(P,Q,R) • Q` — BAC–CAB
  specialisation, pure polynomial identity by `ring` (no axiom).
- `sameProjLine_of_collinear` — the **rotation crux**: collinear `P,Q,R` ⟹
  `P ×₃ Q ∥ Q ×₃ R`. Proof: rewrite by `cross_cross_eq_det_smul`, then
  `collinear` gives `det = 0`, so `0 • Q = 0`. (no axiom)
- `pascalLine_hexRot_sameProjLine` / `pascalLine_hexRev_sameProjLine` — the
  Pascal line of the rotated/reflected hexagon equals (projectively) the
  original. hexRot: PART 4c lemmas give `P' = Q, Q' = R`, reduce to the crux via
  `pascal_hexagon_theorem`. hexRev: `P' = -Q, Q' = -P` so the line is
  `(-Q) ×₃ (-P) = -(P ×₃ Q)`; direct coordinate expansion.
- `pascalLine_generators_sameProjLine` — both generators bundled.

## Key Findings
- The clean engine for line-equality is the BAC–CAB identity
  `(a×b)×(c×d) = [a,b,d]c − [a,b,c]d`. With `a=P,b=Q,c=Q,d=R` the `[P,Q,Q]`
  term dies and the survivor is `det(P,Q,R) • Q`. Collinearity (`det=0`) is then
  *exactly* the condition that the two candidate Pascal lines coincide. This is
  why the Pascal line is canonical — independent of which adjacent pair of the
  collinear triple you join.
- The cross-product-zero characterisation sidesteps the need to *extract* a
  nonzero scalar (which would require a nondegeneracy / nonzero-coordinate
  hypothesis). It is the honest, hypothesis-free notion of "same projective
  line" that still proves what we need.
- The two pure lemmas (`cross_cross_eq_det_smul`, `sameProjLine_of_collinear`)
  are axiom-free; only the Pascal-triple corollaries inherit the parent's
  `conic_implies_pascal_constraint` axiom.

## Files Modified
- `proofs/Proofs/PascalsHexagonOQ03.lean` (+PART 4d, ~95 lines)
- `research/problems/pascals-hexagon-oq-03-incomplete-01/state.md`
- this session file

## Next Steps
Full quotient descent: `Subgroup.closure_induction` over `⟨hexRot, hexRev⟩` +
`sameProjLine` transitivity to propagate generator-invariance to the whole
`hexagonalGroup`, then connect `permuteHexagon hex g` to the `lbl.out'`
representative used by `pascalLine`. That yields genuine `Quotient`-level
well-definedness. Build-verify PR #30630 once host disk/Docker recovers.
