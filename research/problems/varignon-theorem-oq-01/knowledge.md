# Knowledge Base: varignon-theorem-oq-01

Varignon's theorem: the midpoints of the sides of any quadrilateral form a
parallelogram.

---

## Problem Understanding

Given a quadrilateral `ABCD` (no convexity, planarity, or non-degeneracy
hypotheses needed), let
- P = midpoint(A, B)
- Q = midpoint(B, C)
- R = midpoint(C, D)
- S = midpoint(D, A)

Claim: `PQRS` is a parallelogram. Strong form: each side of `PQRS` is parallel
to a diagonal of `ABCD` and has half its length.

---

## Insights

- The result is an **affine** identity, not a metric one: it uses only the
  midpoint (= componentwise average) structure. So it holds for arbitrary,
  even self-intersecting or skew, quadrilaterals.
- Key computation:
  - Q − P = (B+C)/2 − (A+B)/2 = (C − A)/2
  - R − S = (C+D)/2 − (D+A)/2 = (C − A)/2
  so Q − P = R − S = (C − A)/2 = ½·(diagonal AC).
  The second pair: P − S = Q − R = (B − D)/2 = ½·(diagonal BD).
- Modeling points as `ℝ × ℝ` and proving each coordinate identity by `ring`
  (after `dsimp only [midpoint2]` to reduce the pair projections) gives a
  0-sorry / 0-axiom proof. No `Prod` subtraction or `EuclideanSpace` is needed —
  working componentwise keeps `ring` applicable.

---

## Session 2026-06-16 (Session 1, researcher-12) — Coordinate proof written

**Mode**: FRESH
**Outcome**: progress (proof written, 0 sorry / 0 axiom; build pending)

### What I Did
- Wrote `proofs/Proofs/VarignonTheorem.lean` with:
  - `midpoint2 : Point → Point → Point` (componentwise average over `ℝ × ℝ`)
  - `varignon_PQ_eq_half_AC`, `varignon_SR_eq_half_AC` — strong form: each side
    equals half diagonal `AC`, componentwise.
  - `varignon` — the parallelogram property `Q − P = R − S` componentwise.
  - `varignon_PS_eq_QR` — second pair of opposite sides equal (= ½ diagonal BD).
  - All four discharged by `refine ⟨?_, ?_⟩ <;> dsimp only [midpoint2] <;> ring`.

### Key Findings
- Pure `ring` identity; no Mathlib geometry lemmas required.

### Build Status
- **BUILD-VERIFIED GREEN.** `docker-build.sh Proofs.VarignonTheorem` →
  `Built Proofs.VarignonTheorem (8.2s)`, `Build completed successfully
  (3058 jobs)`, 0 errors / 0 sorry / 0 axiom. One fix during build: `midpoint2`
  needed `noncomputable` (real division). Two cosmetic unused-variable warnings
  (`D` in PQ-lemma, `B` in SR-lemma) from the uniform 4-vertex signatures — kept
  for readability.
- The earlier `info: mathlib: cloning ...` log is NORMAL (clones Mathlib source,
  then `lake exe cache get` pulls oleans ~5 min); it is NOT a blackout. The doom
  signal is `Building Mathlib` (thousands of jobs compiling from source).
- Registered: `import Proofs.VarignonTheorem` added to `Proofs.lean`. Gallery
  data added: `src/data/proofs/varignon-theorem-oq-01/{meta.json,annotations.json}`.

### Next Steps
- COMPLETE. Optional follow-ups: area-ratio corollary (Varignon parallelogram =
  ½ area of the quadrilateral), or the iterated-midpoint-quadrilateral limit.
