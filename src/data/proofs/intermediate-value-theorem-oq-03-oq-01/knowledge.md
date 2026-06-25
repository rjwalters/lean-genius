# intermediate-value-theorem-oq-03-oq-01 — 2D Brouwer via Sperner: the Compactness Discharge

## Problem

Pool entry "2D Brouwer via Sperner Lemma Discharge" (tier B, significance 7,
tractability 5). Parent `intermediate-value-theorem-oq-03` proves 1D Brouwer
from the IVT and states the 2D case as `axiom brouwer_2d`. Goal: discharge that
axiom via Sperner's lemma.

## What was found in the gallery (state at 2026-06-25)

- `SpernerNDim.lean` — abstract n-dimensional Sperner parity theorem
  (`sperner_ndim`), fully verified, 0 axioms. Given a `SpernerTriangulation`, a
  Sperner coloring, and boundary-door-oddness, yields a fully-colored simplex.
- `SpernerNDimOQ03.lean` — *claims* the Sperner→Brouwer bridge
  (`approximate_fixed_point`, `brouwer_simplex`) but **references an undefined
  `FSimplex` structure** (`grep` finds `FSimplex`/`countPerm` nowhere in
  `proofs/Proofs/`). It does **not** compile. So there was no actually-verified
  Sperner→Brouwer connection in the gallery. (Potential audit target: its
  meta may overclaim.)
- The genuine gap: the **analytic** step turning Sperner's approximate fixed
  points into an exact one. The combinatorial half (`SpernerNDim`) is verified;
  the analytic half was missing/uncompiled.

## Contribution (this entry)

New file `proofs/Proofs/IntermediateValueTheoremOQ03OQ01.lean`, namespace
`IVTBrouwerDischarge`, imports only `Mathlib`. 5 theorems, 1 def, 202 lines,
0 axioms / 0 sorries (verified via `#print axioms` → only
`propext, Classical.choice, Quot.sound`).

- `exists_fixed_of_approx` — general compactness discharge: continuous `f`,
  nonempty compact `K ⊆ (Fin d → ℝ)`, ε-approximate fixed points for all ε ⟹
  exact fixed point. Extreme value theorem on `dist(f x) x` + minimality
  contradiction. Dimension-agnostic.
- `simplex_isCompact`, `simplex_nonempty` — 2-simplex (any d) compact (closed in
  `[0,1]^d`) and nonempty.
- `brouwer_2d_of_sperner_approx` — conditional 2D Brouwer on the 2-simplex,
  hypothesis = Sperner approximate-fixed-point property (coordinatewise
  `|f x i − x i| < ε`), converted to sup metric via `dist_pi_lt_iff`.
- `brouwer_1d_via_ivt` — unconditional 1D case from `intermediate_value_Icc'`,
  for contrast.

**Honesty**: `brouwer_2d_of_sperner_approx` is a verified *implication*, not an
unconditional 2D Brouwer. It reduces the parent axiom to the combinatorial
Sperner property. Stated explicitly in docstring, meta `assumptions`, and the
header annotation.

## Verification notes / gotchas

- **Docker daemon down** host-wide (2026-06-25) and `import Mathlib` blocked
  locally by a corrupted Mathlib build artifact
  (`Mathlib/RingTheory/PowerSeries/Ideal.ir`, "invalid header"). Verified
  single-file with `LAKE_UNSAFE=1 lake env lean` after temporarily swapping
  `import Mathlib` for a PowerSeries-free umbrella
  (`import Mathlib.Analysis.Convex.Topology` +
  `Mathlib.Topology.Order.IntermediateValue` +
  `Mathlib.Topology.MetricSpace.Pseudo.Pi`). The committed file uses the standard
  `import Mathlib` (project convention; rebuilds clean under docker/CI).
- This Mathlib (v4.26) has **no** `intermediate_value_zero_of_le` and **no**
  `ContinuousOn.dist`. Use `intermediate_value_Icc'`,
  `IsCompact.exists_isMinOn` (+ `isMinOn_iff`), and `Continuous.dist`.
  (The parent file's `brouwer_1d` uses `intermediate_value_zero_of_le` and so
  likely no longer compiles — another possible audit/mechanic target.)
- `grep -cE '^axiom '`/`grep -c sorry` give false positives here: the docstring
  quotes the parent's `axiom brouwer_2d` in a code fence and says "0-axiom".
  Real counts are 0 (confirmed by `#print axioms`).

## Next open question

Derive `happrox` for d = 2 from `SpernerNDim.sperner_ndim`: build the
Kuhn/Freudenthal triangulation as a `SpernerTriangulation` instance, prove
boundary-door-oddness by induction on dimension, run the displacement coloring →
**unconditional** 2D Brouwer. Then transfer simplex → disk via homeomorphism to
match the exact shape of the parent's `brouwer_2d`.
