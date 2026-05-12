# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-12): Initial survey of the **curved-crease origami**
extension of the Huzita-Hatori axiom system. The OQ asks whether the
seven straight-crease axioms in
`proofs/Proofs/AngleTrisectionOQ05.lean` (`HHAxioms`, line 108) can be
*strengthened* to capture the field `K_curved ⊆ ℝ` of points constructible
by a single curved fold along a smooth analytic curve `γ` with dihedral
fold-angle profile `θ` satisfying the Fuchs-Tabachnikov compatibility
identity `κ_n = κ_g · cot(θ/2)`.

The survey produces:
1. A literature inventory (Huffman 1976; Fuchs-Tabachnikov 1999;
   Demaine et al. 2011; Tachi 2010; Mitani 2009; Geretschläger 1995).
2. A three-strand classification of the relevant theory: (i) local
   differential geometry of a single curved fold; (ii) algorithmic /
   discretised construction (out of scope); (iii) constructibility-field
   theory.
3. Three candidate axiom-system strengthenings — (P1) single curved
   axiom O8, (P2) Beloch-style finite degree-bounded restriction,
   (P3) algebraic-closure-only.
4. A Mathlib infrastructure gap analysis: four missing primitives,
   sidestepped for OQ-04 by postulating the FT identity as a structure
   field rather than proving it internally.
5. A five-session decomposition with effort estimates totaling ~450
   Lean lines, 1 intentional open sorry (the unresolved conjecture),
   0 axioms.

## Active Approach

**S1-OBSERVE-only.** Markdown + JSON only. No Lean changes this session.

The reasoning: OQ-04 is a *broad* open question with substantial
literature; a focused S1 survey is more valuable than a half-baked Lean
scaffold. The S2 ORIENT target (the `CurvedCrease` structure plus a
single conservativity theorem statement) is well-defined enough that any
subsequent researcher can pick it up directly.

## Blockers

None mathematical for S1.

Practical:
- The Fuchs-Tabachnikov compatibility identity (FT) is best treated
  as a **structure field** rather than as a derived theorem in S2-S5,
  because proving FT internally requires roughly 350 lines of Darboux-
  frame differential geometry currently absent from Mathlib. Postponing
  FT to a future *integration* sub-PR (S6+) keeps the OQ-04 deliverable
  Lean-tractable without weakening the axiomatic strength.
- The Mathlib pinned curvature API (`Mathlib.Geometry.Euclidean.Curvature.Plane`)
  covers only graph curves `y = f(x)`; extending to parametric unit-speed
  curves is ~80 lines.

## Next Action

**S2 (any researcher)**: Create `proofs/Proofs/AngleTrisectionOQ05OQ04.lean`
with the following minimum content (see `knowledge.md` for the full
sketch):

```lean
import Proofs.AngleTrisectionOQ05
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace AngleTrisectionOQ05OQ04

open AngleTrisectionOQ05

structure CurvedCrease where
  L : ℝ
  hL : 0 < L
  γ : ℝ → ℝ × ℝ
  θ : ℝ → ℝ
  κg : ℝ → ℝ
  κn : ℝ → ℝ
  hθ_pos : ∀ s ∈ Set.Icc 0 L, 0 < θ s ∧ θ s < Real.pi
  ftCompatible :
    ∀ s ∈ Set.Icc 0 L,
      κn s = κg s * (Real.tan (θ s / 2))⁻¹

def CurvedCrease.IsStraight (c : CurvedCrease) : Prop :=
  ∀ s ∈ Set.Icc 0 c.L, c.κg s = 0

/-- (S3 sorry; conservativity.) -/
theorem straight_fold_recovers_HH (c : CurvedCrease)
    (hStraight : c.IsStraight) : True := by
  sorry

end AngleTrisectionOQ05OQ04
```

Then add the gallery entry `src/data/proofs/angle-trisection-oq-05-oq-04/`
with `meta.json` (status `axiomatized`, sorries 1, axioms 0; FT is an
internal structure field, not an `axiom` declaration, but for axiom
integrity it is an *encoded assumption* counted as 1 toward axiomCount).

Total S2 size estimate: ~180 Lean lines + ~40 lines of gallery metadata.

## Session Log

| Step | Action | Outcome |
|------|--------|---------|
| 1 | Probed 14 available tier-B slugs for open-PR / merge activity | 7 had 0 exact-match open PRs |
| 2 | Inspected parent + sibling JSONs (`angle-trisection-oq-05`, `oq-05-oq-01`) | parent verified 0/0/27; sibling completed 0/0/24 |
| 3 | Read parent Lean file `AngleTrisectionOQ05.lean` (695 lines) | catalogued `HHAxioms`, `IsOrigamiConstructible`, `origami_degree_classification` as the primitives OQ-04 strengthens |
| 4 | Claimed `angle-trisection-oq-05-oq-04` via direct slug | knowledge score 0 (EMPTY); fresh slug |
| 5 | Created branch `research/angle-trisection-oq-05-oq-04-S1-<ts>` off `origin/main` | clean diff, no orphan content |
| 6 | Wrote `research/problems/angle-trisection-oq-05-oq-04/{problem,knowledge,state}.md` | ~700 lines of survey |
| 7 | Wrote `src/data/research/problems/angle-trisection-oq-05-oq-04.json` | gallery entry, phase OBSERVE, status active |
| 8 | (pending) Commit + push + PR with label `research` | next |

## References Captured

See `knowledge.md` for the full citation list and Mathlib gap analysis.
