# Chung-Feller via Lindström-Gessel-Viennot (Non-Intersecting Lattice Paths)

**Problem ID**: ballot-problem-oq-01-oq-04-oq-03
**Status**: surveyed
**Phase**: ORIENT

## Summary

This open question asks for an *alternative* proof of the Chung-Feller theorem
— number of (+1,−1) lattice paths from (0,0) to (2n,0) with exactly k upsteps
above the x-axis equals the Catalan number Cₙ, independent of k — using the
Lindström-Gessel-Viennot (LGV) lemma on non-intersecting lattice paths, instead
of the cycle lemma used by the parent.

**Key finding: the target theorem is already fully machine-verified.** The
parent (ballot-problem-oq-01-oq-04) proves Chung-Feller with **0 sorries, 0
axioms** via the cycle lemma:
`ChungFellerBijection.chung_feller_uniform'` in
`proofs/Proofs/BallotProblemOQ01OQ04OQ01.lean`, re-exported as
`ChungFeller.chung_feller_uniform`. So this OQ adds methodology, not correctness.

## Session 2026-06-19 (Session 1) — Feasibility Survey

**Mode**: FRESH
**Outcome**: surveyed

### What I Did
- Confirmed the parent proof already verifies Chung-Feller (0 sorries / 0 axioms).
- Searched Mathlib for the LGV lemma: **absent** (no `Lindstrom`/`GesselViennot`
  sources under `proofs/.lake/packages/mathlib/Mathlib`).
- Inventoried available related infrastructure.

### Key Findings
- Mathlib provides Catalan numbers (`Mathlib/Combinatorics/Enumerative/Catalan.lean`)
  and Dyck words (`.../DyckWord.lean`), but **no** non-intersecting-paths /
  signed-determinant enumeration framework.
- General LGV (det of the path-count matrix = signed sum over non-intersecting
  path families, proved via a sign-reversing involution on intersecting families
  + `Matrix.det` permutation expansion) is a substantial build: estimated **>500
  lines**, depending on `Matrix.det`, `Equiv.Perm` sign, and a careful involution.
- A Chung-Feller-specific specialization (small fixed determinant of binomials
  counting non-intersecting pairs) could avoid the fully general lemma but still
  needs the involution/sign machinery — non-trivial.

### Infrastructure Assessment: LGV lemma
- **Needed**: Lindström-Gessel-Viennot lemma (or a Chung-Feller-specific
  non-intersecting-pair determinant specialization).
- **Size estimate**: >500 lines (general); a few hundred for a specialization.
- **Decision**: ALTERNATIVE / deprioritize. Target is already verified; the LGV
  proof is pedagogical only. If pursued, build a minimal specialized determinant
  lemma rather than general LGV.

### Files Modified
- src/data/research/problems/ballot-problem-oq-01-oq-04-oq-03.json (created)
- research/problems/ballot-problem-oq-01-oq-04-oq-03/knowledge.md (created)

### Next Steps
- If pursued: minimal Gessel-Viennot determinant for two non-intersecting
  monotone lattice paths, reusing Mathlib Catalan and the gallery's Dyck/balanced
  path defs from BallotProblemOQ01OQ04Core.lean.
- Otherwise deprioritize — the theorem is already machine-checked.

## References
- Lindström, B. (1973). On vector representations of induced matroids.
- Gessel, I. & Viennot, G. (1985). Binomial determinants, paths, and hook length formulae.
- Chung, K.L. & Feller, W. (1949). On fluctuations in coin-tossing.
