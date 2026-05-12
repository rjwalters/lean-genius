# Research State: spherical-law-of-sines-oq-03

## Current State
**Phase**: OBSERVE
**Path**: route-A (law-of-cosines + algebra)
**Since**: 2026-05-12T18:01:16Z (claim opened)
**Iteration**: 1

## Current Focus
S1 OBSERVE: document the four-parts/cotangent rule, survey parent
infrastructure (SphericalLawOfSines + SphericalLawOfCosines), establish
proof strategy (Route A: derive from two applications of the spherical
law of cosines + law of sines), and identify the small set of helper
lemmas needed.

## Active Approach
**Route A**: derive cotangent rule as an algebraic consequence of the
parent's `spherical_law_of_sines_sq` plus the sibling
`spherical-law-of-cosines` standard law of cosines. Estimated 60-100 LOC.

**Route B (fallback)**: independent cross-product derivation in the
parent's `Fin 3 → ℝ` framework, mirroring the parent's component-by-
component `linear_combination` style. ~150-200 LOC, reserved for use if
Route A's namespace bridge to the sibling proof proves brittle.

## Attempt Count
- Total attempts: 0 (S1 OBSERVE is doc-only — no Lean code yet)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
* Module-path verification for the sibling `spherical-law-of-cosines`
  proof: worktree `.lake` symlink trap blocks direct LSP-based grep
  per `feedback_researcher_lake_symlink_broken.md`. Deferred to S2
  ORIENT, where a single `head -20 proofs/Proofs/SphericalLawOfCosines.lean`
  resolves it.
* No Mathlib `Real.cot` at v4.26.0 — encode `cot ≡ cos/sin` locally or
  state cleared-of-cotangents polynomial form (preferred).

## Next Action
**S2 ORIENT** (separate session, ~30-45 min):
1. Open `proofs/Proofs/SphericalLawOfCosines.lean`, read its header +
   first 100 lines, record the standard-law-of-cosines theorem name +
   signature.
2. Confirm the framework matches the parent's `Fin 3 → ℝ` convention
   (vs. `EuclideanSpace`).
3. Create `proofs/Proofs/SphericalLawOfSinesOQ03.lean` with:
   - `import Proofs.SphericalLawOfSines` (framework + parent lemmas).
   - `import Proofs.SphericalLawOfCosines` (sibling lemma — name TBD).
   - `import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic`.
   - Helper lemma `sin_arcLen_nonneg` (Real.sin_nonneg_of_nonneg_of_le_pi
     + Real.arccos_nonneg + Real.arccos_le_pi).
   - Helper lemma `sin_arcLen_eq_sqrt` (Real.sqrt of normSq of projPerp).
   - `theorem spherical_cotangent_rule_polynomial : … := by sorry`
     (the boxed algebraic form, see problem.md).
   - Strategic `cotangent_rule_from_cosines` sorry-stub (the 2-LoC
     substitution step) with the algebra carefully spelled out in a
     docstring.
4. Build verify (no new sorries beyond the strategic one).
5. Push as S2 SCAFFOLD PR.

**Race-safety re-check**: before S2 push, re-run
`gh pr list -R rjwalters/lean-genius --search "spherical-law-of-sines-oq-03 in:title"`
and `git branch -r | grep spherical-law-of-sines-oq-03`. If a sibling
agent has filed S1 OBSERVE in the interim, narrow S2's deliverable to
the unique helper lemmas + theorem statement (not the strategic sorry).

## Session Log

### 2026-05-12 18:01 UTC — Session start (researcher-10)
- Probed candidate-pool.json: spherical-law-of-sines-oq-03 is
  seeker-fresh (tier B, sig=5, tract=7), no problem.md, no PR, no
  branch.
- Verified parent gallery: `spherical-law-of-sines` is `verified`
  (323 LOC, 0 axioms, 0 sorries) with three `openQuestions` in
  `meta.json`: spherical excess (OQ-01, OBSERVE), dual law of cosines
  (OQ-02, OBSERVE), four-parts formula (OQ-03 — this slug).
- Claimed via `claim-problem.sh claim spherical-law-of-sines-oq-03`,
  TTL 90 min, expires 2026-05-12T19:31:16Z.
- Wrote `problem.md` (S1 statement + Route A/B sketch + sanity
  checks), `knowledge.md` (Mathlib API + parent infrastructure +
  classical references), this `state.md`.
- Next: write `src/data/research/problems/spherical-law-of-sines-oq-03.json`,
  commit + push, create PR.

## Open Questions for Future Sessions

* Is `Real.cos_arccos` the right way to recover linear `cos(arcLen u w) = dot u w`?
  The unconditional `sin_arccos` form gives sin via sqrt; cos via dot
  needs the `-1 ≤ x ≤ 1` bounds. **Parent's `arcLen` is `arccos(dot u w)`**;
  for unit `u, w`, Cauchy-Schwarz gives `|dot u w| ≤ 1`, so this
  should be a 3-line lemma in S2.
* Should the deliverable theorem be stated in **polynomial form** (no
  cot, suitable for `linear_combination`) or **rational form** (with
  `cot` encoded as `cos/sin`)? Polynomial is preferred for the main
  theorem; the rational form ships as a `corollary` with the
  non-degeneracy hypotheses upgraded to `sin ≠ 0` form.
* Does the sibling `spherical-law-of-cosines` proof export the
  standard cos-side law with the same `Fin 3 → ℝ` framework? If it
  uses `EuclideanSpace (Fin 3) ℝ`, then S2 ORIENT must either (a)
  re-state in the parent's convention or (b) write a thin equivalence
  lemma. **Risk severity**: medium; **mitigation**: Route B fallback.
