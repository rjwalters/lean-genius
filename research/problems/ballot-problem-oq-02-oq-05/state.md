# Current State

**Phase**: ACT
**Since**: 2026-05-15 (S2)
**Iteration**: 2

## Current Focus

S2 (researcher-9, 2026-05-15): ACT — ship statement layer of OQ-05 pipeline.

Created `proofs/Proofs/BallotProblemOQ02OQ05.lean` (~95 LOC) containing:

- `partialSum xi k ω = ∑ i ∈ Finset.range k, xi i ω` — partial-sums helper.
- `interpolatedRescaled xi n t ω = (S_⌊tn⌋ + frac · ξ_⌊tn⌋) / √n` — the canonical $C([0, 1], \mathbb{R})$-valued process used in Donsker's theorem.
- `WeakConvergesInC01 μ Xn X` — ad hoc weak-convergence predicate against pointwise-continuous test functionals. Strictly weaker than the classical sup-norm formulation but compatible with Mathlib v4.26.0 (no Polish/Borel structure on $C([0, 1])$ required).
- `donsker_fclt` — the named axiom: Donsker's FCLT (Wiedijk #45). Asserts existence of a Brownian motion on the same probability space such that the rescaled walk converges weakly in $C([0, 1])$ to its sample-path process.

**Build**: verified via Docker (7744 jobs successful, file built in 6.8s on cache hit). Statement-only — 0 sorries, 1 new axiom, 0 theorems requiring proof.

## Active Approach

**Unchanged from S1**: "Axiomatize Donsker, derive parent axioms" — three parent axioms collapse into one or two named classical axioms.

The S2 deliverable opens the file at the correct module path so that S3 can prove `discrete_reflection` (the only sorry-free deliverable of substance), S4 can axiomatize the continuous mapping for the sup-functional and derive `reflection_principle`, and so on through S7.

## Blockers

None new. Existing Mathlib gaps tracked in `problem.md` (Mathlib infrastructure map): no Polish structure on $C([0, 1])$, no Prokhorov, no Kolmogorov-Centsov, no continuous mapping theorem, no Donsker. These remain Mathlib upstream contributions.

## Next Action

**S3 (any researcher)**: prove `discrete_reflection` for the symmetric ±1 walk.

Target shape (refine against `Finset.card_bij` API):

```lean
theorem discrete_reflection
    {n : ℕ} (hn : 0 < n) (a : ℤ) (ha : 0 < a) :
    -- |{paths in {-1,+1}^n with max ≥ a}| = 2·|{paths ending ≥ a}| - |{paths ending = a}|
    ((Finset.univ.filter fun ω : Fin n → Bool =>
        ∃ k ≤ n, partialSumBool ω k ≥ a).card)
    = 2 * (Finset.univ.filter fun ω => partialSumBool ω n ≥ a).card
      - (Finset.univ.filter fun ω => partialSumBool ω n = a).card := by
  -- via Finset.card_bij with the André-Feller reflection
  sorry
```

**Approach**: André-Feller bijection between paths reaching $a$ that end below $a$ and paths ending strictly above $a$, via reflection at first hit of $a$. Lean encoding uses `Finset.card_bij` for the cardinality-preserving bijection on `Fin n → Bool`.

**Expected size**: ~100 Lean lines, 0 sorries (fully proved), 0 new axioms, 1 new theorem.

**Risk**: the reflection bijection is well-understood mathematically but the Lean encoding of "first time hitting level $a$" via `Nat.find` requires careful decidability handling. Alternative: prefix-reversal-at-hit-time (path-as-list version), which sidesteps `Nat.find`.

**Sibling-coordination note**: `ballot-problem-oq-03-oq-01-oq-01` may have a parallel `discrete_reflection` formulation. Cross-check `Proofs/BallotProblemOQ03OQ01OQ01.lean` before duplicating; if a compatible lemma already exists, import it instead.

## Prior Next-Action Sketch

S1 specified the file structure (definitions + axiom) verbatim. S2 implemented it directly with the only adjustments being (a) added `partialSum` as a named helper for clarity, and (b) **strengthened** the `∀ i j, i ≠ j → IndepFun` (pairwise) hypothesis to `iIndepFun xi μ` (mutual, matching `Proofs/FairGamesTheoremOQ02OQ01OQ01.lean:59`'s pattern). Pairwise independence is insufficient for the classical Donsker theorem; the strengthening keeps the axiom mathematically truthful.

## Attempt Counts

- Total attempts: 2 (S1 OBSERVE survey, S2 ACT statement layer)
- Current approach attempts: 2 (axiomatize-Donsker decomposition)
- Approaches tried: 1

## Open files

- `problem.md` — formal Lean signature targets, classification, Mathlib gap analysis, S2-S7 decomposition.
- `knowledge.md` — historical timeline, reflection-principle bijection proof, three CMT formulations, Lévy arcsine variants, Sparre Andersen, full bibliography.

## S2 Deliverable

- 1 new Lean file: `proofs/Proofs/BallotProblemOQ02OQ05.lean` (~95 LOC).
- 1 new named axiom (`donsker_fclt`).
- 2 new definitions (`partialSum`, `interpolatedRescaled`).
- 1 new predicate (`WeakConvergesInC01`).
- 0 new theorems requiring proof.
- 0 sorries.
- Build: verified by Docker (7744 jobs successful).

The OQ-05 pipeline now has a load-bearing statement layer. Sessions S3+ can begin proving content against the published types without re-litigating the signature.

## S1 Deliverable Summary

(retained for reference — see git history of state.md for full S1 narrative)

S1 produced OBSERVE survey: `problem.md`, `knowledge.md`, JSON entry, with full S2-S7 decomposition. 0 Lean files modified. The S2 ACT executed S1's plan verbatim with two small adjustments documented above under "Prior Next-Action Sketch".
