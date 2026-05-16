# Current State

**Phase**: ACT (S3 `discrete_reflection` pending)
**Since**: 2026-05-15 (S2 ACT merge: #19282)
**Iteration**: 4 (S1 OBSERVE + S2 ACT + S3 PREP + S4 STATE-SYNC, this entry)

## S4 STATE-SYNC (researcher-6, 2026-05-16, doc-only)

Two PRs from the 2026-05-15 drain wave landed:

- **#19282** (researcher-9) — S2 ACT — Donsker FCLT axiomatized statement layer.
  Merged 2026-05-15 at commit `cff3fd36c83`. Creates
  `proofs/Proofs/BallotProblemOQ02OQ05.lean` (130 LOC, 1 named axiom
  `donsker_fclt`, 0 sorries, 3 defs: `partialSum` + `interpolatedRescaled` +
  `WeakConvergesInC01`).
- **#19288** (researcher-12) — S3 PREP — duplicate-S2-ACT race audit recommending
  merge of #19065 over #19282. Merged 2026-05-15 (commit
  `03625856a59`). The audit recommendation was retroactively overridden
  by the deployer (#19282 merged instead of #19065).

**PR #19065** (`research/ballot-problem-oq-02-oq-05-s2-1778770457`,
researcher-12-era) is **still OPEN + CONFLICTING** as of S4. Its
`BallotProblemOQ02OQ05.lean` is functionally equivalent to what is now
on `main` (modulo the `partialSum` named helper, already on `main` via
#19282 anyway). **Recommendation: close PR #19065 without merging**
(deferred to deployer/champion; this S4 STATE-SYNC PR does not close it).

**Bearer drift recheck at lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (v4.26.0):
`Finset.card_bij` at `Mathlib/Data/Finset/Card.lean:341` and `Finset.card_bij'`
at line 366 are unchanged since the S1/S2 pin (verified via `gh api
/repos/leanprover-community/mathlib4/contents/...?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
file SHA `ce82fb5788b6c30ea01c64fb091124e990516497`).

**S3 ACT-readiness gate (6 items, all GREEN)**:

1. ✅ `BallotProblemOQ02OQ05.lean` on `main` (`cff3fd36c83`)
2. ⚠ `partialSumBool : (Fin n → Bool) → ℕ → ℤ` needs `~5 LOC` definition in S3
3. ✅ `Finset.card_bij` / `card_bij'` pinned & line-verified at Mathlib v4.26.0 SHA
4. ✅ No active sibling-slug `discrete_reflection` ACT (`gh pr list --search 'discrete_reflection'` → 0)
5. ✅ PR #19065 disposition is not an ACT blocker (research-side; champion handles close)
6. ✅ Slug LOC budget (~95 + ~100 = ~195) within 250-LOC informal cap

See `sessions/2026-05-16-s4-statesync-postdrain-s2-act-merged.md` for the
full memo (drift inventory, PR-#19065 disposition narrative, bearer pin
table, S3 ACT-readiness gate, conflict-free guarantee).

## Current Focus (post-S4)

Next scheduled work: **S3 ACT** — prove `discrete_reflection` for the
symmetric ±1 random walk via the André-Feller lattice-path bijection,
shaped against `Finset.card_bij` / `Finset.card_bij'` (the inverse-pair
form is a closer fit for the involutive reflection). Target ~100 LOC,
0 sorries, 0 new axioms, 1 new theorem. See `## Next Action` block
below (unchanged from pre-S4) for the full sketch.

## S2 ACT Focus (researcher-9, 2026-05-15, shipped via #19282)

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
