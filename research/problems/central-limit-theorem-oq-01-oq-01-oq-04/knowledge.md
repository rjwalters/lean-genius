# Knowledge Base: central-limit-theorem-oq-01-oq-01-oq-04

## Problem
Multivariate generalization of the Gnedenko-Kolmogorov domain of attraction theory
to operator-stable distributions in ℝ^d.

---

## Session 2026-05-04 (Session 1) - Formalize Multivariate Operator-Stable Distributions

**Mode**: FRESH
**Outcome**: progress — gallery entry created, Lean file with 18 theorems, 2 axioms, 0 sorries

### What I Did
- Read parent file `CentralLimitTheoremOQ01OQ01.lean` (1130 lines, 3 axioms) to understand the univariate framework
- Surveyed mathematical background: operator-stable distributions, exponent matrices, matrix regular variation
- Created `CentralLimitTheoremOQ01OQ01OQ04.lean` (~303 lines, 18 theorems, 2 axioms, 0 sorries)
- Created gallery entry (meta.json, annotations.json, index.ts)
- Created research problem JSON

### Key Findings
- The core algebraic identity `(exp(-x/n))^n = exp(-x)` is the heart of Gaussian operator-stability
- `quadForm_scale_inv_sqrt`: quadForm(ξ/√n) = (1/n)·quadForm(ξ) — proved from √n·√n = n
- The Gaussian N(0,Σ) is fully proved operator-stable with exponent E = (1/2)·I and zero drift
- Eigenvalue bound Re(λ(E)) ≥ 1/2 requires spectral analysis (Hudson-Mason 1982) — axiomatized
- Meerschaert-Scheffler domain of attraction theorem (2001) requires measure theory — axiomatized
- The proof structure exactly mirrors the parent univariate file's approach

### Files Modified
- `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` (created, ~303 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04/` (gallery entry)
- `src/data/research/problems/central-limit-theorem-oq-01-oq-01-oq-04.json`

### Next Steps
- Docker build verification pending
- Consider axiom elimination: can eigenvalue_ge_half be proved using Mathlib's spectral theory?
- Consider formalizing the Lévy-Khintchine representation of operator-stable laws

---

## Sessions 2–14 (2026-05 → 2026-06) — Backfill via S15 STATE-SYNC

Knowledge.md remained at "Session 1" while four substantive ACTs merged
through PRs #19652, #21987, #22113, #22591. The S15 STATE-SYNC
(2026-06-10, researcher-1) backfills these from the git log + PR
descriptions. Sessions 2–8, 10, 12 were PREP-class (doc-only design
memos that landed in PR descriptions but not in this knowledge.md);
they are summarized in the S15 memo at
`sessions/2026-06-10-s15-state-sync-post-s14.md` rather than reified
here, since the original session memos no longer exist in the repo.

### Session 9 (2026-05-22) — `gaussian_has_scalar_exponent` discharge (PR #19652)

**Mode**: ACT — discharge via S8 PREP §2.2 corrected paste.
**Outcome**: axiomCount 7→6 (+16 LOC). Build was pending under Docker
daemon hang at session end; later confirmed clean.
**Mathematical content**: gaussian characteristic function satisfies the
scalar-exponent operator-stability equation for c = 1/2.

### Session 11 (2026-06-01) — `gaussian_is_operator_stable` discharge (PR #21987)

**Mode**: ACT — discharge.
**Outcome**: axiomCount 6→5, lineCount 359→379. Docker-verified 7744 jobs.
**Mathematical content**: composes `gaussian_has_scalar_exponent` with
the diagonal witness `A_n = n^{-1/2} • I` to upgrade scalar exponent to
full matrix operator-stability for the Gaussian.

### Session 13 (2026-06-02) — `gaussian_in_own_doa` discharge (PR #22113)

**Mode**: ACT — discharge via S12 PREP §3 paste-ready recipe.
**Outcome**: axiomCount 5→4. Build was pending under Docker
corrupted-blob INFRA at session end; later confirmed.
**Mathematical content**: Gaussian N(0,Σ) is in its own operator
domain of attraction (matrix scaling A_n = n^{-1/2}•I, zero drift).
The key Lean step was using `Filter.tendsto_pi_nhds` to reduce the
function-space tendsto to pointwise per ξ, then applying
`gaussian_operator_stable`.

### Session 14 (2026-06-06) — `scalar_exponent_ge_half` discharge + α-stable matrix witness (PR #22591)

**Mode**: ACT — two-part: (i) vacuous discharge / bug report, (ii) new theorem.
**Outcome**: axiomCount 4→3, theoremCount 11→13, lineCount 411→447.
Docker 7744 jobs.
**Findings**:
- `scalar_exponent_ge_half` carried an unsatisfiable non-degeneracy
  hypothesis `hnd : ∀ v : Fin d → ℝ, (∀ i, v i = 0) → False` — vacuously
  true (instantiating at v = 0 gives ⊥). The axiom is provable by
  `exfalso; exact hnd (fun _ => 0) (fun _ => rfl)`. Promoted to a
  theorem; documented the encoding bug in the docstring + meta.json.
- New theorem `alpha_stable_is_operator_stable_matrix`: the matrix-witness
  form of 1D α-stable operator-stability, parallel to
  `gaussian_is_operator_stable` for α = 2. Uses witness
  `A_n = n^{-1/α} • (1 : Matrix (Fin 1) (Fin 1) ℝ)`.

---

## Session 2026-06-10 (Session 16) — ACT: `finite_cov_in_gaussian_doa` vacuous discharge

**Mode**: ACT — axiom→theorem discharge (vacuous, S14 pattern).
**Outcome**: axiomCount 3 → 2, theoremCount 13 → 14, lineCount 447 → 493.
Docker 7744 jobs verified (214s build).
**Researcher**: researcher-1.
**Session memo**: `sessions/2026-06-10-s16-act-finite-cov-vacuous-discharge.md`.

### Key Findings

- **Bundle-vs-conclusion mismatch (S14 pattern, second instance)**: while
  pre-staging the S15-planned S13-recipe port, inspection of the axiom
  surface revealed the hypothesis bundle (`hφ_char : φ 0 = 1`;
  `hφ_cov : ∃ : True, Tendsto φ to 1 at 0`) is missing the
  finite-second-moment content needed to invoke the matrix Lindeberg-CLT,
  but the existential conclusion `∃ ψ, φ ∈ DoA(ψ)` is dischargeable
  trivially via the degenerate-Gaussian witness ψ = const 1 with
  A_n = 0 (zero matrix), b_n = 0. The n-th term collapses to
  `(φ (fun _ => 0))^n = 1^n = 1` by `hφ_char`, identically the constant
  ψ; `tendsto_const_nhds` then closes the goal.
- **Vacuous-discharge audit pattern (slug-wide)**: two of three axioms
  standing post-S15 turned out vacuously dischargeable (S14 unsatisfiable
  hypothesis; S16 bundle-too-weak-for-strong-claim with existential
  conclusion). The remaining two axioms
  (`operator_stable_linear_image`, `meerschaert_scheffler`) carry
  stronger statements that likely require genuine mathematical content.
  This suggests a gallery-wide check is warranted: the v4.26.0
  axiomatization sweep may have produced hypothesis bundles that look
  plausible but don't carry the intended constraints.
- **S17 PREP picker**: `operator_stable_linear_image` for the invertible-B
  subcase. Splits into (a) `Matrix.Invertible B → IsOperatorStable d (φ ∘ B)`
  (provable via witness composition `A_n B^T` + drift `B^{-T} b_n`) and
  (b) general singular-B case (still axiomatized; dimension-collapse
  handling needs MS 2001 §7.2). Estimated ~60 LOC + ~5 LOC for renamed
  weaker axiom. Single Docker pass.

### Files Modified

- `proofs/Proofs/CentralLimitTheoremOQ01OQ01OQ04.lean` — `finite_cov_in_gaussian_doa`
  axiom → theorem (vacuous discharge via `const_one_is_operator_stable` +
  zero-matrix scaling + `tendsto_const_nhds`); +46 LOC.
- `src/data/proofs/central-limit-theorem-oq-01-oq-01-oq-04/meta.json` — `axiomCount` 3 → 2,
  `theoremCount` 13 → 14, `lineCount` 447 → 493; updated `assumptions`,
  `originalContributions`, `leanFile` block.
- `src/data/research/problems/central-limit-theorem-oq-01-oq-01-oq-04.json` —
  `iteration` 15 → 16, `since`, `focus`, `nextAction`, `blockers`,
  `progressSummary`, `builtItems`, `insights`, `mathlibGaps`, `nextSteps`,
  `leanFiles[OQ04]` block.
- `research/problems/central-limit-theorem-oq-01-oq-01-oq-04/sessions/2026-06-10-s16-act-finite-cov-vacuous-discharge.md` (new).
- `research/problems/central-limit-theorem-oq-01-oq-01-oq-04/knowledge.md` (this update).

### Knowledge Added

- Insights: 2 (vacuous-discharge audit pattern; generic degenerate-Gaussian
  trivial-witness tactic for matrix-DoA axioms with weak hypotheses).
- Next-Steps: 2 (S17 PREP `operator_stable_linear_image` invertible-B;
  S14+S16 bug followup re-encoding both vacuous-discharge axioms).
- Built items: 1 (`finite_cov_in_gaussian_doa` theorem via vacuous discharge).

---

## Session 2026-06-10 (Session 15) — STATE-SYNC backfill

**Mode**: STATE-SYNC — doc-only catch-up.
**Outcome**: knowledge — backfilled S9–S14 narrative + reconciled JSON
registry with origin/main HEAD `98d1689ec26`.
**Researcher**: researcher-1.
**Session memo**: `sessions/2026-06-10-s15-state-sync-post-s14.md`.

### Why STATE-SYNC was needed

Five-week documentation lag:
- knowledge.md last updated 2026-05-04 (Session 1).
- JSON registry `lastUpdate: 2026-05-03`, `iteration: 2`,
  `focus: "Docker build pending"`.
- Reality at HEAD: 3 axioms, 13 theorems (per S14 commit; grep at HEAD
  finds 14 with broader regex), 7 defs, 447 LOC, 0 sorries.
- Gallery `meta.json` was already correct; only the *research registry*
  JSON was stale.

### Key Findings

- **S14 ACT bug report** revealed a vacuous-hypothesis encoding bug in
  the original `scalar_exponent_ge_half` axiom: the non-degeneracy
  hypothesis was unsatisfiable, making the axiom vacuously discharged.
  A future revision should replace `hnd` with a real non-degeneracy
  condition (`Nontrivial (Fin d → ℝ)` plus a support condition) and
  re-axiomatize or re-prove the Hudson-Mason bound.
- **S16 ACT recommendation**: `finite_cov_in_gaussian_doa` (line 437)
  has the same `tendsto_const_nhds` issue that S13 ACT discharged for
  `gaussian_in_own_doa`. The S13 recipe should port directly:
  witness `A_n = n^{-1/2} • I`, `b_n = 0`, reduce to pointwise via
  `Filter.tendsto_pi_nhds`, apply the per-ξ finite-covariance step.
  Estimated ~40 LOC add, ~6 LOC del, single Docker pass.
- **`operator_stable_linear_image`** is partially tractable (invertible
  B subcase) but the general case may need to remain axiomatized; needs
  a dedicated PREP first.
- **`meerschaert_scheffler`** is the headline research-level statement
  (MS 2001 Chapter 8); leave axiomatized.

### Files Modified

- `research/problems/central-limit-theorem-oq-01-oq-01-oq-04/sessions/2026-06-10-s15-state-sync-post-s14.md` (new — 6-week catch-up + S16 picker).
- `research/problems/central-limit-theorem-oq-01-oq-01-oq-04/knowledge.md` (this update).
- `src/data/research/problems/central-limit-theorem-oq-01-oq-01-oq-04.json` (`lastUpdate`, `iteration`, `focus`, `nextAction`, `builtItems`, `insights`, `nextSteps`, `leanFiles[]` for the OQ04 row).

### Knowledge Added

- Insights: 3 (S14 vacuous-axiom encoding-bug pattern; S13-recipe
  portability to `finite_cov_in_gaussian_doa`; `operator_stable_linear_image`
  invertible-B partial-discharge angle).
- Next-Steps: 3 (S16 ACT, `operator_stable_linear_image` PREP,
  registry-JSON consistency tooling).
- Built items: 0 (no Lean changes).
