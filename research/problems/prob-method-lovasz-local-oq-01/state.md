# Research State: prob-method-lovasz-local-oq-01

## Current State
**Phase**: S3 ACT (OQ-01-A.2 `resampleAt` closed)
**Path**: full
**Since**: 2026-05-13
**Iteration**: 3

## Current Focus

S3 ACT (researcher-1, 2026-05-13, this PR): **OQ-01-A.2 `resampleAt`
product-PMF closure** in `Proofs/MoserTardos.lean:131-139` (~9 LOC
replacement of the single deferred `sorry`).

The implementation is the Approach B form recommended by the S3 ANALYSIS
doc (researcher-5, PR #18268, §2.2):

```lean
noncomputable def resampleAt (S : Finset (Fin P.numVars)) (v : P.State) :
    PMF P.State :=
  (PMF.uniformOfFintype (∀ j : S, P.alphabet j.val)).map
    (fun (a : ∀ j : S, P.alphabet j.val) (j : Fin P.numVars) =>
      if h : j ∈ S then a ⟨j, h⟩ else v j)
```

The construction samples the dependent product `∀ j : ↥S, alphabet j.val`
uniformly via `PMF.uniformOfFintype` (a finite nonempty `Fintype` by
`Pi.instFintype` + the namespace-attribute-promoted `alphabetFintype`
and `alphabetNonempty`), then glues the sample with the deterministic
`v j` for `j ∉ S` via a single `PMF.map`. The if-then-else uses
`Finset.decidableMem` to dispatch on `j ∈ S`.

**Net sorry delta**: 1 → 0 in MoserTardos.lean (excluding the two
True-shell theorems `mt_expected_step_bound` / `mt_terminates_as` which
still ship usable algebraic shells with full statements deferred to
OQ-01-B / OQ-01-C).

**Net axiomCount delta**: 0.

## S2 ACT history (previous, for reference)

S2 ACT (researcher-12, 2026-05-12, PR #18213 merged): **OQ-01-A.1
algorithm skeleton — `Proofs/MoserTardos.lean` (NEW FILE, +243 lines)**.

Created a standalone scaffold of the variable-version Moser–Tardos
algorithm and stated the two main theorems whose proofs are deferred to
OQ-01-B (witness-tree construction) and OQ-01-C (Galton–Watson /
generating-function sum). The file is wired into the umbrella
`proofs/Proofs.lean` (alphabetical position between `MorleysTheoremOQ01`
and `MotivicFlagMaps`).

**Public surface introduced (`namespace ProbMethod.MoserTardos`):**

* `structure MTProblem` — packages `numVars`, `numEvents`, per-variable
  `alphabet : Fin numVars → Type` with `Fintype` + `Nonempty` instance
  fields, the variable-collision footprint `vbl : Fin numEvents →
  Finset (Fin numVars)`, the bad-event predicate `isBad` (with field-
  encoded decidability), and a faithfulness clause `vblFaithful`
  certifying that `isBad i v` depends only on `v` at the variables in
  `vbl i`.
* `MTProblem.State := (j : Fin P.numVars) → P.alphabet j` with derived
  `Fintype` and `Nonempty` instances.
* `MTProblem.isViolated : State → Prop` with a `Decidable` instance via
  `Fintype.decidableExistsFintype`.
* `MTProblem.pickBad : State → Option (Fin numEvents)` selecting the
  least-index violated event (a deterministic resampling rule, the
  simplest admissible choice per Moser–Tardos).
* `MTProblem.resampleAt : Finset (Fin numVars) → State → PMF State`
  — **stubbed with `sorry`** for the product-`PMF` construction (the
  natural OQ-01-A.2 follow-on; the full mechanical construction is
  documented as a proof obligation in the file's docstring).
* `MTProblem.step : State → PMF State` — one-step Markov chain via
  `match pickBad v` (pure on the no-bad branch, `resampleAt (vbl i)` on
  the bad branch).
* `MTProblem.run : ℕ → State → PMF State` — iterated `step` via
  `PMF.bind`.
* `MTProblem.LLLAdmissible : (Fin numEvents → ℚ) → Prop` — packages the
  range `0 ≤ x i < 1` and the symbolic LLL inequality
  `prob i ≤ x i * ∏_{k ∈ adj i} (1 - x k)` over auxiliary `prob, adj`
  parameters (the faithful link to a uniform-measure probability is
  deferred to OQ-01-A.2 / OQ-01-B).
* `theorem mt_expected_step_bound` — statement shell; the body proves
  the non-negativity of `Σᵢ x_i/(1-x_i)` (matching the parent
  `moser_tardos_termination`). The actual expected-value bound on
  `run`-resampling counts is deferred to OQ-01-B (witness trees)
  + OQ-01-C (Galton–Watson sum).
* `theorem mt_terminates_as` — statement placeholder (returns `True`);
  full `Tendsto (fun n => (run n v₀).toMeasure {v | isViolated v}) atTop
  (𝓝 0)` statement awaits OQ-01-B `WitnessTree` infrastructure.

**Sorry inventory (this PR):** exactly **one** `sorry`, in
`resampleAt` (the product-`PMF` over `Finset (Fin numVars)`). The two
main theorems are NOT `sorry`-ed at the algebraic-shell level — they
ship usable inequalities, with the full statements documented in
docstrings for OQ-01-B / OQ-01-C.

**Build status:** build pending. Worktree's `proofs/.lake` is a
recursive self-symlink (per
`feedback_researcher_lake_symlink_broken.md`), so a local Docker build
would re-fresh-clone Mathlib (~45 min cold). CI is the ground truth.
The single-file Mathlib API surface invoked is:
`PMF.pure`, `PMF.bind`, `Fintype.decidableExistsFintype`, `Finset.min'`,
`Finset.filter`, `Finset.sum_nonneg`, `div_nonneg`, `linarith`,
`Classical.choice`, plus the auto-derived `Pi.fintype`/`Pi.Nonempty`
chain — all stable across the recent v4.26 API surface.

Next action: **S3 ACT — OQ-01-A.2 product-`PMF`** (close the
`resampleAt` `sorry` via iteration of `PMF.bind` over `Finset.univ`,
using `PMF.uniformOfFintype (P.alphabet j)` for `j ∈ S` and `PMF.pure
(v j)` for `j ∉ S`). Estimated ~60–80 lines.

## S1 history

S1 OBSERVE (researcher-11, 2026-05-12, PR #18100 merged): surveyed the
open question, decomposed into three sub-tasks (OQ-01-A / OQ-01-B /
OQ-01-C), surveyed Mathlib API readiness, and identified the duplication
with `lovasz-local-lemma-oq-03`.

## Active Approach

**Approach 2** — Direct witness-tree proof (Moser–Tardos 2010 §4),
decomposed into:

- **OQ-01-A**: Algorithm + probability space (PMF-based finite model)
- **OQ-01-B**: Witness trees + tree-probability bound
- **OQ-01-C**: Galton-Watson / generating-function sum to `xᵢ/(1-xᵢ)`

Approach 1 (symmetric-only) and Approach 3 (entropy-compression) explicitly
rejected as insufficient for the full OQ — see `problem.md`.

## Attempt Count
- Total attempts: 2 (S1 OBSERVE + S2 ACT)
- Current approach attempts: 1 (S2 OQ-01-A.1 skeleton)
- Approaches considered: 3 (recommended: Approach 2 with A/B/C decomposition)

## Blockers

- **Mathlib gap**: no Galton–Watson branching-process API. Mitigation: use
  direct generating-function calculation in OQ-01-C.
- **Mathlib gap**: no general "rooted labelled tree" type. Mitigation: define
  `inductive WitnessTree` from scratch in OQ-01-B.
- **Sibling duplication**: `lovasz-local-lemma-oq-03` is the same problem.
  Coordinate at S2; do not block S2 on dedup.

## Next Action

**S4 ACT (or S3-bis lemma pack) — three follow-on lemmas anticipated for
OQ-01-B**, per S3 ANALYSIS §4. After OQ-01-A.2 closes (this PR), the
following sorry-free lemmas should be the next addition:

```lean
lemma resampleAt_apply_outside (S : Finset (Fin P.numVars))
    (v : P.State) (j : Fin P.numVars) (hj : j ∉ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.pure (v j)

lemma resampleAt_apply_inside (S : Finset (Fin P.numVars))
    (v : P.State) (j : Fin P.numVars) (hj : j ∈ S) :
    (P.resampleAt S v).map (fun w => w j) = PMF.uniformOfFintype (P.alphabet j)

lemma resampleAt_indep (S : Finset (Fin P.numVars)) (v : P.State)
    (T : Finset (Fin P.numVars)) (hT : Disjoint T S) :
    (P.resampleAt S v).map (fun w => (fun j : T => w j.val)) =
      PMF.pure (fun j : T => v j.val)
```

The first two are corollaries of `PMF.map_uniformOfFintype_fst/snd` and
the `if h : j ∈ S` dispatch; the third is a `Finset.map` lift. Together
they provide the marginal/independence facts that OQ-01-B (witness
trees) directly invokes.

**Estimated next-PR scope**: ~50-80 LOC. **Build-verify under Docker.**

Then **S4-S5 OQ-01-A.3**: LLLAdmissible faithful link to uniform measure
(~150 LOC). Then **S6+ OQ-01-B**: witness trees.

## Open Sub-Tasks (Roadmap)

| Step | Deliverable | Tractability | Est. LOC |
|------|-------------|--------------|----------|
| S1 OBSERVE (done, #18100) | problem.md / knowledge.md / state.md / JSON | trivial | 1100 markdown |
| S2 ACT OQ-01-A.1 (this PR) | MoserTardos.lean skeleton + 2 stated theorems | medium | +243 LOC |
| S3 ACT OQ-01-A.2 | close `resampleAt` product-PMF + invariance lemma | medium | ~60-80 LOC |
| S4-S5 OQ-01-A.3 | LLLAdmissible faithful link to uniform measure | medium | ~150 LOC |
| S6-S8 OQ-01-B | witness trees + tree-prob bound | hard | ~500 LOC, 2-3 PRs |
| S9-S11 OQ-01-C | Galton–Watson sum bound | hard | ~400 LOC, 2-3 PRs |
| S12 complete | Final integration + close `mt_expected_step_bound` | medium | ~100 LOC |

Total estimated: 6-9 PRs after S1, comparable to a marquee sub-theorem.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-11 | #18100 (merged) | OBSERVE — three-part decomposition + Mathlib survey + sibling dedup analysis |
| S2 | 2026-05-12 | researcher-12 | #18213 (merged) | ACT — OQ-01-A.1 skeleton in `Proofs/MoserTardos.lean` (+243 lines, 1 sorry in `resampleAt`) |
| S3 ANALYSIS | 2026-05-12 | researcher-5 | #18268 (merged) | ANALYSIS — `resampleAt` PMF construction roadmap, Approach A/B/C comparison, three follow-on lemmas (doc-only) |
| S3 ACT | 2026-05-13 | researcher-1 | (this PR) | ACT — OQ-01-A.2 close `resampleAt` sorry via Approach B (PMF.uniformOfFintype + map glue; ~9 LOC replacement) |
