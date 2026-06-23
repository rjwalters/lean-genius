# Current State

**Phase**: ORIENT
**Since**: 2026-03-28T20:57:10Z
**Iteration**: 1 (S1 OBSERVE scaffold, this PR)
**Last Updated**: 2026-05-13 (researcher-12)

## Current Focus

Iteration 1 (2026-05-13, researcher-12, this PR): **S1 OBSERVE — scaffold
`research/problems/erdos-501-incomplete-01/` directory** transcribing prior
JSON-state knowledge into worktree-tracked markdown and identifying the
cleanest near-term research lever.

This is a **doc-only PR**: no Lean changes; sole purpose is to unblock
future iterations by giving working-tree markdown a clean starting point.
The slug has substantial prior `src/data/research/problems/<slug>.json`
content (11 `builtItems`, 3 `nextSteps`) but no `research/problems/<slug>/`
directory until this PR.

## Snapshot — Lean state (current `origin/main`)

| File | Lines | Sorries | Axioms |
|------|-------|---------|--------|
| `Proofs/Erdos501Problem.lean` | 278 | 3 | 0 |
| `Proofs/Erdos501ProblemProvable.lean` | 267 | 3 | 0 |
| `Proofs/Erdos501Aristotle.lean` | 158 | 1 | 0 |

**Aggregate**: 703 lines, 7 sorries, 0 axioms.

The `*Provable.lean` file is a near-duplicate of the main file with one fix:
`continuum_hypothesis` is now `Cardinal.aleph 1 = Cardinal.continuum`
(formalized using `Cardinal`) rather than the older trivially-provable
surjection form `∀ S ⊆ ℝ uncountable, ∃ surjection ℝ → S`. The two files
ship in parallel; the next-action recommendation below proposes
**collapsing them** as one of two parallel research levers.

## Sorries (open work)

Three theorem sorries in each of `Erdos501Problem.lean` and
`Erdos501ProblemProvable.lean` (six total, plus 1 in Aristotle):

### Lever A (most tractable): `exists_independent_tuple` for `n ≥ 2`

**Statement** (Erdős–Hajnal 1960): for `A : SetFamily` with bounded
outer-measure < 1 family condition, every `n : ℕ` admits an n-tuple of
distinct reals `f : Fin n → ℝ` with `f i ∉ A (f j)` for `i ≠ j`.

**Proof sketch** (per the existing docstring): choose `L > n·(n-1)`. The
cube `[0,L]^n ⊆ ℝ^n` has Lebesgue measure `L^n`. For each ordered pair
`(i,j)` with `i ≠ j`, the conflict set
  `C_{ij} = {f ∈ [0,L]^n : f(i) ∈ A(f(j))}`
has product measure `L^(n-1) · m(A_*) ≤ L^(n-1)·1 = L^(n-1)`. Union over
the `n(n-1)` ordered pairs: total conflict mass `≤ n(n-1)·L^(n-1) < L^n`,
so the complement is nonempty — pick any `f` there.

**Mathlib gap**: outer-measure Tonelli/Cavalieri on product spaces. Mathlib
has Fubini for *measurable* sets via `MeasureTheory.integral_prod`; the
outer-measure version may need either bridging to measurable-cover form
(`MeasureTheory.OuterMeasure.toMeasure`) or a direct outer-measure
sub-Fubini estimate. Base cases `n = 0` (`Fin.elim0`) and `n = 1`
(`Subsingleton`) are already proved.

**Build risk**: moderate. The product-measure bookkeeping is Mathlib-heavy;
expect 100-200 LOC including the conflict-set definition + the
union-bound + the existence extraction.

### Lever B (deep): `hechler_under_CH` and `nps_closed_infinite`

Both are deep formalization efforts requiring substantial new Mathlib
infrastructure (transfinite induction over `ω_1` and descriptive set theory
of closed sets respectively). Recommend deferring to a dedicated multi-PR
research thread or to Aristotle proof search on smaller sub-lemmas.

### Lever C (administrative): collapse `Erdos501ProblemProvable.lean` into main

Per the JSON `nextAction`: "Either eliminate file duplication (provable now
mirrors main exactly), or break Mathlib gap with outer-measure Fubini
lemma." The `*Provable.lean` mirror was created during the CH-def bug fix
and is now mostly redundant. A clean-up PR could merge the two and delete
the duplicate, reducing the gallery's mirror-maintenance burden.

## Recommended next research lever

**Lever A** (`exists_independent_tuple` n ≥ 2). Rationale:

1. **Concrete and bounded**: the proof sketch is fully spelled out in the
   docstring; the work is mostly Mathlib bridging, not theorem invention.
2. **High-impact**: discharging it closes the Erdős–Hajnal 1960 result
   completely (currently `erdos_hajnal_finite` is proved CONDITIONAL on
   `exists_independent_tuple`, which is sorried — so the whole chain is
   currently vacuous).
3. **Builds Mathlib leverage**: any outer-measure Tonelli/Cavalieri lemma
   added in passing benefits other CH-sensitive / measure-theoretic
   formalization across the gallery.
4. **No deep set-theory required**: unlike levers B (Hechler/NPS), this is
   pure elementary measure-theoretic counting; tractable without descriptive
   set theory or forcing.

A first ACT iteration could scaffold the `[0,L]^n` cube and the conflict
sets without yet discharging the outer-measure inequality — that splits
the work cleanly across 2-3 PRs.

## Blockers

None for the doc-only S1 OBSERVE scaffold (this PR).

For Lever A: the cleanest formalization may require introducing a Mathlib
helper `MeasureTheory.OuterMeasure.le_prod_outer` (outer-measure
sub-Fubini); if Mathlib already has an equivalent under a different name,
no new infrastructure is needed — that's the first PREP step.

## Attempt Counts

- Total attempts: 1 (this S1 OBSERVE scaffold)
- Current approach attempts: 1 (S1 OBSERVE — directory creation +
  problem.md / state.md transcription from JSON state)
- Approaches tried: 1 (S1 OBSERVE only; no prior worktree-tracked
  research narrative existed)

## Next Action

Commit, push, create PR for S1 OBSERVE (this scaffold). After merge, the
next researcher to claim `erdos-501-incomplete-01` should:

1. Read this state.md + problem.md.
2. Decide on lever A (recommended), B (deep), or C (admin).
3. For lever A: open a S3 PREP PR sketching the conflict-set definition
   and Mathlib bearer audit for outer-measure Tonelli (i.e., is the
   needed inequality already in Mathlib under a different name?).
