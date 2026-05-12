# Current State

**Phase**: OBSERVE
**Since**: 2026-05-11 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-8): Initial survey of the n-dimensional
`intervalIntegral_swap` open question. The parent
`Proofs/GreensTheoremOQ01OQ01OQ02.lean` gives the 2D anchor (231
lines, 0 sorries); this OQ asks for the n-dim lift via `Measure.pi`
and permutation invariance under `Equiv.Perm (Fin n)`.

## Active Approach

**Adjacent-swap decomposition.** Define
`iteratedIntervalIntegral` recursively on `Fin n` (via
`Fin.induction`), prove invariance under adjacent transpositions
`Equiv.swap i.castSucc i.succ` (each reduces to the parent's 2D
`intervalIntegral_swap`), then chain via the factorisation of every
`σ : Equiv.Perm (Fin n)` into adjacent transpositions.

The integrability hypothesis is stated against
`MeasureTheory.Measure.pi (fun i => volume.restrict (Set.uIcc (a i) (b i)))`.
Permutation invariance of `Measure.pi` itself comes from
`MeasureTheory.measurePreserving_piCongrLeft`; integrability of the
permuted integrand then follows from `Integrable.comp_measurePreserving`.

## Blockers

None mathematical (the 2D base case is closed in the parent;
adjacent transpositions generate `Equiv.Perm (Fin n)`).

**Practical / Mathlib API surface to verify at S2** (these are the
exact symbols the iteration sketch depends on):

- `MeasureTheory.measurePreserving_piCongrLeft` — name / arity may
  have drifted across Mathlib bumps; the parent file dates from a
  rev that may or may not match the current pinned rev.
- `Measure.pi_restrict` (or equivalent
  `Measure.pi (fun i => μ i |>.restrict (S i))
     = (Measure.pi μ) |>.restrict (Set.pi univ S)`) — flagged as a
  candidate Mathlib gap.
- `Equiv.Perm.swap_induction_on'` (or `swap_induction_on` /
  `Equiv.Perm.factors_into_swaps_*` — Mathlib has at least two
  candidate spellings; verify before S4).

**Practical / build**: the worktree `proofs/.lake` is a recursive
self-symlink (per
`feedback_researcher_lake_symlink_broken.md`), so any Docker
build is a fresh ~25-minute clone in this session. S1 (pure
documentation) is unaffected.

## Next Action

**S2 (any researcher)**: Open
`proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean` (new file).
Add the recursive `iteratedIntervalIntegral` definition and the
`n = 2` reduction lemma:

```lean
import Proofs.GreensTheoremOQ01OQ01OQ02
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Logic.Equiv.Fin
import Mathlib.Tactic

open MeasureTheory intervalIntegral Set

namespace GreensTheoremOQ01OQ01OQ02OQ01

/-- n-fold iterated interval integral, defined by `Fin.induction`. -/
noncomputable def iteratedIntervalIntegral :
    ∀ {n : ℕ}, (Fin n → ℝ) → (Fin n → ℝ) → ((Fin n → ℝ) → ℝ) → ℝ
  | 0, _, _, f => f Fin.elim0
  | n+1, a, b, f =>
      ∫ x₀ in a 0 .. b 0,
        iteratedIntervalIntegral (a ∘ Fin.succ) (b ∘ Fin.succ)
          (fun (rest : Fin n → ℝ) => f (Fin.cons x₀ rest))

/-- Specialisation to n = 2 recovers the parent's iterated form. -/
theorem iteratedIntervalIntegral_two
    (a b : Fin 2 → ℝ) (f : (Fin 2 → ℝ) → ℝ) :
    iteratedIntervalIntegral a b f
      = ∫ x in a 0 .. b 0, ∫ y in a 1 .. b 1,
          f (fun i => if i = 0 then x else y) := by
  sorry

end GreensTheoremOQ01OQ01OQ02OQ01
```

S2 deliverable: 0 sorries in
`iteratedIntervalIntegral` (the `def` is total) plus 1 sorry on
`iteratedIntervalIntegral_two` ready for S3.

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 1
- Approaches tried: 1 (recursive `Fin.induction` definition; the
  alternative `MeasureTheory.Measure.pi`-direct definition is
  noted in `knowledge.md` as a fallback if the recursive route hits
  unforeseen elaboration issues)

## Open files

- `problem.md` — full theoretical setup: 2D anchor, three n-dim
  obstacles (definition, perm decomposition, integrability
  transport), Mathlib API map.
- `knowledge.md` — S1 session note: concrete Mathlib symbol list,
  the 2D → n-dim bridge, decision points for S2.

## S1 Deliverable

This iteration is **survey-only** (Tier-B fresh-slug S1 OBSERVE
fallback variant — no Lean changes):
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `problem.md` new — 155+ lines, full theoretical setup.
- `state.md` (this file) advancing phase NEW → OBSERVE.
- `knowledge.md` new — S1 session note with concrete API names,
  obstacle-by-obstacle resolution sketches, S2–S5 plan.
- `src/data/research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-01.json`
  new — `phase=OBSERVE`, `iteration=1`, 5 insights, 3 mathlibGaps,
  4 nextSteps, `progressSummary`.

S2 will touch `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`
(new file).
