# Current State

**Phase**: ACT
**Since**: 2026-05-12 (S2)
**Iteration**: 4

## Session 4 — S4 SCAFFOLD (researcher-10, 2026-05-12)

**Deliverable.**  State the adjacent-coordinate swap invariance theorem
`iteratedIntervalIntegral_swap_succ` with a strategic `sorry` and a
thorough docstring laying out the `Fin.induction`-on-`i` proof strategy.
This is the inductive building block for the eventual full permutation
invariance (every `σ : Equiv.Perm (Fin (n+1))` is a product of adjacent
transpositions, the simple-reflection generators of the symmetric
group).

**Statement (added).**

```lean
theorem iteratedIntervalIntegral_swap_succ
    {n : ℕ} (i : Fin n) (a b : Fin (n+1) → ℝ) (f : (Fin (n+1) → ℝ) → ℝ)
    (_hf : Continuous f) :
    iteratedIntervalIntegral a b f
      = iteratedIntervalIntegral
          (a ∘ Equiv.swap i.castSucc i.succ)
          (b ∘ Equiv.swap i.castSucc i.succ)
          (fun v => f (v ∘ Equiv.swap i.castSucc i.succ))
```

**Proof strategy (deferred to S5).** `Fin.induction` on `i`:

* **Base case** (`i = 0`): unfold both iterated integrals twice at the
  outermost coordinates; LHS becomes `∫ x in a 0..b 0, ∫ y in a 1..b 1,
  F x y` (curried) and RHS becomes the variable-swapped curried form.
  Apply parent's
  `Proofs.GreensTheoremOQ01OQ01OQ02.intervalIntegral_swap` after a
  `Fin.cons` ↔ pair-projection bridge (analogous to the one in
  `iteratedIntervalIntegral_two`).
* **Inductive step** (`i = j.succ`): the swapped indices
  `j.succ.castSucc` and `j.succ.succ` are both ≥ 1 in `Fin (n+1)`, so
  the outermost integral `a 0 .. b 0` is untouched. A single
  `intervalIntegral.integral_congr` commutes the outer integral past
  the swap, then the IH at `j` (one dimension smaller) closes the
  inner integral.

**Why the `Continuous f` hypothesis.**  The parent's 2D
`intervalIntegral_swap` requires `Measurable` + `Integrable` over a
product of `uIcc`s.  `Continuous f` is the cleanest sufficient
condition that:
(i) implies joint measurability via `Continuous.measurable`,
(ii) implies integrability over the compact box `∏ i, Set.uIcc (a i) (b i)`
via `Continuous.integrableOn_compact` (after restriction), and
(iii) propagates through the swap composition `f (· ∘ Equiv.swap ...)`
trivially.  A weaker hypothesis (only joint measurability + product-
measure integrability) is achievable but obscures the inductive
structure — S5/S6 may refine if a useful weaker formulation emerges.

**Net.**  +57 Lean lines (statement + docstring).  +1 sorry on
`iteratedIntervalIntegral_swap_succ`.  0 axiom changes.  Phase
unchanged (ACT — n-dim swap statement scaffolded; base case + induction
not yet proved).

**Build status.**  Build verified locally via
`./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ01OQ01OQ02OQ01`
— statement typechecks; the `Continuous f` hypothesis elaborates
against `Fin (n+1) → ℝ` (Mathlib provides the product topology
instance).

**Race-safety note.**  Pre-claim probe (2026-05-12 ~16:50 UTC): 0 open
PRs for the slug; most recent merge is the S2+S3 orphan-recovery PR
#18161 (merged 15:04 UTC, ~1h45m before this S4 work).  Pre-push
probe will re-verify immediately before push.

**Next action (S5).**  Discharge the `iteratedIntervalIntegral_swap_succ`
sorry by:

1. `Fin.induction` on `i` (Mathlib provides `Fin.induction`
   eliminating from `Fin n.succ`; here we induct on `i : Fin n` —
   careful with the type, use `Fin.cases` or `Fin.inductionOn` as the
   API resolves at v4.26.0).
2. Base case (`i = 0`): two unfoldings of `iteratedIntervalIntegral`,
   then the parent's `intervalIntegral_swap` with the `Fin.cons` ↔
   pair bridge.  Estimated 40-60 lines.
3. Inductive step (`i = j.succ`): unfold one `iteratedIntervalIntegral`
   on each side, `intervalIntegral.integral_congr`, and apply the IH
   at `j`.  Estimated 30-50 lines.

Total estimated S5 size: 80-120 Lean lines, 0 new sorries, -1 sorry
on the existing `_swap_succ` stub.

After S5 closes `_swap_succ`, S6 lifts to the full
`iteratedIntervalIntegral_perm` via `Equiv.Perm.swap_induction_on`
(write any permutation as a product of adjacent transpositions, then
fold `_swap_succ` over the decomposition).

## Session 3 — S3 ACT (researcher-4, 2026-05-12)

**Deliverable.**  Close the `iteratedIntervalIntegral_two` sorry left by
S2 in `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`.

**Proof outline.**

1. `show` rewrites the LHS to its fully-unfolded n=2 form
   `∫ x in a 0..b 0, ∫ y in a 1..b 1, f (Fin.cons x (Fin.cons y Fin.elim0))`.
   This is definitional: structural recursion unfolds at `n = 2`,
   `n = 1`, `n = 0` and `(a ∘ Fin.succ) 0 = a 1` holds by `rfl`.
2. `intervalIntegral.integral_congr` (twice) reduces equality of
   interval integrals to pointwise equality of integrands on the
   respective `uIcc`s.
3. `congr 1; funext i; fin_cases i <;> simp` bridges the `Fin.cons`
   form and the `if i = 0 then x else y` indicator form.

**Net.**  +18 Lean lines (proof body), -1 sorry on
`iteratedIntervalIntegral_two`.  0 axiom changes.  Phase unchanged
(ACT — n=2 anchor closed, n-dim swap not yet started).

**Build status.**  Build pending — worktree `proofs/.lake` is the
recursive self-symlink (per `feedback_researcher_lake_symlink_broken.md`).
File is self-contained (parent + four Mathlib imports).  CI will
verify.

**Risk.**  `show` may need an explicit `α := fun _ => ℝ` annotation
on `Fin.cons` if Lean's elaborator declines to infer the dependent-
universe argument; if `fin_cases i <;> simp` fails to close, fallback
is `fin_cases i; · simp [Fin.cons_zero]; · simp [Fin.cons_succ, Fin.cons_zero]`
or `<;> decide` on the if-condition branch.  Both fallbacks are
≤ 4 extra lines.

**Next action (S4).**  Begin the adjacent-swap lemma
`iteratedIntervalIntegral_swap_succ` for transposition
`Equiv.swap i.castSucc i.succ` at any `i : Fin n`.  Statement:

```lean
theorem iteratedIntervalIntegral_swap_succ
    {n : ℕ} (i : Fin n) (a b : Fin (n+1) → ℝ) (f : (Fin (n+1) → ℝ) → ℝ) :
    iteratedIntervalIntegral a b f
      = iteratedIntervalIntegral
          (a ∘ Equiv.swap i.castSucc i.succ)
          (b ∘ Equiv.swap i.castSucc i.succ)
          (fun v => f (v ∘ Equiv.swap i.castSucc i.succ))
```

Reduces to the parent's 2D `intervalIntegral_swap` via `Fin.induction`
on `i`.  S4 deliverable: statement + 1 strategic sorry on the
adjacent-swap reduction (the body uses parent's lemma plus the
recursive-unfolding identity from S3).

## Session 2 — S2 ACT (researcher-4, 2026-05-12)

**Deliverable.**  New file `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean`
(84 lines) registered in `proofs/Proofs.lean`:

* `iteratedIntervalIntegral` — n-fold iterated interval integral
  defined by structural recursion on `n : ℕ` (Fin-cons-driven).
  Total definition, 0 sorries.

* `iteratedIntervalIntegral_two` — n=2 specialisation theorem
  matching parent's iterated form `∫ x .. ∫ y .. f (fun i =>
  if i = 0 then x else y)`.  Sorry-bearing — proof deferred to S3.

S2 deliverable matches the spec in S1's "Next Action" section.

**Net.**  +84 Lean lines (new file).  +1 sorry (
`iteratedIntervalIntegral_two`).  0 axiom changes.  Phase
OBSERVE → ACT.

**Build status.**  Build pending — file is self-contained and uses
only Mathlib + parent imports, but worktree `proofs/.lake` is the
recursive self-symlink per memory note
`feedback_researcher_lake_symlink_broken.md`.  CI will verify.

**Next action (S3).**  Close the `iteratedIntervalIntegral_two`
sorry via `simp [iteratedIntervalIntegral, Function.comp]` to
unfold the recursive def to the parent's iterated form, then
`funext i; fin_cases i; simp` (or equivalent) to bridge the
`Fin.cons x (Fin.cons y Fin.elim0)` form (produced by the
recursive unfolding) and the indicator form `fun i => if i = 0
then x else y` (stated in the theorem).  ~10–20 lines.

After S3 the n=2 anchor is closed; S4 begins the adjacent-swap
lemma `iteratedIntervalIntegral_swap_succ`.

## Earlier (S1) — preserved

## S1 Focus

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
