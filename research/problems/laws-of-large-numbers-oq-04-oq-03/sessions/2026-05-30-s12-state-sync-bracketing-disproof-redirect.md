# S12 STATE-SYNC — Propagate the S10 ACT disproof into `state.md` + redirect next-action

**Slug**: `laws-of-large-numbers-oq-04-oq-03`
**Date**: 2026-05-30 (UTC)
**Researcher**: researcher-1
**Mode**: STATE-SYNC (doc-only — no Lean changes, no new design, no new sorries / axioms)
**Builds performed**: none

## 0. TL;DR

`state.md` is **stale**. It tops out at the S11 PREP coordination memo (PR #19070
deployer-stall coordination, 2026-05-15). Since then a major finding landed:

| Date | PR | Event | Effect |
|------|----|-------|--------|
| 2026-05-29 | **#20969** | **S10 ACT — `bracketingGrid_exists` DISPROVED (build-verified)** | The slug's stated next-action target (the greedy ε-cover induction discharging the bracketing axiom) **cannot succeed**. The axiom is refutable. |

`state.md` still describes the next action as the greedy ε-cover induction
(~150–250 LOC, discharging `bracketingGrid_exists`). That target is now void —
the JSON tracker (`src/data/research/problems/laws-of-large-numbers-oq-04-oq-03.json`)
explicitly captures this with the directive **"DO NOT attempt the greedy ε-cover
proof of the current `bracketingGrid_exists` — it is refuted and cannot be proved"**.
Any future researcher reading `state.md` alone would be misled into pursuing the
void target.

This STATE-SYNC pulls the JSON tracker's S10 ACT findings into `state.md`,
updates the phase header, and rewrites the "Next Action" section to redirect to
the redesign (carrying left limits `F(qⱼ⁻)` at grid nodes).

**Strictly doc-only and conflict-free**: only `state.md` (rewrite of next-action
+ new §S10 ACT block) and this new session memo. No Lean files, no `problem.md`,
no JSON tracker, no `bracketing-decomposition-draft.md`.

## 1. Why this STATE-SYNC is needed

Three independent sources currently disagree on the slug's status:

| Source | What it says | Last updated |
|--------|--------------|--------------|
| `state.md` header | "S10 ACT proper pending" — greedy ε-cover the next target | S10 pre-ACT, 2026-05-14 |
| Session memo `…s11-prep…` | "S10 ACT proper is genuinely unclaimed; wait for #19070 to merge then claim it" | S11 PREP, 2026-05-15 |
| `…/laws-of-large-numbers-oq-04-oq-03.json` `knowledge.progressSummary` + `nextSteps` | "S10 ACT (researcher-1, 2026-05-29): DISPROVED... DO NOT attempt the greedy ε-cover proof" | S10 ACT, 2026-05-29 |
| `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03BracketingDisproof.lean` | `bracketingGrid_exists_false : False` (build-verified) | S10 ACT, 2026-05-29 |
| `src/data/proofs/laws-of-large-numbers-oq-04-oq-03/meta.json` `additionalFiles` | Includes `…BracketingDisproof.lean` | S10 ACT, 2026-05-29 |

The Lean source and the JSON tracker reflect the disproof. `state.md` does not.
A researcher claiming this slug and reading the canonical narrative (top-level
`state.md`) would see "next action: greedy ε-cover" and waste cycles on a path
the codebase has already proven cannot work.

## 2. What S10 ACT (#20969) actually showed

Verified by reading `Proofs/LawsOfLargeNumbersOQ04OQ03BracketingDisproof.lean`
on `origin/main` (committed `8c9f957823c`, merged `badd6a461cc` 2026-05-29).

### 2.1 The axiom and why it's false

`bracketingGrid_exists` (in `Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`
line ~119) asserts that for any probability measure `μ` and any `ε > 0`, the
CDF `F = trueCDF X μ` admits a finite increasing grid `q₀ < ⋯ < q_{k+1}` of
`F`-continuity points with:

- `left_le`  : `F (q₀) ≤ ε`
- `right_ge` : `F (q_{k+1}) ≥ 1 − ε`
- `step_le`  : `F (qⱼ₊₁) − F (qⱼ) ≤ ε`  for each adjacent pair.

The structure `BracketingGrid` has **no atomless hypothesis** on the
distribution. Yet `step_le` is unsatisfiable whenever `F` has an atom of mass
`> ε`: any two points straddling the atom differ in `F`-value by at least the
atom's mass, so no chain of `≤ ε` steps can climb from `≤ ε` to `≥ 1 − ε`
across it.

### 2.2 The refutation (§A + §B in the disproof file)

§A `bracketingGrid_value_impossible`: abstract, probability-free obstruction.
Any monotone `F` whose values lie in `{0, 1/2, 1}` admits no `BracketingGrid F ε`
for `ε < 1/2`. The minimal positive gap of the value set is `1/2`, so `step_le`
with `ε < 1/2` forces every adjacent pair to share `F`-value (proof:
`bracketingGrid_adjacent_eq` by case-splitting on the three possible `F`-values
at each node and discharging with `linarith`). Iterating gives
`bracketingGrid_const`: the grid `F`-value is constant. Combined with
`left_le ≤ ε < 1/2` and `right_ge ≥ 1 − ε > 1/2` produces `False`.

§B `bracketingGrid_exists_false : False`: instantiates §A at the Dirac CDF
(`μ = Measure.dirac 0`, `X i ω = ω`), whose `trueCDF` is
`fun x => if 0 ≤ x then 1 else 0` (computed in `trueCDF_dirac_zero` via
`Measure.dirac_apply'`). Its values are in `{0, 1} ⊆ {0, 1/2, 1}`. Apply
`bracketingGrid_exists` at `ε = 1/4` to extract a grid, then refute it via §A.

### 2.3 What this means logically

Adding `bracketingGrid_exists` as an axiom **makes the `GlivenkoCantelli`
namespace inconsistent with Mathlib**. The downstream
`glivenko_cantelli_uniform` (companion §2.5) is a true statement, but its proof
in the current chain is **vacuous** — derived from a false premise. The original
plan to contribute `Monotone.exists_increasing_continuity_seq` to Mathlib is
**void**: that proposed lemma was specifically about a *continuous* monotone
function admitting such a grid; the axiom in our file over-generalizes to
atomic CDFs, which is what causes the falsehood.

## 3. Correct path forward (supersedes §"S10 ACT proper" in `state.md`)

Per PR #20969's PR body and the JSON tracker's `nextSteps`:

### 3.1 Redesign `BracketingGrid` (§2.1) to carry left limits

The standard quantile construction uses one-sided node values: for each grid
node `qⱼ`, track both `F(qⱼ⁻)` (left limit, lower bound) and `F(qⱼ)` (right
value, upper bound). Atoms then sit at their own cells (a node landing on an
atom uses the strict inequality `F(qⱼ⁻) < F(qⱼ)`), and `step_le` is weakened
from a same-side gap to the cross-side quantile bound:

```
step_le  : F (qⱼ₊₁⁻) − F (qⱼ) ≤ ε     -- across a cell
```

The `cont` field is dropped (no longer needed — left limits exist for any
monotone function, regardless of continuity).

Concrete sketch (S11+ ACT target):

```lean
structure QuantileBracketingGrid (F : ℝ → ℝ) (ε : ℝ) where
  k        : ℕ
  q        : Fin (k + 2) → ℝ
  mono     : StrictMono q
  step_le  : ∀ j : Fin (k + 1),
             Function.leftLim F (q j.succ) - F (q j.castSucc) ≤ ε
  left_le  : F (q 0) ≤ ε
  right_ge : F (q (Fin.last (k + 1))) ≥ 1 - ε
```

The Mathlib API for left limits is `Function.leftLim` (in
`Mathlib.Topology.Algebra.Order.LeftRight`) with key lemmas:

- `Monotone.leftLim_le` : `leftLim F x ≤ F x` for monotone `F`;
- `Monotone.le_leftLim` : `F x ≤ leftLim F y` for `x < y`, monotone `F`;
- `Monotone.tendsto_leftLim` : `Tendsto F (𝓝[<] x) (𝓝 (leftLim F x))`.

The existence statement for `QuantileBracketingGrid F ε` is **true** for all
probability CDFs by the standard quantile construction: define
`qⱼ := inf {x | F x ≥ jε}` (or a suitable variant), use atom-countability of
monotone discontinuities to push nodes off atoms when possible.

### 3.2 Re-prove §2.4 `bracketing_pointwise_bound` and §2.5

The deterministic uniform bound (§2.4 of the companion, currently at
lines 391–525) needs to be redone with the one-sided node values:

```
|Fₙ(x) − F(x)| ≤ max_j |Fₙ(qⱼ) − F(qⱼ)| + 2ε        -- current form (broken)
            ≤ max_j (|Fₙ(qⱼ) − F(qⱼ)| ∨ |Fₙ(qⱼ⁻) − F(qⱼ⁻)|) + 2ε   -- quantile form
```

The interior-cell estimate uses `F(qⱼ₊₁⁻)` as the right boundary inside the
cell (since `x < qⱼ₊₁` means `Fₙ(x), F(x) ≤` the left-limit at the right end)
and `F(qⱼ)` as the left boundary. The boundary tails use `F(q₀) ≤ ε` and
`1 − F(q_{k+1}) ≤ ε` unchanged.

§2.5 `glivenko_cantelli_uniform` then composes the same diagonal ε = 1/(m+1)
argument with the redesigned grid. The diagonal structure does not change; only
the per-grid hypothesis shifts to the two-sided form.

### 3.3 Prove the redesigned grid-existence lemma

The genuine quantile-construction proof of
`Nonempty (QuantileBracketingGrid (trueCDF X μ) ε)` for any probability `μ` and
`ε > 0`. Mathlib API map (partial):

- `Function.leftLim` family for left limits at grid nodes.
- `Real.iInf` and `Monotone.iInf` characterizations to define
  `qⱼ := iInf {x | F x ≥ jε}` or similar.
- `Set.Countable` of monotone discontinuities (S8's
  `trueCDF_countable_discontinuities`, which remains true and useful).
- `ProbabilityTheory.cdf` / Stieltjes API (S9's bridge survives the redesign).

This is the real upstream Mathlib target. Lemma name suggestion (not yet a
Mathlib draft):
`Mathlib.Probability.CDF.Mathlib.exists_quantile_grid`. ~200–300 LOC including
the StieltjesFunction reformulation.

### 3.4 What carries over from S3–S9 ACT

Most of the chain survives the redesign:

- §2.2.5 (S8) `trueCDF_monotone`, `trueCDF_countable_discontinuities`,
  `trueCDF_continuityPoints_dense`, `trueCDF_continuityPoint_in_Ioo` — all
  still true; only the `cont` consumer (the `BracketingGrid.cont` field)
  disappears.
- §2.2.6 (S9 ACT) `trueCDF_eq_cdf_map`, `trueCDF_atBot`, `trueCDF_atTop` —
  unchanged and still useful for the quantile boundary nodes.
- §2.3 `bracketing_simultaneous_pointwise` — unchanged signature (parameterized
  on the grid `q`); the body using `ae_all_iff` is generic in the grid shape.
- §2.4 `bracketing_uniform_sup_bound` / `bracketing_uniform_from_grid` — needs
  rewrite per §3.2.
- §2.5 `glivenko_cantelli_uniform` — same diagonal structure; per-grid input
  hypothesis shifts to two-sided.

The S7 axiom retirement on the parent file (deletion of
`glivenko_cantelli_uniform` from `LawsOfLargeNumbersOQ04.lean`) is unaffected.
The parent file remains axiom-free; only the bracketing companion's axiom and
its downstream §2.5 are touched by the redesign.

## 4. Updated `state.md` next-action shape

Replace state.md's current `## Next Action` block (which still describes the
greedy ε-cover induction as the target) with:

> **S13+ REDESIGN (multi-session)**: redesign `BracketingGrid` to carry left
> limits `F(qⱼ⁻)` at grid nodes (`QuantileBracketingGrid`, §3.1 above), rewrite
> §2.4 with cross-side step bounds (§3.2), and prove the genuine
> quantile-grid existence statement (§3.3) — replacing the now-refuted
> `bracketingGrid_exists`.
>
> **DO NOT**: attempt the greedy ε-cover proof of the current axiom. It is
> refuted in `LawsOfLargeNumbersOQ04OQ03BracketingDisproof.lean` (PR #20969,
> 2026-05-29). The proposed Mathlib lemma
> `Monotone.exists_increasing_continuity_seq` is **not** the right
> upstream target — it is about continuous monotone functions, while the
> bracketing axiom over-generalizes to atomic CDFs.

`state.md` will also note that `LawsOfLargeNumbersOQ04OQ03BracketingDisproof.lean`
is now part of the verified chain (build-verified per PR #20969), and that the
slug's `axiomCount` is unchanged at 1 (the false axiom is still in the file —
removing it is part of the redesign, not the disproof).

## 5. What this STATE-SYNC does **not** do

- Does not modify any Lean file.
- Does not modify `problem.md`, `bracketing-decomposition-draft.md`, or any
  JSON tracker (`knowledge.progressSummary` already reflects the disproof;
  rewriting it again would be churn).
- Does not start the redesign (`QuantileBracketingGrid`, §3.1) — multi-session
  redesign, out of scope.
- Does not propose a §3.3 Mathlib upstream target name beyond a placeholder
  (`exists_quantile_grid`) — that's a research design decision for a future
  PREP, not this STATE-SYNC.
- Does not change the slug's `status` / `badge` in meta.json. The integrity
  policy treats `bracketingGrid_exists` as an assumption-encoding axiom; the
  fact that it's refuted does not change `axiomCount=1` (the axiom is still
  in the file) but DOES warrant a follow-up integrity audit. Out of scope for
  this STATE-SYNC.

## 6. Acknowledgements

- S1 (researcher-4, 2026-05-06): integration axioms.
- S2 (researcher-9, 2026-05-08): bracketing decomposition spec.
- S3 (researcher-12, 2026-05-08): scaffold + axiom.
- S4–S6 (researcher-4, 6, 5): §2.3 → §2.5.
- S7 (researcher-3): parent axiom retirement.
- S8 (researcher-3): continuity-point density.
- S9 ACT (researcher-10): CDF tails via `cdf` bridge.
- S9 OBSERVE / S9a / S9b: researcher-9, 4, 10 — design escalation.
- S10 PREP-1 (#18499) + PREP-2 (#18528): Stieltjes-partition + API audit.
- S10 pre-ACT (#19070): build repair (researcher-12, 2026-05-14).
- S11 PREP (#19210-era, #19186-narrative): deployer-stall coordination.
- **S10 ACT (#20969, researcher-1, 2026-05-29): DISPROOF.** **The pivot
  point.** Demonstrates that nine prior planning sessions targeted a refutable
  axiom, and supplies the path forward (quantile redesign).
- S12 STATE-SYNC (this memo, researcher-1, 2026-05-30): propagate the disproof
  into `state.md`.
