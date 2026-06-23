# Session 12 ACT — IsBigO / IsLittleO bridge to Mathlib idiom

- **Date**: 2026-05-24
- **Session**: 12
- **Phase**: ACT
- **Researcher**: researcher-1
- **Status**: ACT lands the queued S11 ACT recipe per S10 PREP §5.1–§5.3 with all five audit-corrections inlined

## 1. TL;DR

Implements the three-artifact IsBigO / IsLittleO bridge that S6–S10
PREP queued (and S10 PREP §5.1–§5.3 made paste-ready). All five
S9 + S10 audit-flagged bugs are inlined:

| Bug | Fix in this PR |
|-----|----------------|
| **F** (artifact (iii) MUST be existential, not concrete IsLittleO on `maxFourPointLines`: ratio → 1/12 ≠ 0) | `erdos_101_oq_01_isLittleO_form` is `∃ g, IsLittleO atTop ↑g (·^2) ∧ BoundsAtRate ↑g` |
| **G** (per-P corollary MUST carry `NoFiveCollinear`: refutable at 9-collinear with `C(9,4)=126 > 6=maxFourPointLines 9`) | `fourPointLineCount_le_max P (hP : NoFiveCollinear P) : ...` carries `hP`, routed via `improved_upper_bound P hP` |
| **H** (bridge `isLittleOh_n_squared_iff_isLittleO` was always-deferred from S6 onward — first materialised here) | Lemma `isLittleOh_n_squared_iff_isLittleO (g : ℕ → ℕ) : IsLittleOh_n_squared g ↔ IsLittleO atTop ↑g (·^2)` shipped before artifact (iii) |
| **I** (`IsBigO.of_norm_le` hypothesis has ONE norm: `‖f x‖ ≤ g x`, not `≤ ‖g x‖`) | Single-norm collapse via `rw [Real.norm_of_nonneg (by positivity)]`; no `show`, no double `abs_of_nonneg` |
| **J** (sequencing trap: artifact (ii) MUST appear before artifact (iii) iff proof) | Source order: (i) at L208–L246, (ii) at L248–L286, (iii) at L288–L335 |

Insertion point: after `bounds_at_rate_quadratic_over_twelve` (L204
end), before the existing `/- ## The OPEN refinement and its
consequences` doc block (L208 in pre-edit file). Keeps known/elementary
lemmas above open/aspirational.

## 2. Counter deltas

| Metric | Pre-S12 | Post-S12 | Δ |
|---|---|---|---|
| Sorries | 2 | 3 | +1 (`erdos_101_oq_01_isLittleO`) |
| Axioms | 0 | 0 | unchanged |
| Theorems | 9 | 13 | +4 (`maxFourPointLines_isBigO_n_squared`, `fourPointLineCount_le_max`, `erdos_101_oq_01_rate_form_iff_isLittleO`, `erdos_101_oq_01_isLittleO`) |
| Lemmas | 0 | 1 | +1 (`isLittleOh_n_squared_iff_isLittleO`) |
| Defs | 4 | 6 | +2 (`maxFourPointLines`, `erdos_101_oq_01_isLittleO_form`) |
| LOC | 471 | 603 | +132 |

LOC delta is +132 vs the recipe-budgeted +78 — the additional ~54 LOC
are docstrings (each new declaration carries a `/-- ... -/` doc-comment
explaining the rationale) plus the wrapping S11/S12 ACT introduction
block. Pure body LOC matches the recipe.

## 3. Imports added

```lean
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
```

Both are cheap insurance per S11 ACT step 3; the parent file already
transitively imports them through `Mathlib.Analysis.SpecialFunctions.*`,
but explicit imports make the bridge artifacts robust against Mathlib
import-graph reorganisation.

## 4. Build status

**[BUILD UNVERIFIED — worktree symlink trap]**

The researcher worktree's `proofs/.lake` is a recursive self-symlink
(per long-standing `feedback_researcher_lake_symlink_broken.md`).
Docker build requires invocation from the main repo checkout or via
the mechanic agent.

**Forecast**: ≤ 2 Docker iterations per S10 §8 gate 7. Most likely
iter-2 fix sources:

1. `Real.norm_of_nonneg` vs `Real.norm_natCast` normalisation — if the
   norm collapses differently than expected after `intro n`, fall back
   to `simp only [Real.norm_eq_abs, abs_of_nonneg (by positivity)]`.
2. `nlinarith` in artifact (ii) `←` direction — if it doesn't close,
   fall back to explicit `calc` chain documented in S10 §11 (~3 extra
   LOC: `h ≤ (ε/2) * (n : ℝ)^2 < ε * (n : ℝ)^2` via `hn_sq_pos`).

If iter 1 fails for any reason not in this fallback list, mechanic
should escalate to S13 PREP for diagnosis.

## 5. Mathlib bearers used (all v4.26.0 at lake-pin `2df2f01`)

Artifact (i) — `maxFourPointLines_isBigO_n_squared`:
- `Asymptotics.IsBigO.of_norm_le` — `Mathlib/Analysis/Asymptotics/Defs.lean`
- `Real.norm_of_nonneg` — `Mathlib/Analysis/Normed/Group/Basic.lean`
- `Nat.div_le_self`, `Nat.mul_le_mul_left`, `Nat.sub_le`, `Nat.cast_le` — core
- `positivity`, `push_cast`, `ring`, `linarith` — Mathlib tactics

Artifact (ii) — `isLittleOh_n_squared_iff_isLittleO`:
- `Asymptotics.isLittleO_iff` — `Mathlib/Analysis/Asymptotics/Defs.lean`
- `Filter.eventually_atTop` — `Mathlib/Order/Filter/AtTopBot/Basic.lean`
- `Real.norm_of_nonneg` (as above)
- `le_max_left`, `le_max_right` — core
- `positivity`, `linarith`, `nlinarith`, `exact_mod_cast` — Mathlib tactics

Artifact (iii) — `erdos_101_oq_01_isLittleO_form` + iff + main:
- The iff theorem reuses artifact (ii)'s lemma; no new bearers beyond
  `exact_mod_cast` and the previously imported `Asymptotics.IsLittleO`.

## 6. Why this S12 is meaningful

The slug now has *two equivalent statements* of the open OQ-01
conjecture: the original ε–N form (`erdos_101_oq_01`) and the
Mathlib-idiom existential form (`erdos_101_oq_01_isLittleO`). Both
sorry-marked, but the iff theorem
`erdos_101_oq_01_rate_form_iff_isLittleO` certifies that *any future
discharge of one implies the other* via the standard rate-witness
↔ ε-N bridge (the rate_form ↔ conjecture direction is by definition
unfolding; the iff in this PR closes the slug ↔ Mathlib gap).

Downstream consumers (gallery consumers of OQ-01) can now cite the
Mathlib-idiom form directly, e.g. `erdos_101_oq_01_isLittleO_form` as
a `Prop` parameter, without having to translate through the slug's
local `IsLittleOh_n_squared` predicate.

## 7. S13 candidates

Listed in tentative priority:

1. **Mechanic iter-2** (if build fails): apply the calc fallback per §4.
2. **True-sup `maxFourPointLines`**: replace the surrogate `n*(n-1)/12`
   with `Finset.sup'` over no-five-collinear point sets of fixed size.
   ~15 LOC additional; tightens artifact (i) to the actual maximum.
3. **Cauchy–Schwarz refinement**: of `fourCollinearThrough_bound`
   $\leq (n-1)/3$ to yield a $1 - o(1)$ leading constant on the
   elementary $n^2/12$ bound. Still $\Theta(n^2)$, but a concrete
   improvement.
4. **Witness extraction at small `n`**: via `decide` / `native_decide`
   on small finite combinatorics; supplies `native_decide`-certified
   examples for the gallery entry.
5. **Downstream integration**: search the proofs directory for places
   where the `Asymptotics.IsLittleO`-style form of OQ-01 would help
   consume the result without local slug-vocabulary indirection.

None of these block on the OPEN main conjecture's discharge.
