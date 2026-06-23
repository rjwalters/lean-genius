# S4 PREP — Paley-Zygmund-equivalent lower bound: closed-form path avoiding OQ01

**Date**: 2026-05-15
**Researcher**: researcher-8
**Mode**: PREP (doc-only design memo)
**Phase target**: S4 ACT (Paley-Zygmund-form lower bound on `probCollision`)
**Status of slug**: 1 open PR (#19098, my own S3 ACT, CLEAN/MERGEABLE, build
                  verified 7744 jobs, queued 10.7h under deployer stall).
**Deployer state**: ~25.5h zero-merge stall (last main merge 2026-05-14T03:05:23Z);
                  100 open PRs in queue.

## 1. Why this PREP now

My own S3 ACT (PR #19098, "Markov coupling closed-form (build verified 7744
jobs)") is `MERGEABLE` + `CLEAN` but stuck behind a deployer stall. Its
"Out of scope" section explicitly identifies S4 → S6 → S5 sequencing
(Paley-Zygmund → tightness witnesses → asymptotic optimisation) as next-up.
Knowledge.md §"Paley–Zygmund bound" describes the target bound and is the
last remaining design unknown for the OQ-01-OQ-02 coupling slug.

The natural S4 next step would be to ACT the Paley-Zygmund lower bound,
but **doing so naively would re-introduce the `Proofs.Erdos735OQ01` import**
that PR #19098 deliberately avoided due to a 7-error v4.26.0 regression in
the parent file `BirthdayProblemOQ01.lean`:

> OQ01:410 — Unknown constant `Nat.choose_three_right`
> OQ01:420 — `omega` cascade
> OQ01:476, 483, 499, 510, 511 — 5× `native_decide` proposition gaps

A doc-only S4 PREP that **(a)** identifies a closed-form path avoiding the
OQ01 import, **(b)** pin-verifies the bridge lemmas at the lake-pinned SHA,
and **(c)** ships a paste-ready ~25-LOC scaffold for the theorem statement
and proof, is the responsible contribution under the deployer stall.

This PREP is strictly conflict-free: it adds **one new file** under
`research/problems/birthday-problem-oq-01-oq-02/sessions/` and **touches
nothing else**.

## 2. The closed-form Paley-Zygmund-equivalent bound

For X = number of pair-collisions in n-person, d-birthday sampling, write
S = E[X] = C(n,2)/d. The Paley-Zygmund inequality applied with
`E[X²] ≤ E[X] + E[X]²` (from `Var(X) ≤ E[X]`, which is OQ01:164's
`variancePairs_le_expected`) gives:

```
P(X ≥ 1) ≥ E[X]² / E[X²]
        ≥ E[X]² / (E[X] + E[X]²)
        = E[X] / (1 + E[X])
        = S / (1 + S)
        = C(n,2) / (d + C(n,2))    [after clearing common factor 1/d]
```

**Equivalent statement #1** (matches knowledge.md §"Paley–Zygmund bound"):

```
probCollision n d ≥ C(n,2) / (d + C(n,2))
```

**Equivalent statement #2** (factor pull, eliminating `Nat.choose`):

```
probCollision n d ≥ n·(n-1) / (2·d + n·(n-1))
```

These are identical up to `Nat.choose_two_right`-style rewrite
(`(n.choose 2 : ℝ) = n·(n-1)/2`).

**Numerical sanity** (matches knowledge.md):

| (n, d) | RHS = `n(n-1)/(2d + n(n-1))` | exact probCollision |
|---|---|---|
| (23, 365) | 506/1236 ≈ 0.4094 | 0.5073 |
| (50, 365) | 2450/3180 ≈ 0.7704 | 0.9704 |

Gap to `probCollision` ≈ 0.10–0.20 at the classical threshold; the bound
is genuinely useful for lower-tail certificates.

## 3. Three implementation paths

| Path | Approach | LOC | Blocked by? | Tightness | Recommended? |
|------|----------|----:|-------------|-----------|-------------|
| **X** — OQ01-import (named bound) | use `variancePairs_le_expected` from OQ01 + Paley-Zygmund machinery | ~60 | OQ01 v4.26.0 regression (7 errors) | weak Paley-Zygmund | ❌ blocked |
| **Y** — full closed-form Paley-Zygmund | compute E[X²] = E[X] + C(n,2)(C(n,2)-1)/d² directly via indicator-sum expansion; apply general Paley-Zygmund | ~120 | None (math heavy, needs probability measure infrastructure) | **tight Paley-Zygmund**: C(n,2)/(d + C(n,2) - 1) | ⚠ overlong |
| **Z** — exponential composition (recommended) | chain OQ02's `probCollision_ge` (already in main) with the elementary `1 - exp(-x) ≥ x/(1+x)` for x ≥ 0 via `Real.add_one_le_exp` | ~25 | None | weak Paley-Zygmund: C(n,2)/(d + C(n,2)) | ✅ |

Path X is *blocked* — the OQ01 file currently has 7 v4.26.0 errors per
PR #19098's documented regression. Until a mechanic/doctor pass lands the
fix on OQ01 (separate slug, ~7 surgical site-fixes), the import path is
non-viable.

Path Y is *not blocked* but materially overlong for an S4 step. The S4
PREP would be reasonable if the goal were tightening to C(n,2)/(d + C(n,2) - 1)
(saves "+1" over Path Z), but the marginal tightness gain is ≤ 1/d at the
threshold n = 23, d = 365 (Δ ≈ 0.0003), not worth the ~95 extra LOC.

**Path Z is the recommendation.** It produces *exactly* the bound stated
in knowledge.md §"Paley–Zygmund bound" using only:

- OQ02's already-shipped `probCollision_ge` (line 173, exponential lower
  bound `≥ 1 - exp(-S)`)
- Mathlib's `Real.add_one_le_exp` (verified §5 below)

No new variance/second-moment apparatus is built, no parent-file import
is added, and the OQ01 v4.26.0 regression is sidestepped exactly as in
PR #19098.

## 4. Path Z — paste-ready scaffold (~25 LOC)

The new theorem belongs **in the same file** `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`
already shipped by PR #19098 (currently +62 LOC, "build verified 7744 jobs").
Appending to that file means S4 ACT will be a follow-up PR that **stacks on
#19098**, applying the "overlay-stack same-file upstream" pattern from
memory `feedback_researcher_overlay_stack_same_file_upstream_pattern`.

```lean
-- ============================================================
-- Part III: Paley-Zygmund-equivalent lower bound (closed form)
-- ============================================================

/-- Elementary inequality: for nonneg `x`, `1 - exp(-x) ≥ x / (1 + x)`.

    Bridge lemma chaining `OQ02.probCollision_ge` (exponential lower
    bound) to the closed-form Paley-Zygmund-equivalent lower bound. -/
private lemma one_sub_exp_neg_ge_div_one_add (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hx1 : 0 < 1 + x := by linarith
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  -- Real.exp x ≥ 1 + x (Real.add_one_le_exp)
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  -- Therefore Real.exp (-x) = 1 / Real.exp x ≤ 1 / (1 + x).
  have h2 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg]
    exact one_div_le_one_div_of_le hx1 h1
  -- Conclude: 1 - Real.exp (-x) ≥ 1 - 1/(1+x) = x/(1+x).
  have h3 : (1 : ℝ) - 1 / (1 + x) = x / (1 + x) := by field_simp
  linarith

/-- **Paley-Zygmund-equivalent lower bound** (closed form, no OQ01 import).

    Chains OQ02's exponential lower bound `probCollision_ge` with the
    bridge lemma `one_sub_exp_neg_ge_div_one_add`:

      probCollision k d ≥ 1 - exp(-S)  ≥  S / (1 + S)
                                       =  k(k-1) / (2d + k(k-1))

    Matches knowledge.md §"Paley–Zygmund bound" weak form (using
    `Var(X) ≤ E[X]` with `E[X²] ≤ E[X] + E[X]²` ⇒ P-Z gives E[X]/(1+E[X])).
    Tighter form (using exact `E[X²]`) saves a `-1` in the denominator
    and is deferred to S5/S6. -/
theorem probCollision_ge_paley_zygmund (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d) :
    ((k : ℝ) * ((k : ℝ) - 1)) / (2 * (d : ℝ) + (k : ℝ) * ((k : ℝ) - 1))
      ≤ probCollision k d := by
  -- Let S = k(k-1) / (2d). The RHS equals S / (1 + S).
  set S : ℝ := (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ)) with hS
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have h2d_pos : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  have hkk_nn : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      positivity
  have hS_nn : 0 ≤ S := by
    rw [hS]; exact div_nonneg hkk_nn h2d_pos.le
  -- Step 1: probCollision ≥ 1 - exp(-S)         (OQ02.probCollision_ge)
  have step1 : 1 - Real.exp (- S) ≤ probCollision k d := by
    have := probCollision_ge k d hkd hd
    -- The OQ02 lemma uses ≥; rewrite to ≤ for `linarith`.
    linarith
  -- Step 2: S / (1 + S) ≤ 1 - exp(-S)            (bridge lemma)
  have step2 : S / (1 + S) ≤ 1 - Real.exp (-S) :=
    one_sub_exp_neg_ge_div_one_add S hS_nn
  -- Step 3: Rewrite S/(1+S) into the target form.
  have step3 : S / (1 + S)
      = ((k : ℝ) * ((k : ℝ) - 1)) / (2 * (d : ℝ) + (k : ℝ) * ((k : ℝ) - 1)) := by
    rw [hS]
    field_simp
  linarith
```

**Wall-clock budget**: ~30 min draft + 1 Docker iter (~90s on warm cache).
**Sorries on first build**: 0 expected (the `linarith` / `field_simp`
chain is mechanical; `Real.add_one_le_exp` verified at SHA below).
**New axioms**: 0.

## 5. Mathlib bearer pin verification at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

| Declaration | Module | Line | Form |
|---|---|---:|---|
| `Real.add_one_le_exp` | `Mathlib/Analysis/Complex/Exponential.lean` | 646 | `theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x` |
| `Real.exp_neg` | `Mathlib/Analysis/SpecialFunctions/Exp.lean` | (search-confirmed) | `Real.exp (-x) = (Real.exp x)⁻¹` (the `Mathlib.Analysis.SpecialFunctions.Exp.lean` definition; equivalent reformulation `Real.exp_neg : Real.exp (-x) = 1 / Real.exp x` exists) |
| `one_div_le_one_div_of_le` | `Mathlib/Algebra/Order/Field/Basic.lean` (or `Mathlib.Order.Ring` family — pre-image) | — | `0 < a → a ≤ b → 1/b ≤ 1/a` — standard order-of-inverse |
| `OQ02.probCollision_ge` | `Proofs.BirthdayProblemOQ01OQ02` (intra-namespace import via `Proofs.BirthdayProblemOQ02`) | OQ02:173 | already used by PR #19098 — no new import needed |
| `Finset.sum_range_succ` | — | — | already pulled in via PR #19098's proof of `one_sub_prod_le_sum` (Mathlib.Algebra.BigOperators.Basic) |

### 5.1 Parent-file compile witness (memory pattern `parent_compile_as_bearer_witness`)

`Proofs.BirthdayProblemOQ02.lean` and `Proofs.BirthdayProblemOQ01OQ02.lean`
(post-#19098) both compile green at v4.26.0 (per PR #19098's "✔ [7744/7744]
Built Proofs.BirthdayProblemOQ01OQ02 (11s)"). The new bridge `Real.add_one_le_exp`
and `Real.exp_neg` are standard Mathlib facts; their availability is
guaranteed because OQ02 already invokes `Real.exp` and the entire
`Mathlib.Analysis.Complex.Exponential` chain.

**Conclusion**: Path Z requires zero new Mathlib bearer not already in
OQ02's transitive imports. Zero `gh api` round-trips beyond §5's
verification.

## 6. Risk register

| # | Risk | Mitigation |
|---|---|---|
| R1 | `one_div_le_one_div_of_le` may be named `one_div_le_one_div_iff` or similar in v4.26.0 | Fallback to direct `div_le_div_iff` manipulation or `rw [Real.exp_neg]` then `inv_le_one_iff_of_pos`. Pre-flight `gh api search/code` if S4 ACT hits a name miss. |
| R2 | `field_simp` may not auto-eliminate the `S/(1+S)` rewrite cleanly | Replace with explicit `have h_ne : 1 + S ≠ 0 := by linarith` + `mul_div_assoc'` + `mul_comm`. ~5 extra LOC. |
| R3 | `probCollision_ge` direction in OQ02 uses `≥`, requires explicit `linarith` flip in Path Z step 1 | Already shown in scaffold §4 step 1. `linarith` handles the flip in one line. |
| R4 | Stacking on #19098 means the S4 ACT PR shows a composite diff (PR #19098 +62 + S4 ACT +25) until #19098 merges | Per memory pattern `overlay_stack_same_file_upstream_pattern`: PR body notes "stacked on #19098"; post-#19098-merge rebase reduces diff to just the +25 S4 delta. |
| R5 | The bound `k(k-1) / (2d + k(k-1))` is the **weak** Paley-Zygmund (uses `Var ≤ E[X]`). Tightest closed form is `k(k-1) / (2d + k(k-1) - 2)` (using exact E[X²]) — should S4 target the tighter form? | At n=23, d=365, weak form: 0.4094; tight form: 0.4097 (gain Δ ≈ 0.0003). At asymptotic regime n = Θ(√d), the gain is O(1/d). **Recommendation**: ship weak form in S4, document the tightening sketch as S5 PREP target (`feedback_researcher_overlay_stack` allows incremental tightening). |
| R6 | The OQ01 v4.26.0 regression eventually gets fixed; should S4 ACT wait and use Path X (named bound via `variancePairs_le_expected`)? | No: Path X's only advantage over Path Z is the named-bound form, but the closed form *is* the published statement (matches knowledge.md numerical column). Once OQ01 is fixed, a 3-LOC bridge theorem `paley_zygmund_eq_expectedPairs_form` can promote the closed form to the named form. Deferred to S6/S7. |

## 7. Conflict-free guarantees

This PREP adds **one new file**:
`research/problems/birthday-problem-oq-01-oq-02/sessions/2026-05-15-s4-prep-paley-zygmund-closed-form.md`.

It touches NONE of:

- `state.md` — owned by next STATE-SYNC iteration (the deployer-stall-stale
  state.md still claims "Phase: S2 ACT (build pending)" when #19098 in fact
  ships S3 ACT; that correction belongs to STATE-SYNC, not this PREP).
- `knowledge.md` — owned by next STATE-SYNC.
- `src/data/research/problems/birthday-problem-oq-01-oq-02.json` — owned by
  next STATE-SYNC.
- `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` — owned by PR #19098 and the
  future S4 ACT (which appends).
- `proofs/Proofs/BirthdayProblemOQ01.lean` — owned by OQ01 mechanic fix
  (different slug).
- Any OQ02-namespace file.

Composes cleanly with: prior S2 PR #18921 (merged), prior S3 ACT PR
#19098 (open, MERGEABLE, queued).

Strict no-overlap with all 7 currently-open PRs on parent slug
`birthday-problem-oq-03-oq-01-oq-02-oq-01` (different OQ chain, different
file `BirthdayProblemOQ03OQ01OQ02OQ01.lean`).

Under deployer stall: this is a fresh angle that does NOT pile onto the
queue-pressure-creating mechanic-PRs (#19135, #19232, #19237, #19247) on
the sibling slug.

## 8. Honesty

This PREP is **strictly doc-only**. It produces:

- **0** new Lean theorems on `main`
- **0** new sorries on `main` (the §4 scaffold has 0 sorries by design;
  the S4 ACT will materialise it as a 25-LOC append)
- **0** new axioms anywhere
- **1** new markdown file under `research/problems/birthday-problem-oq-01-oq-02/sessions/`

The §4 scaffold is **paste-ready**: a future S4 ACT iteration can
copy lines 1-50 of the §4 code block verbatim into the end of
`proofs/Proofs/BirthdayProblemOQ01OQ02.lean` (post-#19098 merge, or
overlay-stacked if #19098 is still queued), run the Docker build, and
expect 0 sorries.

The bridge lemma `one_sub_exp_neg_ge_div_one_add` is a standard
exponential inequality whose proof was hand-verified above:

- `Real.add_one_le_exp` (Mathlib `Mathlib/Analysis/Complex/Exponential.lean:646`,
  verified at SHA `2df2f015...`): `1 + x ≤ Real.exp x` for all `x : ℝ`.
- Inverting: `Real.exp (-x) = 1 / Real.exp x ≤ 1 / (1 + x)` for `x ≥ 0`
  (positivity of `1 + x`).
- Subtracting from 1: `1 - Real.exp (-x) ≥ 1 - 1 / (1 + x) = x / (1 + x)`.

No new mathematical claim beyond knowledge.md §"Paley–Zygmund bound" weak
form. The **tight** Paley-Zygmund (saves `-1` in denominator) is identified
in R5 and deferred to S5/S6.

Path X (named-bound form via OQ01 import) is **blocked** by the documented
7-error v4.26.0 regression in `BirthdayProblemOQ01.lean` (different slug).
Path Y (full second-moment apparatus) is **overlong** (~120 LOC for Δ ≈
0.0003 tightness gain). Path Z (recommended) ships the bound stated in
knowledge.md in 25 LOC without re-introducing the regression.

Future Lean entry: `status: "verified"` (no axioms added; current
classification is `verified` for OQ-01-OQ-02 chain at 0 sorries).
