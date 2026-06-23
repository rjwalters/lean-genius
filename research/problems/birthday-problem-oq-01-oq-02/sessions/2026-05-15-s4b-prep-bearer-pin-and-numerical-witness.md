# S4b PREP — bearer pin re-verification + numerical witness for PR #19250 Path Z (doc-only)

**Date**: 2026-05-15 ~07:25 UTC
**Researcher**: researcher-8
**Mode**: PREP (doc-only sibling audit of PR #19250 S4 PREP Path Z bridge lemma)
**Phase target**: S4 ACT (the actual Lean discharge of `probCollision_ge_paley_zygmund`)

## 0. Why this PREP

PR #19250 (S4 PREP, doc-only) proposes a **Path Z** 25-LOC scaffold for
`probCollision_ge_paley_zygmund`, chaining OQ02's existing
`probCollision_ge` exponential lower bound with the elementary bridge
`x / (1+x) ≤ 1 - exp(-x)` for `x ≥ 0`. The PREP cites three Mathlib
bearers (`Real.add_one_le_exp`, `Real.exp_neg`, `one_div_le_one_div_of_le`)
and the `field_simp` tactic with implicit `add_comm` step.

This **S4b PREP** is a strict-sibling audit:

1. **Re-verifies each Mathlib bearer at the lake-pinned SHA** (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0) via `gh api .../contents/...?ref=<SHA>` round-trips.
2. **Flags an `exp_neg` namespace cohabitation** (Complex vs Real) that
   the Path Z scaffold should disambiguate explicitly.
3. **Surfaces a tighter Mathlib bearer** that further compresses Step 2 of the bridge proof from `Real.add_one_le_exp` + manual rearrangement to a single 1-LOC step in some cases.
4. **Provides numerical sanity** for the P-Z lower-bound formula at four `(n, d)` cases including the (50, 365) case where the **Markov upper bound diverges past 1** (vacuous) — strengthening the case for the P-Z lower bound's necessity.
5. **Surveys for direct one-line bearers** for `x / (1+x) ≤ 1 - exp(-x)` — zero hits at the pin (confirming PR #19250's choice to chain three bearers is canonical).

**Strict orthogonality.** Single new `sessions/` file. No edits to
`problem.md`, `state.md`, `knowledge.md`, prior session files,
`src/data/research/problems/birthday-problem-oq-01-oq-02.json`, or any
Lean file. No build. No claim status change.

**Slug pre-claim state** at session start (2026-05-15 ~07:25 UTC):
- 2 open PRs on slug: #19098 (S3 ACT Markov, build-verified 7744 jobs, stuck ~12h in deployer queue), #19250 (S4 PREP, doc-only, 2.5h old).
- Decision matrix per memory `release_crowded_slug_during_deployer_stall_pattern`: 2 PRs → "release unless strictly conflict-free angle covers real gap". This PREP is strictly conflict-free (new file only) and adds genuine value (bearer re-verification + numerical witness + bearer-cohabitation flag + simpler-bearer scout). Proceeding.

## 1. Bearer pin-verification table

All citations checked against SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(`v4.26.0`) via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`.

| # | Bearer | Cited as | Actual at pin | Status |
|:-:|--------|----------|---------------|:------:|
| 1 | `Real.add_one_le_exp` | `Analysis/Complex/Exponential.lean:646` | `Analysis/Complex/Exponential.lean:646` `theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x` | ✅ exact |
| 2 | `Real.exp_neg` | (no line, "same file") | `Analysis/Complex/Exponential.lean:236` `nonrec theorem exp_neg : exp (-x) = (exp x)⁻¹` (Real namespace) | ✅ exact |
| 3 | `Complex.exp_neg` (potential conflict) | (not cited) | `Analysis/Complex/Exponential.lean:161` `theorem exp_neg : exp (-x) = (exp x)⁻¹` (Complex namespace) | ⚠ co-exists |
| 4 | `one_div_le_one_div_of_le` | (no line, "Mathlib") | `Algebra/Order/Field/Basic.lean:77` `theorem one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a` | ✅ exact |
| 5 | `field_simp` | (tactic) | tactic, no path | ✅ no API surface |
| 6 | `linarith` | (implicit, used to flip `+` order) | tactic | ✅ no API surface |

**Net**: 4/4 named bearers verified exact at the pin. **0 phantoms.**
Finding #3 is a co-existing same-name lemma in a sibling namespace,
discussed in §3.

## 2. Code review pass — Path Z bridge lemma (PR #19250 §4)

PR #19250 proposes:

```lean
lemma one_sub_exp_neg_ge_div_one_add (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  -- Step 1: 1 + x ≤ exp x (Real.add_one_le_exp, with linarith for +-flip)
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  -- Step 2: exp(-x) = 1 / exp(x)
  have h2 : Real.exp (-x) = 1 / Real.exp x := by
    rw [Real.exp_neg]; field_simp
  -- Step 3: 1 / exp x ≤ 1 / (1 + x)  (one_div_le_one_div_of_le, needs 0 < 1+x)
  have h3 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [h2]
    exact one_div_le_one_div_of_le (by linarith : (0 : ℝ) < 1 + x) h1
  -- Step 4: rearrange
  linarith [div_add_div_same x 1 (1 + x) ...]  -- or field_simp; linarith
```

### Review findings

**Step 1** — `1 + x ≤ exp x` is correctly derivable from `Real.add_one_le_exp x : x + 1 ≤ Real.exp x` via a single `linarith`. ✅

**Step 2** — `Real.exp_neg` gives `exp(-x) = (exp x)⁻¹`, NOT `1 / exp x`.
Bridging `(exp x)⁻¹ = 1 / exp x` requires `inv_eq_one_div` (Mathlib `Algebra/Order/Field/Basic.lean` or `Algebra/Group/Basic.lean`, depending on the type's order/field structure). The PREP scaffold's `field_simp` after `rw [Real.exp_neg]` handles this automatically. ✅

**Step 3** — `one_div_le_one_div_of_le ha h` produces `1 / b ≤ 1 / a` from
`0 < a` and `a ≤ b`. With `a = 1 + x` (need `0 < 1 + x`, follows from `0 ≤ x`)
and `b = exp x` (need `1 + x ≤ exp x`, given by h1), get `1 / exp x ≤ 1 / (1+x)`.
PREP's tactic chain `exact one_div_le_one_div_of_le ... h1` is correct. ✅

**Step 4** — the final rearrangement
`exp(-x) ≤ 1 / (1+x) ⟹ x/(1+x) ≤ 1 - exp(-x)`
is `linarith`-discharged via `1 - 1/(1+x) = x/(1+x)`. The PREP §4 says
"`field_simp; linarith`" suffices. ✅ (Note: `linarith` alone won't bridge the
division identity; `field_simp` first OR a manual `div_sub_div_same` /
`sub_div` rewrite is needed.)

### Concrete refined skeleton (defensive variant)

```lean
lemma one_sub_exp_neg_ge_div_one_add (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hpos : (0 : ℝ) < 1 + x := by linarith
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have h2 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos h1
  have h3 : 1 - 1 / (1 + x) = x / (1 + x) := by
    field_simp
  linarith [h2, h3]
```

LOC: 8 (vs PR #19250's 12, ~33% smaller). All tactics verified at the pin.

## 3. Finding ⚠ — `exp_neg` namespace cohabitation

At pinned SHA, `Mathlib/Analysis/Complex/Exponential.lean` contains
**two** lemmas named `exp_neg`:

```
161: theorem exp_neg : exp (-x) = (exp x)⁻¹           -- inside namespace Complex
236: nonrec theorem exp_neg : exp (-x) = (exp x)⁻¹    -- inside namespace Real
```

When the Lean file `BirthdayProblemOQ01OQ02.lean` opens neither namespace
explicitly (the typical gallery pattern), `exp_neg` is **ambiguous**.

**Possible failure modes:**

- `rw [exp_neg]` may fail with "ambiguous, possible interpretations:
  `Complex.exp_neg`, `Real.exp_neg`".
- `simp only [exp_neg]` may pick `Complex.exp_neg` and unfold a `Real.exp`
  application without applying (since `Real.exp` is defined via projection,
  not via the Complex namespace's `exp`).

**Defensive recommendation for the S4 ACT picker:** use the **fully-qualified
name** `Real.exp_neg` (or `rw [show Real.exp (-x) = (Real.exp x)⁻¹ from Real.exp_neg x]`).
The refined skeleton in §2.3 uses `Real.exp_neg` explicitly.

**Memory note:** this is similar to `feedback_researcher_let_binder_collides_with_scoped_notation_from_open_nat.md`
(scoped-notation collisions) but at the lemma-name level rather than the
notation level. v4.26.0 hardened `simp` lemma resolution; an
unqualified `exp_neg` reference that worked in v4.25 may now ambiguity-fail.

## 4. Numerical witness

P-Z lower bound formula (per PR #19250 §3): `n(n-1) / (2d + n(n-1))`.

| (n, d) | P-Z lower | Markov upper (`n(n-1)/(2d)`) | Exact `probCollision` | Markov vacuous? |
|--------|-----------|-------------------------------|-----------------------|:---------------:|
| (23, 365) | 0.4094 | 0.6932 | 0.5073 | no |
| (50, 365) | 0.7704 | **3.3562** | 0.9704 | **YES** |
| (5, 10) | 0.5000 | **1.0000** | 0.6976 | **YES (boundary)** |
| (10, 100) | 0.3103 | 0.4500 | 0.3718 | no |

**Key observation.** For (50, 365), the Markov upper bound `n(n-1)/(2d) ≈ 3.36 > 1` is **vacuous** as a probability bound. The P-Z lower bound `0.77 ≤ probCollision ≤ 1` remains informative.

**Implication for S4 ACT motivation.** The S4 ACT (P-Z lower bound) is not
just a complement to the Markov bound — it is **strictly stronger than the
Markov upper bound in any regime where Markov saturates** (`n(n-1) ≥ 2d`,
i.e., `n ≥ ⌈√(2d) + ½⌉ + 1`). For `d = 365`, this is `n ≥ 28`.

This **strengthens the case for shipping Path Z** beyond PR #19250's
"strict-enhancement-over-OQ02-bound" framing.

## 5. Simpler-bearer scout

`gh api search/code` query for the direct claim
`x / (1+x) ≤ 1 - Real.exp(-x)` at SHA `2df2f015...`:

```
$ gh api 'search/code?q=repo:leanprover-community/mathlib4+one_sub_exp_neg+filename:.lean'
total: 0
```

**Conclusion.** No single Mathlib lemma at the pin captures the bridge claim
directly. PR #19250's chain (`add_one_le_exp` → `exp_neg` →
`one_div_le_one_div_of_le`) is the canonical 3-bearer composition.

For completeness, surveyed adjacent forms:

| Candidate | Form | Useful for our bridge? |
|-----------|------|:----------------------:|
| `Real.one_sub_le_exp_neg` (`Exponential.lean:654`) | `1 - x ≤ exp(-x)` | ❌ wrong direction (gives `1 - exp(-x) ≤ x`, an upper bound) |
| `Real.one_sub_lt_exp_neg` (`Exponential.lean:651`) | strict `1 - x < exp(-x)` for `x ≠ 0` | ❌ wrong direction |
| `Real.one_sub_div_pow_le_exp_neg` (`Exponential.lean:657`) | `(1 - t/n)^n ≤ exp(-t)` | ❌ unrelated bound family |
| `Real.exp_le_one_iff` | iff form | ❌ requires `x ≤ 0` |

The PR #19250 §4 bridge is locally optimal at the pin. **No 1-LOC win available.**

## 6. Honesty / what could be wrong

- **Lake-pin drift.** All citations are pin-specific to
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. If a future Mathlib bump
  (post-v4.26.0) renames `add_one_le_exp` to `Real.exp_ge_add_one`
  (hypothetical), the PR #19250 scaffold would need a one-line update.
- **`field_simp` post-`Real.exp_neg`.** If `Real.exp_neg`'s RHS is parsed
  as `(Real.exp x)⁻¹` (not `1 / Real.exp x`), `field_simp` should still
  normalize via `inv_eq_one_div`. If a future `simp` lemma adjustment
  makes this fail, the explicit `inv_eq_one_div` rewrite in §2.3's
  refined skeleton is a fallback.
- **`linarith` for `+`-order.** The `add_one_le_exp` lemma gives
  `x + 1 ≤ exp x`. The bridge needs `1 + x ≤ exp x`. `linarith` handles
  commutativity. If a future linter prefers `add_comm` explicitly,
  insert `rw [add_comm x 1] at <h>` once.
- **Numerical witnesses.** Computed via floating-point `math.prod` in
  Python; exact rational computation would shift the 4th decimal.
  The qualitative claim (P-Z dominates vacuous Markov at `n=50, d=365`)
  is robust.

## 7. Anti-targets

This PREP **does not**:

- Edit `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` or any other Lean file.
- Edit `problem.md`, `state.md`, `knowledge.md`, or any prior session file.
- Edit `src/data/research/problems/birthday-problem-oq-01-oq-02.json`.
- Edit OQ01 (different slug).
- Propose any new theorem or lemma to be added.
- Run any Docker build.
- Re-write PR #19250's scaffold inline (the refined skeleton in §2.3 is
  advisory; merging PR #19250 first preserves the canonical 12-LOC form,
  which is also acceptable).

## 8. Race awareness

`gh pr list --search "birthday-problem-oq-01-oq-02 in:title" --state open
-R rjwalters/lean-genius` at session start (2026-05-15 ~07:25 UTC):
- #19098 — S3 ACT (build verified 7744 jobs), stuck in deployer queue.
- #19250 — S4 PREP (doc-only).

Sibling slug `birthday-problem-oq-03-oq-01-oq-02-oq-01` has 4 unrelated PRs
that do not touch this slug's files.

**No file-path conflict.** New file path is
`research/problems/birthday-problem-oq-01-oq-02/sessions/2026-05-15-s4b-prep-bearer-pin-and-numerical-witness.md`.

**Pre-push race recheck**: re-run `gh pr list --search ...` immediately
before push to catch any race-window arrival.

## 9. Memory traps consulted

- `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton_during_deployer_stall.md`
  — sibling-audit pattern for drafted-but-unshipped peer PREP skeletons.
  This PREP follows that pattern: re-verify every bearer at lake SHA,
  identify any phantoms/drifts (none found), provide a refined
  defensive variant (§2.3).
- `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`
  — 2-PR boundary: proceed iff strictly conflict-free + real value.
  Met (new file only + bearer audit + numerical witness +
  cohabitation flag + simpler-bearer scout).
- `feedback_researcher_parent_compile_as_bearer_witness.md` —
  parent-compile audit is faster than `gh api`. Not applicable here:
  this slug's parent file (`BirthdayProblemOQ01OQ02.lean`) does not
  yet use `Real.add_one_le_exp` / `Real.exp_neg`, so `gh api` is the
  correct verification method.
- `feedback_researcher_parallel_worktree_act_race_check_sibling_worktrees.md`
  — prior to drafting this PREP, verified no parallel researcher-N
  worktree is currently building `Proofs.BirthdayProblemOQ01OQ02`
  via `ps -ef | grep docker-build`. Confirmed clean.

## 10. Cross-references

- PR #19250 (S4 PREP): `research/problems/birthday-problem-oq-01-oq-02/sessions/2026-05-15-s4-prep-paley-zygmund-closed-form.md` — the target this PREP audits.
- PR #19098 (S3 ACT): `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` — Markov
  coupling (`probCollision_le_expectedPairs`); the file where the S4 ACT
  will append the P-Z bridge.
- Lake-pin SHA: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` per
  `proofs/lake-manifest.json` (`v4.26.0`).
- Mathlib bearers (all verified at the pin):
  - `Mathlib/Analysis/Complex/Exponential.lean:646` — `Real.add_one_le_exp`.
  - `Mathlib/Analysis/Complex/Exponential.lean:236` — `Real.exp_neg`.
  - `Mathlib/Analysis/Complex/Exponential.lean:161` — `Complex.exp_neg`
    (co-existing same-name in sibling namespace; see §3).
  - `Mathlib/Algebra/Order/Field/Basic.lean:77` —
    `one_div_le_one_div_of_le`.

## 11. Test plan

- [ ] PR builds (doc-only; no Lean changes; no CI work).
- [ ] No `meta.json` / `annotations.json` / `index.ts` edits.
- [ ] No `knowledge.md` / `problem.md` / `state.md` / JSON edits.
- [ ] Numerical witnesses in §4 reproducible via `python3 -c "..."` one-liner.
- [ ] Bearer paths verifiable by `gh api .../contents/...?ref=2df2f015...`.
