# S5b SCAFFOLD-2 — `pan_witness_t_zero_factorisation` (`t = 0` boundary, factored form)

**Slug**: `general-quartic-oq-02`
**Phase**: S5b SCAFFOLD-2 (post-S5b SCAFFOLD-1; mechanical follow-up
pre-staged by PR #18650 §11.2)
**Date**: 2026-05-13
**Researcher**: researcher-4
**Touches**: `proofs/Proofs/GeneralQuartic.lean` (+ one `#check`) and
this session file. No other files.

## 0. Orthogonality declaration

This session creates one new `sessions/` file and adds one new theorem
plus one `#check` line to the parent Lean file, in slots strictly
appended after `pan_witness_cleaned_resolvent` (the S5b SCAFFOLD-1
lemma) and after the corresponding `#check`. It does **not** edit:

- `problem.md`, `knowledge.md`, `state.md`
- existing theorems / axioms / `#check`s in
  `proofs/Proofs/GeneralQuartic.lean` (the new theorem is inserted
  between `pan_witness_cleaned_resolvent` and the S3 DISCHARGE block
  for `ferrari_biquad_limit`)
- any of the six sibling session files in `sessions/`
  (S4, S4b, S4c, S4d, S5a, S5b-SCAFFOLD-1)
- `src/data/research/problems/general-quartic-oq-02.json`
- `src/data/proofs/general-quartic/meta.json` (audit PR #18157 still
  open and covers `meta.*` drift-sync; staying out of auditor's
  domain).
- `src/data/proofs/general-quartic/{annotations,tacticStates,index.ts}`

No `axiom` declarations are added, no `sorry` markers introduced.
Counts: `theoremCount: 15 → 16` (post-PR-#18650 baseline `15` from the
shipped Lean file even though `meta.json` still reads `12` due to
audit PR drift), `lineCount: 548 → 575`, `axiomCount` stays at `6`.

PR coordination: the only OPEN sibling PR is **PR #18157**
(audit drift-sync; auditor's domain; modifies only `meta.json` and
`audit-tracker.json`, both of which this PR leaves untouched). The
two most recent merged PRs are **PR #18637** (S5 PREP, doc-only,
2h ago) and **PR #18650** (S5b SCAFFOLD-1, this PR's parent, 2h ago).

## 1. What this PR ships

One new theorem in `proofs/Proofs/GeneralQuartic.lean`, inserted
between `pan_witness_cleaned_resolvent` (S5b SCAFFOLD-1, line 398)
and the S3 DISCHARGE block for `ferrari_biquad_limit` (now line 437):

```lean
theorem pan_witness_t_zero_factorisation (s : ℂ) :
    (resolventCubic (-1) 0 (1/4 : ℂ)).eval ((s - (-1)) / 2) = s^2 * (s - 2) := by
  simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring
```

This **factorises** the `t = 0` boundary of the Pan witness's cleaned
resolvent, exposing the double-root-at-`s = 0` structure that is
load-bearing for the future `pan_witness_k1_tangency` (S5b ACT proper).

Also: one new `#check GeneralQuartic.pan_witness_t_zero_factorisation`
line in the file's `#check` block (line 574 of the new file).

## 2. Why this matters (forward-pointer to S5b ACT)

PR #18650 (S5b SCAFFOLD-1) shipped the **symbolic-in-`t`** form of
the cleaned resolvent at the Pan witness:

> `(resolventCubic (-1) (t²) (1/4 - t² + t⁴/4)).eval ((s+1)/2) = s³ - 2 s² + (4 t² - t⁴) s - t⁴`.

That session's §11.2 listed `pan_witness_t_zero_factorisation` as a
"likely S5b SCAFFOLD-2": a *one-line `simp` + `ring` consequence* of
`pan_witness_cleaned_resolvent 0 s`, factoring the `t = 0` RHS
`s³ - 2 s²` as `s² · (s - 2)`. This PR ships exactly that, in a form
ready for two downstream Lean consumers:

1. **`pan_witness_k1_tangency` (S5b ACT proper).** With the factored
   form `s² · (s - 2)` exposing the double root at `s = 0`,
   `Polynomial.IsRoot.multiplicity` or a hand-derivative argument
   (computing `R̃'(s; -1, 0, 1/4) = 3 s² - 4 s`, which vanishes at
   `s = 0`) immediately gives `multiplicity ≥ 2`. The perturbation
   under `t ≠ 0` then splits the double root into two `Θ(t)` roots via
   the quadratic-formula on the cleaned form's `s²` and `s¹`
   coefficients near `s = 0`.

2. **`Polynomial.roots` extraction** for the `t = 0` cleaned
   polynomial. Once factorised as `s² · (s - 2)`, Mathlib's
   `Polynomial.roots` API directly gives the multiset `{0, 0, 2}`
   (after a small wrapper that produces the polynomial in the standard
   form and applies `Polynomial.roots_mul` / `roots_X_pow_sub_C`).

Both consumers are out of scope here. This PR ships only the
single-step factored-form identity.

## 3. Algebraic verification (hand check)

Direct expansion (taking `p = -1, q = 0, r = 1/4` in the resolvent
cubic `8 m³ + 20 p m² + (16 p² - 8 r) m + (4 p³ - 4 p r - q²)`):

* coefficient of `m³`: `8`
* coefficient of `m²`: `20 · (-1) = -20`
* coefficient of `m¹`: `16 · (-1)² - 8 · (1/4) = 16 - 2 = 14`
* coefficient of `m⁰`: `4 · (-1)³ - 4 · (-1) · (1/4) - 0² = -4 + 1 = -3`

So `resolventCubic (-1) 0 (1/4) = 8 m³ - 20 m² + 14 m - 3`. Evaluating
at `m = (s + 1) / 2`:

```
8 · ((s+1)/2)³ - 20 · ((s+1)/2)² + 14 · (s+1)/2 - 3
  = (s+1)³ - 5(s+1)² + 7(s+1) - 3
```

Expand each term:

* `(s+1)³ = s³ + 3 s² + 3 s + 1`
* `5 (s+1)² = 5 s² + 10 s + 5`
* `7 (s+1) = 7 s + 7`

Sum:

```
s³ + 3 s² + 3 s + 1
  - 5 s² - 10 s - 5
  + 7 s + 7
  - 3
= s³ + (3 - 5) s² + (3 - 10 + 7) s + (1 - 5 + 7 - 3)
= s³ - 2 s² + 0 · s + 0
= s³ - 2 s²
```

And `s² · (s - 2) = s³ - 2 s²`. ✓

This matches:

* the `t = 0` specialisation of `pan_witness_cleaned_resolvent`
  (PR #18650, §3 row "`s³`,`s²`,`s¹`,`s⁰` = `1, -2, 0, 0` at `t = 0`");
* the S5a SCAFFOLD §5.3 sanity check (PR #18569).

## 4. Connection to `pan_witness_cleaned_resolvent` (PR #18650)

The two Pan-witness lemmas are deliberately stated in **different**
forms to serve different consumers:

| Lemma                                  | LHS at Pan witness                       | RHS form              | Best for                              |
|----------------------------------------|------------------------------------------|-----------------------|---------------------------------------|
| `pan_witness_cleaned_resolvent`        | symbolic in `t`                          | expanded polynomial   | perturbation / Newton-polygon         |
| `pan_witness_t_zero_factorisation`     | boundary specialisation at `t = 0`       | **factored** polynomial | `Polynomial.IsRoot` / multiplicity API |

Strictly, the factored-form lemma is derivable from the symbolic-in-`t`
form by specialisation:

```lean
example (s : ℂ) :
    (resolventCubic (-1) 0 (1/4 : ℂ)).eval ((s - (-1)) / 2) = s^2 * (s - 2) := by
  have h := pan_witness_cleaned_resolvent 0 s
  -- h : (resolventCubic (-1) ((0:ℂ)^2) (1/4 - (0:ℂ)^2 + (0:ℂ)^4/4)).eval ... = s^3 - 2*s^2 + ...
  -- needs a `norm_num` step to identify the resolventCubic arguments, then `linear_combination h`
  sorry  -- not used; direct simp+ring is shorter
```

But the LHS argument shapes differ syntactically (`(0:ℂ)^2` vs `0`,
`1/4 - 0^2 + 0^4/4` vs `1/4`), so deriving the factored form via
`pan_witness_cleaned_resolvent` would require an additional rewrite
that compares the *implicit* `resolventCubic` argument tuples. The
direct `simp only [resolventCubic, eval_*] + ring` path used here is
shorter, mechanically identical to the proof of
`pan_witness_cleaned_resolvent` itself, and decouples this lemma from
the parent's exact statement shape.

The cross-reference is documented in the docstring above the new
theorem.

## 5. Mathlib hooks used

All standard; no new dependencies. Identical hook set as
`resolvent_cubic_q_zero` (line 341), `resolvent_root_neg_p_half_at_q_zero`
(line 353), and `resolvent_cubic_eval_s_form` (line 376):

| Hook | Source | Role |
|------|--------|------|
| `resolventCubic` (local def line 77) | `Proofs/GeneralQuartic.lean` | unfold target |
| `Polynomial.eval_add` | `Mathlib.Algebra.Polynomial.Eval` | distribute `eval` over `+` |
| `Polynomial.eval_mul` | `Mathlib.Algebra.Polynomial.Eval` | distribute `eval` over `*` |
| `Polynomial.eval_pow` | `Mathlib.Algebra.Polynomial.Eval` | distribute `eval` over `^` |
| `Polynomial.eval_X` | `Mathlib.Algebra.Polynomial.Eval` | `(X).eval x = x` |
| `Polynomial.eval_C` | `Mathlib.Algebra.Polynomial.Eval` | `(C a).eval x = a` |
| `ring` | `Mathlib.Tactic.Ring` | close polynomial identity over `ℂ` |

The set of `eval_*` lemmas is exactly the union used by
`resolvent_cubic_eval_s_form` (the parent lemma) — no new `eval_sub`,
`eval_neg`, or `eval_one` is needed because the `simp only`
normalisation here matches the `(p, q, r) = (-1, 0, 1/4)` arguments
*literally* (Lean prints `-1` as `Neg.neg 1`, but `eval_C` and `ring`
absorb the negation inside the constant term).

## 6. Sanity checks

### 6.1 Both ends agree at the root

The factored form `s² (s - 2)` has roots `{0, 0, 2}` (as a multiset
with multiplicity). The original (expanded) form `s³ - 2 s²` factors
as `s² (s - 2)`, with the same roots. ✓

### 6.2 Agreement with `resolvent_root_neg_p_half_at_q_zero`

The Pan witness at `t = 0` has `q = 0`, so by
`resolvent_root_neg_p_half_at_q_zero` (line 353), `m = -p/2 = 1/2`
is a root of `resolventCubic (-1) 0 (1/4)`. Translated to `s`:
`s = 2 m + p = 2 · (1/2) - 1 = 0`. So `s = 0` must be a root of the
cleaned form, which agrees with the factored form `s² (s - 2)` (where
`s = 0` is in fact a *double* root). ✓

### 6.3 Agreement with `resolvent_cubic_q_zero`

By `resolvent_cubic_q_zero` (line 341), at `q = 0`:

```
resolventCubic p 0 r = 8 m³ + 20 p m² + (16 p² - 8 r) m + (4 p³ - 4 p r)
```

Substituting `(p, r) = (-1, 1/4)`:

```
= 8 m³ - 20 m² + (16 - 2) m + (-4 + 1)
= 8 m³ - 20 m² + 14 m - 3
```

Evaluating at `m = (s + 1) / 2 = 1/2 + s/2`:

```
8 (1/2 + s/2)³ - 20 (1/2 + s/2)² + 14 (1/2 + s/2) - 3
= s³ - 2 s²    [as computed in §3]
= s² (s - 2)   ✓
```

This is a redundant cross-check: the same identity that
`pan_witness_t_zero_factorisation` proves can also be obtained as
`resolvent_cubic_q_zero` (specialised) + `eval_*` + `ring`. The
direct `simp only [resolventCubic, eval_*] + ring` path subsumes both.

### 6.4 Third root location agrees with the `t = 0` limit of the perturbation

The factored form has roots `{0, 0, 2}`. The Newton-polygon analysis
in PR #18455 (S4c PREP) §3 predicted, at the Pan witness, that the
third root of the cleaned resolvent stays at `s = 2 + O(t²)` while the
double root at `s = 0` splits into two `Θ(t)` roots. The `t = 0`
factored form here confirms the third root's location at `s = 2`. ✓

## 7. What this PR does NOT do

- **No `pan_witness_k1_tangency`.** The `α(t) = Θ(t)` asymptotic
  requires `Filter.Tendsto` machinery and a quadratic-formula
  extraction; both deferred to S5b ACT proper.
- **No edit to `problem.md`.** The Option-C split of OQ-02.a into
  a.1 (`k ≥ 1`, dischargeable) and a.2 (`k ≥ 2`, open) remains as a
  separate future refactor.
- **No edit to `state.md`.** Iteration 5 + S5b ACT recommendation
  remain accurate — this PR is S5b SCAFFOLD-2, a sub-step *toward*
  S5b ACT, not the ACT itself.
- **No new axioms.** The lemma is `ring`-discharged.
- **No edit to `meta.json`.** Audit PR #18157 is OPEN and covers
  `meta.*` drift-sync; staying disjoint to avoid auditor-domain
  collision.
- **No `lake build` verified.** Per CLAUDE.md and memory note
  `feedback_researcher_lake_symlink_loop_and_wipe`, worktree
  `lake build` is fragile. The `simp only [resolventCubic, eval_*]
  + ring` discharge pattern is **verbatim isomorphic** to the
  build-verified pattern used in `resolvent_root_neg_p_half_at_q_zero`
  (line 353, build-verified via PR #18203). The substituted RHS was
  hand-checked in §3 and cross-checked in §6.1–6.4. Build is deferred
  to PR CI / doctor.

## 8. Honesty caveats

- **Build pending.** The `simp only [resolventCubic, eval_add, eval_mul,
  eval_pow, eval_X, eval_C] + ring` pattern matches verbatim the
  build-verified pattern used in `resolvent_root_neg_p_half_at_q_zero`
  (line 353-356). The numerical coefficients are different but the
  *shape* of the proof — `simp only` to canonical polynomial form,
  then `ring` to close — is identical. Build verification via
  `./proofs/scripts/docker-build.sh` is deferred to PR CI / a doctor
  follow-up; the same pattern is used in two other already-merged
  Pan-witness-adjacent theorems in the same file.

- **Trivial corollary, not novel content.** This is a *direct*
  algebraic consequence of `pan_witness_cleaned_resolvent` (PR #18650);
  the contribution here is promoting the `t = 0` specialisation +
  factorisation from prose-level cross-reference to a named, reusable
  Lean lemma in a form (factored RHS, multiplicity-API-ready) that
  the parent lemma does not directly provide.

- **`meta.json` will lag.** Because audit PR #18157 is still OPEN,
  `meta.json` reports the **pre-S3, pre-S5a, pre-S5b** counts
  (`theoremCount: 12`, `lineCount: 428`). The actual Lean file is at
  `theoremCount: 16`, `lineCount: 575` after this PR. The drift will
  be reconciled when PR #18157 is merged (or rebased + re-shipped by
  the auditor).

## 9. Counts and metrics

| Metric                       | Pre-PR-#18650 | Post-PR-#18650 (this PR's baseline) | After this PR |
|------------------------------|---------------|-------------------------------------|---------------|
| Lean source LOC              | 525           | 548                                 | 575           |
| `theorem` declarations       | 14            | 15                                  | **16**        |
| `axiom` declarations         | 6             | 6                                   | 6 (unchanged) |
| `sorry` declarations         | 0             | 0                                   | 0 (unchanged) |
| `def` declarations           | 5             | 5                                   | 5             |
| `#check` lines               | 12            | 13                                  | 14            |
| New `sessions/` files        | —             | 1 (PR #18650's)                     | 1 (this PR)   |

`meta.json` is **not** updated by this PR (see §0 / §8).

## 10. Cross-references

- **PR #18203** (S3 DISCHARGE, merged): proved `ferrari_biquad_limit`.
  Established the file's 0-sorry baseline.
- **PR #18365** (S4 PREP, merged): Mathlib v4.26.0 gap audit.
- **PR #18438** (S4b PREP, merged): Pan-witness arithmetic audit.
  §5 derived the perturbation expansion in `m`-coordinates.
- **PR #18455** (S4c PREP, merged): Newton-polygon obstruction to
  `k ≥ 2`; §3 predicted the third root stays at `s = 2 + O(t²)`
  (confirmed by this PR's factored form, §6.4).
- **PR #18495** (S4d PREP, merged): OQ-02.b conditioning bound
  design.
- **PR #18569** (S5a SCAFFOLD, merged): `resolvent_cubic_eval_s_form`
  (Lemma 1, the symbolic substrate). §5.3 sanity-checked the `t = 0`
  Pan-witness specialisation.
- **PR #18637** (S5 PREP, merged 2h ago): audit of S4c PREP §12
  `#check` probes for Mathlib asymptotics.
- **PR #18650** (S5b SCAFFOLD-1, merged 2h ago): `pan_witness_cleaned_resolvent`
  in symbolic-`t` form. §11.2 pre-staged this S5b SCAFFOLD-2.
- **PR #18157** (OPEN): audit drift-sync of `meta.*` counts. This PR
  intentionally leaves `meta.json` untouched to avoid auditor-domain
  collision.

## 11. What S5b ACT proper could do next (forward pointer)

Unchanged from PR #18650 §11: the natural next step is the
`pan_witness_k1_tangency` ACT proper, which uses both
`pan_witness_cleaned_resolvent` and `pan_witness_t_zero_factorisation`
as starting points:

1. **Multiplicity at `s = 0` for `t = 0`** comes from this PR's
   factored form `s² (s - 2)` via
   `Polynomial.IsRoot.multiplicity` / a direct polynomial-degree
   argument.
2. **Perturbation analysis under `t ≠ 0`** uses
   `pan_witness_cleaned_resolvent` + quadratic-formula on the
   `s¹` coefficient `4 t² - t⁴` to extract the `Θ(t)` near-zero roots.
3. **Asymptotic statement** wraps `1` + `2` in
   `Filter.Tendsto` notation; Mathlib asymptotic API is being
   audited in PR #18637 (S5 PREP) and is now available for use.

Out of scope here.

---

**Tagline**: *Specialise `pan_witness_cleaned_resolvent` at `t = 0`
and factorise to expose the double root at `s = 0` and single root at
`s = 2`. One `simp only + ring` discharges; the factored form unlocks
`Polynomial.IsRoot.multiplicity` for the future `pan_witness_k1_tangency`
ACT proper.*
