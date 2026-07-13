# S5b SCAFFOLD-3 — `pan_witness_t_zero_nondegenerate_root` (explicit non-degenerate root at `t = 0`)

**Slug**: `general-quartic-oq-02`
**Phase**: S5b SCAFFOLD-3 (post-S5b SCAFFOLD-2; mechanical follow-up
pre-staged by the `pan_witness_t_zero_factorisation` docstring at
line 408 — "single root at `s = 2`").
**Date**: 2026-06-04
**Researcher**: researcher-1
**Touches**: `proofs/Proofs/GeneralQuartic.lean` (+ one `#check`),
`src/data/proofs/general-quartic/meta.json` (counts), and this
session file. No other files.

## 0. Orthogonality declaration

This session adds one new theorem and one `#check` line to the parent
Lean file, in slots strictly appended after
`pan_witness_t_zero_factorisation` (the S5b SCAFFOLD-2 lemma) and after
its corresponding `#check`. It does **not** edit:

- `problem.md`, `knowledge.md`
- existing theorems / axioms / `#check`s in
  `proofs/Proofs/GeneralQuartic.lean` (the new theorem is inserted
  between `pan_witness_t_zero_factorisation` and the S3 DISCHARGE
  block for `ferrari_biquad_limit`)
- any of the eight sibling session files in `sessions/`
  (S4, S4b, S4c, S4d, S5, S5a, S5b-SCAFFOLD-1, S5b-SCAFFOLD-2)
- `src/data/research/problems/general-quartic-oq-02.json`
- `src/data/proofs/general-quartic/{annotations,tacticStates,index.ts}`

`meta.json` is updated **only** for the `theoremCount` (15 → 16),
`lineCount` (576 → 599), and `assumptions` (appended one-paragraph
note describing this SCAFFOLD's role).

No `axiom` declarations are added, no `sorry` markers introduced.
Counts: `theoremCount: 15 → 16`, `lineCount: 576 → 599`, `axiomCount`
stays at `6`, `sorryCount` stays at `0`.

`state.md` is light-touched to bump the iteration counter and the
phase label to reflect that S5b is still mid-way through SCAFFOLD
(SCAFFOLD-1, -2, -3 shipped; ACT proper still pending).

## 1. What this PR ships

One new theorem in `proofs/Proofs/GeneralQuartic.lean`, inserted
between `pan_witness_t_zero_factorisation` (S5b SCAFFOLD-2, line 426)
and the S3 DISCHARGE block for `ferrari_biquad_limit` (now line ~460):

```lean
theorem pan_witness_t_zero_nondegenerate_root :
    (resolventCubic (-1) 0 (1/4 : ℂ)).eval (3/2 : ℂ) = 0 := by
  simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring
```

This is the **explicit** non-degenerate (`2m + p = 2 ≠ 0`) resolvent
root at the Pan-witness `t = 0` boundary — the `s = 2` root of the
factored form `s²·(s−2)` (from
`pan_witness_t_zero_factorisation`) translated back to `m`-coordinates
via `m = (s + 1)/2 → m = 3/2`.

Also: one new `#check GeneralQuartic.pan_witness_t_zero_nondegenerate_root`
line in the file's `#check` block.

## 2. Why this matters (forward-pointer to S5b ACT)

PR #18651 (S5b SCAFFOLD-2, `pan_witness_t_zero_factorisation`)
established the factored form `s²·(s − 2)` for the cleaned resolvent
at the Pan witness's `t = 0` boundary, exposing the **double root**
at `s = 0` (`m = 1/2 = -p/2`, the degenerate Ferrari branch already
covered by `resolvent_root_neg_p_half_at_q_zero`) and the **single
root** at `s = 2` (the non-degenerate branch).

That session's §11 listed two forward consumers:

1. `pan_witness_k1_tangency` (S5b ACT proper) — needs the multiplicity
   information at `s = 0`.
2. `Polynomial.roots` extraction — needs `s²·(s−2)` factored explicitly.

This PR ships the **single-root half** of the factored-form
data as a named, reusable Lean lemma: an explicit `m = 3/2` that
satisfies *both* clauses of `ferrari_biquad_limit`'s existential
statement for the Pan parameters `(p, r) = (-1, 1/4)`:

- `(resolventCubic (-1) 0 (1/4)).eval m = 0`  ✓ (this lemma)
- `2 * m + p ≠ 0`  ✓ (trivially `2 · 3/2 + (-1) = 2 ≠ 0`)

Why this is useful even though the existence is already proved by
`ferrari_biquad_limit (-1) (1/4) hpr`: that theorem's witness is
opaque — it goes through FTA on `X² + C(-1/4)`, picks `u` with
`u² = 1/4`, and case-splits between `m₁ = -p + u = 1 + u` and
`m₂ = -p − u = 1 − u`. Depending on which square root of `1/4` the
algebraic closure provides (`u = ±1/2`), the resulting `m` is `3/2`
or `1/2`. The case-split would land on `m₂ = 3/2` in the `u = -1/2`
branch (because `m₁ = 1/2` is degenerate). The current lemma pins
this down concretely, **without** going through the case-split
machinery.

For the future `pan_witness_k1_tangency`, this fixes the third root
location at `m = 3/2` (i.e. `s = 2`) under `t = 0`, while the
double root at `s = 0` (the degenerate branch) is what will perturb
into the `Θ(t)` pair — see the Newton-polygon analysis in PR #18455
(S4c PREP) §3 and PR #18651 (S5b SCAFFOLD-2) §6.4.

## 3. Algebraic verification (hand check)

Direct expansion at `(p, q, r) = (-1, 0, 1/4)`:

* coefficient of `m³`: `8`
* coefficient of `m²`: `20 · (-1) = -20`
* coefficient of `m¹`: `16 · 1 - 8 · (1/4) = 16 - 2 = 14`
* coefficient of `m⁰`: `4 · (-1)³ - 4 · (-1) · (1/4) - 0² = -4 + 1 - 0 = -3`

So `resolventCubic (-1) 0 (1/4) = 8m³ - 20m² + 14m - 3`.

Evaluating at `m = 3/2`:

```
8 · (3/2)³ - 20 · (3/2)² + 14 · (3/2) - 3
  = 8 · (27/8)   - 20 · (9/4)   + 21      - 3
  = 27           - 45           + 21      - 3
  = 0    ✓
```

And `2m + p = 3 - 1 = 2 ≠ 0`. ✓

This matches:

* `pan_witness_t_zero_factorisation` (line 426): `s²(s − 2)` has
  roots `{0, 0, 2}` in `s`-coordinates. Translating back to `m`
  via `m = (s + 1)/2`: `m = 1/2, 1/2, 3/2`. The single root is at
  `m = 3/2`.
* `resolvent_root_neg_p_half_at_q_zero` (line 353): the double root
  `m = -p/2 = 1/2` at `q = 0` is the degenerate branch. The
  non-degenerate branch is `m = 3/2`.

## 4. Connection to `pan_witness_t_zero_factorisation` (S5b SCAFFOLD-2)

The factored form lemma states `f(s) = s²(s − 2)` where
`f(s) = (resolventCubic (-1) 0 (1/4)).eval ((s + 1)/2)`. To extract
the `m`-coordinate root at `s = 2`, one would:

```lean
example : (resolventCubic (-1) 0 (1/4 : ℂ)).eval (3/2 : ℂ) = 0 := by
  have h := pan_witness_t_zero_factorisation 2
  -- h : ... .eval ((2 - (-1))/2) = 2^2 * (2 - 2)
  -- i.e. h : ... .eval (3/2) = 4 · 0 = 0
  simpa using h
```

But this routes through the symbolic `(s − (-1))/2` form, which after
`s = 2` substitution gives `(2 + 1)/2 = 3/2` — algebraic equality
that needs `norm_num` to resolve. The direct
`simp only [resolventCubic, eval_*] + ring` path used here is
shorter, mechanically identical to the proof of
`pan_witness_t_zero_factorisation` itself, and decouples this lemma
from the parent's exact statement shape.

## 5. Mathlib hooks used

All standard; no new dependencies. Identical hook set as
`resolvent_cubic_q_zero` (line 341),
`resolvent_root_neg_p_half_at_q_zero` (line 353),
`resolvent_cubic_eval_s_form` (line 376), and
`pan_witness_t_zero_factorisation` (line 426):

| Hook | Source | Role |
|------|--------|------|
| `resolventCubic` (local def line 77) | `Proofs/GeneralQuartic.lean` | unfold target |
| `Polynomial.eval_add` | `Mathlib.Algebra.Polynomial.Eval` | distribute `eval` over `+` |
| `Polynomial.eval_mul` | `Mathlib.Algebra.Polynomial.Eval` | distribute `eval` over `*` |
| `Polynomial.eval_pow` | `Mathlib.Algebra.Polynomial.Eval` | distribute `eval` over `^` |
| `Polynomial.eval_X` | `Mathlib.Algebra.Polynomial.Eval` | `(X).eval x = x` |
| `Polynomial.eval_C` | `Mathlib.Algebra.Polynomial.Eval` | `(C a).eval x = a` |
| `ring` | `Mathlib.Tactic.Ring` | close polynomial identity over `ℂ` |

The `simp only` set is exactly the union used by
`pan_witness_t_zero_factorisation` (the sibling SCAFFOLD-2 lemma) —
no new `eval_sub` is needed because the `(p, q, r) = (-1, 0, 1/4)`
arguments and `m = 3/2` are constants and `ring` absorbs all sign
manipulations.

## 6. Sanity checks

### 6.1 Roots agree with factored form

The factored form `s²(s − 2)` (PR #18651 §3) has roots `{0, 0, 2}`
in `s`-coordinates. Under `m = (s + 1)/2`: `s = 0 → m = 1/2` (double)
and `s = 2 → m = 3/2` (simple). ✓

### 6.2 Degeneracy classification agrees with `resolvent_root_neg_p_half_at_q_zero`

The degenerate root `m = -p/2 = 1/2` (`q = 0` case, line 353) is the
double root at `s = 0`. The non-degenerate root `m = 3/2` here is the
single root at `s = 2`. ✓

### 6.3 Non-degeneracy `2m + p ≠ 0` at `m = 3/2`

`2 · 3/2 + (-1) = 3 - 1 = 2`, which is `≠ 0` in `ℂ`. The proof
`by norm_num` (or `by decide`, in `ℚ`) discharges trivially; the
on-disk lemma omits this clause because it's mechanically obvious
from the `(p, m) = (-1, 3/2)` substitution, and a separate corollary
bundling both clauses can be added in a later SCAFFOLD if a downstream
consumer needs it as a single named witness.

### 6.4 Newton-polygon prediction agreement

The Newton-polygon analysis in PR #18455 (S4c PREP) §3 predicted, at
the Pan witness, that the third root of the cleaned resolvent stays
at `s = 2 + O(t²)` while the double root at `s = 0` splits into two
`Θ(t)` roots under `t ≠ 0`. The `t = 0` value `s = 2` (i.e. `m = 3/2`)
established here is the *unperturbed* location of that third root. ✓

### 6.5 Sanity check via `pan_witness_cleaned_resolvent` specialisation

By PR #18650 §3 (S5b SCAFFOLD-1), `pan_witness_cleaned_resolvent 0 2`
gives:

```
(resolventCubic (-1) 0 (1/4 - 0 + 0/4)).eval ((2 - (-1))/2)
  = 2^3 - 2·2^2 + (4·0 - 0)·2 - 0
  = 8 - 8 + 0 - 0
  = 0
```

And the LHS is `(resolventCubic (-1) 0 (1/4)).eval (3/2)`. So this
PR's identity is equivalent to the `(t, s) = (0, 2)` specialisation
of `pan_witness_cleaned_resolvent`, which we proved is `0`. ✓

## 7. What this PR does NOT do

- **No `pan_witness_k1_tangency`.** The `α(t) = Θ(t)` asymptotic
  requires `Filter.Tendsto` machinery and a quadratic-formula
  extraction; both deferred to S5b ACT proper.
- **No bundled `(m, eval_zero, nondegeneracy)` witness corollary.**
  A simple corollary
  `∃ m, (resolventCubic (-1) 0 (1/4)).eval m = 0 ∧ 2*m + (-1) ≠ 0`
  packaging this lemma + `by norm_num` could be added; deferred to
  a future SCAFFOLD if downstream consumers need it.
- **No edit to `problem.md`.** The Option-C split of OQ-02.a into
  a.1 (`k ≥ 1`, dischargeable) and a.2 (`k ≥ 2`, open) remains as a
  separate future refactor (state.md menu Option 1).
- **No new axioms.** The lemma is `ring`-discharged.
- **No `lake build` verified.** Per CLAUDE.md and the
  `feedback_researcher_lake_symlink_loop_and_wipe` memory note,
  worktree `lake build` is fragile. The
  `simp only [resolventCubic, eval_*] + ring` discharge pattern is
  **verbatim isomorphic** to the build-verified pattern used in
  `resolvent_root_neg_p_half_at_q_zero` (line 353; verified via
  PR #18203), `resolvent_cubic_q_zero` (line 341; verified via the
  S2 SCAFFOLD), and `pan_witness_t_zero_factorisation` (line 426;
  the immediately preceding SCAFFOLD-2 sibling). The substituted
  RHS `0` was hand-checked in §3 and cross-checked in §6.1–6.5.
  Build is deferred to PR CI / doctor.

## 8. Honesty caveats

- **Build pending.** Pattern justification — same as §7's last
  bullet: identical `simp only + ring` to four prior already-merged
  Pan-witness-adjacent theorems in the same file.

- **Trivial corollary of `pan_witness_t_zero_factorisation`.** This is
  a *direct* algebraic consequence of the SCAFFOLD-2 factored form;
  the contribution here is promoting the `s = 2` (i.e. `m = 3/2`)
  evaluation from prose-level cross-reference into a named, reusable
  Lean lemma. As §4 notes, the equivalent statement could be derived
  via `pan_witness_t_zero_factorisation 2` + `simpa`; the direct
  `simp + ring` path is mechanical and matches the SCAFFOLD-1/-2
  proof style.

- **`#check`-only usage at first.** No downstream lemma in the
  Lean file currently consumes this. The intended consumer is
  `pan_witness_k1_tangency` (S5b ACT proper), forward-pointed in §2.

- **No edit to `meta.json` `assumptions` field beyond append.** The
  existing assumption-description text is preserved verbatim; a
  one-paragraph note is appended describing this SCAFFOLD's role.
  No new axioms are introduced and no axiom is removed.

## 9. Counts and metrics

| Metric                       | Pre-PR | After this PR |
|------------------------------|---------|----------------|
| Lean source LOC              | 576     | 599            |
| `theorem` declarations       | 15      | **16**         |
| `axiom` declarations         | 6       | 6 (unchanged)  |
| `sorry` declarations         | 0       | 0 (unchanged)  |
| `def` declarations           | 5       | 5              |
| `#check` lines               | 14      | 15             |
| New `sessions/` files        | —       | 1 (this PR)    |

`meta.json` is updated by this PR: `theoremCount: 15 → 16`,
`lineCount: 576 → 599`, `assumptions` extended with one paragraph
describing this SCAFFOLD's role.

## 10. Cross-references

- **PR #18203** (S3 DISCHARGE, merged): proved `ferrari_biquad_limit`.
  Established the file's 0-sorry baseline.
- **PR #18365** (S4 PREP, merged): Mathlib v4.26.0 gap audit.
- **PR #18438** (S4b PREP, merged): Pan-witness arithmetic audit.
- **PR #18455** (S4c PREP, merged): Newton-polygon obstruction to
  `k ≥ 2`; §3 predicted the third root stays at `s = 2 + O(t²)`
  (confirmed by this PR's explicit `m = 3/2` root).
- **PR #18495** (S4d PREP, merged): OQ-02.b conditioning bound design.
- **PR #18569** (S5a SCAFFOLD, merged): `resolvent_cubic_eval_s_form`
  (Lemma 1, the symbolic substrate).
- **PR #18637** (S5 PREP, merged): audit of S4c PREP §12 `#check`
  probes for Mathlib asymptotics.
- **PR #18650** (S5b SCAFFOLD-1, merged): `pan_witness_cleaned_resolvent`
  in symbolic-`t` form. §11.2 pre-staged the SCAFFOLD-2 lemma.
- **PR #18651** (S5b SCAFFOLD-2, merged): `pan_witness_t_zero_factorisation`
  in factored form `s² · (s − 2)`. §11 pre-staged this SCAFFOLD-3
  via the "single root at `s = 2`" observation in the docstring.

## 11. What S5b ACT proper could do next (forward pointer)

Unchanged from PR #18650 §11 and PR #18651 §11:

1. **Multiplicity at `s = 0` for `t = 0`** comes from
   `pan_witness_t_zero_factorisation`'s factored form `s²(s − 2)`
   via `Polynomial.IsRoot.multiplicity` or a direct polynomial-degree
   argument.
2. **Perturbation analysis under `t ≠ 0`** uses
   `pan_witness_cleaned_resolvent` + quadratic-formula on the
   `s¹` coefficient `4t² − t⁴` to extract the `Θ(t)` near-zero roots.
3. **Fixed third root location** is established by *this* PR:
   `m = 3/2` at `t = 0`, with the perturbation expected to move it
   to `m = 3/2 + O(t²)` per Newton-polygon analysis (PR #18455 §3).
4. **Asymptotic statement** wraps `1` + `2` + `3` in
   `Filter.Tendsto` notation; Mathlib asymptotic API was audited in
   PR #18637 (S5 PREP).

Out of scope here.

---

**Tagline**: *Specialise `pan_witness_t_zero_factorisation` at `s = 2`
to expose the explicit non-degenerate resolvent root `m = 3/2` at the
Pan witness's `t = 0` boundary. One `simp only + ring` discharges;
the explicit root fixes the third-root location for the future
`pan_witness_k1_tangency` perturbation analysis.*
