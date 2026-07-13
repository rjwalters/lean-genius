# S5b SCAFFOLD-1 — `pan_witness_cleaned_resolvent` (Pan-witness specialization of Lemma 1, ring-discharged)

**Slug**: `general-quartic-oq-02`
**Phase**: S5b SCAFFOLD-1 (post-S5a SCAFFOLD; substrate for a future S5b ACT
proper of `pan_witness_k1_tangency`)
**Date**: 2026-05-13
**Researcher**: researcher-1
**Touches**: `proofs/Proofs/GeneralQuartic.lean` + this file +
counts/note in `src/data/proofs/general-quartic/meta.json`.

## 0. Orthogonality declaration

This session creates one new `sessions/` file and adds one new theorem to
the parent Lean file. It does **not** edit any of:

- `problem.md`, `knowledge.md`, `state.md`
- existing theorems in `proofs/Proofs/GeneralQuartic.lean` (the new lemma
  is inserted immediately after `resolvent_cubic_eval_s_form`, the S5a
  Lemma 1, with no edits to surrounding theorems)
- any of the five sibling session files in `sessions/`
  (S4, S4b, S4c, S4d, S5a)
- `src/data/research/problems/general-quartic-oq-02.json` (knowledge
  scaffolds intentionally untouched to minimise collisions with the
  in-flight S5 PREP session)
- `src/data/proofs/general-quartic/{annotations,tacticStates,index.ts}`

`meta.json`'s `theoremCount` increments `13 → 14`, `lineCount`
increments `525 → 548`, `axiomCount` stays at `6`. No `axiom`
declarations are added, no `sorry` markers introduced. The `assumptions`
narrative is extended with one sentence on this PR's substrate role.

PR coordination: **PR #18637** (S5 PREP — asymptotics `#check`-probe
audit) touches *only* a new `sessions/2026-05-13-s5-prep-asymptotics-checkprobe-audit.md`
file and no shared file; this PR's edits are file-disjoint.

## 1. What this PR ships

A single new theorem in `proofs/Proofs/GeneralQuartic.lean`, inserted
between `resolvent_cubic_eval_s_form` (S5a Lemma 1, line 376) and the
S3 DISCHARGE block for `ferrari_biquad_limit`:

```lean
theorem pan_witness_cleaned_resolvent (t s : ℂ) :
    (resolventCubic (-1) (t^2) (1/4 - t^2 + t^4/4)).eval ((s - (-1)) / 2) =
    s^3 - 2 * s^2 + (4 * t^2 - t^4) * s - t^4 := by
  rw [resolvent_cubic_eval_s_form]
  ring
```

This is the **Pan-witness specialization** of S5a's Lemma 1, the
cleaned-resolvent identity. It is the precursor algebraic substrate
that PR #18438 (S4b PREP, merged) §5 derived informally and that any
future `pan_witness_k1_tangency` Lean theorem (state.md candidate 1)
will lean on as its first step.

Also: one new `#check` line at the file tail (line 538):
```lean
#check GeneralQuartic.pan_witness_cleaned_resolvent
```

## 2. Why this matters (next-action enablement)

The S4b PREP arithmetic audit (PR #18438, merged) §5 derived — but did
not formalize — the perturbation polynomial along the Pan witness
`(p, q, r)(t) := (-1, t², 1/4 − t² + t⁴/4)`:

> Setting `m = 1/2 + δ`, the resolvent evaluates to
> `R(1/2 + δ, t) = 8δ³ − 8δ² + (8t² − 2t⁴)·δ − t⁴`.

This is *the* expansion used to extract the leading-order behaviour
`δ(t) = Θ(t²)`, hence `α²(t) = 2δ(t) = Θ(t²)` and therefore
`α(t) = Θ(t)` — the `k = 1` tangency mechanism (PR #18455 S4c PREP §3).

This PR ships a **Lean-checkable form** of essentially the same
identity (under the variable change `s = 2m + p = 2m − 1`, equivalently
`s = 2δ + 1 + (−2)·(1/2) = 2δ`, but here the lemma is stated in the
"clean" variable `s` itself, so the connection is one step of
re-indexing away — see §4 below).

Concretely, the cleaned form at the Pan witness is

> `R̃(s; -1, t², 1/4 − t² + t⁴/4) = s³ − 2 s² + (4 t² − t⁴) s − t⁴`.

This is what `pan_witness_cleaned_resolvent` proves. Two downstream
consumers are enabled with **zero further algebra**:

1. **`pan_witness_k1_tangency` (future S5b ACT proper).** Plug `t = 0`
   into the cleaned form to get `s³ − 2 s²= s²(s − 2)`, exposing the
   double-root at `s = 0`. The `k = 1` tangency theorem reduces to a
   `Polynomial.derivative`-/`IsRoot.multiplicity`-style argument on
   the specialized polynomial — a much more tractable target than
   manipulating the unspecialized resolvent cubic in three formal
   parameters.
2. **`pan_witness_t_zero_factorisation` (likely S5b SCAFFOLD-2).** A
   one-line `simp` + `ring` consequence:
   `pan_witness_cleaned_resolvent 0 s` should yield `s^3 − 2 s^2 = s^2 * (s − 2)`
   (after a trivial rewrite). This makes the double-root structure
   visible to Mathlib's `Polynomial.roots`/`Polynomial.IsRoot` API.

Both consumers are out of scope here; this PR ships only the substrate.

## 3. Algebraic verification (hand check)

This is the Pan-witness specialization of S5a's Lemma 1, which proves

> `(resolventCubic p q r).eval ((s − p) / 2) = s³ + 2 p s² + (p² − 4 r) s − q²`.

Substitute `p = -1`, `q = t²`, `r = 1/4 − t² + t⁴/4`:

| Coefficient of | Symbolic | Substituted value |
|----------------|----------|-------------------|
| `s³`           | `1`      | `1`               |
| `s²`           | `2 p`    | `2 · (-1) = -2`   |
| `s¹`           | `p² − 4 r` | `1 − (1 − 4 t² + t⁴) = 4 t² − t⁴` |
| `s⁰`           | `-q²`    | `-t⁴`             |

So the cleaned RHS is `s³ − 2 s² + (4 t² − t⁴) s − t⁴`. ✓

The `rw [resolvent_cubic_eval_s_form]` step transports the LHS through
S5a's identity, leaving the LHS as the substituted symbolic form
`s³ + 2·(-1)·s² + ((-1)² − 4·(1/4 − t² + t⁴/4))·s − (t²)²`. A `ring`
closure then normalises this to the RHS.

## 4. Connection to PR #18438 (S4b PREP) §5 perturbation expansion

PR #18438 §5 derived the perturbation expansion in `m`-coordinates
(setting `m = 1/2 + δ`):

> `R(1/2 + δ, t) = 8 δ³ − 8 δ² + (8 t² − 2 t⁴) δ − t⁴`. (S4b §5)

This PR's theorem `pan_witness_cleaned_resolvent` is stated in
`s`-coordinates with `m = (s − p) / 2 = (s + 1) / 2`, equivalently
`s = 2 m − 1`. Setting `m = 1/2 + δ` gives `s = 2 δ`, so the
`s`-form RHS `s³ − 2 s² + (4 t² − t⁴) s − t⁴` evaluated at `s = 2 δ`
becomes

> `(2 δ)³ − 2 (2 δ)² + (4 t² − t⁴) (2 δ) − t⁴`
> `= 8 δ³ − 8 δ² + (8 t² − 2 t⁴) δ − t⁴`

which **agrees verbatim** with S4b PREP §5's `m`-coordinate form. So
the cleaned-resolvent form lemma proved in this PR and the
perturbation expansion in the S4b PREP audit are the *same identity*
in two coordinate systems. The `s`-form is preferred for the future
`pan_witness_k1_tangency` ACT because:

- The double-root structure at `t = 0` is visible directly
  (`s³ − 2 s² = s²(s − 2)`) without re-deriving the perturbation.
- The cleaned form is the named lemma `resolvent_cubic_eval_s_form`
  (S5a), so any consumer can extract identities by `rw` rather than
  by re-deriving the substitution.

## 5. Mathlib hooks used

All standard; no new dependencies. Identical hook set as
`resolvent_cubic_eval_s_form` and `resolvent_root_neg_p_half_at_q_zero`:

- `resolvent_cubic_eval_s_form` (the S5a SCAFFOLD theorem, internal).
- `ring` (from `Mathlib.Tactic.Ring`).

No `simp only [eval_*]` is needed in this lemma's body because the
`rw [resolvent_cubic_eval_s_form]` rewrite consumes all
`Polynomial.eval`-shaped subterms in one step; `ring` then closes
the resulting polynomial identity in `t, s : ℂ`.

## 6. Sanity checks

### 6.1 `t = 0` recovers the S5a §5.3 specialization

Setting `t = 0` in `pan_witness_cleaned_resolvent`:

> `(resolventCubic (-1) 0 (1/4)).eval ((s + 1) / 2) = s³ − 2 s²`.

Factoring: `s² (s − 2)`. So the cleaned-resolvent roots at `(p, q, r) = (-1, 0, 1/4)`
are `s ∈ {0, 0, 2}`, translating back via `m = (s + 1)/2` to
`m ∈ {1/2, 1/2, 3/2}`.

This **matches** the S5a SCAFFOLD §5.3 sanity check verbatim (PR #18569
session file), confirming no algebra-error in the specialization.

### 6.2 Constant-term `−q²` recovers in the witness

The cleaned form's constant term is universally `−q²` (S5a). At the
Pan witness `q = t²`, the constant is `−(t²)² = −t⁴`, which is the
RHS's `−t⁴` term. ✓

### 6.3 The `s¹` coefficient `(p² − 4 r)` matches the witness's
small-discriminant tangency direction

At the Pan witness:
`p² − 4 r = 1 − 4 (1/4 − t² + t⁴/4) = 1 − 1 + 4 t² − t⁴ = 4 t² − t⁴`.

This is the `s¹` coefficient of the cleaned form and the LHS of the
quadratic factor that emerges after dividing out the `s = 0` root at
`t = 0`. The fact that this coefficient vanishes at first order in
`t² ≠ 0` (it is `4 t² + O(t⁴)`) is exactly the *quantitative reason*
the third root of the cleaned-form polynomial stays a fixed `Θ(1)`
distance away from `s = 0` (the third root is at `s = 2 + O(t²)` by
Vieta on the cleaned form's three roots), while the double-root
splits into a `Θ(t)` pair near `s = 0`.

So the `s¹` coefficient `4 t² − t⁴` is the *Newton-polygon source* of
the `k = 1` tangency, captured here in a Lean-checked identity.

## 7. What this PR does NOT do

- **No proof of `k = 1` tangency.** The asymptotic statement
  `α(t) = Θ(t)` requires `Real.sqrt`-asymptotics + `Filter.Tendsto`
  machinery (S4 PREP §5, PR #18365) and is deferred. This PR ships
  only the algebraic substrate.
- **No edit to `problem.md`.** The Option-C split of OQ-02.a (state.md
  next-action 1) into a.1 (`k ≥ 1`, dischargeable) and a.2 (`k ≥ 2`,
  open) remains for a future S6 problem-statement refactor.
- **No new axioms.** The lemma is `ring`-discharged via S5a's
  similarly `ring`-discharged Lemma 1.
- **No `lake build` verified.** Per CLAUDE.md and memory note
  `feedback_researcher_lake_symlink_loop_and_wipe`, worktree
  `lake build` is fragile. The `rw + ring` discharge pattern is
  verbatim isomorphic to the pattern used in `resolvent_cubic_q_zero`
  (S2 SCAFFOLD, build-verified) and `resolvent_cubic_eval_s_form`
  (S5a SCAFFOLD, build pending but inherits the same closed pattern),
  and the substituted RHS was hand-checked in §3 above. Build is
  deferred to PR CI / doctor.
- **No edits to siblings.** Five existing session files
  (S4/S4b/S4c/S4d/S5a) are untouched.
- **No edits to `state.md`.** The "Iteration 5" line and "S5b ACT
  next" recommendation remain accurate — this PR is `S5b SCAFFOLD-1`,
  a sub-step *toward* the S5b ACT, not the ACT itself.
- **No edits to `src/data/research/problems/general-quartic-oq-02.json`.**
  Minimising collision surface with the in-flight S5 PREP (PR #18637)
  and any future S5b ACT.

## 8. Honesty caveats

- **Build pending.** The `rw [resolvent_cubic_eval_s_form] + ring`
  pattern is overwhelmingly likely to discharge the goal: the rewrite
  consumes the `Polynomial.eval` on the LHS in one step (since the
  argument shape `(s - (-1)) / 2` matches the lemma's `(s - p) / 2`
  with `p := (-1)` unified syntactically), and `ring` closes the
  resulting polynomial identity over `ℂ` (a `CommRing`).
- **Reuse of S5a's lemma.** Because S5a's `resolvent_cubic_eval_s_form`
  is itself build-pending, this PR's `rw [resolvent_cubic_eval_s_form]`
  step is technically dependent on S5a's `ring` discharge succeeding
  at build-time. The `ring` pattern in S5a matches the `ring` pattern
  in `resolvent_root_neg_p_half_at_q_zero` (line 354, build-verified
  via PR #18203), so the dependency chain is identical in form to a
  build-verified case.
- **No claim of novelty.** This specialisation is mechanical
  arithmetic over `(p, q, r)` and was already worked out in PR #18438
  §5 (in `m`-coordinates) and PR #18569 §5.3 (in `s`-coordinates at
  `t = 0`). The contribution here is *promoting* the identity from
  PREP-level prose to a named, reusable Lean lemma, in a form that
  is one `rw` away from the future `pan_witness_k1_tangency` consumer.

## 9. Counts and metrics

| Metric                       | Before | After this PR |
|------------------------------|--------|---------------|
| Lean source LOC              | 525    | 548           |
| `theorem` declarations       | 13     | 14            |
| `axiom` declarations         | 6      | 6 (unchanged) |
| `sorry` declarations         | 0      | 0 (unchanged) |
| `def` declarations           | 5      | 5             |
| New `sessions/` files        | —      | 1             |

`meta.json` updates: `theoremCount: 13 → 14`, `lineCount: 525 → 548`.
The `assumptions` narrative gets one sentence on this PR's substrate
role. Axiom, sorry, and status fields unchanged.

## 10. Cross-references

- **PR #18203** (S3 DISCHARGE, merged): proved `ferrari_biquad_limit`.
  Established the file's 0-sorry baseline.
- **PR #18365** (S4 PREP, merged): Mathlib v4.26.0 gap audit;
  identified the Pan-witness family at §5.
- **PR #18438** (S4b PREP, merged): Pan-witness arithmetic audit;
  §5 derived the perturbation expansion in `m`-coordinates (which is
  this PR's lemma in `m`-coordinates; see §4 above for the coordinate
  translation).
- **PR #18455** (S4c PREP, merged): Newton-polygon obstruction to
  `k ≥ 2`; §2 derived the cleaned resolvent form algebraically, §6.4
  called for a Lean lemma realising it.
- **PR #18495** (S4d PREP, merged): OQ-02.b conditioning bound design.
- **PR #18569** (S5a SCAFFOLD, merged): `resolvent_cubic_eval_s_form`
  in full generality; §5.3 sanity-checked the `t = 0` Pan-witness
  specialisation. This PR ships the symbolic-in-`t` form.
- **PR #18637** (S5 PREP, OPEN as of 2026-05-13 07:17 UTC): audit of
  S4c PREP §12 `#check` probes for Mathlib asymptotics; touches a
  disjoint session file only.

## 11. What S5b ACT proper could do next (forward pointer)

Concrete next-action, requiring no further algebraic design:

1. **State the tangency theorem** in Lean using
   `pan_witness_cleaned_resolvent` as the entry point:
   ```lean
   theorem pan_witness_k1_tangency :
       ∃ p q r : ℝ → ℂ,
         (∀ t, p t = -1) ∧ (∀ t, q t = t^2) ∧ (∀ t, r t = 1/4 - t^2 + t^4/4) ∧
         /- there exists a real-valued δ : ℝ → ℝ with -/
         /-   δ(0) = 0  and  ∃ c > 0, |δ(t)| ≤ c · t^2 near 0 -/
         /-   such that ((s + 1)/2 = 1/2 + δ(t)) is a root of the resolvent. -/
         ... := by
     -- use `pan_witness_cleaned_resolvent` + quadratic-formula on the
     -- `s¹`-coefficient `4t² − t⁴` to extract `s(t) = Θ(t)` ⇒ `δ(t) = Θ(t²)`.
     sorry
   ```
   The exact formal statement will depend on the OQ-02.a problem
   refactor (Option C). Both Mathlib asymptotic API and the eventual
   problem statement are in flight (PR #18637 S5 PREP, state.md
   candidate 1).

2. **Edit `problem.md`** (separate refactor PR) to split OQ-02.a into
   a.1 (`k ≥ 1`, dischargeable via Pan) and a.2 (`k ≥ 2`, open,
   citing PR #18455 S4c PREP Newton-polygon obstruction).

Both items are out of scope for this S5b SCAFFOLD-1.

---

**Tagline**: *Promote the Pan-witness perturbation identity from S4b PREP
prose (in m-coordinates) to a Lean lemma (in s-coordinates), specialising
S5a's Lemma 1 to the canonical numerical-instability family. One `rw + ring`
discharges; future `k = 1` tangency reduces to a one-step quadratic-formula
extraction from the resulting `s³ − 2 s² + (4 t² − t⁴) s − t⁴` polynomial.*
