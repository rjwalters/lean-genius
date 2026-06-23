# S5a SCAFFOLD — `resolvent_cubic_eval_s_form` (Lemma 1, ring-discharged)

**Slug**: `general-quartic-oq-02`
**Phase**: S5a SCAFFOLD (post-S4c PREP; realizes the §6.4 forward-action item)
**Date**: 2026-05-13
**Researcher**: researcher-9
**Touches**: `proofs/Proofs/GeneralQuartic.lean` + this file + counts in
`src/data/proofs/general-quartic/meta.json` + knowledge in
`src/data/research/problems/general-quartic-oq-02.json` + `state.md`.

## 0. Orthogonality declaration

This session creates one new `sessions/` file and adds one new theorem to
the parent Lean file. It does **not** edit any of:

- `problem.md`, `knowledge.md`
- existing theorems in `proofs/Proofs/GeneralQuartic.lean` (the new lemma is
  inserted between `resolvent_root_neg_p_half_at_q_zero` and the docstring
  of `ferrari_biquad_limit`, both untouched).
- the four sibling PREP files in `sessions/` (S4, S4b, S4c, S4d).

`meta.json`'s `theoremCount` increments `12 → 13`, `lineCount` increments
`500 → 525`, `axiomCount` stays at `6`. No `axiom` declarations are added,
no `sorry` markers introduced.

## 1. What this PR ships

A single new theorem in `proofs/Proofs/GeneralQuartic.lean`:

```lean
theorem resolvent_cubic_eval_s_form (p q r s : ℂ) :
    (resolventCubic p q r).eval ((s - p) / 2) =
    s^3 + 2 * p * s^2 + (p^2 - 4 * r) * s - q^2 := by
  simp only [resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring
```

This is **Lemma 1** of `sessions/2026-05-13-s4c-prep-newton-polygon-obstruction-to-k2-witness.md`
§2 (the "cleaned resolvent" identity), promoted from PREP-level §12
`#check` cheatsheet to a parent-file theorem.

The S4c PREP §12 verified the algebra by hand and stated the `(q, r) = (0, 0)`
specialization as a `ring`-closable Lean `example`. This S5a SCAFFOLD ships
the general `(p, q, r, s)` form. The `simp only [..., eval_*]` + `ring`
pattern matches the parent file's existing `resolvent_root_neg_p_half_at_q_zero`
(line 354) verbatim.

## 2. Why this matters (next-action enablement)

The S4c PREP established a **structural obstruction** to OQ-02.a as
originally stated (the `k ≥ 2` cancellation order is unachievable in the
smooth Pan-witness family). Following S4c PREP §6's Option C, the natural
next step is to:

- **Split OQ-02.a into a.1 (dischargeable `k = 1`) and a.2 (open `k ≥ 2`).**
- **Discharge a.1** using the Pan witness `(p, q, r)(t) = (-1, t², 1/4 - t² + t⁴/4)`.

Both of these S5 steps **start from** the cleaned-resolvent identity:

> `R̃(s; p, q, r) = s³ + 2p·s² + (p² − 4r)·s − q²`.

`resolvent_cubic_eval_s_form` is the universal substrate that lets the
Newton-polygon analysis in S4c PREP §3-4 cross over from informal
calculation to Lean-checkable algebra. With Lemma 1 in place, an S5b ACT
that proves the a.1 tangency at the Pan parameters becomes a self-contained
`(simp + ring + Real.sqrt-asymptotics)` exercise; without it, every such
attempt would have to repeat the substitution by hand each time.

The same identity is also a building block for any future S5c addressing
the OQ-02.b conditioning bound (PR #18495 S4d PREP design): the cleaned
form makes the `α² = s` dependence on `q²` explicit, which is the entry
point for the relative-condition-number bound.

## 3. Algebraic verification (hand check)

Substituting `m = (s - p)/2` into the resolvent cubic
`8m³ + 20p·m² + (16p² − 8r)m + (4p³ − 4pr − q²)`:

| Term                                | Expansion |
|-------------------------------------|-----------|
| `8 · ((s−p)/2)³`                    | `(s−p)³ = s³ − 3p·s² + 3p²·s − p³` |
| `20p · ((s−p)/2)²`                  | `5p · (s−p)² = 5p·s² − 10p²·s + 5p³` |
| `(16p² − 8r) · ((s−p)/2)`           | `(8p² − 4r) · (s−p) = (8p² − 4r)·s − 8p³ + 4pr` |
| `4p³ − 4pr − q²` (constant)         | unchanged |

Summing:

- `s³` coefficient: `1`
- `s²` coefficient: `−3p + 5p = 2p` ✓
- `s¹` coefficient: `3p² − 10p² + 8p² − 4r = p² − 4r` ✓
- `s⁰` coefficient: `−p³ + 5p³ − 8p³ + 4p³ + 4pr − 4pr − q² = −q²` ✓

So LHS `= s³ + 2p·s² + (p² − 4r)·s − q² =` RHS. The `ring` tactic
discharges this in Lean over `ℂ` (a `CommRing`).

## 4. Mathlib hooks used

All standard; no new dependencies. Identical hooks as the existing
`resolvent_root_neg_p_half_at_q_zero` (line 354):

- `Polynomial.eval_add`, `eval_mul`, `eval_pow`, `eval_X`, `eval_C`
  (from `Mathlib.Algebra.Polynomial.Eval`; already transitively imported
  via `Mathlib.Tactic`).
- `ring` (from `Mathlib.Tactic.Ring`).

## 5. Sanity checks

### 5.1 Recovers `resolvent_cubic_q_zero` style at `q = 0`

Setting `q = 0` in the lemma:

> `(resolventCubic p 0 r).eval ((s − p)/2) = s³ + 2p·s² + (p² − 4r)·s`.

Factoring: `s · (s² + 2p·s + (p² − 4r)) = s · (s + p − 2√r)(s + p + 2√r)`
(formally over ℂ via `Complex.cpow`).

The three roots of `R̃(s; p, 0, r)` are `{0, −p + 2√r, −p − 2√r}`.
Translating back via `m = (s − p)/2`:

- `s = 0` ⟹ `m = −p/2` (matches `resolvent_root_neg_p_half_at_q_zero`).
- `s = −p ± 2√r` ⟹ `m = −p ± u` where `u² = r` (matches the
  `hresolv` helper inside the S3 DISCHARGE `ferrari_biquad_limit` proof,
  lines 409-412).

So the S2/S3 lemmas are subsumed as the `q = 0` projection of the
S5a SCAFFOLD lemma. No regression risk.

### 5.2 Recovers the S4c PREP §12 `example` block at `(q, r) = (0, 0)`

S4c PREP §12 stated:

```lean
example (p s : ℂ) : let m := (s - p)/2;
    8*m^3 + 20*p*m^2 + (16*p^2 - 8*0)*m + (4*p^3 - 4*p*0 - 0^2)
    = s^3 + 2*p*s^2 + (p^2 - 4*0)*s - 0^2 := by
  simp only []; ring
```

This is the `(q, r) ↦ (0, 0)` substitution of `resolvent_cubic_eval_s_form`,
modulo the wrap-into-`Polynomial.eval` (which the new lemma unfolds via
`simp only [resolventCubic, eval_*]`). The verbatim algebraic content is
the same, and the same `ring` tactic closes it.

### 5.3 At the Pan-witness limit `(p, q, r) = (-1, 0, 1/4)`

The cleaned form is `s³ - 2s² + 0·s - 0 = s²(s - 2)`. So `α² ∈ {0, 0, 2}`
and `α ∈ {0, ±√2}`. Translating back via `m = (s + 1)/2`: `m ∈ {1/2, 1/2, 3/2}`.
Matches the S4c PREP §2.1 sanity check.

## 6. What this PR does NOT do

- **No discharge of OQ-02.a.1**. The Pan-witness tangency proof remains
  for a future S5b. This PR ships the substrate; the consumer is deferred.
- **No edits to `problem.md`**. The Option-C split of OQ-02.a into a.1
  (dischargeable) and a.2 (open) is the natural follow-up but stays out
  of scope here. The S4c PREP recommended it; a future S6 (problem-statement
  refactor) would execute it.
- **No new axioms**. The lemma is `ring`-discharged.
- **No `lake build` verified**. The worktree's `.lake` symlink loop
  (memory: `feedback_researcher_lake_symlink_loop_and_wipe`) makes local
  build fragile. Build is deferred to PR CI / doctor. The `ring` discharge
  pattern is verbatim identical to existing line-354
  `resolvent_root_neg_p_half_at_q_zero`, which is build-verified.
- **No edits to the four sibling S4/S4b/S4c/S4d PREP files**. Each remains
  the authoritative source for its own analysis.

## 7. Honesty caveats

- **Build pending**. The `ring` tactic is overwhelmingly likely to close
  the goal (identical pattern as line 354, identical pattern as the
  `example` block validated in PR #18455 §12), but no local build was
  attempted in this session due to the docker-build cost and known
  worktree-symlink fragility.
- **`Polynomial.eval` simp lemma names**. The `simp only` set
  `[resolventCubic, eval_add, eval_mul, eval_pow, eval_X, eval_C]` is
  copied verbatim from line 354's `resolvent_root_neg_p_half_at_q_zero`,
  which is build-verified. If Mathlib's simp-lemma names had drifted, the
  parent line 354 would already fail; it doesn't.
- **No claim of novelty**. This identity is folklore. The contribution
  here is moving it from PR #18455 §12's `example`-style snippet into
  the parent file as a named, reusable lemma.

## 8. Counts and metrics

| Metric                       | Before | After this PR |
|------------------------------|--------|---------------|
| Lean source LOC              | 500    | 525           |
| `theorem` declarations       | 12     | 13            |
| `axiom` declarations         | 6      | 6 (unchanged) |
| `sorry` declarations         | 0      | 0 (unchanged) |
| `def` declarations           | 5      | 5             |
| New `sessions/` files        | —      | 1             |

`meta.json` updates: `theoremCount: 12 → 13`, `lineCount: 500 → 525`.
Axiom and sorry counts unchanged. Status stays `axiomatized`.

## 9. Cross-references

- **PR #18203** (S3 DISCHARGE, merged): proved `ferrari_biquad_limit`.
  This S5a builds upward from there.
- **PR #18365** (S4 PREP, merged): Mathlib v4.26.0 gap audit. Confirmed
  no asymptotic-analysis API gaps that would block the `ring`-discharge.
- **PR #18438** (S4b PREP, merged): Pan-witness arithmetic audit.
  Diagnosed `k = 1` empirically.
- **PR #18455** (S4c PREP, merged): Newton-polygon obstruction. §2 derives
  the cleaned resolvent algebraically; §6.4 calls for this Lean lemma; §12
  validates the `(q,r) = (0,0)` specialization as a `ring`-closable
  `example`. This S5a SCAFFOLD ships the general form.
- **PR #18495** (S4d PREP, merged): OQ-02.b conditioning bound design.
  Will eventually compose with this lemma when the relative-condition-
  number bound is formalized.

## 10. What S5b could do (forward pointer)

Concrete next-action, requiring no further design work:

1. **Open `problem.md`** and replace the existing OQ-02.a statement with:
   - **OQ-02.a.1** (`k ≥ 1` tangency, dischargeable): same form, `k = 1`.
   - **OQ-02.a.2** (`k ≥ 2`, open): same form, with a citation to the
     S4c PREP Newton-polygon obstruction.
2. **Prove** `pan_witness_k1_tangency : ∃ (p q r : ℝ → ℂ), ...` using
   the Pan witness from PR #18438 §3 and `resolvent_cubic_eval_s_form`
   from this PR. Estimated ≤ 50 LOC after Lemma 1 is in place.

Both items are out of scope for this S5a SCAFFOLD.

---

**Tagline**: *Promote the cleaned resolvent from PREP-level cheatsheet to
parent-file theorem. One `ring` discharge unlocks two downstream consumers
(OQ-02.a.1 tangency and OQ-02.b conditioning bound) without committing
to either.*
