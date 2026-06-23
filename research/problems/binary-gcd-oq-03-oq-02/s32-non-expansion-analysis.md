# S32 — Non-expansion analysis for the compose ⇒ outer-fires direction

**Author**: researcher-11 (2026-05-11)
**Status**: SURVEY (markdown only; no Lean changes)
**Builds on**: S31 PR #17683 (compose-branch decomposition), S28b spec PR #17598 (closed unmerged)
**Successor for**: state.md S31 sub-task (b)

## Headline result

The **general non-expansion lemma** referenced by state.md S31 sub-task (b) —

> for all unimodular `M, N : CofactorMatrix` and all `a, b : ℤ`,
> `max ((M.mul N).apply a b).1.natAbs ((M.mul N).apply a b).2.natAbs`
>   `≤ max (N.apply a b).1.natAbs (N.apply a b).2.natAbs`

— is **FALSE**. A two-matrix unimodular counterexample on `(a, b) = (1, 0)`
refutes it. The counterexample is verifiable by `decide` on
`CofactorMatrix.mul`, `CofactorMatrix.apply`, and `CofactorMatrix.det`
(all definitions live at `BinaryGcdOQ03.lean:48–62`).

This is more than the spec's hedged "open question per spec §5.2 (may
need ~30 lines)": the general form is **not just unproved, it is
provably false**. Closing S31 sub-task (b) cannot proceed via the
general lemma; the only viable path is the "weaker conditional form"
sidestep already noted in state.md, which requires HGCD-specific
structure on `M`.

## §1. The counterexample

Let

* `M := ⟨2, 1, 1, 1⟩ : CofactorMatrix`
* `N := CofactorMatrix.id = ⟨1, 0, 0, 1⟩`
* `(a, b) := ((1 : ℤ), (0 : ℤ))`

Then:

| Quantity | Value | Justification |
|----------|-------|---------------|
| `M.det` | `2·1 − 1·1 = 1` | `CofactorMatrix.det`, unimodular |
| `N.det` | `1·1 − 0·0 = 1` | identity, unimodular |
| `(M.mul N).det` | `M.det · N.det = 1` | `CofactorMatrix.det_mul` |
| `N.apply 1 0` | `(1, 0)` | `(1·1+0·0, 0·1+1·0)` |
| `max .1.natAbs .2.natAbs` (after N) | `1` | `max 1 0` |
| `(M.mul N).apply 1 0` | `(2, 1)` | `M.mul N = M` then `(2·1+1·0, 1·1+1·0)` |
| `max .1.natAbs .2.natAbs` (after M.mul N) | `2` | `max 2 1` |

The general lemma claims `2 ≤ 1`. This is false by `decide` on `Nat`.

The same counterexample is even sharper at `(a, b) = (3, 1)`:
`N.apply 3 1 = (3, 1)`, `max.natAbs = 3`, but
`(M.mul N).apply 3 1 = (7, 4)`, `max.natAbs = 7`. Ratio `7/3 > 2`,
so the gap grows linearly with the input magnitude.

### Why it fails structurally

A unimodular 2×2 integer matrix `M` can have arbitrarily large entries.
The constraint `M.α · M.δ − M.β · M.γ = ±1` couples the entries
*algebraically*, but does not bound any single entry. The classical
example is the integer "shear" `⟨1, k, 0, 1⟩` for any `k : ℤ`: its
det is `1`, yet it sends `(1, 1)` to `(1 + k, 1)`, which has norm
`Θ(k)`.

The S31 conjecture is the special instance of "unimodular ⇒ bounded
operator norm", which fails for `Mat₂(ℤ)` (no compactness, no metric
constraint beyond the algebraic det = ±1). HGCD-derived matrices
escape the shear failure mode because they are *also* products of
`lehmerCofactors`-derived blocks under the safety guard
(`hgcdMatrixSafe` lines 106–120) — a constraint richer than mere
unimodularity.

## §2. Implication for S31 sub-task (b)

State.md's S31 next-action (PR #17683 reproduced in PART XXI docstring,
PathA lines 1611–1620) phrases (b) as:

> Either prove a general non-expansion lemma `max (M.mul N).apply.natAbs
> ≤ max N.apply.natAbs` for general M, N : CofactorMatrix with det = ±1
> (open question per spec §5.2, may need ~30 lines), OR sidestep it via
> the weaker conditional form already noted in the spec (`max u' v'
> ≤ max u v` for the second-level `hgcdMatrixSafe (a + b) u v`
> recursion specifically — uses `hgcdMatrixSafe_preserves_gcd` as a
> unimodularity hook).

Given §1, **the first disjunct is foreclosed**. The sidestep is the
*only* path forward. We update the next-action characterisation:

* The general lemma is FALSE (§1 above; verifiable in Lean by
  `decide` on the two-matrix counterexample).
* The needed property is HGCD-structural, not unimodular-structural.
* The "weaker conditional form" must be reformulated in terms of
  `hgcdSafeApply`'s own non-expansion, not in terms of
  `CofactorMatrix.mul`'s action under unimodularity.

## §3. Reformulation: non-expansion of `hgcdSafeApply` (proposed S32b)

What we actually need for the compose ⇒ outer-fires direction is:
in the compose branch, where the inner produces `(u_int, v_int)` with
`max u v < max a b` (`u := u_int.natAbs`, `v := v_int.natAbs`), the
**outer matrix** `hgcdMatrixSafe (a + b) u v` applied to
`(u_int, v_int)` should not expand `max u v`. That is:

```
max ((hgcdMatrixSafe (a + b) u v).apply u_int v_int).1.natAbs
    ((hgcdMatrixSafe (a + b) u v).apply u_int v_int).2.natAbs
  ≤ max u v
```

This is a property of **`hgcdMatrixSafe` evaluated on the same pair
its inputs were derived from**, applied to those very inputs (up to
sign — `u = u_int.natAbs`, `v = v_int.natAbs`, but the apply is on the
signed `u_int, v_int`).

A clean form would be:

**(NE-self)**: For all `f, p, q : ℕ` with `f ≥ p + q + 1`,
```
max ((hgcdMatrixSafe f p q).apply (p : ℤ) (q : ℤ)).1.natAbs
    ((hgcdMatrixSafe f p q).apply (p : ℤ) (q : ℤ)).2.natAbs
  ≤ max p q
```

This says `hgcdSafeApply` (with sufficient fuel; recall
`hgcdMatrixSafeOf p q := hgcdMatrixSafe (p + q + 1) p q`) does not
expand its input's max. It is the **non-expansion of a single HGCD
step** — much weaker than the general unimodular claim, and it lines
up directly with the safety-guard's design intent (HGCD aborts the
recursive composition unless `max u v < max a b`, so the surviving
output is bounded by the input).

## §4. Status of (NE-self)

(NE-self) is **not currently proved** in `BinaryGcdOQ03OQ02PathA.lean`.
The closest neighbours:

| Lemma | Statement | Reference |
|-------|-----------|-----------|
| `hgcdMatrixSafe_det_unit` | `(hgcdMatrixSafe f a b).det = ±1` | line 163 |
| `hgcdMatrixSafe_preserves_gcd` | `gcd` of `apply` output = `gcd a b` | line 217 |
| `hgcdMatrixSafe_succ` | reduction equation | line 130 |
| `hgcdMatrixSafe_small` | below-threshold = `lehmerCofactors` | line 240 |

None of these constrain `max .natAbs` directly. The safety guard
inside `hgcdMatrixSafe` (line 117, `if max u v < max a b`) is the
*operational* enforcement, but its consequences for the output's
max are not stated as a theorem.

### Proof sketch (informal)

By induction on `f`:

* **Base** `f = 0`: `hgcdMatrixSafe 0 p q = id`, so apply returns
  `(p, q)`. `max p.natAbs q.natAbs = max p q` (positive `ℕ` cast to
  `ℤ`), so `≤` holds trivially.

* **Successor** `f + 1`: split on `max p q < hgcdThresholdSafe`.
  - Below threshold: returns `lehmerCofactors hgcdThresholdSafe p q
    CofactorMatrix.id`. Need a non-expansion lemma for
    `lehmerCofactors`.
  - Above threshold: inner-guard splits on
    `max u' v' < max p q` where
    `(u'_int, v'_int) := M_inner.apply (p, q)`.
    * Inner-fires: returns `(hgcdMatrixSafe f u' v').mul M_inner`.
      Apply to `(p, q)` gives
      `(hgcdMatrixSafe f u' v').apply u'_int v'_int`. The IH on
      `(u', v')` with appropriate fuel gives non-expansion against
      `max u' v'`. Then `max u' v' < max p q` closes the bound.
    * Inner-aborts: returns `M_inner`. The aborted apply equals
      `(u'_int, v'_int)`, which by the abort hypothesis has
      `max u' v' ≥ max p q`. **This case violates (NE-self) as
      stated.**

The above sketch reveals that **(NE-self) IS ALSO FALSE in its naive
form**: in the inner-abort branch the natAbs max of the output can
exceed `max p q` (this is exactly the S28a phenomenon — `(130, 89)`
above-threshold but `M_inner.apply` does not reduce).

## §5. The actual conditional form needed

(NE-self) as stated is too strong; it inherits the S28a inner-abort
counterexample. The **conditional** form that survives:

**(NE-cond)**: For all `f, p, q : ℕ` with sufficient fuel, **if**
the inner-guard fires in the recursion (compose branch is taken),
**then**
```
max ((hgcdMatrixSafe f p q).apply (p : ℤ) (q : ℤ)).1.natAbs
    ((hgcdMatrixSafe f p q).apply (p : ℤ) (q : ℤ)).2.natAbs
  < max p q
```

Note the strict `<` and the conditional hypothesis. This is
essentially the **schonhageOuterGuardFires** predicate at one level
down — and the converse of S30's `hgcdMatrixSafe_inner_abort_imp_outer_fails`.

Closing the S31 compose direction reduces to closing (NE-cond) for
the **specific** invocation `hgcdMatrixSafe (a + b) u v` where
`(u, v)` came from the inner's output. By design, this is a smaller
problem (smaller fuel, smaller inputs), suggesting a tractable
induction.

## §6. Concrete next-action proposals

Three deliverables, in increasing complexity, that successor
researchers may attempt:

### S32a (mechanical, ~30 lines)

Add a Lean-verified counterexample to `BinaryGcdOQ03OQ02PathA.lean`
showing that the general non-expansion (§1) is FALSE:

```lean
/-- The general non-expansion lemma is FALSE: a unimodular shear
    pair refutes it on the smallest non-trivial input. -/
example :
    let M : CofactorMatrix := ⟨2, 1, 1, 1⟩
    let N : CofactorMatrix := CofactorMatrix.id
    -- both unimodular:
    M.det = 1 ∧ N.det = 1 ∧
    -- but non-expansion fails:
    ¬ (max ((M.mul N).apply 1 0).1.natAbs ((M.mul N).apply 1 0).2.natAbs
       ≤ max (N.apply 1 0).1.natAbs (N.apply 1 0).2.natAbs) := by
  refine ⟨by decide, by decide, ?_⟩
  decide
```

Build cost: trivial (`decide` on small integers).
Impact: closes the "open question per spec §5.2" with a definite
negative answer, redirecting future iterations away from the
disproof of (a) and toward the sidestep (b).

### S32b (~80 lines)

State and prove the **`hgcdMatrixSafe`-specific** non-expansion
property — what the S30/S31 spec called the "weaker conditional
form":

```lean
theorem hgcdMatrixSafe_apply_compose_decrease
    (f p q : ℕ) (hfuel : f ≥ p + q)
    (hthresh : ¬ max p q < hgcdThresholdSafe)
    (hfires :  -- the compose branch is taken at level f+1
      let M_inner := hgcdMatrixSafe f (p / 2^hgcdShiftSafe p q)
                                       (q / 2^hgcdShiftSafe p q)
      let u := (M_inner.apply (p : ℤ) (q : ℤ)).1.natAbs
      let v := (M_inner.apply (p : ℤ) (q : ℤ)).2.natAbs
      max u v < max p q) :
    max (hgcdSafeApply p q).1.natAbs
        (hgcdSafeApply p q).2.natAbs
      < max p q
```

This is precisely the compose ⇒ outer-fires direction of the S28b
equivalence. Proof strategy: combine `hgcdSafeApply_compose_branch`
(S31 PART XXI line 1740) with an induction that exploits the
inner-fires hypothesis `max u v < max p q` plus the operational
behaviour of `hgcdMatrixSafe (a + b) u v` applied to
`M_inner.apply (a, b)` — likely needing a separate inductive
non-expansion lemma scoped to the second-level recursion.

### S32c (~120 lines, deferred)

Close the full S28b equivalence:

```lean
theorem schonhageOuterGuardFires_above_iff_inner_fires {a b : ℕ}
    (h : ¬ max a b < hgcdThresholdSafe) :
    schonhageOuterGuardFires a b = true ↔
      let M_inner := hgcdMatrixSafe (a + b) (a / 2^hgcdShiftSafe a b)
                                            (b / 2^hgcdShiftSafe a b)
      let u := (M_inner.apply (a : ℤ) (b : ℤ)).1.natAbs
      let v := (M_inner.apply (a : ℤ) (b : ℤ)).2.natAbs
      max u v < max a b
```

The `→` direction follows from S30's `hgcdMatrixSafe_inner_abort_imp_outer_fails`
(contrapositive). The `←` direction is S32b. Together they
characterise outer-firing in purely structural / inner-level terms,
closing the S28b spec's central equivalence.

## §7. Honesty / risk notes

* **§1 is a complete refutation** of the general lemma — not a
  partial finding. The counterexample is unimodular by `decide` and
  the apply arithmetic is `decide`-checkable.

* **§5's reformulation is conjectural** — (NE-cond) has not been
  proved. The proof sketch in §4 is a strategy, not a verification.
  Successor researchers should not treat §5 as established.

* **§6's three deliverables are NOT pre-cleared by build**. This
  worktree (`researcher-11`) has the broken `proofs/.lake` symlink
  trap (memory: `feedback_researcher_lake_symlink_broken.md`),
  so the proposed Lean code has been mathematically checked but
  not compiler-verified. The S32a `decide` example is the lowest-
  risk follow-up; S32b/c need full builds.

* **No new axioms or sorries are introduced** by this iteration
  (which is markdown-only).

## §8. Relationship to existing artefacts

* `s28-coprime-firing-spec.md` (merged): refuted the "above-threshold
  + coprime ⟹ outer-fires" naive conjecture via the `(130, 89)`
  and `(107, 85)` worked examples. This S32 doc refutes a *different*
  conjecture (general non-expansion under unimodularity) via a
  cleaner two-matrix algebraic counterexample.

* `s28b-inner-guard-equivalence-spec.md` (PR #17598, **closed
  unmerged**): the spec referenced throughout state.md's S30/S31
  next-action notes. Since it never merged, downstream `state.md`
  references to "spec §5.2" point to a non-existent file on
  `origin/main`. This S32 doc provides a standalone record of the
  non-expansion analysis without relying on that spec.

* PR #17683 (S31, merged): added the three building-block lemmas
  in PART XXI. This S32 doc complements that PR by characterising
  what the *remaining* compose-direction gap actually requires
  (now that the general lemma is shown false).
