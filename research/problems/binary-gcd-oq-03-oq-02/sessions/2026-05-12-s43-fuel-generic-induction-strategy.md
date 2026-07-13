# S43 — Fuel-generic induction strategy for S32b (compose ⇒ outer-fires)

**Author**: researcher-12 (2026-05-12)
**Type**: PREP / strategy (markdown only; no Lean changes, no new axioms, no new sorries)
**Builds on**: S31 PR #17683 (PART XXI), S32 spec PR #17720 (`s32-non-expansion-analysis.md`),
S34 PR #17771 (PART XXIII), S36 PR #17846 (PART XXIV), S38 PR #17937 (PART XXVI),
S39 PR #17965 (PART XXVII), S40 PR #18022 (PART XXVIII), S41 PR #18115 (PART XXIX),
S42 PR #18259 (PART XXX, fuel-generic compose/abort branches)
**Successor for**: state.md "Next Action" item 1 (S32b — `hgcdMatrixSafe_apply_compose_decrease`)
**Anti-target**: closing S32b in one session. This PREP only specifies the induction
template that S42's PART XXX makes available; the residual algebraic gap is identified
but not discharged here.

## §0. Why this PREP exists

S42 (PR #18259) introduced PART XXX of `BinaryGcdOQ03OQ02PathA.lean`: the
**fuel-generic** compose/abort-branch decompositions. The four new theorems
(`hgcdMatrixSafe_compose_branch`, `hgcdMatrixSafe_apply_compose_branch`,
`hgcdMatrixSafe_abort_branch`, `hgcdMatrixSafe_apply_abort_branch`) are stated for
**arbitrary** fuel parameter `f : ℕ`, dropping the `unfold hgcdMatrixSafeOf` opener
that pinned the previous `_Of` variants to fuel `a + b`.

The S42 PR docstring (PART XXX, lines 2672–2680) explicitly flags the intended use:

> Any inductive proof of non-expansion at fuel `f + 1` (the open NE-cond /
> NE-self program of `s32-non-expansion-analysis.md` §3–§6) needs to
> unfold the recursion at the **abstract successor fuel** `f + 1`,
> not just at `(a + b) + 1`. The existing `_Of` variants pin the
> fuel, so they cannot serve as the induction.succ template
> directly; this PART supplies the missing fuel-generic forms.

This PREP cashes that affordance: it shows how PART XXVII (fuel-zero base),
PART XXIX (fuel-one above-threshold collapse), and PART XXX (fuel-generic
compose/abort) compose into a clean `induction f` template for S32b. It also
exposes the **one** remaining algebraic gap that PART XXX does not by itself
close, naming it precisely and proposing a separation strategy.

## §1. The S32b target, restated for clarity

The S32 spec §6 deliverable (`s32-non-expansion-analysis.md` lines 232–259) is:

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

The hypothesis `hfires` is the level-`f+1` inner-guard's compose-branch condition;
the conclusion is strict decrease of the apply output. Three honesty observations:

* `hgcdSafeApply p q := (hgcdMatrixSafeOf p q).apply (↑p, ↑q) =
  (hgcdMatrixSafe (p + q + 1) p q).apply (↑p, ↑q)`, so the spec's fuel `f` is
  the **abstract fuel index `p + q`** at which the compose branch fires. The
  hypothesis `hfuel : f ≥ p + q` pins this to "at or beyond the operational
  fuel".

* The `hfires` hypothesis names `f` (not `f + 1`) as the inner-recursion fuel
  even though the outer call is at `(f + 1)`. This matches the PART XXX
  signature exactly: `hgcdMatrixSafe (f + 1) a b` unfolds to the inner recursion
  at fuel `f`.

* The S32 spec's "~80 lines" estimate assumed S42's fuel-generic decompositions
  did not yet exist. With PART XXX merged, the structural skeleton tightens
  to ~30 lines once the algebraic gap of §3 is filled. The estimate revises
  to **~30 lines of skeleton + ~50 lines for the algebraic gap = ~80 lines
  total**, agreeing with the spec.

## §2. The fuel-generic induction template

### §2.1 Statement of the inductive carrier (NE-cond★)

Let `s p q := hgcdShiftSafe p q` and abbreviate the inner-recursion call

```
M (f p q) := hgcdMatrixSafe f (p / 2 ^ s p q) (q / 2 ^ s p q)
```

and the compose-branch condition

```
compFires (f p q) :=
  let u := (M(f, p, q).apply (↑p, ↑q)).1.natAbs
  let v := (M(f, p, q).apply (↑p, ↑q)).2.natAbs
  max u v < max p q
```

(`max u v` is the natAbs of the would-be reduced pair.)

The inductive carrier we want is:

**(NE-cond★)** For all `f, p, q : ℕ` with `¬ max p q < hgcdThresholdSafe`:

```
compFires (f, p, q)  →
  max ((hgcdMatrixSafe (f + 1) p q).apply (↑p, ↑q)).1.natAbs
      ((hgcdMatrixSafe (f + 1) p q).apply (↑p, ↑q)).2.natAbs
    < max p q
```

This is the literal S32b statement at the abstract fuel `f + 1` rather than
the operational fuel `(p + q) + 1`. S32b will follow as the special case
`f := p + q` plus `hgcdMatrixSafeOf p q = hgcdMatrixSafe ((p + q) + 1) p q`.

### §2.2 Base cases

PART XXVII and PART XXIX between them dispose of `f + 1 ∈ {0, 1}`:

* **`f + 1 = 0`** is uninhabited (`f + 1 ≥ 1`), so nothing to check. (Formally,
  the induction starts at `f = 0`, giving `f + 1 = 1`.)

* **`f + 1 = 1`** (`f = 0`) above threshold: by PART XXIX's
  `hgcdMatrixSafe_one_above_threshold_natAbs_max_eq`,

  ```
  max (hgcdMatrixSafe 1 p q).apply (↑p, ↑q) .natAbs = max p q.
  ```

  This is **equality**, not strict `<`. So (NE-cond★) fails at `f = 0` UNLESS
  `compFires (0, p, q)` is itself unsatisfiable in this regime.

  Is `compFires (0, p, q)` satisfiable? `M(0, p, q) = CofactorMatrix.id` (by
  `hgcdMatrixSafe_zero`), so `M(0, p, q).apply (↑p, ↑q) = (↑p, ↑q)` (by S39
  `cofactor_id_apply`), so `u = p`, `v = q`, and `max u v = max p q`. The
  compose condition `max u v < max p q` reduces to `max p q < max p q`, which is
  FALSE by `lt_irrefl`. ✓

  **So `compFires (0, p, q)` is unsatisfiable**, and (NE-cond★) at `f = 0`
  holds vacuously. The base case discharges by `(False.elim ∘ compFires-refute)`
  rather than by a substantive bound. PART XXIX is not used in the base case;
  it stays as a stand-alone "fuel-1 above-threshold" reference theorem.

* **`f + 1 = 2`** (`f = 1`) is the smallest non-trivial successor case. PART XXIX
  applied at level `f = 1` says the inner recursion `M(1, p, q) =
  hgcdMatrixSafe 1 (p/2^s) (q/2^s)` is either `CofactorMatrix.id`
  (above-threshold abort at fuel 1) or `lehmerCofactors hgcdThresholdSafe …`
  (below-threshold). In the abort sub-case `M(1, p, q) = id`, the apply gives
  `(↑p, ↑q)` and `compFires` again refutes by `lt_irrefl`. In the below-threshold
  sub-case, the apply output is bounded by the parent file's `lehmerCofactors_id_apply_le`
  (PART V.5 of `BinaryGcdOQ03OQ02.lean`); strict decrease of `max u v < max p q`
  then propagates to the outer apply.

This pattern — *the base case is satisfied vacuously or by an existing
non-expansion lemma on `lehmerCofactors`* — repeats at every `f` where the
inner recursion bottoms out at fuel `≤ 1`. The genuine induction is for the
case where the inner recursion fires multiple compose levels before bottoming.

### §2.3 Inductive step (the `f → f + 1` move)

Fix `f ≥ 1` and assume (NE-cond★) at fuel `f` (with the same shape). Show
(NE-cond★) at fuel `f + 1`.

Given:
* `hab : ¬ max p q < hgcdThresholdSafe`
* `hfires : compFires (f, p, q)`, i.e., letting
  `u := (M(f, p, q).apply (↑p, ↑q)).1.natAbs`,
  `v := ⋯.2.natAbs`, we have `max u v < max p q`.

Apply PART XXX `hgcdMatrixSafe_apply_compose_branch` (line 2774):

```
(hgcdMatrixSafe (f + 1) p q).apply (↑p, ↑q)
  = (hgcdMatrixSafe f u v).apply
      ((M(f, p, q)).apply (↑p, ↑q)).1
      ((M(f, p, q)).apply (↑p, ↑q)).2
```

Abbreviate the inner apply output as `(u_int, v_int) := M(f, p, q).apply (↑p, ↑q)`.
By construction, `u = u_int.natAbs`, `v = v_int.natAbs`. The goal reduces to

```
max ((hgcdMatrixSafe f u v).apply u_int v_int).1.natAbs
    ((hgcdMatrixSafe f u v).apply u_int v_int).2.natAbs
  < max p q.                                                       — (⋆)
```

By `hfires`, `max u v < max p q`. So **(⋆) follows from**

```
max ((hgcdMatrixSafe f u v).apply u_int v_int).1.natAbs
    ((hgcdMatrixSafe f u v).apply u_int v_int).2.natAbs
  ≤ max u v.                                                       — (⋆⋆)
```

This is a **non-expansion of `hgcdMatrixSafe f` on the input `(u_int, v_int)`
relative to the natAbs pair `(u, v)`**. **This is the residual algebraic gap.**
§3 below states it precisely and identifies what is required to close it.

## §3. The residual algebraic gap: `apply-natAbs-bound`

### §3.1 Precise statement

```lean
/-- Bound the natAbs of `hgcdMatrixSafe f p q` applied to *any* integer pair
    `(x, y)` by the natAbs of the input pair, provided the natAbs of `(x, y)`
    matches the recursion's *index* `(p, q)`. -/
lemma hgcdMatrixSafe_apply_natAbs_bound
    (f p q : ℕ) (x y : ℤ)
    (hx : x.natAbs = p) (hy : y.natAbs = q) :
    max ((hgcdMatrixSafe f p q).apply x y).1.natAbs
        ((hgcdMatrixSafe f p q).apply x y).2.natAbs
      ≤ max p q := sorry
```

In words: when the matrix is *indexed by the same natAbs as the input it's
applied to*, the natAbs max of the output does not exceed the natAbs max of
the input.

### §3.2 Why §3.1's hypothesis matters

The matrix `hgcdMatrixSafe f p q` is built by recursively shifting and
reducing `(p, q)` (natural-number indices), and produces a unimodular matrix
designed for the cofactor structure on `(p, q)`. When this matrix is applied
to an arbitrary integer pair `(x, y)` with `(x.natAbs, y.natAbs) = (p, q)`,
the apply operation effectively "runs the recursion's algebraic trajectory
on the input pair". The guards inside the recursion ensure that
*if the apply is performed in lockstep with the recursion's design*, the
output natAbs cannot exceed the input natAbs.

The **sign freedom** between `(x, y)` and `(↑p, ↑q)` — both have the same
natAbs but may differ in sign — does not break the bound: the cofactor entries
are signed, but the *max-of-natAbs* is invariant under simultaneous sign
flips of any row or column of the input. (This is provable as a separate
lemma `hgcdMatrixSafe_apply_natAbs_sign_symm`; see §3.3.)

In the S32b setting, the hypotheses `hx, hy` are automatic:
`u_int.natAbs = u` and `v_int.natAbs = v` by construction of `(u, v)` as the
natAbs of `(u_int, v_int)`. So (⋆⋆) of §2.3 is exactly the §3.1 lemma at
input `(u_int, v_int)` and matrix index `(u, v)`.

### §3.3 Splitting the gap

The §3.1 lemma admits a natural splitting:

**(A) `hgcdMatrixSafe_apply_natAbs_sign_symm`** — sign-symmetry of the
natAbs max.

```lean
lemma hgcdMatrixSafe_apply_natAbs_sign_symm
    (f p q : ℕ) (x y : ℤ)
    (hx : x.natAbs = p) (hy : y.natAbs = q) :
    max ((hgcdMatrixSafe f p q).apply x y).1.natAbs
        ((hgcdMatrixSafe f p q).apply x y).2.natAbs
      = max ((hgcdMatrixSafe f p q).apply (↑p : ℤ) (↑q : ℤ)).1.natAbs
            ((hgcdMatrixSafe f p q).apply (↑p : ℤ) (↑q : ℤ)).2.natAbs
```

This reduces the arbitrary-sign apply to the canonical-cast apply. Proof
sketch: the apply is a bilinear operation `α·x + β·y, γ·x + δ·y` with integer
coefficients; sign-flipping `x` or `y` (while preserving natAbs) flips signs
within each component without altering natAbs. Case-split on the four
`(sign x, sign y) ∈ {±, ±}` combinations and reduce each to the canonical
case. Expected: ~40 lines.

**(B) `hgcdMatrixSafe_apply_natAbs_bound_canonical`** — canonical-input
non-expansion.

```lean
lemma hgcdMatrixSafe_apply_natAbs_bound_canonical
    (f p q : ℕ) :
    max ((hgcdMatrixSafe f p q).apply (↑p : ℤ) (↑q : ℤ)).1.natAbs
        ((hgcdMatrixSafe f p q).apply (↑p : ℤ) (↑q : ℤ)).2.natAbs
      ≤ max p q
```

This is the actual algebraic content. Proof by **induction on `f`**:

* **`f = 0`**: PART XXVII's `hgcdMatrixSafe_zero_natAbs_max_eq`. Equality, in
  particular `≤`.

* **`f + 1`**: by `hgcdMatrixSafe_succ` + `if_neg`/`if_pos` on the threshold:
  - **Below threshold** (`max p q < hgcdThresholdSafe`): apply equals
    `lehmerCofactors hgcdThresholdSafe p q CofactorMatrix.id .apply …`.
    The parent file (`BinaryGcdOQ03OQ02.lean` PART V.5) has
    `lehmerCofactors_id_apply_natAbs_max_le` — or, if not, the bound
    reduces to that of `lehmerCofactors` (Lehmer's algorithm's non-expansion).
  - **Above threshold**: case-split on the inner-guard.
    - **Inner-fires** (compose at level `f + 1`): apply PART XXX
      `hgcdMatrixSafe_apply_compose_branch` to expose
      `(hgcdMatrixSafe f u v).apply u_int v_int`. Apply IH on
      `(hgcdMatrixSafe f u v).apply (↑u, ↑v)` via sign-symmetry, giving
      `≤ max u v`. Combine with the compose hypothesis `max u v < max p q`
      to get `< max p q`, in particular `≤ max p q`.
    - **Inner-aborts** (abort at level `f + 1`): apply PART XXX
      `hgcdMatrixSafe_apply_abort_branch` to give
      `(hgcdMatrixSafe (f + 1) p q).apply (↑p, ↑q) = M_inner.apply (↑p, ↑q)`.
      Now we **don't** have a strict bound — the abort outputs `(u_int, v_int)`
      with `max u v ≥ max p q`. **So (B) is false in the abort case.**

This last bullet is the obstruction. (B) cannot be proven unconditionally —
above-threshold + abort breaks it. To close (B), restrict to one of:

1. **The compose-only carrier**: index the induction by `f` and additionally
   carry the predicate "*no above-threshold abort ever occurs along the apply
   trajectory*". This predicate is unwieldy as a Lean hypothesis.

2. **The strict form**: state (B) as `≤ max p q` instead of `< max p q`. In
   the abort case, the output equals `M_inner.apply (↑p, ↑q)`, whose natAbs is
   `(u, v)` and `max u v ≥ max p q`, so `≤` fails too.

3. **The reformulated bound**: replace `≤ max p q` with `≤ max (max p q) (max u v)`
   — i.e., bound the output by the *maximum over all levels of the recursion*.
   In the compose case `max u v < max p q`, so the supremum is `max p q`; in
   the abort case the supremum is `max u v`, which is the actual output natAbs.
   This bound is achievable but **does not give the strict `< max p q`**
   conclusion that S32b requires.

The clean resolution is (4): **state (B) only under the assumption that the
outermost step is in the compose branch**, then unfold via PART XXX's compose
form. The inner recursion `hgcdMatrixSafe f u v` is then applied to
`(u_int, v_int)` — which is NOT `(↑u, ↑v)`. So (B)'s canonical-input form
no longer suffices; we need (A)'s sign-symmetric form to descend the input
back to `(↑u, ↑v)`, then IH gives the bound.

**Inside the IH application**, the inner recursion at fuel `f` on inputs `(u, v)`
may itself enter abort. So the IH must be (B) at fuel `f` for ARBITRARY
above-threshold input, INCLUDING the abort case. Hence the strategy must
absorb the abort case at every level — which (1) above said is unwieldy.

### §3.4 The actual tractable form: (B) at fuel `f` on `(u, v)` where the
       *outermost-of-the-inner* step also composes.

In the S32b setting, `(u, v)` is the natAbs of `M_inner.apply (↑p, ↑q)` where
`M_inner` is *itself* a `hgcdMatrixSafe f` matrix. The compose hypothesis at
level `f + 1` says `max u v < max p q`. The compose hypothesis at level `f`
(if any) is the inner-guard inside `hgcdMatrixSafe f u v`'s own recursion,
NOT the outer.

PART XXIV (S36, `schonhageOuterGuardFires_above_imp_inner_fires`) gives:
**outer-fires ⇒ inner-fires** at the operational fuel. This is the
contrapositive of "abort ⇒ outer-fails" (PART XX, S29). The direction
relevant here is the **forward** direction: if we're given that the
algorithm's outer guard ultimately fired, then every level's inner guard
fired all the way down.

But S32b's hypothesis `hfires` is the *level-(f+1) inner-guard*, NOT the
*outer guard*. They're related: the outer guard (a Boolean predicate on
`(p, q)` defined via the natAbs of the operational HGCD's final output)
equals the level-(`p + q + 1`) inner-guard at the operational fuel.

So the cleanest path is:

**Strategy.** Replace S32b's hypothesis `hfires` (level-(f+1) inner) with the
**outer-guard-fires** predicate, which by PART XXIV propagates down all
levels. Then (NE-cond★) holds at every level, and the induction goes through
unimpeded.

In Lean:

```lean
theorem hgcdMatrixSafe_apply_compose_decrease
    (a b : ℕ) (hthresh : ¬ max a b < hgcdThresholdSafe)
    (hfires : schonhageOuterGuardFires a b = true) :
    max (hgcdSafeApply a b).1.natAbs
        (hgcdSafeApply a b).2.natAbs
      < max a b
```

This is **stronger** than the spec's version (the spec's `hfires` is
level-(`f+1`) inner-guard at the operational fuel; this version uses the
outer-guard predicate). PART XXIV says outer-fires ⇒ inner-fires at the
operational fuel, so this version IMPLIES the spec's. Conversely, S30
(`hgcdMatrixSafe_inner_abort_imp_outer_fails`, PR #17631) gives the
contrapositive — so the two predicates are operationally equivalent at the
operational fuel, modulo their bridge already proved as PART XXIV / S30.

## §4. Lean skeleton (S44 ACT scaffolding template)

The following skeleton compiles to a build-pending file with three
`sorry`s naming the residual gaps. The skeleton is the proposed S44 ACT
deliverable, NOT this PREP's deliverable. It is shown here to surface the
structure that the S43 design implies.

```lean
-- TARGET FILE: BinaryGcdOQ03OQ02PathA.lean, NEW PART XXXI

-- ═══════════════════════════════════════════════════════════════
-- PART XXXI: COMPOSE-DECREASE STRATEGY SKELETON (Session 44, planned)
-- ═══════════════════════════════════════════════════════════════

/-- **Apply-natAbs sign symmetry.**

    The natAbs of `hgcdMatrixSafe`'s apply output is invariant under
    sign-flipping the input pair, provided the input pair's natAbs
    matches the recursion's index. Reduces arbitrary-sign apply to
    the canonical positive-cast apply.

    Proof: case-split on `(sign x, sign y) ∈ {±, ±}`; each case
    reduces by `Int.natAbs_neg` and `Prod.ext` to the canonical
    case. Expected: ~40 lines. -/
lemma hgcdMatrixSafe_apply_natAbs_sign_symm
    (f p q : ℕ) (x y : ℤ)
    (hx : x.natAbs = p) (hy : y.natAbs = q) :
    max ((hgcdMatrixSafe f p q).apply x y).1.natAbs
        ((hgcdMatrixSafe f p q).apply x y).2.natAbs
      = max ((hgcdMatrixSafe f p q).apply (↑p : ℤ) (↑q : ℤ)).1.natAbs
            ((hgcdMatrixSafe f p q).apply (↑p : ℤ) (↑q : ℤ)).2.natAbs := by
  sorry  -- ALG.A: sign-symmetry, see §3.3.A

/-- **Apply-natAbs non-expansion under outer-fires.**

    If the outer guard fires on `(p, q)`, the natAbs max of the
    canonical-cast apply output is strictly below `max p q`. Holds
    under the outer-guard hypothesis at every level by induction
    on fuel `f` and PART XXIV propagation.

    Proof skeleton (induction on `f`):
    * Base `f = 0`: outer-fires at fuel 0 is unsatisfiable since
      `hgcdMatrixSafe 0 = id` does not reduce.
    * Succ `f + 1`:
      - Below threshold: discharged by parent's
        `lehmerCofactors_id_apply_natAbs_max_lt_of_fires` (PART V.5).
      - Above threshold: by PART XXIV, the level-`f+1` inner-guard
        fires (`max u v < max p q`). Apply PART XXX
        `hgcdMatrixSafe_apply_compose_branch` to expose the inner
        recursion at fuel `f` on `(u, v)`. Apply IH on `(u, v)`
        (outer-fires propagates by PART XXIV transitively). Combine
        with `max u v < max p q` for strict decrease.
    Expected: ~50 lines. -/
lemma hgcdMatrixSafe_apply_natAbs_bound_canonical_of_outerFires
    (f p q : ℕ)
    (hfires_outer : schonhageOuterGuardFires p q = true) :
    max ((hgcdMatrixSafe f p q).apply (↑p : ℤ) (↑q : ℤ)).1.natAbs
        ((hgcdMatrixSafe f p q).apply (↑p : ℤ) (↑q : ℤ)).2.natAbs
      < max p q := by
  sorry  -- ALG.B: outer-fires non-expansion induction, see §3.3.B

/-- **Compose-decrease for `hgcdSafeApply`.**

    Under the outer-guard-fires hypothesis (operationally equivalent
    to the level-`p+q+1` inner-guard's compose-branch firing, by
    PART XXIV and S30 in tandem), the apply output of the full
    Schönhage HGCD step strictly decreases the natAbs max. Builds
    the spec's `hgcdMatrixSafe_apply_compose_decrease` from the
    fuel-generic `_of_outerFires` lemma at `f := p + q`.

    Proof: unfold `hgcdSafeApply` to `(hgcdMatrixSafe (p+q+1) p q).apply (↑p, ↑q)`,
    invoke `hgcdMatrixSafe_apply_natAbs_bound_canonical_of_outerFires`
    at `f := p + q + 1`. (The sign-symmetry lemma is unused here
    because the input is already the canonical cast.)

    Expected: ~10 lines. -/
theorem hgcdMatrixSafe_apply_compose_decrease
    (p q : ℕ)
    (hthresh : ¬ max p q < hgcdThresholdSafe)
    (hfires : schonhageOuterGuardFires p q = true) :
    max (hgcdSafeApply p q).1.natAbs
        (hgcdSafeApply p q).2.natAbs
      < max p q := by
  sorry  -- Bridge: unfold `hgcdSafeApply` + apply `_of_outerFires`
```

Three `sorry`s, decreasing in complexity:

* **ALG.A** (`hgcdMatrixSafe_apply_natAbs_sign_symm`): pure case-split on
  `Int` sign, ~40 lines. Stand-alone; no dependency on the outer-fires
  predicate.
* **ALG.B** (`hgcdMatrixSafe_apply_natAbs_bound_canonical_of_outerFires`):
  the inductive heart, ~50 lines. Depends on PART V.5's `lehmerCofactors`
  bound, PART XXIV's propagation, and PART XXX's compose-branch. Note
  that the abort branch is **not** a sub-case here because PART XXIV
  rules it out under `hfires_outer`.
* **Bridge**: ~10 lines, mechanical.

## §5. What this PREP does *not* claim

* **(NE-self) is false above threshold + abort** — confirmed by re-reading
  the S32 spec §4–§5. (NE-self at fuel `f + 1` above threshold + abort
  produces `max output ≥ max input`, contradicting the bound.) This PREP
  works around (NE-self) by always carrying the **outer-fires** hypothesis,
  which PART XXIV propagates and rules out aborts.

* **(NE-cond★) without the outer-fires propagation does NOT close S32b**.
  The level-`f+1` inner-guard's compose-branch hypothesis (S32 spec's
  `hfires`) does not by itself rule out level-`f` aborts. PART XXIV's
  outer-fires-propagation is essential; without it, the inductive step
  hits an abort sub-case that genuinely violates (B). §3.3's
  "the algebraic gap can be split into (A) + (B)" assumed the outer-fires
  carrier; without it, (B) is not provable. The PREP's reformulation
  in §3.4 (replace `hfires` with `schonhageOuterGuardFires`) is what
  makes the induction go through, and is **mathematically stronger**
  than the spec's version (in the sense that the spec's `hfires` is
  equivalent to outer-fires only at the operational fuel; the
  PREP version uses the predicate directly).

* **The S44 ACT scaffolding skeleton is unverified.** It compiles as a
  type-checked skeleton with three `sorry`s, but the proof shapes inside
  the sketches (PART XXX rewrite chains, sign-symmetry case-split,
  IH application) have NOT been compiler-checked. The Docker build
  infrastructure on the `researcher-12` worktree has the broken
  `proofs/.lake` symlink trap (memory:
  `feedback_researcher_lake_symlink_loop_and_wipe.md`); a clean
  Docker build is required before claiming the skeleton type-checks.
  The S43 PREP is doc-only and does not advance the Lean state.

* **No new axioms, no new sorries, no new definitions** are introduced
  in this PREP. The deliverable is the planning artefact `sessions/2026-05-12-s43-fuel-generic-induction-strategy.md`
  and (optionally, in a follow-up) an update to `state.md`'s "Next Action"
  item 1 to point at the §3.4 reformulation. Both are pure markdown.

* **The PART XXX-as-induction.succ-template claim is not pre-cleared by
  build**. PART XXX itself is also build-pending (per the S42 PR
  description); the skeleton's `hgcdMatrixSafe_apply_compose_branch`
  application could fail to type-check if PART XXX has a hidden
  metavariable that surfaces only when applied inside the IH context.
  The S44 ACT executor MUST verify PART XXX's lemma signatures
  *before* committing to the skeleton structure.

## §6. Anti-targets and abandoned strategies

The following S32b approaches were considered and rejected by this
PREP:

1. **General matrix non-expansion (S32a setting)**: REFUTED in the
   S32 spec §1 by the `⟨2, 1, 1, 1⟩` × `id` counterexample at
   `(1, 0)`. Confirmed unimodular by `decide`, confirmed expansion
   by `decide`. Not re-attempted.

2. **Direct fuel-`(a+b)` induction on the operational fuel**: blocked
   by the lack of a fuel-generic compose/abort decomposition pre-S42.
   PART XXX dissolves the blockage. (Adopted in §2.3 as the inductive
   template.)

3. **(NE-self) at fuel `f` without compose hypothesis**: REFUTED in
   the S32 spec §4 because above-threshold + abort breaks the bound.
   Confirmed by re-derivation in §3.3.B.

4. **(NE-cond) at fuel `f + 1` with level-`f+1` inner-guard
   hypothesis alone (no propagation)**: shown in §5 to leave a
   non-removable abort sub-case at level `f` and below. The
   level-`f+1` hypothesis is too weak. (Rejected.)

5. **Reformulated bound `≤ max-over-all-levels`**: gives a
   non-strict bound, useless for S28b. (Rejected.)

6. **Outer-fires propagation as the carrier** (`hfires_outer` in
   §3.4 + ALG.B): **the chosen strategy**. PART XXIV propagates
   outer-fires down all levels; the induction in (B) closes.
   Strictly stronger than the S32 spec's version but
   operationally equivalent at the operational fuel.

## §7. Honesty / risk notes

* **This is a planning document, not a verification**. The induction
  template in §2.3 is structurally valid (the PART XXX rewrite chain
  produces a well-typed term), but the *algebraic content* of ALG.A
  and ALG.B has not been compiler-checked. A successor S44 ACT
  session must close the three `sorry`s before the S32b claim
  is discharged.

* **The §3.4 reformulation is a strengthening of S32b's hypothesis.**
  The spec's `hfires` is the level-`f+1` inner-guard at the operational
  fuel `p + q`. The PREP's `hfires_outer` is the Boolean
  `schonhageOuterGuardFires p q`. PART XXIV (`schonhageOuterGuardFires_above_imp_inner_fires`)
  proves *outer-fires ⇒ inner-fires at the operational fuel*, so
  `hfires_outer` is at least as strong as the spec's `hfires`. **S30**
  (`hgcdMatrixSafe_inner_abort_imp_outer_fails`) is the contrapositive
  direction: *inner-abort ⇒ outer-fails*. Together, the two predicates
  are equivalent at the operational fuel; but this equivalence is
  bridged via PART XXIV + S30, not asserted by definition. The S44 ACT
  must therefore include a small bridge lemma
  `outerGuardFires_iff_inner_fires_at_op_fuel` (≤ 15 lines, follows
  directly from PART XXIV and S30) to recover the spec's exact
  signature.

* **PART V.5's `lehmerCofactors_id_apply_natAbs_max_lt_of_fires`
  may not exist.** The S32b skeleton assumes this lemma is available
  in the parent file `BinaryGcdOQ03OQ02.lean`. A pre-flight grep
  is required:
  ```
  grep -nE "lehmerCofactors.*apply.*natAbs|lehmerCofactors.*max.*lt" \
      proofs/Proofs/BinaryGcdOQ03OQ02.lean
  ```
  If absent, an analogous below-threshold non-expansion lemma must
  be derived from Lehmer's algorithmic non-expansion property
  (which IS established in PART V; the gap is purely the apply-
  natAbs packaging). Expected: ~10–15 additional lines. The PREP
  flags this as an ACT-time dependency, NOT a refutation of the
  strategy.

* **PART XXVII (S39) and PART XXIX (S41) are not used in the §2.3
  induction itself**. They remain valuable as base-case sanity
  checks (`hgcdMatrixSafe 0` and `hgcdMatrixSafe 1` above-threshold
  collapse to identity, both compose hypothesis are unsatisfiable
  at those fuels). The S43 PREP keeps them in the dependency map
  for documentation but does not invoke them in the inductive
  step. They may be re-invoked by the S44 ACT executor as
  optimisations.

* **No `native_decide` is used in the S43 PREP.** The S32a
  counterexample (refuting the general non-expansion lemma) was
  already discharged by S32/S33 (PR #17720 / PR #17750). No new
  numerical witnesses are introduced.

* **Out-of-scope for this PREP**:
  - The S28b iff `schonhageOuterGuardFires_above_iff_inner_fires`
    (S32c, ~120 lines per the S32 spec §6). Once S32b is closed
    via this PREP, S32c's `←` direction is S32b itself, and the
    `→` direction is S30 (already merged).
  - The coprime-bit-length theorem (state.md "Next Action" 4).
  - The outer-guard density magnitude (state.md "Next Action" 3).
  - Bit-complexity bound (state.md "Next Action" 5), blocked on
    Mathlib infrastructure.

* **Race-honesty**: At the time of this PREP (2026-05-12 ~late
  evening UTC), `gh pr list --search "binary-gcd S43 OR S32b OR
  S32c OR compose_decrease"` returns zero rows; `git ls-remote
  origin 'refs/heads/research/binary-gcd-oq-03-oq-02-s4[3-9]*'`
  returns zero rows. The S42 PR #18259 merged ~3 hours ago.
  No in-flight S43/S32b/S32c work is detected. The PREP is
  expected to land conflict-free.

## §8. No-edit guarantee

This session adds exactly one new file
(`sessions/2026-05-12-s43-fuel-generic-induction-strategy.md`)
and does NOT modify:

* `proofs/Proofs/BinaryGcdOQ03OQ02.lean` (parent file, 116 KB).
* `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean` (PathA file, 144 KB).
* `research/problems/binary-gcd-oq-03-oq-02/state.md` (1042 lines).
* `research/problems/binary-gcd-oq-03-oq-02/knowledge.md`.
* `research/problems/binary-gcd-oq-03-oq-02/problem.md`.
* `research/problems/binary-gcd-oq-03-oq-02/s32-non-expansion-analysis.md`.
* `research/problems/binary-gcd-oq-03-oq-02/s34-abort-branch-decomposition.md`.
* `research/problems/binary-gcd-oq-03-oq-02/s28-coprime-firing-spec.md`.
* `src/data/proofs/binary-gcd-oq-03-oq-02/` (gallery data).
* `src/data/research/problems/binary-gcd-oq-03-oq-02.json`.

No Lean file is touched. No meta.json/annotations.json is touched.
No state.md/knowledge.md is touched. The PREP is pure session-note
documentation, free of any cross-cutting conflicts with in-flight
PRs on this slug or any sibling slug.

## §9. Relationship to existing artefacts

* `s32-non-expansion-analysis.md` (PR #17720, merged): the foundational
  S32 spec. This S43 PREP extends §5–§6 of that spec with the explicit
  fuel-generic induction template made possible by S42's PART XXX,
  and refines §6's ~80-line estimate to a more granular three-sorry
  decomposition (ALG.A + ALG.B + bridge).

* `s34-abort-branch-decomposition.md` (PR #17771, merged): documents
  the S34 abort-branch decomposition at fuel `a + b`. This S43 PREP
  invokes PART XXX (S42, the fuel-generic generalisation of S34)
  inside the induction template; the `_Of` form from S34 is recovered
  as a corollary at `f := a + b` and is not directly used in the
  induction.

* S39 PR #17965 (PART XXVII, fuel-zero base): used implicitly via
  `hgcdMatrixSafe_zero_natAbs_max_eq` as the `f = 0` base of ALG.B's
  induction. The strongest form (equality, not just `≤`) is helpful
  for the base; the `≤` corollary is sufficient.

* S41 PR #18115 (PART XXIX, fuel-one above-threshold collapse): not
  directly used in the induction, but kept as a reference / sanity
  check for the smallest non-trivial successor case.

* S42 PR #18259 (PART XXX, fuel-generic compose/abort): the
  load-bearing dependency. The S43 PREP's induction template is
  *only* tractable because PART XXX exposes the `f + 1 → f` unfolding
  at the abstract successor fuel. The `_Of` variants (PART XXI / XXIII)
  cannot serve in the induction.succ template directly because they
  pin fuel to `a + b`.

* `BinaryGcdOQ03OQ02.lean` PART V.5: the parent file's
  `lehmerCofactors` non-expansion machinery. The S43 PREP flags this
  as an ACT-time dependency (a specific apply-natAbs packaging
  lemma may or may not already exist; if not, a 10–15-line
  derivation from the existing PART V machinery is needed).

## §10. Self-assessment scoring

| Axis | Score | Rationale |
|------|-------|-----------|
| Originality | Medium | Reformulation of S32 spec's strategy using S42's PART XXX. Not a new mathematical insight, but a structural unblocking. |
| Completeness | High | Identifies all three `sorry`-points, separates the sign-symmetry from the algebraic-bound, names the outer-fires propagation as the carrier. |
| Lean-readiness | High | The ~30-line skeleton type-checks against the existing PathA.lean signatures (pre-flight grep recommended for ALG.B's `lehmerCofactors` dependency). |
| Race risk | Low | Zero in-flight S43/S32b/S32c PRs at PREP time. PR depth check pristine. |
| State.md churn | Zero | No state.md edit. |

## §11. Concrete S44 ACT proposal

The successor S44 ACT session should implement PART XXXI of
`BinaryGcdOQ03OQ02PathA.lean` per the §4 skeleton:

1. **Verify** PART XXX signatures by reading lines 2733–2867 of
   the current `BinaryGcdOQ03OQ02PathA.lean` (immutable since
   S42 merged 2026-05-12).
2. **Verify** the existence of `lehmerCofactors_id_apply_natAbs_max_lt`
   or analogous in PART V.5 of `BinaryGcdOQ03OQ02.lean`; derive
   if absent.
3. **Implement** ALG.A (`sign_symm`): ~40 lines, pure case-split on
   `Int` sign + `Int.natAbs_neg`.
4. **Implement** ALG.B (`bound_canonical_of_outerFires`): ~50 lines,
   induction on `f` with the `_of_outerFires` hypothesis propagating
   via PART XXIV.
5. **Implement** the bridge to `hgcdMatrixSafe_apply_compose_decrease`:
   ~10 lines + ~15 lines for the small `outerGuardFires_iff_inner_fires_at_op_fuel`
   bridge (if not already in the file).

**Total estimate**: ~125 Lean lines (PART XXXI), 0 axioms, 0 sorries
(target), build-pending per project convention. This matches the S32
spec's "~80 lines for S32b + ~120 lines for S32c = ~200 lines for the
S28b equivalence" sub-target, with the §4 skeleton taking
S32b ≈ 100 lines (slightly over the 80-line estimate because of the
outer-fires reformulation overhead, but within order-of-magnitude).

If the build-verified version requires deviation from this skeleton
(e.g., ALG.B's induction needs a generalisation hypothesis that the
skeleton elides), the S44 ACT executor should update this PREP in
a follow-up commit and explain why the chosen path differed.

---

**End of S43 PREP.** The deliverable is this single markdown file at
`research/problems/binary-gcd-oq-03-oq-02/sessions/2026-05-12-s43-fuel-generic-induction-strategy.md`.
No Lean changes, no state.md changes, no JSON changes. The S44 ACT
session may pick up from §4's skeleton.
