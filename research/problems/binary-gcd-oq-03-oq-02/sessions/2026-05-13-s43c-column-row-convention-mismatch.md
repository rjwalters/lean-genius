# S43c — Column-form vs row-form convention mismatch in S43 §3.3 (B) / §4 base case (doc-only)

**Author**: researcher-4 (2026-05-13 ~05:30 UTC)
**Type**: PREP audit-correction (markdown only; no Lean changes, no new axioms,
no new sorries)
**Builds on**: S43 PREP `2026-05-12-s43-fuel-generic-induction-strategy.md`
(merged), S43b PREP `2026-05-13-s43b-strategic-gap-audit.md` (merged PR #18539)
**Audits**: S43 §3.3 (B) below-threshold base-case reduction to "Lehmer's
algorithm's non-expansion" + S43 §4 skeleton's docstring citation of
`lehmerCofactors_id_apply_natAbs_max_lt_of_fires` as a "PART V.5" lemma
**Anti-target**: solving S32b. This PREP only audits S43's base-case bearer
against the actual file contents; it does not propose a replacement strategy
beyond identifying the concrete column-form lemmas that would be needed.

## §0. TL;DR

S43 §3.3 (B) reduces the below-threshold sub-case of the canonical-input
non-expansion lemma to **Lehmer's algorithm's non-expansion**, and S43 §4's
skeleton names a specific bearer `lehmerCofactors_id_apply_natAbs_max_lt_of_fires`
in PART V.5 of `BinaryGcdOQ03OQ02.lean`. Direct file inspection finds:

1. **Phantom name**: `lehmerCofactors_id_apply_natAbs_max_lt_of_fires` does
   **NOT** exist in `BinaryGcdOQ03OQ02.lean` or any sibling file. The closest
   match is `lehmerCofactors_id_apply_le` (line 439) — same prefix, no
   `natAbs_max_lt_of_fires` suffix. The S43 §4 citation must be read as
   "if/once such a lemma is added".

2. **Convention mismatch (the substantive finding)**: the file's
   `lehmerCofactors_id_apply_le` is in **row-vector form** —

   ```
   ∃ ahat' bhat',  ahat·α + bhat·γ = ahat'  ∧  ahat·β + bhat·δ = bhat'
                ∧  max ahat' bhat' ≤ max ahat bhat
   ```

   The `hgcdMatrixSafe` recursion (line 106) and `hgcdSafeApply` (line 308)
   use `CofactorMatrix.apply` which is in **column-vector form** —

   ```
   M.apply a b := (α·a + β·b,  γ·a + δ·b)
   ```

   The two forms produce the same first-coordinate value (`α·a + β·b` vs
   `a·α + b·γ`) only when `β = γ`. The accumulated Lehmer cofactor matrix is
   built by right-multiplication of symmetric step matrices
   `[[0, 1], [1, −q]]` (lines 192–195 of BinaryGcdOQ03), but the product
   `S_1 · S_2 · … · S_n` is generally **not symmetric**, so the row-form and
   column-form applies give genuinely different output pairs.

3. **Below-threshold reduction is not 1-step**: S43 §3.3 (B)'s
   "the bound reduces to that of `lehmerCofactors` (Lehmer's algorithm's
   non-expansion)" is correct in spirit but **non-immediate** in the file's
   convention. The row-form bound on `(a·α + b·γ, a·β + b·δ)` does NOT
   directly imply a bound on `(α·a + β·b, γ·a + δ·b)`. A bridge is required.

**Audit conclusion.** The S43 strategy's below-threshold base case has a
convention gap. The actual lemmas the file proves about `lehmerCofactors`
are in row-vector form, but the S32b conclusion (column-form `hgcdSafeApply`)
needs column-form bounds. The eventual S44 ACT must either (a) build a
column-form Lehmer non-expansion lemma, (b) restate the canonical-input
non-expansion in row-form throughout, or (c) supply a transpose bridge
between the two conventions. §4 below catalogs the three options.

This PREP is doc-only. New file in `sessions/`. No Lean changes, no edits to
`state.md` / `knowledge.md` / `problem.md` / `meta.json`.

## §1. Direct verification of the conventions

### §1.1 `CofactorMatrix.apply` is column-form

`proofs/Proofs/BinaryGcdOQ03.lean:61–62`:

```lean
def CofactorMatrix.apply (M : CofactorMatrix) (a b : ℤ) : ℤ × ℤ :=
  (M.α * a + M.β * b, M.γ * a + M.δ * b)
```

Interpretation: `M.apply a b = M · (a, b)^T` — multiply the matrix `M` on the
left of the column vector `(a, b)^T`. Output coordinates:

* `.1 = α·a + β·b` (first row dot product)
* `.2 = γ·a + δ·b` (second row dot product)

### §1.2 `hgcdMatrixSafe`'s recursion uses column-form throughout

`proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean:106–120`:

```lean
def hgcdMatrixSafe : ℕ → ℕ → ℕ → CofactorMatrix
  | 0, _, _ => CofactorMatrix.id
  | fuel + 1, a, b =>
    if max a b < hgcdThresholdSafe then
      lehmerCofactors hgcdThresholdSafe a b CofactorMatrix.id
    else
      let M_inner :=
        hgcdMatrixSafe fuel (a / 2 ^ hgcdShiftSafe a b)
                            (b / 2 ^ hgcdShiftSafe a b)
      let u := (M_inner.apply (a : ℤ) (b : ℤ)).1.natAbs
      let v := (M_inner.apply (a : ℤ) (b : ℤ)).2.natAbs
      if max u v < max a b then
        (hgcdMatrixSafe fuel u v).mul M_inner
      else
        M_inner
```

Lines 115–116: `(M_inner.apply (a : ℤ) (b : ℤ)).1.natAbs` is column-form on
the **outer** integer pair `(a, b)`, where `M_inner` is indexed by the
**reduced** pair `(a / 2^s, b / 2^s)`. Note: the apply input is NOT
`(↑(a / 2^s), ↑(b / 2^s))` — it's the original `(↑a, ↑b)`. This is the
non-canonical apply (input natAbs ≠ matrix index) that S43 §3.3 (A)'s
sign-symmetry lemma attempts to normalize.

### §1.3 `hgcdSafeApply` is column-form

`proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean:308–309`:

```lean
def hgcdSafeApply (a b : ℕ) : ℤ × ℤ :=
  (hgcdMatrixSafeOf a b).apply (a : ℤ) (b : ℤ)
```

The top-level apply is column-form `(α·a + β·b, γ·a + δ·b)`, and this is
the pair whose `natAbs.max` appears in S32b's conclusion.

### §1.4 `lehmerCofactors_id_apply_le` is row-form

`proofs/Proofs/BinaryGcdOQ03OQ02.lean:439–450`:

```lean
theorem lehmerCofactors_id_apply_le (fuel ahat bhat : ℕ) :
    ∃ ahat' bhat' : ℕ,
      (ahat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).α
        + (bhat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).γ
            = (ahat' : ℤ) ∧
      (ahat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).β
        + (bhat : ℤ) * (lehmerCofactors fuel ahat bhat CofactorMatrix.id).δ
            = (bhat' : ℤ) ∧
      max ahat' bhat' ≤ max ahat bhat := by
  apply lehmerCofactors_invariant_le
  · simp [CofactorMatrix.id]
  · simp [CofactorMatrix.id]
```

Output coordinates:

* `ahat' = ahat·α + bhat·γ` (which is `α·ahat + γ·bhat`, i.e., the FIRST
  column of `M` dotted with the row `(ahat, bhat)`)
* `bhat' = ahat·β + bhat·δ` (SECOND column of `M` dotted with `(ahat, bhat)`)

This is the row-vector convention: `(ahat, bhat) · M = (ahat', bhat')`.

### §1.5 `lehmerCofactors`'s definition is right-multiplication

`proofs/Proofs/BinaryGcdOQ03.lean:212–218`:

```lean
def lehmerCofactors (fuel : ℕ) (ahat bhat : ℕ) (M : CofactorMatrix) : CofactorMatrix :=
  match fuel with
  | 0 => M
  | fuel' + 1 =>
    match lehmerInnerStep ahat bhat M with
    | none => M
    | some (ahat', bhat', M') => lehmerCofactors fuel' ahat' bhat' M'
```

`lehmerInnerStep` returns the new cofactor `M' = M · S` where
`S = [[0, 1], [1, −q]]` is the symmetric step matrix (`proofs/.../BinaryGcdOQ03.lean:192–195`).
The accumulation `M_0 = id, M_1 = id · S_1 = S_1, M_2 = S_1 · S_2, …` is
right-multiplication.

**Consistency check.** The row-form invariant `(a₀, b₀) · M_n = (a_n, b_n)` is
preserved under `M_{n+1} = M_n · S`:

```
(a₀, b₀) · M_{n+1}  =  (a₀, b₀) · (M_n · S)  =  ((a₀, b₀) · M_n) · S
                    =  (a_n, b_n) · S  =  (a_{n+1}, b_{n+1}).
```

This makes the row-vector interpretation NATURAL for `lehmerCofactors`. The
matrix `M` it produces is precisely the matrix that, when right-multiplied by
the input row, produces the reduced output. **`lehmerCofactors` is a
row-form algorithm.**

## §2. The column-form vs row-form output pairs are different

Fix a generic `M = ⟨α, β, γ, δ⟩` and inputs `(a, b)`.

* Column-form: `M.apply a b = (α·a + β·b, γ·a + δ·b)`
* Row-form: `(a, b) · M = (a·α + b·γ, a·β + b·δ)`

Comparing coordinate-wise:

* `.1`: `α·a + β·b` (col) vs `a·α + b·γ` (row). Equal iff `β = γ`.
* `.2`: `γ·a + δ·b` (col) vs `a·β + b·δ` (row). Equal iff `β = γ` (same
  condition).

**Concrete example.** Take `S_1 · S_2` where `S_i = [[0, 1], [1, −q_i]]`:

```
S_1 · S_2  =  [[0, 1], [1, −q_1]] · [[0, 1], [1, −q_2]]
           =  [[1, −q_2], [−q_1, 1 + q_1 q_2]]
```

This product has `β = −q_2` and `γ = −q_1`. Generically `q_1 ≠ q_2`, so
`β ≠ γ` and the column-form and row-form applies of this 2-step
`lehmerCofactors` matrix on a given input `(a, b)` produce different pairs.

**Numerical witness.** Take `q_1 = 2, q_2 = 3`, so `S_1 · S_2 = [[1, −3], [−2, 7]]`.
At `(a, b) = (10, 4)`:

* Column: `(1·10 + (−3)·4, (−2)·10 + 7·4) = (10 − 12, −20 + 28) = (−2, 8)`
* Row: `(10·1 + 4·(−2), 10·(−3) + 4·7) = (10 − 8, −30 + 28) = (2, −2)`

`natAbs.max` of column = `max 2 8 = 8`. `natAbs.max` of row = `max 2 2 = 2`.
The two bounds are GENUINELY different (the row form happens to be
non-expanding from `max 10 4 = 10`; the column form is also non-expanding here
but the value 8 is unrelated to `(2, −2)`).

The row-form bound in `lehmerCofactors_id_apply_le` says
`max ahat' bhat' ≤ max ahat bhat = 10` — which gives `max 2 2 = 2 ≤ 10`. ✓
The column-form bound the S43 induction would need is on `(−2, 8)`, whose
natAbs-max is 8, and the row-form bound says nothing about this.

## §3. The phantom name in S43 §4

S43 §4 docstrings (the planning skeleton, lines 419–421) say:

> Below threshold: discharged by parent's
> `lehmerCofactors_id_apply_natAbs_max_lt_of_fires` (PART V.5).

Grep results across the full file tree:

```
$ grep -rn 'lehmerCofactors_id_apply_natAbs_max\|apply_natAbs_max_lt_of_fires' \
    /Users/rwalters/GitHub/lean-genius/proofs/Proofs/
# (0 matches)
```

**The cited lemma does not exist in any form.** The closest matches in
`BinaryGcdOQ03OQ02.lean` are:

| Line | Name | Form |
|------|------|------|
| 358 | `lehmerCofactors_id_apply_eq` | row, `(ahat, bhat) · M = (ahat', bhat')` |
| 439 | `lehmerCofactors_id_apply_le` | row + `max ahat' bhat' ≤ max ahat bhat` |
| 702 | `cofactor_apply_natAbs_le` | col, triangle bound on each component |

The PART V.5 reference in S43 §4 must be interpreted as **specification**, not
as a citation to an existing lemma. The S44 ACT would have to PROVE this
lemma (or a column-form equivalent) before invoking it. S43 §3.3's parenthetical
"or, if not, the bound reduces to that of `lehmerCofactors` (Lehmer's
algorithm's non-expansion)" acknowledges this potential gap but does not
spell out the convention bridge.

## §4. The actual missing lemmas (concrete S44 prerequisites)

To make S43 §3.3 (B)'s below-threshold base case go through in the file's
column-form convention, one of three approaches is required.

### §4.1 Approach (a): direct column-form Lehmer non-expansion

State the column-form analog of `lehmerCofactors_id_apply_le`:

```lean
/-- **Column-form non-expansion of `lehmerCofactors` on the canonical
    input pair.** When `lehmerCofactors` is accumulated starting from
    `CofactorMatrix.id` and applied (column-form) to its index pair
    `(↑ahat, ↑bhat)`, the natAbs-max of the output is bounded by
    `max ahat bhat`. -/
lemma lehmerCofactors_id_apply_canonical_natAbs_max_le
    (fuel ahat bhat : ℕ) :
    max ((lehmerCofactors fuel ahat bhat CofactorMatrix.id).apply
            (↑ahat : ℤ) (↑bhat : ℤ)).1.natAbs
        ((lehmerCofactors fuel ahat bhat CofactorMatrix.id).apply
            (↑ahat : ℤ) (↑bhat : ℤ)).2.natAbs
      ≤ max ahat bhat
```

This is the lemma S43 §3.3 (B)'s below-threshold case implicitly needs at
`fuel := hgcdThresholdSafe`.

**Provability sketch.** By induction on `fuel`, mirroring
`lehmerCofactors_invariant_le`'s structure but tracking the COLUMN-form
invariant. The step matrix `S = [[0, 1], [1, −q]]` is symmetric, so for the
FIRST step, the column-form and row-form applies coincide. The subsequent
steps (`M_n = S_1 · S_2 · …`) are NOT symmetric, so the column-form bound
needs a separate invariant.

Specifically, the row-form invariant
`a₀·α + b₀·γ = ahat' ∧ a₀·β + b₀·δ = bhat'` is preserved by right-
multiplication `M_{n+1} = M_n · S`. The column-form invariant
`α·a₀ + β·b₀ = ahat' ∧ γ·a₀ + δ·b₀ = bhat'` is preserved by LEFT-
multiplication `M_{n+1} = S · M_n` — which is NOT what `lehmerCofactors`
does. So a direct column-form induction does not parallel the row-form
proof; a different inductive carrier is required.

**Estimated complexity.** ~60–100 lines, comparable to
`lehmerCofactors_invariant_le`'s ~30 lines but with the additional
sign-tracking burden because column-form invariants involve products of M's
entries in different orders.

**Open sub-question.** Is the column-form bound `≤ max ahat bhat` actually
TRUE for the canonical-input column-apply of a general accumulated
`lehmerCofactors`? The row-form bound is true (proved). The column-form bound
is a DIFFERENT statement (per §2's numerical witness, the two output pairs
are different vectors). One would need to verify by induction or computer
algebra that the column-form bound holds.

**Heuristic check.** At fuel-0 (id matrix): `id.apply ahat bhat = (ahat, bhat)`,
natAbs-max = `max ahat bhat`. ≤ holds with equality. ✓
At fuel-1 (one Lehmer step `S_1`): `S_1.apply ahat bhat = (bhat, ahat − q·bhat)`.
natAbs-max = `max bhat |ahat − q·bhat|`. Since `q = ahat / bhat`,
`ahat − q·bhat = ahat % bhat < bhat ≤ max ahat bhat`. ✓

So fuel-1 holds; the question is whether the composition stays bounded under
column-form. The §2 numerical witness shows the column-form output of a
2-step matrix `S_1·S_2 = [[1, −q_2], [−q_1, 1 + q_1·q_2]]` applied to
`(↑(input ahat), ↑(input bhat))` — but in the LEHMER algorithm, the INPUT to
which this matrix is applied is `(ahat, bhat)` at the BEGINNING (i.e., the
original input, NOT the intermediate `(b, a − q·b)`). Need to check whether
`S_1 · S_2 .apply (ahat₀, bhat₀)` is non-expanding when `(ahat₀, bhat₀)` is
the original Lehmer input.

This is an open question that the S44 ACT would have to settle.

### §4.2 Approach (b): row-form restatement of the canonical bound

Sidestep column-form entirely by restating S43 §3.3 (B) in row-form:

```lean
/-- **Row-form non-expansion of `hgcdMatrixSafe` on the canonical input pair.**
    Using the row-vector apply `(↑p, ↑q) · M`, the natAbs-max of the output is
    bounded by `max p q`. -/
lemma hgcdMatrixSafe_apply_row_natAbs_bound_canonical
    (f p q : ℕ) :
    max
      ((p : ℤ) * (hgcdMatrixSafe f p q).α
        + (q : ℤ) * (hgcdMatrixSafe f p q).γ).natAbs
      ((p : ℤ) * (hgcdMatrixSafe f p q).β
        + (q : ℤ) * (hgcdMatrixSafe f p q).δ).natAbs
      ≤ max p q
```

This is the EXACT analog of `lehmerCofactors_id_apply_le` lifted to
`hgcdMatrixSafe`. The below-threshold base case is then a 2-line application
of `lehmerCofactors_id_apply_le` at `fuel := hgcdThresholdSafe`.

**Downside.** The S32b conclusion is about `hgcdSafeApply` which is
column-form. So this approach requires an additional bridge — a theorem
relating row-form and column-form bounds — to actually close S32b.

**Bridge lemma**:

```lean
/-- For `hgcdMatrixSafe`'s accumulated matrix, the column-form apply on the
    canonical-cast input equals the row-form apply on the same input under
    a sign/permutation correction. -/
lemma hgcdMatrixSafe_apply_col_eq_row_canonical
    (f p q : ℕ) :
    -- some explicit equation relating the two forms
    True := True.intro  -- placeholder
```

This bridge is non-trivial and per §2 generally requires β = γ in the
underlying matrix, which doesn't hold. So Approach (b) requires more than
the row-form bound — it requires a fundamentally new identity.

### §4.3 Approach (c): transpose bridge

Define `CofactorMatrix.transpose` and prove `M.apply = M.transpose.apply_row`
(where `apply_row` is row-form). Then `lehmerCofactors_id_apply_le` directly
bounds the column-form apply of the TRANSPOSED `lehmerCofactors` matrix.

```lean
def CofactorMatrix.transpose (M : CofactorMatrix) : CofactorMatrix :=
  ⟨M.α, M.γ, M.β, M.δ⟩

lemma cofactor_apply_eq_transpose_apply_row (M : CofactorMatrix) (a b : ℤ) :
    M.apply a b = ((a : ℤ) * M.transpose.α + (b : ℤ) * M.transpose.γ,
                   (a : ℤ) * M.transpose.β + (b : ℤ) * M.transpose.δ) := by
  simp [CofactorMatrix.apply, CofactorMatrix.transpose]; ring_nf; sorry
```

This identity would let `lehmerCofactors_id_apply_le` bound the column-form
apply of `(lehmerCofactors fuel ahat bhat id).transpose`. But the algorithm
uses the un-transposed matrix. So the bridge would require ALSO showing that
the row-form bound on the TRANSPOSE implies the column-form bound on the
ORIGINAL — which it generically doesn't (the transpose has different entries
and therefore different apply values).

**Net.** Approach (c) doesn't actually close the gap either; it just
restates the convention issue at a different level.

### §4.4 Practical recommendation

Approach (a) (direct column-form induction) is the cleanest path but requires
verifying that the column-form bound actually holds (the §4.1 open sub-question).
The S44 ACT executor should:

1. **First**: empirically verify the column-form bound on a few small
   `lehmerCofactors` instances via `native_decide`. If it holds, proceed with
   approach (a)'s direct induction.

2. **If it fails empirically**: pivot to a different strategy entirely. The
   convention mismatch is then a genuine mathematical obstruction (the
   accumulated `lehmerCofactors` matrix may have column-form behaviour that
   is not non-expanding), and S32b's conclusion would need a different proof
   route — possibly going through the GCD-preservation identity rather than
   through cofactor bounds.

## §5. Cross-validation against S37 and S38 / PART XXV-XXVI

S37's `compose_apply_natAbs_strict_decrease_of_outerFires` (line 2200) and
S38's compose-coordinate forms (PART XXVI) all use column-form throughout —
`(hgcdMatrixSafe f u v).apply u_int v_int` and similar. None of them go
through `lehmerCofactors_id_apply_le` as a base case; they all reduce to
`schonhageOuterGuardFires_strict_decrease` (line 826), which is itself a
1-line unfolding of the outer-fires predicate's definition (which is the
`decide` clause on the column-form strict decrease).

**Key observation.** The file's current strict-decrease results
(`schonhageOuterGuardFires_strict_decrease`, S37, S38) all assume `outer-fires`
and DERIVE the strict decrease tautologically from the predicate's definition.
There is no `lehmerCofactors`-based non-expansion lemma at the column-form
canonical input used anywhere in `BinaryGcdOQ03OQ02PathA.lean`. The S43
strategy is the FIRST attempt to bridge the cofactor-level non-expansion to
the column-form output, and it's precisely where the convention mismatch
surfaces.

## §6. What this PREP does *not* claim

* **S32b is unprovable.** Not claimed. The conclusion is provable under
  outer-fires (by `schonhageOuterGuardFires_strict_decrease`). The
  level-`f+1` inner-fires hypothesis from the S32 spec may also suffice, but
  S43b showed that the natural reduction to outer-fires is circular, and
  S43c shows that the direct base-case reduction to `lehmerCofactors_id_apply_le`
  has a convention gap. A different proof route is needed.

* **The column-form bound is false.** Not claimed. §4.1's heuristic check at
  fuel-0 and fuel-1 supports the bound holding. The S44 ACT must verify by
  induction or by `native_decide` on a range of small inputs.

* **The S43 strategy is fully refuted.** Not claimed. The strategy's §1–§3.2
  (induction template, hypothesis form, residual algebraic gap identification)
  remain useful. §3.3 (B)'s base-case reduction has a convention mismatch
  (this PREP); §3.4's outer-fires propagation is circular (S43b PREP). The
  combined refutation is partial — both gaps point at concrete missing
  lemmas that an S44 ACT could attempt.

* **Approaches (a), (b), (c) are exhaustive.** Not claimed. There may be a
  fourth approach via Approach (d) — bypass the cofactor-level analysis
  entirely and prove S32b via a GCD-preservation / unimodular argument that
  doesn't require column-form non-expansion of `hgcdMatrixSafe`. This PREP
  does not explore Approach (d).

* **The S44 ACT skeleton in S43 §4 is salvageable as-is.** Not claimed. The
  skeleton's `lehmerCofactors_id_apply_natAbs_max_lt_of_fires` placeholder
  must either be filled in via Approach (a) (new column-form lemma) or
  replaced by a different base-case strategy. The skeleton's three `sorry`s
  would need to be augmented with a fourth `sorry` for the column-form
  non-expansion of `lehmerCofactors`.

## §7. Honesty notes

* **No Docker build.** This PREP is doc-only. The convention-mismatch
  observations are verifiable by reading the file headers + grep; no Lean
  compilation is needed.

* **§2's numerical witness verified by hand.** The 2-step Lehmer matrix
  `[[1, −3], [−2, 7]]` at input `(10, 4)` gives column-form `(−2, 8)` and
  row-form `(2, −2)`. These are computed by hand, not by `native_decide`.
  A future computational confirmation is straightforward but unnecessary
  for the audit conclusion (the algebraic identity that column ≠ row when
  β ≠ γ is independent of any specific instance).

* **The phantom name `lehmerCofactors_id_apply_natAbs_max_lt_of_fires` is
  verified absent across the full Proofs/ tree** (grep returned 0 hits).
  Not just in `BinaryGcdOQ03OQ02.lean` but in `BinaryGcdOQ03OQ02PathA.lean`
  too. The S43 §4 citation is a forward-looking placeholder.

* **No new axioms, no new sorries, no new definitions, no Lean changes.**
  The deliverable is the planning artefact
  `sessions/2026-05-13-s43c-column-row-convention-mismatch.md`.

* **S43b ownership.** S43b PREP was authored by researcher-4 (this agent)
  in the prior session (~03:35 UTC, merged as PR #18539). This S43c PREP is
  a continuation — orthogonal angle (convention, not circularity) on the
  same overall goal (auditing S43 strategy for S44 ACT readiness).

## §8. Suggested S44 ACT entry points (informational only)

Three concrete paths an S44 ACT could take, in increasing risk order:

1. **Empirical-first**: `native_decide` test the column-form bound on
   ~20 `(ahat, bhat)` pairs spanning the below-threshold range and
   `fuel := hgcdThresholdSafe`. If all pass, proceed with Approach (a)'s
   induction. ~30 LOC, very low risk.

2. **Approach (a) full induction**: write the column-form non-expansion of
   `lehmerCofactors` from scratch, mirroring `lehmerCofactors_invariant_le`'s
   row-form proof but with a column-form invariant. ~80 LOC, moderate risk
   (the inductive invariant may not have a clean form because step
   matrices' right-multiplications don't commute with column-form applies).

3. **Approach (d) GCD-preservation route**: attempt S32b without the
   cofactor-level non-expansion. Use `hgcdMatrixSafeOf_preserves_gcd` plus
   bounds on integer-pair sizes that preserve a fixed GCD. ~150+ LOC,
   high risk (no obvious entry, no existing skeleton).

All three are out of scope for this PREP. They are suggestions for the
eventual S44 ACT executor.

---

**Build status**: doc-only; no Lean compilation needed; no race risk with
in-flight Lean PRs (sessions/ subdirectory is pristine for this slug).
The S43 + S43b + S43c PREP series is mutually orthogonal:

* S43 (researcher-12, merged): proposes the fuel-generic induction strategy
  with outer-fires reformulation in §3.4.
* S43b (researcher-4, merged PR #18539): refutes §3.4's outer-fires
  propagation as circular.
* S43c (researcher-4, this PR): identifies §3.3 (B)'s column-form vs
  row-form convention mismatch in the below-threshold base case.

Together they sharpen the S43 strategy's two open gaps — the strategic gap
at §3.4 (S43b) and the algebraic-bearer gap at §3.3 (B) (S43c) — into
concrete missing-lemma checklists that an S44 ACT can use as scaffolding.
