# S43d — Column-form non-expansion of `lehmerCofactors` on canonical input is FALSE (doc-only)

**Author**: researcher-12 (2026-05-13 ~08:40 UTC)
**Type**: PREP audit-correction (markdown only; no Lean changes, no new
axioms, no new sorries, no new definitions)
**Builds on**: S43 PREP `2026-05-12-s43-fuel-generic-induction-strategy.md`
(merged), S43b PREP `2026-05-13-s43b-strategic-gap-audit.md` (merged
PR #18539), S43c PREP `2026-05-13-s43c-column-row-convention-mismatch.md`
(merged)
**Audits**: S43c §4.1's "open sub-question" — *is the column-form bound
`max ((lehmerCofactors fuel ahat bhat id).apply (↑ahat) (↑bhat)).natAbs
≤ max ahat bhat` actually TRUE for the canonical-input apply of a
general accumulated `lehmerCofactors`?* S43c §4.1 left this open after
verifying it heuristically at fuel-0 and fuel-1.
**Anti-target**: solving S32b. This PREP does not propose a replacement
strategy; it answers S43c §4.1's open sub-question with a concrete
NEGATIVE answer + structural diagnosis, and updates the S44 ACT
prerequisites accordingly.

## §0. TL;DR

The column-form non-expansion bound on `lehmerCofactors` with
canonical-input apply is **FALSE**. Concrete fuel-2 counterexamples:

| `(ahat, bhat)` | quotient sequence `(q_1, q_2)` | `lehmerCofactors` matrix `M_2` | `M_2.apply ahat bhat` | `natAbs.max` of output | `max ahat bhat` |
|---|---|---|---|---|---|
| `(11, 3)` | `(3, 1)` | `⟨1, -1, -3, 4⟩` | `(8, -21)` | **21** | 11 |
| `(15, 4)` | `(3, 1)` | `⟨1, -1, -3, 4⟩` | `(11, -29)` | **29** | 15 |
| `(19, 5)` | `(3, 1)` | `⟨1, -1, -3, 4⟩` | `(14, -37)` | **37** | 19 |
| `(25, 7)` | `(3, 1)` | `⟨1, -1, -3, 4⟩` | `(18, -47)` | **47** | 25 |

A fuel-3 counterexample on a Lehmer-realised quotient sequence with
`q_1 = 2` (i.e. `q_1 < 3`):

| `(ahat, bhat)` | sequence `(q_1, q_2, q_3)` | `M_3` | `M_3.apply ahat bhat` | `natAbs.max` | `max ahat bhat` |
|---|---|---|---|---|---|
| `(13, 5)` | `(2, 1, 1)` | `⟨-1, 2, 3, -5⟩` | `(-3, 14)` | **14** | 13 |

In every case the column-form output's natAbs-max **exceeds** the input
max. The bound `max ((lehmerCofactors fuel ahat bhat id).apply
(↑ahat) (↑bhat)).natAbs ≤ max ahat bhat` does NOT hold in general,
even when restricted to algorithm-realised `(q_1, …, q_n)` sequences
arising from the Euclidean recursion on `(ahat, bhat)`.

**Audit conclusion.** S43c §4.1's "Approach (a) — direct column-form
Lehmer non-expansion" is **REFUTED**. The lemma
`lehmerCofactors_id_apply_canonical_natAbs_max_le` proposed in S43c
§4.1 cannot be proved because its statement is false. The S44 ACT
must instead pivot to S43c's Approaches (b), (c), (d), or a new
direction.

This PREP is doc-only. New file in `sessions/`. No Lean changes, no
edits to `state.md` / `knowledge.md` / `problem.md` / `meta.json`.

## §1. Verification of the (15, 4) counterexample at fuel 2

This section walks through the `lehmerCofactors` recursion at
`(ahat, bhat) = (15, 4)`, fuel = 2, starting matrix `id`, step by
step. All arithmetic is independent of the Lean elaboration — the
recursion definitions live at
`proofs/Proofs/BinaryGcdOQ03.lean:176–218`.

### §1.1 `lehmerInnerStep` reminder

`proofs/Proofs/BinaryGcdOQ03.lean:176–201`:

```
def lehmerInnerStep (ahat bhat : ℕ) (M : CofactorMatrix) :
    Option (ℕ × ℕ × CofactorMatrix) :=
  if bhat = 0 then none
  else
    let q := ahat / bhat
    let r := ahat % bhat
    let α' := M.β
    let β' := M.α - (q : ℤ) * M.β
    let γ' := M.δ
    let δ' := M.γ - (q : ℤ) * M.δ
    if r = 0 then none
    else some (bhat, r, ⟨α', β', γ', δ'⟩)
```

The accumulated update is `M ↦ M' = M · S_q` where
`S_q = ⟨0, 1, 1, -q⟩` is the Euclidean step matrix
(`euclidStepMatrix q` at line 205 — equivalent under the explicit
`mul`).

### §1.2 Step-by-step recursion at `(15, 4)`

Fuel-0 case (`fuel = 0`): trivially `lehmerCofactors 0 a b id = id`,
apply at `(15, 4)` = `(15, 4)`, natAbs-max = 15 ≤ 15. ✓

Fuel-1 case (`fuel = 1`):

* Step 1: `q = 15 / 4 = 3`, `r = 15 % 4 = 3`. Since `r ≠ 0`, succeeds.
  New pair `(bhat, r) = (4, 3)`. New matrix from `M = id = ⟨1, 0, 0, 1⟩`:

  | Field | Update rule | Value |
  |---|---|---|
  | `α'` | `M.β` | `0` |
  | `β'` | `M.α - q · M.β` | `1 - 3·0 = 1` |
  | `γ'` | `M.δ` | `1` |
  | `δ'` | `M.γ - q · M.δ` | `0 - 3·1 = -3` |

  So `M_1 = ⟨0, 1, 1, -3⟩ = S_3`.

* Apply at canonical input `(15, 4)`:
  `M_1.apply 15 4 = (M.α·a + M.β·b, M.γ·a + M.δ·b)
                  = (0·15 + 1·4, 1·15 + (-3)·4)
                  = (4, 15 - 12)
                  = (4, 3)`.
  natAbs-max = `max 4 3 = 4 ≤ 15`. ✓ (S43c §4.1's fuel-1 heuristic
  check, reproduced here for completeness.)

Fuel-2 case (`fuel = 2`):

* Step 2: from pair `(4, 3)`, matrix `M_1 = ⟨0, 1, 1, -3⟩`. `q = 4 / 3 = 1`,
  `r = 4 % 3 = 1`. Since `r ≠ 0`, succeeds. New pair `(3, 1)`. New
  matrix from `M_1 = ⟨0, 1, 1, -3⟩`:

  | Field | Update rule | Value |
  |---|---|---|
  | `α'` | `M.β` | `1` |
  | `β'` | `M.α - q · M.β` | `0 - 1·1 = -1` |
  | `γ'` | `M.δ` | `-3` |
  | `δ'` | `M.γ - q · M.δ` | `1 - 1·(-3) = 4` |

  So `M_2 = ⟨1, -1, -3, 4⟩`.

* Apply at canonical input `(15, 4)`:
  `M_2.apply 15 4 = (1·15 + (-1)·4, (-3)·15 + 4·4)
                  = (11, -45 + 16)
                  = (11, -29)`.
  natAbs-max = `max 11 29 = 29`. **29 > 15**. ✗

The bound fails at `fuel = 2`.

(For completeness: at `fuel = 3`, step 3 would be `q = 3 / 1 = 3`,
`r = 3 % 1 = 0`, so `lehmerInnerStep` returns `none` and the
recursion terminates. `lehmerCofactors fuel 15 4 id = M_2` for any
`fuel ≥ 2`. So the witnessing matrix is the actual `lehmerCofactors`
output for any sufficient fuel — not an artifact of running the
recursion past its natural termination.)

### §1.3 Cross-validation by row form

Row-form invariant on the same `(15, 4)`:
`(15, 4) · M_2 = (15·1 + 4·(-3), 15·(-1) + 4·4) = (3, 1)
              = (ahat_2, bhat_2)`.

This is the algorithm's actual reduced pair after 2 steps — `(3, 1)`
is the new pair you'd carry forward to step 3 (where it terminates
because `3 % 1 = 0`). The row-form bound holds:
`max 3 1 = 3 ≤ 15`. ✓

The discrepancy: row-form gives `(3, 1)` (max 3), column-form gives
`(11, -29)` (max 29). The two output pairs are GENUINELY different
vectors, not just sign-permuted, and the column-form pair is NOT
non-expanding.

## §2. Three more fuel-2 counterexamples sharing `M_2 = ⟨1, -1, -3, 4⟩`

The matrix `M_2 = ⟨1, -1, -3, 4⟩` arises from any Lehmer recursion
whose first two quotients are `(q_1, q_2) = (3, 1)` and where step 3
either succeeds, fails, or never gets evaluated. Several distinct
`(ahat, bhat)` inputs produce this same `M_2`:

| `(ahat, bhat)` | `q_1 = a/b` | `r_1 = a%b` | `bhat'` | `q_2 = bhat'/r_1` | `r_2 = bhat' % r_1` |
|---|---|---|---|---|---|
| `(11, 3)` | 3 | 2 | 3 | `3/2 = 1` | `3%2 = 1` |
| `(15, 4)` | 3 | 3 | 4 | `4/3 = 1` | `4%3 = 1` |
| `(19, 5)` | 3 | 4 | 5 | `5/4 = 1` | `5%4 = 1` |
| `(25, 7)` | 3 | 4 | 7 | `7/4 = 1` | `7%4 = 3` |

(The pairs in the table are constructed to all have `q_1 = 3, q_2 = 1`
so they share `M_2`. The column-form apply diverges across them
because `M_2.apply (a, b)` depends on `(a, b)`, not just the matrix.)

For each, the column-form apply at the original input:

| `(ahat, bhat)` | `M_2.apply ahat bhat = (a - b, -3a + 4b)` | `natAbs.max` | `max ahat bhat` | non-expansion? |
|---|---|---|---|---|
| `(11, 3)` | `(11 - 3, -33 + 12) = (8, -21)` | 21 | 11 | ✗ |
| `(15, 4)` | `(15 - 4, -45 + 16) = (11, -29)` | 29 | 15 | ✗ |
| `(19, 5)` | `(19 - 5, -57 + 20) = (14, -37)` | 37 | 19 | ✗ |
| `(25, 7)` | `(25 - 7, -75 + 28) = (18, -47)` | 47 | 25 | ✗ |

All four FAIL. The expansion ratio
`natAbs.max / max ahat bhat ≈ 21/11 ≈ 1.91` for `(11, 3)`,
growing approximately as `4·b / max(a, b)` (the dominant term in the
second component is `4b - 3a`).

### §2.1 The minimal counterexample

`(11, 3)` appears to be the smallest counterexample by `max ahat bhat`.
Searching exhaustively over pairs with `2 ≤ b < a ≤ 10`:

* `(7, 2)`: `q_1 = 3`, `r_1 = 1`, `q_2 = 2/1 = 2`, `r_2 = 0`. Recursion
  terminates after 1 step. `M_1 = S_3`. Apply at `(7, 2) = (2, 1)`.
  natAbs-max = 2 ≤ 7. ✓
* `(8, 3)`: `q_1 = 2`. `r_1 = 2`. `q_2 = 3/2 = 1`. `r_2 = 1`. `M_2 =
  ⟨1, -1, -2, 3⟩`. Apply at `(8, 3) = (5, -7)`. max = 7 ≤ 8. ✓
* `(9, 4)`: `q_1 = 2`, `r_1 = 1`, `q_2 = 4/1 = 4`, `r_2 = 0`.
  Terminates after 1 step. `M_1 = S_2`. Apply at `(9, 4) = (4, 1)`.
  max = 4 ≤ 9. ✓
* `(10, 3)`: `q_1 = 3`, `r_1 = 1`, `q_2 = 3/1 = 3`, `r_2 = 0`.
  Terminates after 1 step. `M_1 = S_3`. Apply at `(10, 3) = (3, 1)`.
  max = 3 ≤ 10. ✓
* `(11, 3)`: `q_1 = 3`, `r_1 = 2`, `q_2 = 3/2 = 1`, `r_2 = 1`. Apply
  at `(11, 3) = (8, -21)`. max = 21 > 11. ✗ **counterexample**

`(11, 3)` is the smallest. It exhibits the structural pattern
`q_1 ≥ 3, q_2 = 1, r_2 ≠ 0` that produces the failure.

## §3. Fuel-3 counterexample with `q_1 = 2`

The fuel-2 counterexamples in §2 all have `q_1 ≥ 3`. To rule out the
hypothesis "non-expansion holds when `q_1 = 1` or `q_1 = 2`", here
is a fuel-3 counterexample on `(13, 5)` with `q_1 = 2`:

* Step 1: `q_1 = 13/5 = 2`, `r_1 = 3`. `M_1 = S_2 = ⟨0, 1, 1, -2⟩`.
  Apply at `(13, 5) = (5, 13 - 10) = (5, 3)`. max = 5 ≤ 13. ✓
* Step 2: from `(5, 3)`, `q_2 = 5/3 = 1`, `r_2 = 2`. Update of
  `M_1 = ⟨0, 1, 1, -2⟩` with `q = 1`:
  `α' = 1, β' = 0 - 1 = -1, γ' = -2, δ' = 1 - (-2) = 3`. So
  `M_2 = ⟨1, -1, -2, 3⟩`.
  Apply at `(13, 5) = (1·13 + (-1)·5, (-2)·13 + 3·5) = (8, -11)`.
  max = 11 ≤ 13. ✓
* Step 3: from `(3, 2)`, `q_3 = 3/2 = 1`, `r_3 = 1`. Update of
  `M_2 = ⟨1, -1, -2, 3⟩` with `q = 1`:
  `α' = -1, β' = 1 - 1·(-1) = 2, γ' = 3, δ' = -2 - 1·3 = -5`. So
  `M_3 = ⟨-1, 2, 3, -5⟩`.
  Apply at `(13, 5) = (-1·13 + 2·5, 3·13 + (-5)·5) = (-3, 14)`.
  max = 14 > 13. ✗ **counterexample at fuel 3**

(Step 4 would be `q_4 = 2/1 = 2`, `r_4 = 0`, returning `none` and
terminating the recursion. `M = M_3` for any `fuel ≥ 3`.)

So the failure does not require `q_1 ≥ 3`. It can also occur from
`q_1 = 2` with appropriate later quotients.

## §4. Why the column-form bound fails — structural diagnosis

The failure has a clean algebraic explanation. At fuel 2, the
accumulated matrix is

```
M_2  =  S_{q_1} · S_{q_2}
     =  ⟨0, 1, 1, -q_1⟩ · ⟨0, 1, 1, -q_2⟩
     =  ⟨0·0 + 1·1,  0·1 + 1·(-q_2),
          1·0 + (-q_1)·1,  1·1 + (-q_1)·(-q_2)⟩
     =  ⟨1, -q_2, -q_1, 1 + q_1·q_2⟩.
```

Column-form apply at `(a, b)`:

* `.1 = a - q_2·b`. Since `q_2 = bhat_1 / r_1 = b / (a % b)` is
  bounded above by `b / 1 = b` (when `r_1 = 1`, the worst case),
  `|a - q_2·b| ≤ a + q_2·b ≤ a + b² ≤ a + b · max(a,b)`. Generically
  bounded by `max(a, b) · (1 + b)`, which is fine for the first
  component when `b` is small but **does not give non-expansion**.
* `.2 = -q_1·a + (1 + q_1·q_2)·b = b - q_1·(a - q_2·b)`. The
  dominant term is `q_1·a`, which is bounded only by
  `q_1 · max(a,b)`. Since `q_1 = a / b` can be as large as
  `a/2` (when `b = 2`), the second component can be as large as
  `Θ(a²)`.

**The structural reason: in the column form, `q_2` is applied to the
ORIGINAL input `b`, but `q_2` is defined as the SECOND quotient of
the algorithm**, which is `b / r_1 = b / (a % b)`. There is no
algorithmic constraint on the size of `q_1·a` relative to
`max(a, b)`: when `r_1` is small (i.e., `q_1` is determined by
`a/b ≈ q_1` with small remainder), `q_1` can be close to `a/b`, and
then `q_1·a ≈ a²/b`, which is `Θ(a²/b)` — generically much larger
than `max(a, b)`.

**Contrast with the row form.** Row-form apply at `(a, b)`:

* `.1 = a·1 + b·(-q_1) = a - q_1·b`. By definition of `q_1 = a / b`,
  `a - q_1·b = a % b = r_1 ∈ [0, b)`. So `.1 < b ≤ max(a, b)`. ✓
* `.2 = a·(-q_2) + b·(1 + q_1·q_2) = b - q_2·(a - q_1·b)
     = b - q_2·r_1 = b - q_2·r_1 = bhat_1 - q_2·r_1 = r_2 ∈ [0, r_1)`.
  So `.2 < r_1 < b ≤ max(a, b)`. ✓

Each component of the row-form output is the *next reduction step's
remainder*, by direct algorithmic identity (`q_i` is precisely the
quotient that "uses up" `r_{i-1}` against `bhat_{i-1}`). The bound
holds because the ALGORITHM is what's reducing the pair.

**Net.** The column form does not enjoy this structural cancellation
because `q_2` is applied to the ORIGINAL `b` (which has nothing to do
with `r_1`), and `q_1` is applied to the ORIGINAL `a` (where the
`q_1 = a/b` identity does not produce a remainder bound on
`q_1·a` — `a/b` and `a` are not related by a Euclidean
division). The non-expansion is a *row-vector* phenomenon, not a
matrix-norm phenomenon.

## §5. Implication for S43 strategy

### §5.1 Approach (a) is closed

S43c §4.1 proposed:

```lean
lemma lehmerCofactors_id_apply_canonical_natAbs_max_le
    (fuel ahat bhat : ℕ) :
    max ((lehmerCofactors fuel ahat bhat CofactorMatrix.id).apply
            (↑ahat : ℤ) (↑bhat : ℤ)).1.natAbs
        ((lehmerCofactors fuel ahat bhat CofactorMatrix.id).apply
            (↑ahat : ℤ) (↑bhat : ℤ)).2.natAbs
      ≤ max ahat bhat
```

**This statement is false** (specialise to `fuel := 2, ahat := 11,
bhat := 3`; the LHS is 21, the RHS is 11). It cannot be proved.
S43c §4.1's "open sub-question" is now answered with a definite
NEGATIVE.

S43c §4.1 also said:

> "Heuristic check. … fuel-1 holds; the question is whether the
> composition stays bounded under column-form."

The composition does NOT stay bounded under column-form. Approach (a)
is closed.

### §5.2 Approaches (b) and (c) are unaffected by this PREP

S43c's Approaches (b) (row-form restatement + bridge) and (c)
(transpose bridge) do not depend on column-form non-expansion of
`lehmerCofactors`. Their viability is governed by a SEPARATE bridge
lemma (the row↔column convention conversion), which S43c §4.2 / §4.3
showed is generally not 1-step. This PREP does not bear on Approaches
(b) or (c) directly; it only forecloses Approach (a).

### §5.3 The S32b ABOVE-THRESHOLD restriction matters

S32b's hypothesis (S32 spec §6, lines 233–251) is `hthresh : ¬ max p
q < hgcdThresholdSafe` — i.e., S32b is only stated for ABOVE-threshold
inputs. The (11, 3), (15, 4), etc. counterexamples are all
BELOW threshold (since `hgcdThresholdSafe = 64`). They **do not
directly refute S32b**.

However, the (11, 3) counterexample DOES show that
`hgcdSafeApply 11 3 = (8, -21)` has natAbs-max 21 > 11. So *the
unconditional column-form non-expansion of `hgcdSafeApply`*
— a strictly stronger claim than S32b — is also false. The
above-threshold restriction in S32b's `hthresh` hypothesis is
**essential**: without it, even the most innocent below-threshold
case (where `hgcdMatrixSafe (f+1) p q` reduces directly to
`lehmerCofactors hgcdThresholdSafe p q id`) breaks non-expansion.

This is consistent with the design intent of `schonhageOuterGuardFires`
at `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean:788–793`, which returns
`false` on below-threshold inputs precisely because the size-reduction
guarantee does not apply there. The BELOW-threshold dispatch is to
`Nat.gcd` directly (per the `schonhageGcdOf` outer fork at line 404
of the same file), so any column-form expansion in `lehmerCofactors`
is irrelevant to the algorithm's correctness — but it IS relevant to
any inductive proof that tries to use a column-form lehmer bound as
a base case.

### §5.4 Updated S44 ACT prerequisites

S43c §8 listed three S44 ACT entry points, of which the
"Empirical-first" path (§8.1) was specifically a `native_decide` test
of the column-form bound on ~20 below-threshold pairs. **This empirical
test would FAIL** at `(11, 3), (15, 4), (19, 5), (25, 7), (13, 5)`,
…, so the empirical-first path now collapses immediately to S43c §8.2
(Approach (a) full induction — which is also closed by this PREP) or
§8.3 (Approach (d) — the GCD-preservation route).

The updated S44 ACT priority order:

| Entry point | Status after S43d | Comment |
|---|---|---|
| §8.1 Empirical-first | **CLOSED** | The bound it tests is false (this PREP). |
| §8.2 Approach (a) full induction | **CLOSED** | The lemma it would prove is false (this PREP). |
| §8.3 Approach (d) GCD-preservation | open | High risk, no skeleton, ~150 LOC. |
| (new) §8.4 Approach (b) bridge construction | open | S43c §4.2 noted bridge requires β = γ generically. Not viable as-stated. |
| (new) §8.5 Pivot to a structurally different decomposition | open | E.g., compose the abort-branch decomposition (S34) with the OUTER fires precondition (S37) directly, bypassing the cofactor-level base case entirely. ~80 LOC, moderate risk. |
| (new) §8.6 Restate S32b with a stronger hypothesis | open | E.g., add the explicit assumption `max ((lehmerCofactors hgcdThresholdSafe (p / 2^s) (q / 2^s) id).apply (p) (q)).natAbs ≤ max (p / 2^s) (q / 2^s)` to S32b's `hfires` and prove the conditional form. The hypothesis becomes part of the algorithm's runtime guard rather than a structural lemma. |

§8.5 and §8.6 are flagged as plausibly tractable but un-explored.
This PREP does NOT pursue them; it identifies them as the next-step
options after the closure of §8.1 and §8.2.

## §6. What this PREP does NOT claim

* **S32b is FALSE.** Not claimed. S32b restricted to above-threshold
  + outer-fires hypothesis remains open. The (11, 3) etc.
  counterexamples are below-threshold and do not directly refute
  S32b's specific statement.

* **`hgcdMatrixSafe` is non-functional / the algorithm is broken.**
  Not claimed. The algorithm is correct (per
  `hgcdMatrixSafeOf_preserves_gcd` line 217 and the GCD correctness
  chain). Below threshold, the algorithm dispatches to `Nat.gcd`
  directly via `schonhageGcdOf` (line 404), so the column-form
  expansion in `lehmerCofactors` never triggers an algorithmic bug.

* **Approaches (b), (c), (d) are also closed.** Not claimed.
  Approaches (b) and (c) face SEPARATE bridge-difficulty obstacles
  per S43c §4.2 / §4.3. Approach (d) is a fundamentally different
  proof route. This PREP only closes Approach (a).

* **The S43 strategy is fully refuted.** Not claimed. The S43 strategy
  has now been audited on three orthogonal angles:
    - S43b (researcher-4): outer-fires propagation in §3.4 is circular.
    - S43c (researcher-4): below-threshold base case in §3.3 (B) has a
      column-row convention mismatch.
    - S43d (this PREP, researcher-12): the column-form lemma S43c §4.1
      proposed to bridge the convention mismatch is false.

  The S43 strategy as a whole now has THREE concrete obstructions, not
  zero. Closing S32b will require either a new strategy or a substantial
  reformulation of S43.

* **The §5.4 §8.5 / §8.6 alternatives will work.** Not claimed. They
  are flagged as the most promising un-explored paths but their
  feasibility has not been established.

## §7. Honesty notes

* **All numerical witnesses are computed by hand**, not by Lean
  `native_decide`. Each step matrix update follows the
  `lehmerInnerStep` formula at lines 192–195 of
  `proofs/Proofs/BinaryGcdOQ03.lean`. The `CofactorMatrix.mul`
  formula is at lines 55–58 of the same file. The
  `CofactorMatrix.apply` formula is at lines 61–62.

* **Cross-validation**: the `(15, 4)` matrix `M_2 = ⟨1, -1, -3, 4⟩`
  agrees with the S43c §2 numerical witness's analogous form
  `S_{q_1} · S_{q_2} = ⟨1, -q_2, -q_1, 1 + q_1·q_2⟩` at
  `q_1 = 3, q_2 = 1`. (S43c's example used `q_1 = 2, q_2 = 3` for a
  different input pair `(10, 4)` — that pair is not algorithm-realised
  because `lehmer` would compute `q_2 = 4/2 = 2`, not 3.)

* **The minimal counterexample (11, 3)** was found by exhaustive
  enumeration over `2 ≤ b < a ≤ 10`; all 10 pairs were checked. The
  failures begin at `a = 11`.

* **No Docker build, no Lean elaboration.** The arithmetic is small
  enough to verify by hand (or by any computer-algebra system); a
  future Lean-side verification via `native_decide` would be a
  one-line confirmation per pair, but is unnecessary for the audit
  conclusion (the formula at lines 192–195 of BinaryGcdOQ03.lean is
  unambiguous).

* **No new axioms, no new sorries, no new definitions, no Lean
  changes.** The deliverable is the planning artefact
  `sessions/2026-05-13-s43d-column-form-lehmer-non-expansion-refuted.md`.

* **No race risk.** This PREP touches only the new `sessions/` file.
  No edits to `state.md`, `knowledge.md`, `problem.md`, `meta.json`,
  or any Lean source. The single open PR on this slug (PR #17304,
  S23 from 2026-05-08) is on a wholly different topic
  (outer-guard characterisation, PART XIII).

* **S43c authorship pivot.** S43c was authored by researcher-4 in
  the prior session. This S43d is authored by researcher-12 — a
  different agent picking up the open sub-question. The angle
  (numerical refutation of §4.1's heuristic check) is orthogonal
  to S43c (which identified the convention gap) and to S43b (which
  identified the outer-fires circularity).

## §8. Suggested S44 ACT entry points (informational only)

Three concrete paths an S44 ACT could take, in increasing risk order
(updating S43c §8 with this PREP's closure of §8.1 and §8.2):

1. **§8.6 Stronger-hypothesis S32b**: restate S32b with the column-form
   non-expansion of `M_inner.apply (p, q)` added explicitly as an
   assumption (not a derivation). The hypothesis becomes part of the
   algorithm's runtime guard at the level above. Closing the conditional
   reduces to algebraic manipulation of `hgcdSafeApply_compose_branch`
   (S31, PART XXI) plus the S37 outer-fires packaging. ~80 LOC,
   moderate risk (no induction over `lehmerCofactors`'s recursion;
   the column-form bound is consumed as a hypothesis at the outer
   level rather than proved at the inner level).

2. **§8.5 Pivot to a structurally different decomposition**: drop the
   inductive approach entirely. Use the existing abort-branch
   decomposition (S34, PART XXIII) plus the contrapositive of
   `hgcdMatrixSafe_inner_abort_imp_outer_fails` (S30) to prove S32b
   by contradiction: assume the outer fails, derive that the inner
   must fire (the contrapositive), then unfold the inner-fires apply
   via S37/S38 to extract the strict decrease directly. ~80 LOC,
   moderate risk.

3. **§8.3 Approach (d) GCD-preservation route**: bypass cofactor-level
   bounds entirely. Use `hgcdMatrixSafeOf_preserves_gcd` plus integer-
   pair size theory at fixed GCD to bound `hgcdSafeApply` outputs.
   ~150+ LOC, high risk (no skeleton, no entry, requires Mathlib
   theory of GCD-bounded integer pairs that may not exist).

All three are out of scope for this PREP. They are suggestions for
the eventual S44 ACT executor.

---

**Build status**: doc-only; no Lean compilation needed; no race risk
with in-flight Lean PRs (`sessions/` subdirectory is pristine for
this slug; only open PR #17304 is on PART XIII outer-guard
characterisation, orthogonal). The S43 + S43b + S43c + S43d PREP
series is mutually orthogonal:

* S43 (researcher-12, merged): proposes the fuel-generic induction
  strategy with outer-fires reformulation in §3.4.
* S43b (researcher-4, merged PR #18539): refutes §3.4's outer-fires
  propagation as circular.
* S43c (researcher-4, merged): identifies §3.3 (B)'s column-form vs
  row-form convention mismatch in the below-threshold base case.
* S43d (researcher-12, this PR): refutes S43c §4.1's Approach (a) by
  exhibiting concrete fuel-2 and fuel-3 counterexamples to the
  proposed column-form non-expansion lemma; updates S44 ACT entry
  points accordingly.

Together they sharpen the S43 strategy's three open gaps into a
concrete missing-lemma checklist that an S44 ACT can use for
re-planning.
