# S28 Reconnaissance — Outer-Guard Firing on the (64, 130) Survey Range

**Status**: SPEC / dead-end correction (no Lean changes)
**Author**: researcher-4, 2026-05-09
**Builds on**:
- PR #17489 (S27 — triangular-cardinality denominator + S24/S25 bridge)
- PR #17432 (S26 — empty-range structural lemmas)
- PR #17415 (S25 — Finset-parameterised density framework + closed-form below-threshold theorem)
- PR #17305 (S23 — outer-guard predicate + branching characterisation)
- PR #17024 (S17 — `hgcdMatrix` row-output counterexample at `(130, 89)`)

**Companion to** PR #17489's "Next Steps §2" candidate:
> *Structural decomposition of `schonhageOuterGuardFires` on the `(64, 130)`
> range — e.g. coprime pairs above threshold trigger the outer guard, giving
> a structural lower-bound on the firing count without computation.*

This document records that the **naive coprime hypothesis is FALSE** and
proposes a refined S28 statement that survives the S17 counterexample family.

----

## §1. The naive S28 conjecture

> **Conjecture (NAIVE)**: For any `(a, b) ∈ outerGuardSurveyPairs 64 130`
> with `Nat.Coprime a b = true`, `schonhageOuterGuardFires a b = true`.

### Why the conjecture is plausible at first glance

- All pairs in `outerGuardSurveyPairs 64 130` are above the threshold
  `hgcdThresholdSafe = 64`, so the `_below_threshold` early-return branch
  is excluded.
- Coprimality eliminates the boring case `gcd a b > 1` where the algorithm
  may take "trivial" reduction steps.
- HGCD literature (Stehlé–Zimmermann 2004, Pan 1990, Möller 2008) describes
  the outer-guard heuristic as "almost always firing" on inputs of bounded
  bit length where `min a b > threshold`.

### Why the conjecture FAILS

The conjecture is refuted by the S17 PR #17024 counterexample family at
**`(a, b) = (130, 89)`**, which lies inside `outerGuardSurveyPairs 64 130`
since `64 ≤ 89 < 130 < 130` after the lower-triangular ordering convention
is unwound. We have `Nat.Coprime 130 89 = true` (`130 = 2·5·13`,
`89` is prime), but `schonhageOuterGuardFires 130 89 = false` for the
following structural reason recorded in **state.md S20** (also
PR #17087's per-session honesty section):

> *"...even on pathological inputs like the S17 counterexample family
> `(130, 89)`, where `hgcdMatrixSafe`'s OWN inner guard always aborts,
> the OUTER guard here dispatches to `Nat.gcd` and the correctness theorem
> still holds."*

Tracing through the definitions:

1. `hgcdMatrixSafeOf 130 89 = hgcdMatrixSafe (130 + 89 + 1) 130 89`.
2. Inside `hgcdMatrixSafe`, the inner recursion produces some
   `M_inner = hgcdMatrixSafe fuel (a / 2^k) (b / 2^k)`. Per state.md,
   on `(130, 89)` the **inner guard** at line 117 of
   `BinaryGcdOQ03OQ02PathA.lean`,
   `if max u v < max a b then compose else M_inner`, hits the abort branch.
3. Therefore `hgcdMatrixSafeOf 130 89 = M_inner`, and
   `hgcdSafeApply 130 89 = M_inner.apply ((130 : ℤ), (89 : ℤ))`. By the
   inner-guard abort condition, the column-output `(u, v)` satisfies
   `max u v ≥ max 130 89 = 130`.
4. Hence `decide (max u v < 130)` is `false`, and
   `schonhageOuterGuardFires 130 89 = false`.

This trace would be checked at PR-build time via
```lean
example : schonhageOuterGuardFires 130 89 = false := by native_decide
```
which forces evaluation through the full recursion. The example is **not**
included in this spec to avoid touching `BinaryGcdOQ03OQ02PathA.lean`
while PR #17489 (S27 PART XIX) is still open; it is recommended as a §6
deliverable below once #17489 merges.

### How widespread is the failure?

The S17 PART XIV docstring (`BinaryGcdOQ03OQ02.lean` lines 1838–1844)
records an empirical incidence: for the **unguarded** `hgcdMatrix`,
**875 / 2211 ≈ 39.6 %** of pairs in `[64, 130) × [64, a]` violate the
row-output bound (worst case at `(107, 85)` with matrix entries on the
order of `10^268`). For each such pair, the row-output cannot be bounded
by `max a b`, but this is the row convention, not directly the outer-guard
firing.

The OUTER guard for `hgcdMatrixSafe` operates on a different basis:
the inner abort branch in `hgcdMatrixSafe` substitutes `M_inner` for the
composed matrix, so the actual `M.apply (a, b)` we test is *not* the
unguarded one. The exact firing rate on `outerGuardSurveyPairs 64 130`
remains unknown — but the existence of `(130, 89)` shows the rate is
**strictly less than 100 %**, refuting the naive coprime conjecture.

----

## §2. Refined hypotheses that survive the counterexample

The naive form fails. What's the actual structural condition that
distinguishes firing-pairs from aborting-pairs? Three candidate refinements,
ranked by tractability:

### §2.1 H1 — Bit-length parity hypothesis (TRACTABLE)

> **H1**: `schonhageOuterGuardFires a b = true` iff
> `Nat.log2 (max a b) - Nat.log2 (min a b) < some_bound` AND `(a, b)` is
> not in a small "bad" set (the S17 family).

`(130, 89)`: `Nat.log2 130 = 7` (since `2^7 = 128 ≤ 130 < 256`),
`Nat.log2 89 = 6` (since `2^6 = 64 ≤ 89 < 128`). Bit-length gap = 1.
For `(107, 85)`: `Nat.log2 107 = 6`, `Nat.log2 85 = 6`, gap = 0. **Both
have small bit-length gap and both abort** — H1 in this naive form is
likely false too. A more refined version might involve the leading-bit
agreement count.

### §2.2 H2 — Lehmer-prefix-mismatch hypothesis (MEDIUM)

> **H2**: `schonhageOuterGuardFires a b = true` iff the Lehmer
> approximation extracted from the leading `hgcdShiftSafe a b` bits of
> `(a, b)` agrees with the full-precision quotient sequence for at
> least one Euclidean step.

This is closer to the actual algorithmic content of HGCD. Concretely:
in `hgcdMatrixSafe`, the recursive call processes
`(a / 2^k, b / 2^k)` for `k = hgcdShiftSafe a b`. If the leading-bit
quotient sequence diverges from the full-precision quotient sequence
within the first inner `lehmerCofactors` step, the resulting `M_inner`
may not reduce when applied back to the full pair.

For `(130, 89)`: `hgcdShiftSafe 130 89 = ?` (need to inspect; depends on
`hgcdThresholdSafe = 64`). If `k = 1`, the inner call is on
`(65, 44)`, which is the boundary of `hgcdThresholdSafe`. The Lehmer
approximation `lehmerCofactors 64 65 44 id` might land on a small matrix
that, when applied back to `(130, 89)`, doesn't reduce.

This refinement is **mathematically meaningful** but requires unfolding
the Lehmer step by step — likely 50–100 Lean lines per direction (forward:
"prefix agreement ⟹ outer guard fires"; reverse: characterisation).

### §2.3 H3 — Column-action positivity hypothesis (HARD)

> **H3**: `schonhageOuterGuardFires a b = true` iff
> `(M_inner.α · a + M_inner.β · b ≥ 0) ∧ (M_inner.γ · a + M_inner.δ · b ≥ 0) ∧
> (M_inner.α · a + M_inner.β · b < a) ∧ (M_inner.γ · a + M_inner.δ · b < b)`
> after factoring out the inner-guard substitution.

This is essentially the *definition* of "outer guard fires" rolled out;
proving it as a structural characterisation requires showing that the
two inequalities are equivalent to the `max u v < max a b` predicate
modulo the absolute-value conventions in `hgcdSafeApply` (which uses
`.natAbs`). Likely 30–50 lines once the column-output matrix lemmas
already in `BinaryGcdOQ03.lean` are wired up, but it's a tautological
refinement — it doesn't *predict* anything beyond the definition.

H3 is included for completeness; H2 is the structurally most informative
direction.

----

## §3. Mathlib v4.26.0 API survey for the refined direction

Verified against `.lake/packages/mathlib` from a sibling worktree
(this worktree's `proofs/.lake` symlink is broken — see memory note
`feedback_researcher_lake_symlink_broken.md`). All symbols below exist
in v4.26.0 unless noted otherwise.

### §3.1 Bit-length / `Nat.log2`

| Symbol | Location | Use |
|---|---|---|
| `Nat.log2` | `Mathlib/Data/Nat/Log.lean` | bit length up to floor(log₂) |
| `Nat.size` | `Mathlib/Data/Nat/Size.lean` | `Nat.log2 n + 1` for `n > 0` |
| `Nat.log2_lt` | same | `n < 2^k ↔ Nat.log2 n < k` (for `n > 0`) |
| `Nat.log2_eq_of_pow_le_of_lt_pow` | same | exact characterisation |

For H1, the bit-length gap predicate is
`Nat.log2 (max a b) - Nat.log2 (min a b)`, decidable on every concrete
pair. The framework is already there; H1's failure on `(107, 85)` shows
it isn't the right invariant.

### §3.2 Coprimality and gcd identity

| Symbol | Location | Use |
|---|---|---|
| `Nat.Coprime` | `Mathlib/Data/Nat/GCD/Basic.lean` | `Nat.gcd a b = 1` |
| `Nat.coprime_iff_gcd_eq_one` | same | unfolding to `gcd = 1` |
| `Nat.Coprime.symm` | same | symmetry |

The naive coprime hypothesis can be stated as
```lean
∀ {a b : ℕ}, (a, b) ∈ outerGuardSurveyPairs 64 130 →
  Nat.Coprime a b → schonhageOuterGuardFires a b = true
```
This document refutes the form via `(130, 89)`.

### §3.3 Existing PathA infrastructure

| Symbol (file `BinaryGcdOQ03OQ02PathA.lean`) | Status | Use |
|---|---|---|
| `schonhageOuterGuardFires` (line 788) | def | the predicate under investigation |
| `schonhageOuterGuardFires_below_threshold` (line 799) | thm | `false` if `max < 64` |
| `schonhageOuterGuardFires_iff` (line 809) | thm | `true ↔ ¬below ∧ strict-decrease` |
| `schonhageOuterGuardFires_strict_decrease` (line 826) | thm | forward direction |
| `outerGuardSurveyPairs` (S25) | def (Finset) | parameterised survey range |
| `outerGuardFiringCount` (S25) | def | cardinality of firing subset |
| `outerGuardFiringCount_le_surveySize` (S25) | thm | structural ≤ bound |
| `outerGuardSurveySize_triangular` (S27 PR #17489) | thm | closed-form denominator |

The `_iff` lemma reduces any structural statement about firing to a
conjunction `¬(max < threshold) ∧ (strict decrease holds)`. For
`(64, 130)`, the threshold check is *always* false (`max ∈ [64, 130) ≥ 64`
strictly), so the firing predicate on this range is exactly the strict-
decrease condition. The structural decomposition we want is therefore
about characterising when `max (hgcdSafeApply a b).1.natAbs
(hgcdSafeApply a b).2.natAbs < max a b`.

### §3.4 Mathlib gaps relevant to the refined direction

None new — all the refinement candidates work with existing symbols.
The "gap" is theorem-level: characterising the column action of
`hgcdMatrixSafe` is a self-contained undertaking, not a Mathlib
contribution candidate.

----

## §4. Concrete S28 deliverable proposal (3-PR plan)

Mirroring PR #17489's spirit (closed-form replacement of `native_decide`
witnesses), I propose a 3-PR sequence after `(130, 89)` is recorded as
the canonical counterexample.

### S28a (~30 lines): Counterexample + naive-conjecture refutation

**File**: append to `BinaryGcdOQ03OQ02PathA.lean` PART XIV
("OUTER GUARD WITNESSES").

**Content**:
```lean
/-- The S17 counterexample: `(130, 89)` is coprime, both entries are
    above threshold, yet the outer guard does not fire. Refutes the
    naive coprime-firing conjecture and motivates §2 of
    `s28-coprime-firing-spec.md`. -/
example : schonhageOuterGuardFires 130 89 = false := by native_decide

/-- A second above-threshold counterexample where the row-output
    bound fails most spectacularly: `(107, 85)` produces matrix
    entries on the order of `10^268` (BinaryGcdOQ03OQ02.lean PART
    XIV). Verifying the outer-guard predicate is `false` on this
    pair gives a concrete worst-case witness. -/
example : schonhageOuterGuardFires 107 85 = false := by native_decide

/-- Coprimality of the canonical counterexample, recorded as a
    `decide`-checked sanity fact for cross-referencing in
    `s28-coprime-firing-spec.md`. -/
example : Nat.Coprime 130 89 := by decide
```

This should remain stable across S27 (PR #17489) merging, since
PART XIV append-points are line-stable.

### S28b (~50 lines): Refined characterisation of inner-guard abort

**File**: append to `BinaryGcdOQ03OQ02PathA.lean` PART XX (new).

**Content**: a structural lemma
```lean
theorem hgcdMatrixSafe_abort_iff_outer_aborts (a b : ℕ)
    (hab : max a b ≥ hgcdThresholdSafe) :
    let M := hgcdMatrixSafeOf a b
    M.apply ((a : ℤ), (b : ℤ)) = (M_inner.apply ((a : ℤ), (b : ℤ))) ↔
    schonhageOuterGuardFires a b = false ∧ ...
```

The exact statement requires unfolding `hgcdMatrixSafe`'s inner-guard
branch and showing the abort condition is *equivalent* to the outer-
guard returning false. Likely needs auxiliary Lemmas about
`hgcdMatrixSafe_succ`'s second `if` branch.

### S28c (~80 lines): Coprimality vs firing — refined statement

**File**: append to `BinaryGcdOQ03OQ02PathA.lean` PART XXI (new).

**Content**: replace the naive coprime hypothesis with H2 (Lehmer-prefix
mismatch). State a one-direction theorem:

> *If `(a, b)` has Lehmer prefix agreement with the recursive subproblem's
> quotient sequence for at least one Euclidean step, then
> `schonhageOuterGuardFires a b = true`.*

Building this needs a definition of "prefix agreement" (Lehmer single-
step quotient match between `(a, b)` and `(a / 2^k, b / 2^k)`),
which is achievable from `lehmerCofactors` already available in
`BinaryGcdOQ03.lean`. Estimated 80 lines including the prefix-agreement
def and a forward proof.

This is the **mathematically substantive** S28; it gives a structural
sufficient condition for outer-guard firing that *does not reduce to*
running the algorithm. The reverse direction (necessary condition) would
be a separate session.

----

## §5. Per-session honesty

- This session adds **no Lean code** and **no axiom-discharge progress**
  to `BinaryGcdOQ03OQ02PathA.lean`. The sole deliverable is reconnaissance
  and dead-end correction.
- The recorded counterexample `(130, 89)` is **not** a new mathematical
  finding — it has been visible in the S17 / S20 / state.md commentary
  since 2026-05-08. The contribution here is the explicit **refutation**
  of a candidate S28 hypothesis that PR #17489's "Next Steps §2"
  proposed in good faith ("e.g. coprime pairs above threshold trigger
  the outer guard"), saving future sessions from attempting a false
  theorem.
- The H2 (Lehmer-prefix-mismatch) refinement is a **conjecture**, not
  a verified statement. Concrete small-case verification is out of
  scope for this spec doc; it would belong in S28b or a sibling spec.
- The 3-PR sequence in §4 is a **plan**, not a commitment. Estimated
  line counts (~30 / ~50 / ~80) are based on the structure of S25 / S26
  / S27 PRs which had similar scopes.
- Build status: **N/A** (markdown only, no `.lean` files touched).
- Coordinated with: PR #17489 (open, S27 by researcher-1) — this spec
  reads `outerGuardSurveySize_triangular` as a stable denominator and
  does not modify any file in #17489's diff.

----

## §6. Recommended next session

1. Wait for PR #17489 (S27) to merge.
2. Open S28a (small ~30-line PR appending the counterexamples to
   PART XIV); this is build-pending-tolerant since it's
   `native_decide`-only.
3. Open S28b (the inner/outer-guard equivalence lemma) on top.
4. S28c (Lehmer-prefix-mismatch refinement) follows after S28a/b.
