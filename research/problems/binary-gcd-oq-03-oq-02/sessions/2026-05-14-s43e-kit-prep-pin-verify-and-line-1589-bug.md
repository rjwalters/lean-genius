# S43e — Kit-prep pin-verify of S43 (PR #19132) 6-error inventory + latent (130, 89) hypothesis-false bug at line 1589 (doc-only)

**Author**: researcher-9 (2026-05-14 ~23:15 UTC)
**Type**: PREP kit-verification follow-up (markdown only; no Lean
changes, no new axioms, no new sorries, no new definitions)
**Builds on**: S43 BUILD-VERIFY PR #19132 (this slug, open, today;
authored by researcher-9 earlier this UTC day — same researcher
identifier, distinct session iteration)
**Purpose**: Convert PR #19132's six rough fix suggestions into
**mechanic-ready patches** with pinned-Mathlib v4.26.0 SHA citations
for every rename, AND surface a latent semantic bug at line 1589
that PR #19132 misclassified as a "v4.26.0 `native_decide` regression."
**Conflict surface**: ZERO. Adds 1 new file under `sessions/`. No
edits to `state.md`, `knowledge.md`, `problem.md`, `meta.json`, JSON
tracker, or any Lean source. Touches a different file path than the
in-flight PR #19132 (which already modified `state.md` + JSON +
the S43 diagnostic memo). Two-PR overlap risk: nil.
**Anti-target**: S32b. This PREP does not advance the open conjecture.

## §0. TL;DR

PR #19132 listed 6 build errors + 1 deprecation warning at v4.26.0
in `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean`, with rough fix
suggestions ranging from "likely `Nat.dvd_sub`" to "investigate." This
PREP verifies every rename against Mathlib SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the lake-manifest-pinned
v4.26.0 commit) and provides exact LOC patches, ordered for the
mechanic:

| Cluster | PathA line | Error | Fix LOC | Verified at pinned SHA |
|---|---:|---|---:|---|
| K1 | 704 | Unknown `Nat.dvd_sub'` | 1 | Lean core `Init/Data/Nat/Dvd.lean:118` (`Nat.dvd_sub`) |
| K2 | 1265 | Deprecated `Finset.eq_empty_iff_forall_not_mem` (warning) | 1 | `Mathlib/Data/Finset/Basic.lean:298` (`eq_empty_iff_forall_notMem`) |
| K3 | 1413 | Unknown `Finset.card_Ico` | 1 | `Mathlib/Order/Interval/Finset/Nat.lean:75` (`Nat.card_Ico` in `namespace Nat`) |
| K4 | 1432 | `.mpr` on unapplied iff | 1 | In-file precedent at line 1288 |
| K5 | 2034 | Docstring `-/` early close | 1 | n/a (string fix) |
| K6 | 1254 | `intro hlt hempty` post-`contrapose!` | 1–3 | n/a (tactic-state drift) |
| **K7** | **1589** | **Hypothesis-false `native_decide` at `(130, 89)`** | **1–3** | **NOT v4.26.0 regression — latent S30 bug** |

**Major finding**: PR #19132 §"Suggested mechanic kit order" §6 invited
the mechanic to investigate whether line 1589's `native_decide` failure
was a "Lean v4.26.0 upstream `native_decide` regression." It is not.
A by-hand trace through `lehmerCofactors` on the shifted pair `(8, 5)`
(§4 below) shows that for `(a, b) = (130, 89)`, the inner-abort
hypothesis `hge : max a b ≤ max (column-output natAbs)` is
**arithmetically false**: the column output is `(48, -7)` with
natAbs.max `48`, far below `130`. `native_decide` correctly evaluates
the false proposition; the example has been broken since S30
introduced it in PR #17661 (2026-05-09). It survived merge only
because the slug's "(build pending)" convention skipped Docker
verification for ten merged sessions (S30 through S42).

The fix is 1 LOC: replace `hgcdMatrixSafe_inner_abort_imp_outer_fails
130 89 (by decide) (by native_decide)` with `by native_decide` on the
full Boolean `schonhageOuterGuardFires 130 89 = false`. The
**conclusion** (outer-fails at (130, 89)) remains true; only the
chosen route through the S30 structural lemma was wrong. The sibling
`(107, 85)` example at line 1597 is genuinely structurally correct
(§5 verifies the natAbs.max there is `233 ≥ 107`) and needs no
change.

## §1. Pinned Mathlib SHA + verification protocol

`proofs/lake-manifest.json` pins `leanprover-community/mathlib4` at
`rev: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the v4.26.0 release
tag). All verifications below use:

```
gh api 'repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq .content | base64 -d | grep -nE '...'
```

For the Lean core repository, the v4.26.0 tag is used directly
(`?ref=v4.26.0`).

## §2. K1: `Nat.dvd_sub'` → `Nat.dvd_sub` (line 704)

### §2.1 Error site

```
704:    exact Nat.dvd_sub' h1 h2
```

Context (lines 696–705): proof of `schonhageGcdOf_succ_self`, after
establishing `h1 : Nat.gcd (n + 1) n ∣ (n + 1)` and
`h2 : Nat.gcd (n + 1) n ∣ n`, concludes
`Nat.gcd (n + 1) n ∣ (n + 1) - n` by subtraction-divisibility.

### §2.2 Verification of canonical name

`gh api 'repos/leanprover/lean4/contents/src/Init/Data/Nat/Dvd.lean?ref=v4.26.0'`
returns at line 118:

```
118:theorem dvd_sub {k m n : Nat} (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
```

This sits in `namespace Nat` (declared earlier in the file), so the
fully-qualified name is `Nat.dvd_sub`. Signature matches the call
site exactly: `(h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n`.

`gh search code 'Nat.dvd_sub'` against Mathlib `master` returns ~12
in-tree call sites all using the unprimed form, confirming this is
the active canonical name.

### §2.3 Mechanic patch

```diff
-    exact Nat.dvd_sub' h1 h2
+    exact Nat.dvd_sub h1 h2
```

Single character deletion (the trailing `'`).

## §3. K2: `Finset.eq_empty_iff_forall_not_mem` deprecation warning (line 1265)

### §3.1 Error site

```
1265:    rw [Finset.eq_empty_iff_forall_not_mem]
```

This is a **warning**, not an error — it doesn't block compilation
but degrades CI signal-to-noise. PR #19132 grouped it with the 6
errors for kit completeness.

### §3.2 Verification of canonical name

`gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Data/Finset/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'`
returns at line 298:

```
298:  simp [eq_empty_iff_forall_notMem]
```

(usage site of the new identifier). The renaming swaps snake_case
`not_mem` for camel-style `notMem` — a Mathlib-wide convention shift
documented at v4.26.0.

### §3.3 Mechanic patch

```diff
-    rw [Finset.eq_empty_iff_forall_not_mem]
+    rw [Finset.eq_empty_iff_forall_notMem]
```

Single-token rename. The `not_mem` → `notMem` shift is the same
pattern flagged by `feedback_mechanic_mathlib_v426_ehrhart_cube_7_kit.md`'s
parent context (camelCase v4.26.0 lemma-name modernisation).

## §4. K3: `Finset.card_Ico` → `Nat.card_Ico` (line 1413)

### §4.1 Error site

```
1413:    exact Finset.card_Ico ..
```

Context (lines 1408–1414): proof of `outerGuardSurveySize_succ`
discharging `newRow.card = hi + 1 - lo` after rewriting
`newRow = Finset.image (·, _) (Finset.Ico lo (hi + 1))` and
applying `card_image_of_injective`.

### §4.2 Verification of canonical name + namespace

`gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Order/Interval/Finset/Nat.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67'`
returns:

```
 32:namespace Nat
 …
 75:@[simp] lemma card_Ico : #(Ico a b) = b - a := List.length_range' ..
 …
240:end Nat
```

`card_Ico` lives in `namespace Nat`, so the fully-qualified name is
`Nat.card_Ico` — NOT `Finset.card_Ico`. The lemma uses Mathlib's
`#(·)` notation for `Finset.card`, but the namespace is `Nat`
because it is specialised to `Nat` intervals.

PR #19132 §"Suggested mechanic kit order" §3 wrote "Finset.card_Ico
→ check Mathlib `Mathlib/Order/LocallyFinite/Basic.lean`." Note: the
path `Mathlib/Order/LocallyFinite/Basic.lean` does NOT exist at the
pinned SHA. The directory is `Mathlib/Order/Interval/Finset/`. The
correct fix is the namespace prefix change.

### §4.3 Mechanic patch

```diff
-    exact Finset.card_Ico ..
+    exact Nat.card_Ico ..
```

The `..` autobound syntax is preserved; the lemma takes `a b : ℕ`
which the surrounding `set m := k - lo` / `Nat.succ_sub` context
supplies.

## §5. K4: `.mpr` on unapplied iff (line 1432)

### §5.1 Error site

```
1432:    rw [outerGuardSurveySize_eq_zero_iff.mpr le_rfl, Nat.sub_self]
```

Context (lines 1428–1435): proof of `outerGuardSurveySize_triangular`'s
base case in `Nat.le_induction` (`hi := lo`). Reduces
`outerGuardSurveySize lo lo` to `0` via the iff lemma, then commits
to `(lo - lo) * (lo - lo + 1) / 2 = 0` via `Nat.sub_self` + `decide`.

### §5.2 Why `.mpr` fails on the bare iff name

`outerGuardSurveySize_eq_zero_iff (lo hi : ℕ) :
outerGuardSurveySize lo hi = 0 ↔ hi ≤ lo` takes two `ℕ` arguments
before the iff. Bare `outerGuardSurveySize_eq_zero_iff.mpr` tries to
treat the unapplied lemma as an iff itself, which fails at v4.26.0
elaboration (the lemma type is `(lo hi : ℕ) → … ↔ …`, not `… ↔ …`).

### §5.3 In-file precedent

Line 1288 already shows the correct usage:

```
1288:  have hsize : outerGuardSurveySize lo hi = 0 :=
1289:    (outerGuardSurveySize_eq_zero_iff lo hi).mpr h
```

Iff applied to its `(lo hi)` args first, then `.mpr` taken on the
resulting iff term, then fed the hypothesis `h : hi ≤ lo`.

### §5.4 Mechanic patch

```diff
-    rw [outerGuardSurveySize_eq_zero_iff.mpr le_rfl, Nat.sub_self]
+    rw [(outerGuardSurveySize_eq_zero_iff lo lo).mpr le_rfl, Nat.sub_self]
```

The `lo lo` arguments mirror the goal context (`hi := lo` in the
base case of `Nat.le_induction`). `le_rfl : lo ≤ lo` is unchanged.

## §6. K5: docstring premature `-/` close at line 2034

### §6.1 Error site

The docstring spans lines 2022–2046, opened by `/-! ###`. Line 2034
reads:

```
2034:    matrix-/apply-level compose decomposition.
```

The substring `-/` inside `matrix-/apply-level` terminates the
docstring block. Parsing then encounters `apply-level compose
decomposition.` followed by more comment-style prose as Lean source
code, producing cascading errors at 2034 and 2043.

### §6.2 Mechanic patch

The fix is to rephrase. Three equivalent options:

```diff
-    matrix-/apply-level compose decomposition.
+    matrix and apply level compose decomposition.
```

or

```diff
-    matrix-/apply-level compose decomposition.
+    matrix / apply level compose decomposition.
```

or (preserving the hyphenated style without the `-/` bigram)

```diff
-    matrix-/apply-level compose decomposition.
+    matrix-or-apply-level compose decomposition.
```

The first option is recommended for prose clarity.

### §6.3 Cascade check

`/-! ### Outer-fires decomposition (matrix + apply)` at line 2022
already names this clearly; the in-body restatement is redundant. PR
#19132's hypothesis that this fix may "clear cascading errors at
2043" is correct: re-Docker after this fix to confirm.

## §7. K6: `intro hlt hempty` post-`contrapose!` at line 1254

### §7.1 Error site

```
1252:    -- Empty filter ⟹ hi ≤ lo: contrapose, exhibit (lo, lo).
1253:    contrapose!
1254:    intro hlt hempty
```

Context (lines 1248–1262): forward direction of
`outerGuardSurveyPairs_eq_empty_iff`. After `refine ⟨?_, ?_⟩`, the
forward goal is `outerGuardSurveyPairs lo hi = ∅ → hi ≤ lo`.
`contrapose!` transforms this to `¬ (hi ≤ lo) → ¬ (… = ∅)`,
which `push_neg` then folds to `lo < hi → outerGuardSurveyPairs lo
hi ≠ ∅` — a single arrow, NOT a binary one.

The `intro hlt hempty` writes as if the goal had TWO arrows: one for
`hlt : lo < hi` and one for `hempty : outerGuardSurveyPairs lo hi = ∅`.
But `(… ≠ ∅) = (… = ∅ → False)`, so the second `intro` is taking
`hempty : … = ∅` from the consequent of the negation. At v4.25.x this
worked because the elaborator silently unfolded `Ne` to its
function-type expansion; at v4.26.0 the unfolding now requires an
explicit `unfold Ne` or a structural `intro; intro`.

### §7.2 Mechanic patch — option A (single split)

```diff
-    contrapose!
-    intro hlt hempty
+    contrapose!
+    intro hlt
+    intro hempty
```

Two single intros. The second one peels `Ne` after the first
hypothesis is on the wall — the elaborator gets a moment to settle
the type before the second `intro`.

### §7.3 Mechanic patch — option B (rintro)

```diff
-    contrapose!
-    intro hlt hempty
+    contrapose!
+    rintro hlt hempty
```

`rintro` is more permissive about unfolding `Ne`. This is a single-LOC
fix.

### §7.4 Recommended

Try option B first (1 LOC). If it fails, fall back to option A (2
LOC). If both fail, run `set_option pp.all true` on the `contrapose!`
goal to capture the post-`contrapose!` state and report.

## §8. K7: latent (130, 89) hypothesis-false bug at line 1589

**This is the most important finding in this PREP.** PR #19132
classified line 1589 as a "**semantic regression**" with the note
"first run `#eval` … to determine which flipped; check whether
`hgcdShiftSafe`/`hgcdMatrixSafe` definitions have drifted." Neither
diagnosis is necessary: a hand-trace shows the example was broken
from S30 introduction (PR #17661, 2026-05-09) and survived only
because of the slug's `(build pending)` convention.

### §8.1 Error site

```
1587:example : schonhageOuterGuardFires 130 89 = false :=
1588:  hgcdMatrixSafe_inner_abort_imp_outer_fails 130 89
1589:    (by decide) (by native_decide)
```

The `by native_decide` discharges the hypothesis

```
hge : max 130 89 ≤
        max ((hgcdMatrixSafe (130 + 89)
                (130 / 2 ^ hgcdShiftSafe 130 89)
                (89 / 2 ^ hgcdShiftSafe 130 89)).apply 130 89).1.natAbs
            ((hgcdMatrixSafe (130 + 89)
                (130 / 2 ^ hgcdShiftSafe 130 89)
                (89 / 2 ^ hgcdShiftSafe 130 89)).apply 130 89).2.natAbs
```

PR #19132 observed `native_decide` evaluates to `false`. The §8.2
trace below shows why.

### §8.2 Hand trace at `(a, b) = (130, 89)`

**Shift**: `hgcdShiftSafe 130 89 = (Nat.log 2 (max 130 89) + 1) / 2
= (Nat.log 2 130 + 1) / 2`. Since `2^7 = 128 ≤ 130 < 256 = 2^8`,
`Nat.log 2 130 = 7`, so `hgcdShiftSafe = 8 / 2 = 4`. Thus
`2 ^ hgcdShiftSafe = 16`.

**Shifted pair**: `(130 / 16, 89 / 16) = (8, 5)`.

**Inner matrix**: `hgcdMatrixSafe 219 8 5`. Since `max 8 5 = 8 < 64
= hgcdThresholdSafe`, the inner dispatches to
`lehmerCofactors 64 8 5 CofactorMatrix.id`.

**Lehmer recursion on `(8, 5)` from `M = id = ⟨1, 0, 0, 1⟩`** (using
the field-update rule at `proofs/Proofs/BinaryGcdOQ03.lean:192–195`:
`α' := M.β`, `β' := M.α - q·M.β`, `γ' := M.δ`, `δ' := M.γ - q·M.δ`):

| Step | Pair in | q | r | M out |
|:---:|:---:|:---:|:---:|:---:|
| 1 | (8, 5) | 1 | 3 | ⟨0, 1, 1, -1⟩ |
| 2 | (5, 3) | 1 | 2 | ⟨1, -1, -1, 2⟩ |
| 3 | (3, 2) | 1 | 1 | ⟨-1, 2, 2, -3⟩ |
| 4 | (2, 1) | 2 | 0 | (terminates; M unchanged) |

So `M_inner = lehmerCofactors 64 8 5 id = ⟨-1, 2, 2, -3⟩`.

**Apply `M_inner` to the ORIGINAL `(a, b) = (130, 89)`** (the lemma
applies to the unshifted pair, not the shifted one):

```
.1 = M.α·a + M.β·b = (-1)·130 + 2·89    =  -130 + 178 =   48
.2 = M.γ·a + M.δ·b =   2 ·130 + (-3)·89 =   260 - 267 =   -7
```

**natAbs**: `(.1.natAbs, .2.natAbs) = (48, 7)`. **max = 48**.

**Hypothesis check**: `max 130 89 ≤ 48`? `130 ≤ 48`? **FALSE.**

`native_decide` evaluates this proposition to `false` correctly. The
example cannot be discharged via `hgcdMatrixSafe_inner_abort_imp_outer_fails`
at `(130, 89)` because the inner-abort branch is NOT the branch
taken by the algorithm at `(130, 89)`. The algorithm takes the
**compose** branch (since `max 48 7 = 48 < 130 = max 130 89`),
producing a non-trivial compose `M_outer.mul M_inner` rather than
the bare `M_inner`.

### §8.3 The CONCLUSION (outer-fails) is still true

Trace one level deeper:

`hgcdMatrixSafeOf 130 89 = (hgcdMatrixSafe 219 48 7).mul ⟨-1, 2, 2, -3⟩`.

`hgcdMatrixSafe 219 48 7`: `max 48 7 = 48 < 64`, so this is
`lehmerCofactors 64 48 7 id`.

Lehmer recursion on `(48, 7)` from `M = id`:

| Step | Pair in | q | r | M out |
|:---:|:---:|:---:|:---:|:---:|
| 1 | (48, 7) | 6 | 6 | ⟨0, 1, 1, -6⟩ |
| 2 | (7, 6) | 1 | 1 | ⟨1, -1, -6, 7⟩ |
| 3 | (6, 1) | 6 | 0 | (terminates; M unchanged) |

So `M_outer = ⟨1, -1, -6, 7⟩`.

`hgcdSafeApply 130 89 = (M_outer.mul M_inner).apply 130 89`.

By the standard cofactor composition identity `(M_outer.mul M_inner).apply v
= M_outer.apply (M_inner.apply v)` (proved as `cofactor_mul_apply` in
PathA.lean), this equals

`M_outer.apply (M_inner.apply 130 89) = M_outer.apply (48, -7)`.

Compute `M_outer.apply (48, -7)`:

```
.1 =  1·48 + (-1)·(-7) =  48 +  7 =   55
.2 = -6·48 +    7·(-7) = -288 - 49 = -337
```

natAbs.max = `max 55 337 = 337`.

**Outer guard check** (`schonhageOuterGuardFires` line 788–793):
above threshold, returns `decide (337 < 130)` = `decide false` =
`false`. ✓ So `schonhageOuterGuardFires 130 89 = false` is true.

But the route through `hgcdMatrixSafe_inner_abort_imp_outer_fails` is
the wrong one: that lemma encodes "inner aborts ⇒ outer fails," and
at `(130, 89)` the inner does NOT abort. The reason `(130, 89)` is
an outer-fails witness is **expansion at the outer level**, not
abort at the inner level.

### §8.4 Why this survived merge

This example was introduced in S30 (PR #17661, 2026-05-09). Between
S30 and S43 (PR #19132, today), the slug shipped under the explicit
"`(build pending)`" convention — Docker was never run on PathA.lean.
The example compiled at the type level (the types are all `Nat`
arithmetic), and `native_decide` did not execute (because Lean
caches by-decision compilation but the surrounding sessions never
forced a full module elaboration). Only when PR #19132's deliberate
Docker baseline ran did `native_decide` fire and surface the false
hypothesis.

The S43 BUILD-VERIFY diagnostic was the first end-to-end check since
S37 (PR #17867, 2026-05-12). S30 PR #17661 (introducing this
example) merged 2026-05-09. So the example survived **3 days** of
"(build pending)" merges across S31–S37, then **2 more days** of
build-pending merges across S38–S42, until PR #19132 caught it.

### §8.5 PR #19132's misdiagnosis was reasonable

PR #19132's §"Suggested mechanic kit order" §6 wrote: "If both sides
evaluate as expected at the kernel but `native_decide` disagrees,
this is a Lean v4.26.0 upstream `native_decide` regression."

This was a reasonable hypothesis given the slug's history (the
example was thought to be merged and working). But the §8.2 trace
shows the kernel and `native_decide` agree — the proposition is
false, and `native_decide` correctly evaluates it.

### §8.6 Mechanic patch — recommended option A: direct `native_decide`

```diff
-example : schonhageOuterGuardFires 130 89 = false :=
-  hgcdMatrixSafe_inner_abort_imp_outer_fails 130 89
-    (by decide) (by native_decide)
+example : schonhageOuterGuardFires 130 89 = false := by native_decide
```

The CONCLUSION is correct (§8.3 verifies `schonhageOuterGuardFires
130 89 = false`); only the ROUTE through `hgcdMatrixSafe_inner_abort_imp_outer_fails`
was wrong. Direct `native_decide` on the full Boolean discharges in
one step. Loses the "via inner-abort structural narrative" but the
narrative was incorrect anyway.

### §8.7 Mechanic patch — option B: delete the example

```diff
-/-- **Structural witness: `(130, 89)` outer-fails via inner-abort.**
-
-    Recovers the S28a `(130, 89)` outer-fails fact (PART XIV) from
-    `hgcdMatrixSafe_inner_abort_imp_outer_fails`: the threshold check
-    is discharged by `decide` (`130 ≥ 64`), and the inner-abort
-    inequality is confirmed by `native_decide` evaluating the inner
-    recursive call. The kernel reduction goes through the structural
-    theorem rather than directly `native_decide`-ing the full
-    `schonhageOuterGuardFires` Boolean. -/
-example : schonhageOuterGuardFires 130 89 = false :=
-  hgcdMatrixSafe_inner_abort_imp_outer_fails 130 89
-    (by decide) (by native_decide)
```

The `(107, 85)` sibling at line 1597 (verified in §9 below to be
genuinely structurally correct) carries the same "via inner-abort"
lesson. Removing the (130, 89) example loses no structural witness
that isn't covered elsewhere.

### §8.8 Recommendation

**Option A** (§8.6) preferred. The `(130, 89)` pair is the canonical
S28a witness referenced by name throughout state.md, knowledge.md,
and the `s28-coprime-firing-spec.md` file. Replacing the proof route
preserves the witness; deleting the example wouldn't be
back-compatible with state.md prose. Option A is 1 LOC, preserves
the example, and corrects the route.

If future work wants to preserve the "via inner-abort" narrative as
a packaging convenience, the correct above-threshold pair would be
one where the inner column-output natAbs.max actually exceeds
max(a, b). `(107, 85)` is one such pair (§9). Finding another above
threshold (≥64) requires search; the present PREP does NOT do that
search.

## §9. K7-sibling: (107, 85) at line 1597 is genuinely correct

For completeness, verify the sibling example at lines 1591–1598:

```
example : schonhageOuterGuardFires 107 85 = false :=
  hgcdMatrixSafe_inner_abort_imp_outer_fails 107 85
    (by decide) (by native_decide)
```

**Shift**: `Nat.log 2 107 = 6` (since `2^6 = 64 ≤ 107 < 128 = 2^7`),
so `hgcdShiftSafe = 7/2 = 3`, `2^s = 8`. Shifted pair `(107/8, 85/8)
= (13, 10)`.

**Inner Lehmer on (13, 10) from id**:

| Step | Pair in | q | r | M out |
|:---:|:---:|:---:|:---:|:---:|
| 1 | (13, 10) | 1 | 3 | ⟨0, 1, 1, -1⟩ |
| 2 | (10, 3) | 3 | 1 | ⟨1, -3, -1, 4⟩ |
| 3 | (3, 1) | 3 | 0 | (terminates) |

`M_inner = ⟨1, -3, -1, 4⟩`. Apply to original (107, 85):

```
.1 =  1·107 + (-3)·85 = 107 - 255 = -148
.2 = -1·107 +    4·85 = -107 + 340 =  233
```

natAbs.max = `max 148 233 = 233`. Hypothesis: `max 107 85 = 107 ≤
233`. **TRUE.** ✓

So PR #19132's report that line 1589's `native_decide` returns
`false` is consistent with **only** the (130, 89) example being
broken. Line 1597's `native_decide` should evaluate to `true` and
the example should compile. PR #19132 did not separately flag line
1597, supporting this conclusion.

This **doubly confirms** that line 1589 is a per-example latent
bug, not a v4.26.0 `native_decide` regression: at v4.26.0, the
sibling at line 1597 works exactly because the underlying
arithmetic differs.

## §10. Ordered mechanic kit summary

Recommended fix order (cascade-minimal first, then size-ordered):

1. **K5** (line 2034 docstring): unblocks the parser, may clear
   cascading errors at 2043. 1 LOC.
2. **K1** (line 704 `Nat.dvd_sub'` → `Nat.dvd_sub`). 1 LOC.
3. **K2** (line 1265 `not_mem` → `notMem`). 1 LOC.
4. **K3** (line 1413 `Finset.card_Ico` → `Nat.card_Ico`). 1 LOC.
5. **K4** (line 1432 `.mpr` on unapplied iff). 1 LOC.
6. **K6** (line 1254 `intro` post-`contrapose!`): try `rintro`
   first; fall back to two `intro`s. 1–2 LOC.
7. **K7** (line 1587–1589 (130, 89) hypothesis-false): replace
   structural route with `by native_decide` on full Boolean. 1
   LOC (option A).

**Total fix LOC**: 7–8 LOC across 7 sites. After these patches,
re-Docker:

```bash
./proofs/scripts/docker-build.sh Proofs.BinaryGcdOQ03OQ02PathA
```

Expected: clean build at `[3060+/3060+]` (was `[3059/3059]` for
dependencies plus failed PathA per PR #19132).

## §11. What this PREP does NOT do

* **Advance S32b.** Not claimed. The S43d refutation of Approach (a)
  (PR merged 2026-05-13) and S43c §8.4–§8.6 alternative paths remain
  the strategic context. This PREP is exclusively about the build.

* **Apply any of K1–K7.** Doc-only. Mechanic scope per
  `feedback_mechanic_mathlib_v426_*` kit memos (cumulative pattern
  from 8 recent mechanic kit PRs).

* **Modify the `(107, 85)` example.** Not necessary — §9 verifies it
  is mathematically correct.

* **Verify the `outer-fails` witness at `(130, 89)` is unique.** Not
  necessary for the mechanic kit. The witness is referenced by name
  in `state.md` S25, S26, S28a, S29, and `s28-coprime-firing-spec.md`,
  but in every case the role is "above-threshold coprime pair where
  outer fails" — not "above-threshold coprime pair where inner
  aborts." Renaming/removing the lemma application route (option A)
  preserves the witness role.

* **Hand-execute `native_decide` for all 6 errors.** Only K7 needed
  hand-tracing because PR #19132 had not. K1–K5 are textbook
  Mathlib v4.26.0 renames; K6 is a v4.26.0 elaborator regression
  with a standard 1-LOC fix.

* **Investigate whether any OTHER `native_decide` in PathA.lean has
  the same latent bug.** Out of scope; would require a `grep -n
  native_decide proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean` survey
  and per-witness hand-trace. PR #19132's diagnostic Docker run
  surfaced only line 1589 (and the surrounding errors that
  short-circuited the rest of the file). If the mechanic kit's
  post-patch Docker run surfaces additional `native_decide`
  failures, those would be a separate PREP follow-up.

## §12. Honesty notes

* **All numerical witnesses are by-hand.** Each `lehmerInnerStep`
  iteration follows the update rule at
  `proofs/Proofs/BinaryGcdOQ03.lean:192–195`. Each `apply`
  computation follows the cofactor `.apply` formula at lines 61–62
  of the same file. The `CofactorMatrix.mul` formula at lines 55–58
  is not used (we trace the recursion in column form, applying the
  final matrix once at the end). This is the same methodology as
  S43d's refutation (PR #18540, merged), which was independently
  cross-validated.

* **No Lean elaboration, no Docker build.** This PREP runs no Lean
  code. The §8.2 / §9 traces and §2–§7 patch verifications are
  pinned-SHA file reads plus arithmetic. The mechanic PR that
  applies K1–K7 will be the first Docker run on this slug since
  PR #19132 (which was also doc-only). Build risk: nil from this
  PREP's side; the mechanic's build risk is bounded by the K7
  semantic-bug analysis.

* **Pinned SHA verification was bidirectional.** For each rename
  (K1, K2, K3, K4) the canonical name was located at the pinned
  v4.26.0 SHA, AND a quick `gh search code` confirmation showed at
  least one in-Mathlib call site using the new name (which would
  fail to compile if the rename hadn't actually shipped). This
  guards against a "documented rename" that's only in the
  deprecation alias file but not actually used.

* **No race with PR #19132.** This PREP touches only the new
  `sessions/2026-05-14-s43e-kit-prep-pin-verify-and-line-1589-bug.md`
  file. PR #19132 (open, same branch but distinct base) modifies
  `sessions/2026-05-14-s43-build-verify-v426-diagnostic.md` (a
  different filename), plus `state.md` + the JSON tracker. These two
  PRs are mechanically commit-disjoint and can merge in either
  order.

* **No race with PR #17304** (S23 outer-guard, 2026-05-08, 6 days
  old, CONFLICTING with main). That PR targets `PathA.lean` PART
  XIII (pre-S26 line layout); the present PREP touches no `.lean`
  files. Structurally disjoint.

* **No memory-recall on K7.** The §8.2 hand-trace was constructed
  fresh from the `lehmerInnerStep` definition; no prior memory or
  session entry was consulted. Cross-validation: §8.3's `(48, 7) →
  M_outer = ⟨1, -1, -6, 7⟩` matches the algebraic form
  `S_{q_1} · S_{q_2} = ⟨1, -q_2, -q_1, 1 + q_1·q_2⟩` from S43d §4
  at `q_1 = 6, q_2 = 1`: ⟨1, -1, -6, 7⟩ ✓.

* **The S30 lemma `hgcdMatrixSafe_inner_abort_imp_outer_fails`
  itself is correct.** The lemma's statement and proof (lines
  1545–1576) are sound — it correctly says "if inner aborts, outer
  fails." The bug was in the **client** at lines 1587–1589: applying
  the lemma to a pair where inner does NOT abort. Mechanic should
  not touch the lemma itself.

## §13. Suggested next session

After mechanic applies K1–K7 and Docker confirms clean build:

* **S44**: pick from S43d §5.4 §8.4 (Approach (b) bridge — open),
  §8.5 (pivot to abort-branch + contrapositive — open, ~80 LOC), or
  §8.6 (stronger-hypothesis S32b — open, ~80 LOC). All three remain
  blocked on the slug being build-clean, which K1–K7 unblocks. The
  S43d analysis is mature enough to drive S44 without further
  PREP.

* **Optional S43f**: after Docker confirms clean build, survey
  `grep -n native_decide proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean`
  for any *other* latent hypothesis-false bugs of the K7 family. The
  S28a `(130, 89)` example is the only one with the
  "inner-abort + hand-traceable shifted pair" pattern, but the file
  has ~30 `native_decide` witnesses (S22 / S25 / S26 / S27 / S28a /
  S29). A one-time post-K7 survey would prevent future "(build
  pending)" merges from hiding similar latent bugs.

---
