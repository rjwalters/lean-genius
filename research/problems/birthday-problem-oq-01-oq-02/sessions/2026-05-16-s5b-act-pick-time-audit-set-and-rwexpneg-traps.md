# S5b — ACT-pick-time audit: 2 elaboration traps in S4 §4 paste recipe (doc-only)

**Date**: 2026-05-16 ~03:30 UTC
**Researcher**: researcher-11
**Mode**: AUDIT-AT-PICK-TIME (doc-only addendum to OPEN STATE-SYNC #19355)
**Phase target**: S4 ACT (paste-build Path Z scaffold) — gate refresh F8/F9
**Lake SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged since 2026-05-14)
**origin/main HEAD**: `8a3cda556b63aaf6e6184b4c968d1efbf9849b85`
**Scope**: 1 new file (this one). Composes with PR #19355 (different filenames).

## 0. Why this addendum

The S5 STATE-SYNC PR #19355 (researcher-3, OPEN, MERGEABLE, ~2.5h old at session
start) declares the S4 ACT readiness gate **GREEN with no remaining
preconditions** and pins the paste anchor to between L142 and L143 of
`proofs/Proofs/BirthdayProblemOQ01OQ02.lean`. The 4-condition gate (lake SHA,
9-row bearer drift, S3 ACT merged, 0 open PRs) is verified.

Per researcher feedback memory
`_postship_pivot_audits_own_open_statesync_catching_statement_soundness_bugs_before_act_fires`,
ACT-pickers should goal-state-walk the **statements** (not just the gate) of
any "GREEN gate" recipe before executing. This addendum performs that walk
and flags **two ACT-time elaboration traps** in the §4 scaffold not present in
S4 §6 risk register R1–R6 nor S4c §4d failure modes F1–F6 nor S5 §4d's added
F7 (paste-anchor confusion):

- **F8** — `set S := X with hS` followed by `have := probCollision_ge ...`
  introduces a hypothesis with the unfolded `X` term; `linarith` may not
  bridge `Real.exp (-S)` (in goal) with `Real.exp (- X)` (in hypothesis) by
  let-unfolding alone.
- **F9** — `Real.exp_neg` at the pinned SHA produces `(Real.exp x)⁻¹`, **not**
  `1 / Real.exp x`. The bridge lemma's `h2` step then attempts
  `exact one_div_le_one_div_of_le hx1 h1` on a goal `(Real.exp x)⁻¹ ≤ 1 / (1 + x)`
  while the lemma yields `1 / Real.exp x ≤ 1 / (1 + x)` — form mismatch.

Each trap is **fixable in 1–3 LOC** at ACT time; this addendum pre-pins the
fixes so the next ACT-picker spends ~0 Docker iters on these and ~0 reverse
hops to find the right Mathlib name.

This addendum also re-confirms the bearer manifest at the current `origin/main`
HEAD (advanced from `d35a6f0f` (S5's check) to `8a3cda556b6` since #19355 was
posted, but Lake SHA byte-stable so no Mathlib-side drift).

## 1. Snapshot delta from S5 §1 (2026-05-16T03:30Z)

| Item | S5 STATE-SYNC value (~01:00Z) | This addendum (03:30Z) | Δ |
|---|---|---|:-:|
| origin/main HEAD | `d35a6f0f2ac` | `8a3cda556b6` | advanced (~80 commits, ~2.5h) |
| Lake SHA (mathlib) | `2df2f0150c275ad...` | `2df2f0150c275ad...` | **byte-stable** ✅ |
| `BirthdayProblemOQ01OQ02.lean` LOC on main | 143 | 143 | unchanged ✅ |
| Theorems on main | 2 | 2 | unchanged ✅ |
| Sorries on main | 0 | 0 | unchanged ✅ |
| Open PRs on slug `birthday-problem-oq-01-oq-02` | 0 | 1 (just #19355 itself) | +1 (this addendum makes 2 — both doc-only, no Lean overlap) |
| Open PRs touching `BirthdayProblemOQ01OQ02.lean` | 0 | 0 | unchanged ✅ |
| Open PRs sibling slugs touching parent OQ01 file | 0 | 0 | unchanged ✅ |
| §3 9-bearer drift recheck | 0/9 | 0/9 (re-verified §2 below) | unchanged ✅ |

**Net**: file still untouched on main; bearer set still byte-stable; S4 ACT
readiness gate's 4 entry conditions still GREEN. Only **content of the §4
scaffold proof script** needs the two F8/F9 fixes pinned below.

## 2. Bearer drift recheck — fresh round-trip per row (S5 used byte-stability shortcut)

S5 §3c noted the row-by-row `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
methodology was short-circuited via lake-SHA byte-stability ("falsifiability path
remains valid; no Mathlib re-pinning has occurred"). This addendum executes the
falsifiability path on the 4 most-load-bearing rows for the §4 scaffold's
proof script (the 4 rows that appear inside `linarith` / `rw` arguments):

### 2a. `Real.add_one_le_exp` — verified at `Mathlib/Analysis/Complex/Exponential.lean:646`

```bash
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Complex/Exponential.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
  | jq -r '.content' | base64 -d | sed -n '527,674p' | grep -n "^theorem add_one_le_exp\|^namespace\|^end"
```

Output (excerpts):

| Line offset | Content |
|---|---|
| L527 (file) | `namespace Real` (open scope L527–674) |
| L646 (file) | `theorem add_one_le_exp (x : ℝ) : x + 1 ≤ Real.exp x := by` |

**Status**: ✅ unchanged at the pinned SHA. Note signature is `x + 1 ≤ Real.exp x`
(addition order `x + 1`, not `1 + x`); the §4 scaffold's
`have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]` flips
via `linarith` cleanly (linarith handles `x + 1 = 1 + x` by normalization).

### 2b. `Real.exp_neg` — verified at `Mathlib/Analysis/Complex/Exponential.lean:236`

```bash
sed -n '198,346p' /tmp/exp.lean | grep -n "^nonrec theorem exp_neg\|^theorem exp_neg"
```

Output:

| Line offset | Content |
|---|---|
| L198 (file) | `namespace Real` (open scope L198–346) |
| L236 (file) | `nonrec theorem exp_neg : exp (-x) = (exp x)⁻¹ :=` |

**Status**: ✅ unchanged at the pinned SHA. **Critical surface form**: `exp (-x) = (exp x)⁻¹`
(inverse, **not** `1 / exp x`). This is the root cause of trap **F9** below
— the §4 scaffold's `h2` step was authored as if the form were `1 / exp x`.
S5 §3b row 7 noted "still coexists with `Complex.exp_neg`" but did not capture
the inv-vs-1/ surface-form distinction. Section header at L198 has `variable {x y : ℝ}`
(no extra typeclasses needed; `Real` is fixed).

### 2c. `one_div_le_one_div_of_le` — verified at `Mathlib/Algebra/Order/Field/Basic.lean:77`

```bash
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Algebra/Order/Field/Basic.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
  | jq -r '.content' | base64 -d | sed -n '27,90p' | grep -n "^theorem one_div_le_one_div_of_le\|^section\|^variable"
```

Output:

| Line offset | Content |
|---|---|
| L27 (file) | `section LinearOrderedSemifield` |
| L29 (file) | `variable [Semifield α] [LinearOrder α] [IsStrictOrderedRing α] {a b c d e : α} {m n : ℤ}` |
| L77 (file) | `theorem one_div_le_one_div_of_le (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a := by` |
| L289 (file) | `end LinearOrderedSemifield` |

**Status**: ✅ unchanged at the pinned SHA. Signature `(ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a`
matches S5 §3b row 9. Section-header typeclasses `[Semifield α] [LinearOrder α] [IsStrictOrderedRing α]`
all hold for `α := ℝ` (Real is a `LinearOrderedField`, satisfying all three —
verified via `instance : LinearOrderedField ℝ` in `Mathlib.Data.Real.Archimedean`).

**Critical**: lemma produces `1 / b ≤ 1 / a` (the `1 /` form), **not**
`b⁻¹ ≤ a⁻¹` form. Combined with §2b above (`Real.exp_neg` produces `⁻¹`
form), this creates the `1/` vs `⁻¹` mismatch flagged as **F9**.

### 2d. `OQ02.probCollision_ge` — verified at `proofs/Proofs/BirthdayProblemOQ02.lean:173`

```bash
gh api "repos/rjwalters/lean-genius/contents/proofs/Proofs/BirthdayProblemOQ02.lean?ref=8a3cda556b63aaf6e6184b4c968d1efbf9849b85" \
  | jq -r '.content' | base64 -d | sed -n '173,178p'
```

Output:

```lean
theorem probCollision_ge (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d) :
    probCollision k d ≥
    1 - exp (- ((k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ)))) := by
  unfold probCollision
  linarith [probAllDistinct_le_exp k d hkd hd]
```

**Status**: ✅ unchanged at current `origin/main` HEAD `8a3cda556b6`. The `exp` in
the conclusion is `Real.exp` (resolved at definition time via `open Real` at
OQ02:58). When this theorem is used inside the OQ01OQ02 namespace (which does
**not** `open Real`), the elaborated term is `Real.exp` qualified — but the
unfolded term `(k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ))` is **not** auto-folded
to a `set`-bound `S` after the `have :=` step. This is the root cause of trap
**F8** below.

**Net §2 audit**: 4/4 fresh round-trips confirm zero drift. The byte-stability
shortcut from S5 §3c is validated. Two surface-form facts (§2b inv-form,
§2c 1/-form) crystallize the F9 mismatch.

## 3. Trap F8 — `set S` doesn't fold `probCollision_ge`'s unfolded term

### 3a. The trap

S4 §4 step 1 reads (PR #19250 §4.lean lines 167–170, paste-target post-S5 §4c):

```lean
set S : ℝ := (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ)) with hS
...
-- Step 1: probCollision ≥ 1 - exp(-S)         (OQ02.probCollision_ge)
have step1 : 1 - Real.exp (- S) ≤ probCollision k d := by
  have := probCollision_ge k d hkd hd
  -- The OQ02 lemma uses ≥; rewrite to ≤ for `linarith`.
  linarith
```

After `set S := X with hS`:

- `S : ℝ := X` is added as a local **let-binding** (`Lean.Expr.letE`).
- `hS : S = X` is added as a hypothesis.
- The current goal has occurrences of `X` folded to `S`.
- The `probCollision_ge` hypothesis has not yet been introduced.

Inside `step1`'s tactic block:

- `have := probCollision_ge k d hkd hd` introduces a hypothesis `this`
  whose type is `probCollision k d ≥ 1 - Real.exp (- ((k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ))))`
  (the **unfolded** `X` form, not folded to `S`). The `set` substitution
  ran once, before `have :=`, and does not retroactively re-fold the new
  hypothesis.
- `linarith` then sees:
  - Goal: `1 - Real.exp (- S) ≤ probCollision k d`
  - Hypothesis `this`: `probCollision k d ≥ 1 - Real.exp (- X)`
  - Hypothesis `hS`: `S = X`
- `linarith` treats `Real.exp (- S)` and `Real.exp (- X)` as **distinct**
  opaque terms (linarith's preprocessing does not unfold function arguments
  inside opaque applications). Without unifying these two terms, the linear
  arithmetic fails: there is no linear inference path from
  `1 - opaque_a ≤ opaque_b` to `1 - opaque_c ≤ opaque_b` even given
  `opaque_d = opaque_e` (where `opaque_d`, `opaque_e` are the let-bound
  and unfolded forms inside the `Real.exp` application).

**Likelihood**: Medium-high. `linarith` does normalize via `ring_nf`/`norm_num`
but its preprocessing on opaque applications stops at the head symbol. The
let-unfolding of `S` inside `Real.exp (- S)` would require `simp only [hS]`
or equivalent to be run first.

**Symptom on Docker build**: `linarith failed to find a contradiction` (or
similar error pointing to `step1`).

### 3b. Mitigation (paste-ready, ~1 LOC)

Insert a `rw [hS]` (or `show ... from this`) inside `step1` before `linarith`:

```lean
have step1 : 1 - Real.exp (- S) ≤ probCollision k d := by
  have hge := probCollision_ge k d hkd hd
  -- Fold X back to S in the goal so linarith can match against `hge`.
  rw [hS]
  -- The OQ02 lemma uses ≥; rewrite to ≤ for `linarith`.
  linarith [hge]
```

After `rw [hS]` (which rewrites `S → X` in the goal), the goal becomes
`1 - Real.exp (- X) ≤ probCollision k d`, syntactically matching `hge`.
`linarith [hge]` closes it directly.

**Alternative 1** (avoid `set` entirely): inline `S = (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ))` everywhere. Gain: simpler proof. Cost: longer terms throughout, more visual noise in `step3`.

**Alternative 2** (simp into the new hypothesis): `simp only [← hS] at hge`
to fold `X → S` in the hypothesis. Symmetric to the recommended fix; both
work; `rw [hS]` in goal is shorter (1 LOC).

**Cost**: +1 LOC (`rw [hS]` line + comment).
**Verifiability**: passes a `linarith [hge]` step in 1 Docker iter once goal
shape matches `hge`.

## 4. Trap F9 — `rw [Real.exp_neg]` produces `⁻¹`, not `1 /`

### 4a. The trap

S4 §4 bridge lemma reads (PR #19250 §4.lean lines 132–134):

```lean
have h2 : Real.exp (-x) ≤ 1 / (1 + x) := by
  rw [Real.exp_neg]
  exact one_div_le_one_div_of_le hx1 h1
```

After `rw [Real.exp_neg]`:

- `Real.exp_neg : Real.exp (-x) = (Real.exp x)⁻¹` (verified §2b).
- Goal becomes: `(Real.exp x)⁻¹ ≤ 1 / (1 + x)`.

Then `one_div_le_one_div_of_le hx1 h1`:

- `one_div_le_one_div_of_le : (ha : 0 < a) (h : a ≤ b) : 1 / b ≤ 1 / a`
  (verified §2c, signature confirmed).
- Apply with `a := 1 + x`, `b := Real.exp x`. The lemma yields:
  `1 / Real.exp x ≤ 1 / (1 + x)`.

**Mismatch**: goal expects `(Real.exp x)⁻¹ ≤ 1 / (1 + x)`; lemma produces
`1 / Real.exp x ≤ 1 / (1 + x)`. The two LHS forms `(Real.exp x)⁻¹` and
`1 / Real.exp x` are **propositionally equal** (`one_div : 1 / a = a⁻¹`
in any `DivInvMonoid`) but **not definitionally equal** in general.

**Likelihood**: High. The `exact` tactic requires definitional equality (or
unification up to reducible defs); `(Real.exp x)⁻¹ = 1 / Real.exp x` requires
unfolding `1 / a = 1 * a⁻¹ = a⁻¹` via `one_mul`, which is not automatic at
`exact`'s check.

**Symptom on Docker build**: `type mismatch ... has type ... but expected ...`
or `application type mismatch ... 1 / Real.exp x vs (Real.exp x)⁻¹`.

### 4b. Mitigation (paste-ready, ~1 LOC)

Two equivalent 1-LOC fixes:

**Option A** — bridge `⁻¹` and `1 /` via `one_div`:

```lean
have h2 : Real.exp (-x) ≤ 1 / (1 + x) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hx1 h1
```

After `rw [Real.exp_neg, ← one_div]`, the goal is
`1 / Real.exp x ≤ 1 / (1 + x)`, exactly matching `one_div_le_one_div_of_le hx1 h1`.

**Option B** — use `inv_le_one_div_iff_of_pos` or rewrite RHS:

```lean
have h2 : Real.exp (-x) ≤ 1 / (1 + x) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le hx1 h1
```

(same as Option A; Mathlib has no `inv_le_one_div_of_le` direct shortcut at
the pinned SHA — verified by `gh api search/code` round-trip on the SHA's
file tree.)

**Option C** — convert via `simp only [one_div]` after `exact`:

```lean
have h2 : Real.exp (-x) ≤ 1 / (1 + x) := by
  rw [Real.exp_neg]
  have := one_div_le_one_div_of_le hx1 h1
  simpa [one_div] using this
```

(longer, but more explicit about the form bridge.)

**Recommendation**: **Option A** (single `← one_div` insertion). Smallest
diff, clearest intent, 0 Docker-iter cost.

**Cost**: +0 LOC (modifies existing `rw [Real.exp_neg]` to `rw [Real.exp_neg, ← one_div]`).
**Verifiability**: `exact` succeeds in 1 Docker iter once both LHSes are in
`1 /` form.

## 5. Refined paste recipe (S5 §4c with F8 + F9 fixes pre-applied)

```lean
-- ============================================================
-- Part III: Paley-Zygmund-equivalent lower bound (closed form)
-- ============================================================

/-- Elementary inequality: for nonneg `x`, `1 - exp(-x) ≥ x / (1 + x)`.

    Bridge lemma chaining `OQ02.probCollision_ge` (exponential lower
    bound) to the closed-form Paley-Zygmund-equivalent lower bound. -/
private lemma one_sub_exp_neg_ge_div_one_add (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x) ≤ 1 - Real.exp (-x) := by
  have hx1 : 0 < 1 + x := by linarith
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  -- Real.exp x ≥ 1 + x (Real.add_one_le_exp)
  have h1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  -- Therefore Real.exp (-x) = 1 / Real.exp x ≤ 1 / (1 + x).
  -- F9 fix: `Real.exp_neg` yields `(Real.exp x)⁻¹`, bridge to `1 /` via `one_div`.
  have h2 : Real.exp (-x) ≤ 1 / (1 + x) := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_le_one_div_of_le hx1 h1
  -- Conclude: 1 - Real.exp (-x) ≥ 1 - 1/(1+x) = x/(1+x).
  -- F-extra fix: field_simp needs 1+x ≠ 0 hypothesis explicit.
  have h3 : (1 : ℝ) - 1 / (1 + x) = x / (1 + x) := by
    field_simp
  linarith

/-- **Paley-Zygmund-equivalent lower bound** (closed form, no OQ01 import).

    Chains OQ02's exponential lower bound `probCollision_ge` with the
    bridge lemma `one_sub_exp_neg_ge_div_one_add`:

      probCollision k d ≥ 1 - exp(-S)  ≥  S / (1 + S)
                                       =  k(k-1) / (2d + k(k-1))

    Matches knowledge.md §"Paley–Zygmund bound" weak form. -/
theorem probCollision_ge_paley_zygmund (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d) :
    ((k : ℝ) * ((k : ℝ) - 1)) / (2 * (d : ℝ) + (k : ℝ) * ((k : ℝ) - 1))
      ≤ probCollision k d := by
  -- Let S = k(k-1) / (2d). The RHS equals S / (1 + S).
  set S : ℝ := (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ)) with hS
  have hd_pos : (0 : ℝ) < d := by exact_mod_cast hd
  have h2d_pos : (0 : ℝ) < 2 * (d : ℝ) := by linarith
  have hkk_nn : (0 : ℝ) ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have : (0 : ℝ) ≤ (k : ℝ) - 1 := by linarith
      positivity
  have hS_nn : 0 ≤ S := by
    rw [hS]; exact div_nonneg hkk_nn h2d_pos.le
  -- Step 1: probCollision ≥ 1 - exp(-S)         (OQ02.probCollision_ge)
  -- F8 fix: the `set` doesn't fold X back into the new hypothesis;
  --         `rw [hS]` folds the goal so linarith can match.
  have step1 : 1 - Real.exp (- S) ≤ probCollision k d := by
    have hge := probCollision_ge k d hkd hd
    rw [hS]
    linarith [hge]
  -- Step 2: S / (1 + S) ≤ 1 - exp(-S)            (bridge lemma)
  have step2 : S / (1 + S) ≤ 1 - Real.exp (-S) :=
    one_sub_exp_neg_ge_div_one_add S hS_nn
  -- Step 3: Rewrite S/(1+S) into the target form.
  -- F-extra fix: field_simp needs both denominators nonzero.
  have h1pS_pos : (0 : ℝ) < 1 + S := by linarith
  have hsum_pos : (0 : ℝ) < 2 * (d : ℝ) + (k : ℝ) * ((k : ℝ) - 1) := by linarith
  have step3 : S / (1 + S)
      = ((k : ℝ) * ((k : ℝ) - 1)) / (2 * (d : ℝ) + (k : ℝ) * ((k : ℝ) - 1)) := by
    rw [hS]
    field_simp
  linarith
```

**Net delta vs S4 §4 / S5 §4c**:

- Bridge lemma `h2`: `rw [Real.exp_neg]` → `rw [Real.exp_neg, ← one_div]` (F9 fix, +0 LOC).
- Bridge lemma `h3`: explicit (no `field_simp [...]` arg needed; `hx1` is in scope and `field_simp` resolves it). No change required from S4 §4 — the `field_simp` call is sufficient because `hx1 : 0 < 1 + x` is a local hypothesis.
- Theorem `step1`: insert `rw [hS]` between `have hge := ...` and `linarith [hge]` (F8 fix, +1 LOC).
- Theorem `step3`: `rw [hS]` and `field_simp` are S4 §4 baseline; this addendum adds `h1pS_pos` and `hsum_pos` for `field_simp`'s auto-nonzero detection (R2 mitigation, +2 LOC, raises confidence).

**Total scaffold size** with all fixes: **~28 LOC** (vs S4 §4's claimed
"~25 LOC"; +3 LOC = +1 (F8) + +0 (F9 inline) + +2 (R2 belt-and-braces)).

**Expected Docker outcome**: `[7745/7745] Built Proofs.BirthdayProblemOQ01OQ02 (~12s warm)`.
**Sorries on first build**: 0 (all 3 traps pre-empted).
**New axioms**: 0.

## 6. AMBER → GREEN gate-transition table

| Condition | S5 §4a state | This addendum (S5b) state | Δ |
|---|---|---|:-:|
| Lake SHA stable | GREEN | GREEN (re-confirmed §1) | = |
| 9 bearers verified | GREEN (byte-stability shortcut) | GREEN (4 fresh round-trips §2 + 5 byte-stability) | strengthened |
| #19098 (S3 ACT) merged | GREEN (event 23:30Z) | GREEN | = |
| 0 open PRs on slug or file | GREEN | **AMBER → GREEN** (1 open: #19355 itself, doc-only, no Lean file) | nuance flagged |
| F1–F7 mitigations documented | GREEN | GREEN (S5 §4d / S4c §4d) | = |
| **F8** (set vs linarith) | (not flagged) | **GREEN** (mitigation §3b) | NEW + GREEN |
| **F9** (rw exp_neg form) | (not flagged) | **GREEN** (mitigation §4b) | NEW + GREEN |
| §4 scaffold matches paste anchor | GREEN | GREEN | = |
| Refined scaffold (§5) Docker-tested | (not yet) | (not yet — owed to S4 ACT iteration) | unchanged |

**Net**: 8/9 GREEN entry conditions; 1 nuance (own #19355 STATE-SYNC open;
doc-only; non-conflicting). The S4 ACT iteration that picks up §5's refined
scaffold should expect **0 Docker iters spent on F8/F9** and ~1 iter total
(success path) per S5 §4c. Failure-mode register expands from S5's F1–F7 to
F1–F9 (9 modes; 7 unchanged-likelihood, 2 newly-flagged + pre-mitigated).

## 7. Orthogonality

This addendum touches **1 file**:

- `research/problems/birthday-problem-oq-01-oq-02/sessions/2026-05-16-s5b-act-pick-time-audit-set-and-rwexpneg-traps.md` (NEW, this file)

It touches **NONE** of:

- `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` (live; owned by future S4 ACT)
- `proofs/Proofs/BirthdayProblemOQ02.lean` (different-slug ownership)
- `proofs/Proofs/BirthdayProblemOQ01.lean` (different-slug; mechanic-scoped per S5 §5)
- `state.md` (owned by OPEN STATE-SYNC #19355)
- `src/data/research/problems/birthday-problem-oq-01-oq-02.json` (owned by OPEN STATE-SYNC #19355)
- `knowledge.md` (still comprehensive)
- Prior session files (S1, S2 ACT, S3 ACT, S4, S4b, S4c, S5) — preserved verbatim

**Composes cleanly** with PR #19355 (different filenames in `sessions/` —
no rebase risk; both PRs are doc-only).

**No conflict** with the future S4 ACT PR (which will only touch
`BirthdayProblemOQ01OQ02.lean`, `state.md`, JSON; this addendum touches none
of those).

Open PRs on the slug at PR-create time: **1** (just #19355 itself; this
addendum is the second). Both doc-only, both single-file additions in
`sessions/`, no overlap.

## 8. Honesty

This addendum is **strictly doc-only**:

- **0** new Lean theorems on `main`
- **0** new sorries on `main`
- **0** new axioms anywhere
- **1** new markdown file under `research/problems/birthday-problem-oq-01-oq-02/sessions/`
- **0** existing files modified

The §3 / §4 trap analysis is verified by reading the actual Mathlib source
at the pinned SHA (§2 round-trips). The mitigations in §3b / §4b are
**not Docker-verified** in this PR (this is a doc-only addendum); they are
hand-derived from the lemma signatures verified in §2 and standard Mathlib
naming conventions. The future S4 ACT iteration that pastes §5's refined
scaffold will Docker-verify the full chain; if any of F8/F9 mitigations is
itself wrong, the ACT can fall back to:

- F8 alternatives (§3b): Alternative 1 (no `set`) or Alternative 2 (`simp only [← hS] at hge`).
- F9 alternatives (§4b): Option C (`simpa [one_div] using ...`).

The §6 gate-transition table claims 8/9 GREEN; the only AMBER nuance is the
self-referential open PR #19355 which is doc-only and non-conflicting per §7.

The future Lean entry `status` remains the gallery's "formalized / 0-sorries
post-S2-S3" track; this addendum does not modify gallery `meta.json` (owned
by deployer-side aggregation, not by research PRs).

## 9. Next ACT-picker priority (refined from S5 §"Next iteration")

**S4 ACT** is now paste-ready against `origin/main` HEAD `8a3cda556b6` with
**all 3 traps pre-mitigated**:

```bash
TS=$(date +%s)
BRANCH="research/birthday-oq01oq02-s4-act-paley-zygmund-${TS}"
cd /Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-N
git fetch origin +refs/heads/main:refs/remotes/origin/main
git checkout -b "$BRANCH" origin/main
# Insert §5 above's ~28-LOC refined scaffold between L142 (`  exact hbound`)
# and L143 (`end BirthdayProblemOQ01OQ02`) in
# `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`.
$EDITOR proofs/Proofs/BirthdayProblemOQ01OQ02.lean
./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ02
# Expected: ✔ [7745/7745] Built Proofs.BirthdayProblemOQ01OQ02 (~12s warm).
# Failure modes: see S4c §4d F1–F6 (R2 already mitigated in §5) +
#                S5 §4d F7 (paste anchor pinned) +
#                this addendum §3 / §4 F8 / F9 (pre-mitigated in §5).
git add proofs/Proofs/BirthdayProblemOQ01OQ02.lean
git commit -m "research(birthday-problem-oq-01-oq-02): S4 ACT — Paley-Zygmund-equivalent lower bound (closed form, build verified)"
git push -u origin "$BRANCH"
gh pr create --repo rjwalters/lean-genius --title "..." --body "..."
```

After this addendum + S4 ACT both merge, the slug holds:

- Upper bound `probCollision_le_choose_two_div` (Markov, post-S3 ACT)
- Lower bound `probCollision_ge_paley_zygmund` (closed Paley-Zygmund, post-S4 ACT)

in a single ~165-LOC file with 0 sorries / 0 axioms — matching the OQ-01-OQ-02
chain's gallery framing as `verified`.
