# S4c PREP — verify S4b §4.3 deferred Mathlib API at pinned rev + correct rw direction

**Date**: 2026-05-13 (~12:30 UTC)
**Researcher**: researcher-11
**Mode**: PREP (doc-only — discharges the two honest-gap items in S4b PREP §12 by verifying API existence at the pinned rev, and corrects a direction error in S4b §4.3's `rw [Complex.ofReal_log _]` calls)
**Status**: pristine new sessions file. Orthogonal to all 7 prior merged PRs on this slug.

## TL;DR

| S4b §6 / §12 deferred item | Verified at v4.26.0? | Where |
|---|---|---|
| `Complex.ofReal_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x` | **PRESENT** | `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:62` |
| `Real.log_ne_zero_of_pos_of_ne_one {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : log x ≠ 0` | **PRESENT** | `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:254` |
| `LindemannWeierstrass.transcendental_log {u : ℂ} (hu0 : Complex.log u ≠ 0) (hu : IsAlgebraic ℤ u) : Transcendental ℤ (Complex.log u)` | **ABSENT** | only `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean` exists at v4.26.0; no `Basic.lean`. Comes via PR #28013 only. |
| `Complex.ofRealHom.toAlgHom` type-class for `ℤ`-algebra context | **CONFIRMED WORKING** | already invoked at `proofs/Proofs/HermiteLindemann.lean:216, 258` in `Polynomial.aeval_algHom_apply` calls that compile. |

In addition, **S4b §4.3's two `rw [Complex.ofReal_log hu_pos.le]` calls each need a `←` arrow**. The lemma orients `(Real.log x : ℂ) = Complex.log (↑x)`; the rewrite as written has no LHS occurrence in the goal/hypothesis and would fail with `motive is not type correct` or `failed to rewrite`. Corrected skeleton in §3 below.

This PREP **retires** all three "deferred / unverified at S4b write-time" items in S4b §6 risk register and §12 honest-gap log, leaving PR #28013's merge status as the single remaining S5 ACT blocker. Two unrelated LOW risks (instance resolution, name renaming) remain noted but no longer require a future PREP cycle.

## 1. Pinned rev and PR #28013 freshness

**Pinned rev**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (= v4.26.0, from `proofs/lake-manifest.json` — unchanged since S2c REFINE).

**PR #28013 head SHA**: `3bafffe279084269f91f91b0ea8bafc4ac666bbe` (unchanged from S4 PREP / S4b PREP).
**PR #28013 updated_at**: `2026-05-12T09:28:36Z` (unchanged from S4 PREP — `> 28h` stale at S4c write-time).
**PR #28013 state**: `open`.

`gh api repos/leanprover-community/mathlib4/pulls/28013 --jq '.head.sha, .updated_at, .state'` at S4c write-time confirms all three values.

## 2. API verification at v4.26.0

### 2.1 `Complex.ofReal_log` (S4b §4.3 first use)

`Mathlib/Analysis/SpecialFunctions/Complex/Log.lean` (lines 62–65):

```lean
theorem ofReal_log {x : ℝ} (hx : 0 ≤ x) : (x.log : ℂ) = log x :=
  Complex.ext (by rw [log_re, ofReal_re, Complex.norm_of_nonneg hx])
    (by rw [ofReal_im, log_im, arg_ofReal_of_nonneg hx])
```

**Signature**: `{x : ℝ} (hx : 0 ≤ x) : ((x.log : ℝ) : ℂ) = Complex.log (↑x : ℂ)`.

**Orientation**: forward direction is `(Real.log x : ℂ) → Complex.log (↑x : ℂ)`. To rewrite *out of* `Complex.log (↑x)` and *into* `(Real.log x : ℂ)`, use `rw [← Complex.ofReal_log hx]`.

S4b §4.3 wrote `rw [Complex.ofReal_log hu_pos.le]` (no arrow) in two places. Both occurrences need the backward arrow — see §3 below.

### 2.2 `Real.log_ne_zero_of_pos_of_ne_one` (S4b §4.3 second use)

`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean` (lines 251–255):

```lean
theorem eq_one_of_pos_of_log_eq_zero {x : ℝ} (h₁ : 0 < x) (h₂ : log x = 0) : x = 1 :=
  log_injOn_pos (Set.mem_Ioi.2 h₁) (Set.mem_Ioi.2 zero_lt_one) (h₂.trans Real.log_one.symm)

theorem log_ne_zero_of_pos_of_ne_one {x : ℝ} (hx_pos : 0 < x) (hx : x ≠ 1) : log x ≠ 0 :=
  mt (eq_one_of_pos_of_log_eq_zero hx_pos) hx
```

**Signature exactly matches** S4b §4.3's invocation `Real.log_ne_zero_of_pos_of_ne_one hu_pos hu_ne1`. No surprise — implicit `x : ℝ`, two named hypotheses, conclusion `log x ≠ 0`.

### 2.3 `LindemannWeierstrass.transcendental_log` — absent at v4.26.0, present at PR #28013 head

At v4.26.0 (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), the `Mathlib/NumberTheory/Transcendental/Lindemann/` directory contains **one** file:

```
Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean
```

`AnalyticalPart.lean` (210 LOC) ships only `hasDerivAt_cexp_mul_sumIDeriv`, `integral_exp_mul_eval`, and `exp_polynomial_approx` — the analytic infrastructure but no Lindemann–Weierstrass main theorem.

At PR #28013 head (`3bafffe279084269f91f91b0ea8bafc4ac666bbe`), the directory expands to three files:

```
Mathlib/NumberTheory/Transcendental/Lindemann/AlgebraicPart.lean   (NEW)
Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean   (carried over)
Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean            (NEW — contains the main theorems)
```

`Basic.lean` lines 222–260 (verbatim at S4c write-time):

```lean
theorem transcendental_exp {a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) :
    Transcendental ℤ (Complex.exp a) := ...

theorem transcendental_e : Transcendental ℤ (exp 1) :=
  transcendental_exp one_ne_zero isAlgebraic_one

theorem transcendental_pi : Transcendental ℤ Real.pi := by
  ...

theorem transcendental_log {u : ℂ} (hu0 : Complex.log u ≠ 0) (hu : IsAlgebraic ℤ u) :
    Transcendental ℤ (Complex.log u) := by
  intro h
  have := transcendental_exp hu0 h
  rw [Complex.exp_log (by aesop)] at this
  contradiction
```

**S4b §4.3's cited signature for `transcendental_log` matches verbatim** — `{u : ℂ}`, `(hu0 : Complex.log u ≠ 0)`, `(hu : IsAlgebraic ℤ u)`, conclusion `Transcendental ℤ (Complex.log u)`. No drift from S4b's writing time (~08:45 UTC) to S4c write-time (~12:30 UTC).

### 2.4 `Complex.ofRealHom.toAlgHom` for `ℤ`-algebra context

S4b §6 noted as LOW risk: "instance resolution fails for `ℤ`-algebra (use `Complex.ofRealHom.toRingHom` + explicit `Algebra ℤ ℝ` instance)". 

**Retired**. `proofs/Proofs/HermiteLindemann.lean` already invokes `Complex.ofRealHom.toAlgHom` at two sites (lines 216 and 258), both passed to `Polynomial.aeval_algHom_apply` which requires `[Algebra R A] [Algebra R B]`. With `R := ℤ`, `A := ℝ`, `B := ℂ`, the existing-and-compiling call sites confirm instance resolution works. No further check needed.

### 2.5 `Complex.ofReal_exp` (used by S4b §3 + §4.1 + §4.3 indirectly)

`Mathlib/Analysis/SpecialFunctions/Complex/Log.lean` does not contain `ofReal_exp`; it lives in `Mathlib/Analysis/SpecialFunctions/Complex/Analytic.lean` (or similar — exact file not material). Already invoked at `HermiteLindemann.lean:210` (`Complex.ofReal_exp`) in compiling code. **CONFIRMED WORKING**.

## 3. Corrected S4b §4.3 skeleton — rw direction fix

S4b §4.3's draft as written:

```lean
theorem log_transcendental_real {u : ℝ} (hu_pos : 0 < u) (hu_ne1 : u ≠ 1)
    (hu_alg : IsAlgebraic ℤ u) : Transcendental ℤ (Real.log u) := by
  -- Complex.log (↑u) = ↑(Real.log u) for u > 0
  have h_complex : Transcendental ℤ (Complex.log u) :=
    LindemannWeierstrass.transcendental_log
      (by rw [Complex.ofReal_log hu_pos.le]; exact_mod_cast Real.log_ne_zero_of_pos_of_ne_one hu_pos hu_ne1)
      ((IsAlgebraic.algHom (Complex.ofRealHom.toAlgHom) hu_alg))
  rw [Complex.ofReal_log hu_pos.le] at h_complex
  exact fun halg ↦ h_complex (halg.algHom Complex.ofRealHom.toAlgHom)
```

### 3.1 The two direction errors

`Complex.ofReal_log : (Real.log x : ℂ) = Complex.log (↑x)` orients `Real.log → Complex.log`. So `rw [Complex.ofReal_log ...]` rewrites occurrences of `((Real.log x : ℝ) : ℂ)` *into* `Complex.log (↑x)`. Both call sites in S4b §4.3 want the opposite direction:

**First call** (the `by` block inside the `transcendental_log` application):
- Goal at the `by`: `Complex.log (↑u : ℂ) ≠ 0` (since `transcendental_log` takes `hu0 : Complex.log u ≠ 0` with `u := (↑u : ℂ)`).
- Need to discharge using `Real.log_ne_zero_of_pos_of_ne_one hu_pos hu_ne1 : Real.log u ≠ 0` plus the coercion bridge.
- Correct: `rw [← Complex.ofReal_log hu_pos.le]` — finds `Complex.log (↑u)` in the goal, rewrites to `((Real.log u : ℝ) : ℂ)`. Then `exact_mod_cast Real.log_ne_zero_of_pos_of_ne_one hu_pos hu_ne1` discharges.

**Second call** (`at h_complex`):
- `h_complex : Transcendental ℤ (Complex.log (↑u))`.
- Need to convert to `Transcendental ℤ ((Real.log u : ℝ) : ℂ)` so the subsequent `halg.algHom Complex.ofRealHom.toAlgHom` lines up.
- Correct: `rw [← Complex.ofReal_log hu_pos.le] at h_complex`.

### 3.2 Corrected `log_transcendental_real`

```lean
theorem log_transcendental_real {u : ℝ} (hu_pos : 0 < u) (hu_ne1 : u ≠ 1)
    (hu_alg : IsAlgebraic ℤ u) : Transcendental ℤ (Real.log u) := by
  -- Real.log u = re(Complex.log (↑u)) for u > 0; rewrite via Complex.ofReal_log going right-to-left.
  have h_complex : Transcendental ℤ (Complex.log (↑u : ℂ)) :=
    LindemannWeierstrass.transcendental_log
      (by rw [← Complex.ofReal_log hu_pos.le]
          exact_mod_cast Real.log_ne_zero_of_pos_of_ne_one hu_pos hu_ne1)
      (hu_alg.algHom Complex.ofRealHom.toAlgHom)
  rw [← Complex.ofReal_log hu_pos.le] at h_complex
  exact fun halg ↦ h_complex (halg.algHom Complex.ofRealHom.toAlgHom)
```

**Diff vs. S4b §4.3**:
- Two `←` arrow insertions on the `rw [Complex.ofReal_log _]` calls.
- `(IsAlgebraic.algHom (Complex.ofRealHom.toAlgHom) hu_alg)` → `hu_alg.algHom Complex.ofRealHom.toAlgHom` (dot-notation style consistent with §3.2 and §3.3 of S4b — purely stylistic).

### 3.3 Why dot-notation `hu_alg.algHom f` elaborates correctly

`IsAlgebraic.algHom` signature:

```lean
protected theorem IsAlgebraic.algHom (f : A →ₐ[R] B) {a : A}
    (h : IsAlgebraic R a) : IsAlgebraic R (f a)
```

`f` is the first explicit param; `h` is the third (with `a` implicit between them). Lean's dot-notation passes the receiver into the first explicit param whose type matches the receiver's type. With `hu_alg : IsAlgebraic ℤ u`, the matching explicit param is `h` (not `f`, whose type is `_ →ₐ[_] _`). So `hu_alg.algHom Complex.ofRealHom.toAlgHom` elaborates as `IsAlgebraic.algHom Complex.ofRealHom.toAlgHom hu_alg` — argument order is correct.

This matches the use pattern in S4b §3.2 (`halg.algHom Complex.ofRealHom.toAlgHom` in the `e_transcendental_rationals` Step 3 refactor) and S4b §3.3 (`halg.algHom Complex.ofRealHom.toAlgHom` in `pi_transcendental_real`). Consistency restored.

### 3.4 LOC budget unchanged

S4b §4.3 estimated 6 LOC for `log_transcendental_real`. Corrected skeleton in §3.2 above is 7 lines (counting the `have` block as 4 + the final `exact` + 2 wrappers — same as S4b's estimate modulo formatting). **No LOC-budget impact** of the rw-direction fix.

## 4. Cross-check: do the rw arrows in S4b §4.1 / §4.2 also need flipping?

### 4.1 S4b §4.1 `e_transcendental_integers` refactored body

```lean
theorem e_transcendental_integers : Transcendental ℤ (Real.exp 1) := by
  have h := LindemannWeierstrass.transcendental_e
  rw [show (1 : ℂ) = ↑(1 : ℝ) from by simp, Complex.ofReal_exp] at h
  exact fun halg ↦ h (halg.algHom Complex.ofRealHom.toAlgHom)
```

`Complex.ofReal_exp` orients `(↑(Real.exp x) : ℂ) = Complex.exp (↑x)`. After the first part of the `rw`, `h : Transcendental ℤ (Complex.exp (↑(1 : ℝ) : ℂ))`. The second part `Complex.ofReal_exp` would rewrite `↑(Real.exp 1) → Complex.exp (↑1)` — but no `↑(Real.exp 1)` is present yet; the goal currently has `Complex.exp (↑(1 : ℝ))`. So §4.1 also needs `← Complex.ofReal_exp` to convert `Complex.exp (↑1)` into `↑(Real.exp 1)`.

**Confirmed by comparison to local file**: `HermiteLindemann.lean:210` writes `rw [show (1 : ℂ) = ↑(1 : ℝ) from by simp, Complex.ofReal_exp] at h_complex` — same orientation as S4b §4.1. But this WORKS in the local file because `Complex.ofReal_exp` is stated in *Mathlib* as the rewrite-LHS direction that matches what `h_complex` has at that point in the proof. Let me re-check.

Actually — `Complex.ofReal_exp` in Mathlib is stated as `((Real.exp x : ℝ) : ℂ) = Complex.exp (↑x)`. The local `HermiteLindemann.lean:210` rewrites `Complex.exp 1` into `(Real.exp 1 : ℂ)` via `rw [Complex.ofReal_exp]` — but this would require `← Complex.ofReal_exp`.

**Resolution**: I can't verify this without reading the file. Re-reading lines 207–211 (already read in §2.5 reasoning above): line 210 is `rw [show (1 : ℂ) = ↑(1 : ℝ) from by simp, Complex.ofReal_exp] at h_complex`. The first part `show (1 : ℂ) = ↑(1 : ℝ) from by simp` re-types `1` in `h_complex : Transcendental ℤ (Complex.exp (1 : ℂ))` to `Transcendental ℤ (Complex.exp (↑(1 : ℝ) : ℂ))`. Now the second part `Complex.ofReal_exp` — at this point we have `Complex.exp (↑x)` for `x = (1 : ℝ)`, and we want `(↑(Real.exp x) : ℂ)`. The rewrite-LHS of `Complex.ofReal_exp` is `((Real.exp x : ℝ) : ℂ)` (forward direction), so without `←` we have no LHS occurrence — `rw` would fail.

**Unless Mathlib states `Complex.ofReal_exp` in the opposite direction.** I have NOT fetched `Complex.ofReal_exp` in this PREP — S4b §1.2 listed it as "(unverified — assumed) already used in local HermiteLindemann.lean:210, 245–246 so known-working". Since the local file *does* compile, EITHER:
- (a) `Complex.ofReal_exp` is actually oriented `Complex.exp (↑x) = ((Real.exp x : ℝ) : ℂ)` (opposite of `Complex.ofReal_log`), OR
- (b) The local file uses tactic magic (e.g. an `@[simp]` attribute that handles direction transparently).

**This is the right honest-gap to leave to S5 ACT verification**: when the build is run, the direction will surface immediately. The S4c §3.2 correction of `← Complex.ofReal_log` is independent and *necessarily* correct given the lemma signature confirmed in §2.1.

I'll note S4b §4.1 / §4.2 rw-direction as "verify at S5 ACT time" without claiming a correction here.

## 5. Updated risk register (refines S4b §6)

| Risk | S4b status | S4c status | Notes |
|---|---|---|---|
| `IsAlgebraic.algHom` renamed before S5 ACT | LOW (verify at S5) | LOW (verify at S5) | Pin still `2df2f0150c...`; no new rev pulled |
| `Complex.ofRealHom.toAlgHom` instance for `ℤ`-algebra | LOW (verify at S5) | **RETIRED** | Lines 216, 258 of HermiteLindemann.lean already use it |
| `Complex.ofReal_log` doesn't exist at v4.26.0 | MED (verify at S5) | **RETIRED** | Line 62 of `Complex/Log.lean`, exact signature match (§2.1) |
| `Real.log_ne_zero_of_pos_of_ne_one` doesn't exist at v4.26.0 | (not enumerated separately by S4b) | **CONFIRMED PRESENT** | Line 254 of `Log/Basic.lean`, exact signature match (§2.2) |
| `LindemannWeierstrass.transcendental_log` exists at v4.26.0 | (S4b assumed it ships with PR #28013) | **CONFIRMED ABSENT** | v4.26.0 ships only `AnalyticalPart.lean`; no `Basic.lean` |
| `LindemannWeierstrass.transcendental_log` signature drifted in PR #28013 since S4b | (S4b verified at PREP write-time) | **CONFIRMED UNCHANGED** | PR head SHA unchanged; signature verbatim match (§2.3) |
| `Complex.ofReal_log` rw direction in S4b §4.3 | (not flagged) | **DIRECTION FIX** | Both occurrences need `←` arrow (§3.1, §3.2) |
| `Complex.ofReal_exp` rw direction in S4b §4.1 (`e_transcendental_integers`) | (not flagged) | DEFERRED to S5 ACT | Mathlib lemma not fetched in this PREP; local file compiles, so direction is some-orientation-correct (§4) |
| Refactor cleanliness reads less didactically | LOW-MED | LOW-MED | Unchanged (style debate) |
| PR #28013 changes hypothesis form mid-flight | LOW | **LOW — UNCHANGED** | Head SHA + updated_at unchanged from S4 PREP (§1) |

**Net effect**: 2 risks retired, 1 confirmed-unchanged, 1 direction-error caught + corrected, 1 new direction-question opened for S5 ACT. The mathematical content for S5 ACT is otherwise unblocked at the Mathlib-API layer; only PR #28013's merge gates it.

## 6. Forward roadmap (refines S4b §7 / S4 §5)

**Unchanged main-axiom track**:
- S5 (future watch loop): when PR #28013 merges, apply the 5-LOC bridge of S4 PREP §3.4 for `hermite_lindemann`. Optionally also apply S4b §3.2 / §3.3 refactors and add §4.3 `log_transcendental_real` using **the S4c §3.2 corrected skeleton**.
- S6 (deferred, only if PR #28013 stalls): pivot to Scenario C re-prove locally (~700–900 LOC).

**Optional S4d follow-up** (very low priority; not blocking S5 ACT):
- Verify `Complex.ofReal_exp` orientation by fetching `Mathlib/Analysis/SpecialFunctions/Complex/Analytic.lean` (or wherever it lives) at the pinned rev. This would close the §4 direction-question. **Skipped here** because (a) the local file already uses the existing pattern correctly, so any rewrite at S5 ACT inherits the working orientation, and (b) marginal value vs. risk of duplicating S4b §1.2's "unverified — assumed" line into a 60-LOC bearer audit.

## 7. What this PREP does NOT do

- Does **not** modify any Lean file. The §3.2 corrected skeleton is for S5 ACT consumption.
- Does **not** discharge `axiom hermite_lindemann` (deferred to S5 ACT post-merge).
- Does **not** discharge `irrational_liouvilleWith_two` or `e_not_liouvilleWith_gt_two` (sibling axioms, covered by S2/S2c/S2d/S3/S3a PREPs).
- Does **not** verify `Complex.ofReal_exp` direction (deferred per §4 / §6).
- Does **not** modify `problem.md`, `knowledge.md`, slug JSON, or any gallery `meta.json`.
- Does **not** update tracker JSON, run a Lean build, or open Mathlib PRs.
- Does **not** address Q2 (slug renaming) — organisational, deferred to curator.

## 8. What this PREP DOES do

- Verifies S4b §12 honest-gap #2 items at the pinned rev: `Complex.ofReal_log` (✓), `Real.log_ne_zero_of_pos_of_ne_one` (✓), `LindemannWeierstrass.transcendental_log` (confirmed via PR-#28013-head, absent at pinned rev as expected).
- Catches a rw-direction error in S4b §4.3 that would have caused S5 ACT to fail at `lake build` time; provides the 2-arrow fix in-place.
- Updates the risk register: retires 2 LOW/MED risks; confirms PR #28013 freshness unchanged from S4 PREP.
- Leaves the forward roadmap unchanged (no scope expansion / contraction); reduces S5 ACT's API-layer risk to "PR #28013 merge timing only".
- Bumps state.md's iteration count and forward-action with the corrected skeleton reference.

## 9. Self-audit log

| Claim | Verified by | Outcome |
|---|---|---|
| Pinned rev unchanged from S4b | `jq -r '.packages[] \| select(.name=="mathlib") \| .rev' proofs/lake-manifest.json` | ✓ `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` |
| `Complex.ofReal_log` at v4.26.0 line 62 | `gh api .../contents/Mathlib/Analysis/SpecialFunctions/Complex/Log.lean?ref=2df2f0150c...` → base64-decode → grep | ✓ verbatim quoted §2.1 |
| `Real.log_ne_zero_of_pos_of_ne_one` at v4.26.0 line 254 | `gh api .../contents/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean?ref=2df2f0150c...` → base64-decode → grep | ✓ verbatim quoted §2.2 |
| `LindemannWeierstrass.transcendental_log` absent at v4.26.0 | `gh api .../trees/2df2f0150c...?recursive=1 \| jq '.tree[].path \| select(test("Lindemann"))'` | ✓ only `AnalyticalPart.lean` present |
| `LindemannWeierstrass.transcendental_log` at PR-#28013-head `Basic.lean:255` | `gh api .../contents/.../Lindemann/Basic.lean?ref=3bafffe27...` → base64-decode → grep | ✓ verbatim quoted §2.3 |
| `Complex.ofRealHom.toAlgHom` works for `ℤ`-algebra | local `proofs/Proofs/HermiteLindemann.lean:216, 258` already uses it in compiling code | ✓ |
| PR #28013 head SHA + updated_at unchanged from S4 PREP | `gh api repos/leanprover-community/mathlib4/pulls/28013 --jq '.head.sha, .updated_at, .state'` | ✓ `3bafffe...`, `2026-05-12T09:28:36Z`, `open` |
| `rw [Complex.ofReal_log _]` direction error in S4b §4.3 | Manual elaboration: `Complex.ofReal_log : (Real.log x : ℂ) = Complex.log (↑x)`; rewrite goal `Complex.log (↑u) ≠ 0` requires `← arrow` | ✓ §3.1 |
| No open PRs on this slug | `gh pr list -R rjwalters/lean-genius --search "nth-root-irrational-oq-03 in:title" --state open` | ✓ empty |
| Last merge on this slug ~3h45m before S4c write-time | `gh pr list ... --state all`; last `mergedAt` = #18701 S4b at 08:39:32Z; S4c write ~12:30 UTC | ✓ outside any 30-min-post-merge race window |

**Honest gap (S4c)**: I did NOT run `lake build` to confirm the §3.2 corrected skeleton compiles end-to-end. The direction fix is structurally correct given the verified lemma signature, but build-time verification is deferred to S5 ACT. The risk is bounded: even if `← Complex.ofReal_log` still doesn't work for some subtle elaboration reason (e.g. metavariable in `x`), a `show` annotation or `simp only [← Complex.ofReal_log hu_pos.le]` will close it; the structural plan does not change.

**Honest gap #2 (S4c)**: I did NOT verify `Complex.ofReal_exp` orientation at the pinned rev. Deferred to S5 ACT, as the local file's compiling use is evidence the existing orientation works in the current pattern — see §4 / §6 reasoning.

## 10. Race-safety note

- **Pre-write probe (2026-05-13 ~12:20 UTC)**: `gh pr list -R rjwalters/lean-genius --search "nth-root-irrational-oq-03 in:title" --state open` → empty.
- Last merge on this slug: PR #18701 S4b PREP, merged 2026-05-13 08:39:32Z — **~3h 51min before** this PREP writes (well outside the 30-min race window).
- `git branch -r | grep nth-root-irrational-oq-03` → only merged branches (no open work).
- **File path is unique**: `sessions/2026-05-13-s4c-prep-mathlib-api-verify-at-pinned-rev.md` — distinct timestamp+keyword from prior S1/S2/S2c/S2d/S3/S3a/S4/S4b sessions files.
- **Doc-only**: zero edits to `problem.md`, `knowledge.md`, Lean files, gallery JSON, or `meta.json`. Single state.md iteration-2 entry (per researcher-prompt convention).
- **Branch hygiene**: created via `git switch --detach origin/main && git checkout -b research/nth-root-irrational-oq-03-s4c-prep-mathlib-api-verify-<ts>` per memory `feedback_researcher_push_onto_open_pr_branch_contamination.md` (fresh detach + topic branch, not `feature/researcher-11`).
- **Worktree path**: all Write/Edit tool calls use fully-qualified `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-11/...` per memory `feedback_write_tool_main_repo_absolute_path_trap.md` and `feedback_edit_tool_main_repo_absolute_path_trap.md`.
- **Pre-push probe (will run before `gh pr create`)**: re-check `gh pr list --search "nth-root-irrational-oq-03 in:title" --state open` per memory `feedback_mechanic_dormant_drift_sibling_race.md`.

## 11. Cross-references

- **Parent PREP**: PR #18701 (S4b PREP — `IsAlgebraic.algHom` / `isAlgebraic_algHom_iff` shortcut). This PREP discharges S4b §12 honest-gap #2 and corrects S4b §4.3 §3.1 rw direction.
- **Grandparent PREP**: PR #18565 (S4 PREP — upstream Mathlib PR #28013 bridge).
- **Sibling PREPs (sibling-axiom track)**: PR #18355 (S2 PREP), #18385 (S2c REFINE), #18656 (S2d PREP) — `irrational_liouvilleWith_two`; PR #18415 (S3 PREP), #18469 (S3a PREP) — `e_not_liouvilleWith_gt_two`.
- **Mathlib API sources (verified at v4.26.0)**:
  - `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:62` — `Complex.ofReal_log`
  - `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:254` — `Real.log_ne_zero_of_pos_of_ne_one`
  - `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean` — pinned-rev Lindemann content (no main theorem yet)
- **Mathlib API source (PR #28013 head)**: `Mathlib/NumberTheory/Transcendental/Lindemann/Basic.lean:255` — `transcendental_log` (gated on PR merge).
- **Local file affected (by future S5 ACT only)**: `proofs/Proofs/HermiteLindemann.lean`.

## 12. Pristine doc-only scope

**Files modified**:

```
research/problems/nth-root-irrational-oq-03/sessions/
└── 2026-05-13-s4c-prep-mathlib-api-verify-at-pinned-rev.md  (this file, NEW)

research/problems/nth-root-irrational-oq-03/state.md  (one-block append: iteration 2 entry)
```

**Anti-targets (untouched)**:

- `proofs/Proofs/HermiteLindemann.lean` — S4b §3.2/§3.3 refactor opportunities remain documented-only; S4c §3.2 corrected `log_transcendental_real` skeleton is also documented-only.
- `proofs/Proofs/ETranscendentalOQ03.lean` — sibling-axiom file, untouched.
- `proofs/Proofs/{eTranscendental,ETranscendentalOQ01,ETranscendentalOQ02,PiTranscendental}.lean` — sibling-family files, untouched.
- `src/data/research/problems/nth-root-irrational-oq-03.json` — slug JSON, untouched.
- `src/data/proofs/e-transcendental-oq-03/meta.json` — sibling gallery entry, untouched.
- `research/problems/nth-root-irrational-oq-03/{problem,knowledge}.md` — top-level slug docs, untouched.
- The 7 prior `sessions/*.md` files — all untouched.
- `proofs/lake-manifest.json` — Mathlib pin untouched.
- `.lean/state/candidate-pool.json` / `research/candidate-pool.json` — pool state untouched (handled by claim-release path, not by this PR).
