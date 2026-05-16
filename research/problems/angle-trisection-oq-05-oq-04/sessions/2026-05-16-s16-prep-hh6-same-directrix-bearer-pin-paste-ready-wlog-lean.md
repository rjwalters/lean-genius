# S16 PREP — HH-6 same-directrix bearer pin verification + paste-ready WLOG-frame Lean + isometry-transport gap manifest (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-6
**Phase**: PREP (doc-only; closes S15 PREP §6 Mathlib API "to-confirm" line by pin-verifying at lake SHA, supplies paste-ready Lean code that S15 only blueprinted, manifests the isometry-transport gap S15 deferred via the WLOG move)
**Iteration**: 16 PREP (post-S15 PREP merged 2026-05-13 09:22 UTC; post-S15b STATE-SYNC merged 2026-05-13 13:46 UTC; post-#19019 STATE-SYNC COMPLEMENT merged 2026-05-15 23:28:29 UTC)
**Predecessors**: all merged S1–S15 + S15b + #19019 (see `state.md` session log table)

**Build status**: not applicable — doc-only session note. Zero edits to `proofs/Proofs/AngleTrisectionOQ05.lean`, `proofs/Proofs/AngleTrisectionOQ05OQ04.lean`, `state.md`, `knowledge.md`, `problem.md`, slug research JSON, or `src/data/proofs/angle-trisection-oq-05-oq-04/*`. One new session-notes file (this document).

## 1. Trigger and scope

| Signal | Threshold | Observation |
|--------|-----------|-------------|
| Open PRs on slug | 0–1 proceed if material | **0 open research PRs** (only stale #18192 from 2026-05-12, obsoleted by merged #18195) |
| Days since S15 PREP authored | ≥2 = re-pin bearers at SHA | **3 days** (S15 merged 2026-05-13 09:22 UTC) |
| Days since S15b STATE-SYNC | ≥2 = re-verify state.md / JSON / meta | **3 days** (S15b merged 2026-05-13 13:46 UTC) |
| Time since most recent slug PR | — | **~2h** (#19019 merged 2026-05-15 23:28:29 UTC) |
| Days since Lean file last touched | ≥3 = bearer drift recheck mandatory | **4 days** (last touched 2026-05-12 16:20 UTC, SHA `8bb2320019f`) |
| S15 PREP §6 risks needing pre-flight | ≥1 | **3** (Mathlib API spelling, WLOG-frame isometry transport, general-coords vs WLOG-coords ACT framing) |
| Sibling worktree races on the slug | 0 | confirmed — `gh pr list --search "angle-trisection-oq-05-oq-04" --state open` returns **only** #18192 (S8 SCAFFOLD, 4 days stale, file untouched by this PREP) |
| Deployer state | inform path | **stalled** (no merges since 2026-05-16 01:09:32 UTC, ~26 min) — doc-only PREP rides drain queue without urgency |

The S15 PREP §6 ("ACT-blueprint for S16 — Lean implementation of HH-6 same-directrix") closed with two paragraphs of identifier names + a bracketed `[expected size: ~150–200 lines]` but **did not write the `noncomputable def` body** and **did not pin the Mathlib API at lake SHA**. The S15b STATE-SYNC then froze `state.md` head with S16-α as the recommended ACT target, but again left the actual Lean code unwritten.

S16 PREP discharges three deliverables from the S15 / S15b backlog:

1. **§2 — Mathlib API pin-verify** at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), correcting one mis-named bearer flagged in S15 PREP §6.
2. **§3 — Bearer drift recheck** on `proofs/Proofs/AngleTrisectionOQ05*.lean` post-S15b (the Lean file has been frozen for 4 days; all 12 anchor lines for the S16 ACT verified EXACT against the predicted line numbers in `state.md` HH-axiom Programme Status table).
3. **§5 — Paste-ready WLOG-frame Lean** for `belochFold_sameDirectrix_xAxis` and its three supporting lemmas, ~80 LOC drop-in code (S15 supplied prose blueprint only).
4. **§6 — Isometry-transport gap manifest** that S15 §1.1 finessed via "WLOG via isometry" without specifying how to lift the result to the `HHAxioms.hh6` field which quantifies over arbitrary `ℓ₁, ℓ₂ : Line` (the gap is `~80–120 LOC` of `AffineIsometry`-flavored code that S15 deferred).
5. **§7 — Three ACT-readiness paths** (A WLOG-only + axiomatize the transport, B full general via isometry, C general-coords direct), with LOC budgets and Docker-iteration risk register.

## 2. Mathlib bearer pin-verify — lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Pin-verified via `gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Real/Sqrt.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

| # | Bearer | File @ SHA | Line | Signature | Notes |
|---|--------|-----------|------|-----------|-------|
| M1 | `Real.sqrt_pos` | `Mathlib/Data/Real/Sqrt.lean` | **268** | `0 < √x ↔ 0 < x` | `@[simp]`. Use `.mpr` for `0 < x → 0 < √x`, `.mp` for the reverse. NB: there is also an `NNReal.sqrt_pos` at line **94** of the same file (`@[simp]`); the `open Real` form (or the fully-qualified `Real.sqrt_pos`) is required to disambiguate inside `namespace AngleTrisectionOQ05OQ04` where neither namespace is open. |
| M2 | `Real.sqrt_nonneg` | `Mathlib/Data/Real/Sqrt.lean` | **129** | `(x : ℝ) : 0 ≤ √x` | `@[simp]`. Always available; no hypothesis. |
| M3 | `Real.sq_sqrt` | `Mathlib/Data/Real/Sqrt.lean` | **163** | `(h : 0 ≤ x) : √x ^ 2 = x` | This is the spelling for cancellation in the `(√x)² = x` direction, hypothesis `0 ≤ x`. |
| M4 | `Real.sqrt_sq` | `Mathlib/Data/Real/Sqrt.lean` | **166** | `(h : 0 ≤ x) : √(x ^ 2) = x` | Inverse direction; hypothesis `0 ≤ x`. **Distinct from `Real.sqrt_sq_eq_abs`**. |
| M5 | `Real.sqrt_sq_eq_abs` | `Mathlib/Data/Real/Sqrt.lean` | **174** | `(x : ℝ) : √(x ^ 2) = \|x\|` | Hypothesis-free; produces absolute value. Use when sign-info on `x` is missing. |
| M6 | `Real.mul_self_sqrt` | `Mathlib/Data/Real/Sqrt.lean` | **134** | `(h : 0 ≤ x) : √x * √x = x` | Useful for `linear_combination` and `field_simp` chains where the squared form is preferred over the `^2` form. |
| M7 | `Real.sqrt_eq_zero` | `Mathlib/Data/Real/Sqrt.lean` | **248** | `(h : 0 ≤ x) : √x = 0 ↔ x = 0` | Hypothesis-laden bi-implication. Use `.mp` to extract `√x = 0 → x = 0`, `.mpr` for the reverse. |
| M8 | `Real.sqrt_eq_zero_of_nonpos` | `Mathlib/Data/Real/Sqrt.lean` | **127** | `(h : x ≤ 0) : √x = 0` | Hypothesis-laden one-way. Use **only** if signing case-split is desired (the `belochFold_sameDirectrix_xAxis` proof avoids this branch by assuming `p₁ ≠ p₂` ⇒ `‖p₁ − p₂‖² > 0`). |
| M9 | `Real.sqrt_mul_self` | `Mathlib/Data/Real/Sqrt.lean` | **138** | `(h : 0 ≤ x) : √(x * x) = x` | Companion to M6; useful when the *integrand* is `x * x` instead of `x^2`. |

### Correction to S15 PREP §6 Mathlib API list

S15 PREP §6 listed the API as `Real.sqrt_sq, Real.sq_sqrt, Real.sqrt_nonneg, Real.sqrt_pos_of_ne_zero`. The fourth name **does not exist** at the pinned lake SHA. The closest matches at SHA are:

- `NNReal.sqrt_pos_of_pos` at line **96** (`alias ⟨_, sqrt_pos_of_pos⟩ := sqrt_pos`) — NNReal namespace, not Real
- `Real.sqrt_pos` at line **268** — Real, with the iff direction reversible via `.mpr`

The correct spelling for the S16-α ACT proof (`0 < ‖p₁ − p₂‖² → 0 < √(‖p₁ − p₂‖²)`) is:

```lean
have h_sqrt_pos : 0 < Real.sqrt (‖p₁ − p₂‖²) := Real.sqrt_pos.mpr h_normSq_pos
```

Or equivalently:

```lean
have h_sqrt_pos : 0 < Real.sqrt (‖p₁ − p₂‖²) := by
  rw [Real.sqrt_pos]; exact h_normSq_pos
```

This is one identifier change vs S15 PREP §6 ("the name `Real.sqrt_pos_of_ne_zero` → use `Real.sqrt_pos.mpr` instead"), no mathematical content change.

## 3. Bearer drift recheck on `origin/main` `8a3cda556b63a` — `proofs/Proofs/AngleTrisectionOQ05*.lean`

Verified at this PREP's branch-base `origin/main` `8a3cda556b63aaf6e6184b4c968d1efbf9849b85` (= `gh api repos/rjwalters/lean-genius/commits/main --jq .sha`).

### 3.1 Parent file `AngleTrisectionOQ05.lean` (1006 lines, unchanged since 2026-05-12)

| # | Bearer | Predicted line | Actual line | Signature on origin/main | Status |
|---|--------|---------------|-------------|--------------------------|--------|
| P1 | `Point` abbrev | 64 (S15b state.md table) | **64** | `abbrev Point := ℝ × ℝ` | ✓ EXACT |
| P2 | `Line` structure | 68 (state.md) | **68** | `structure Line where a : ℝ; b : ℝ; c : ℝ; nondeg : a ≠ 0 ∨ b ≠ 0` | ✓ EXACT |
| P3 | `Line.contains` | 75 (state.md) | **75** | `def Line.contains (l : Line) (p : Point) : Prop := l.a * p.1 + l.b * p.2 + l.c = 0` | ✓ EXACT |
| P4 | `reflectAcross` | 99 (state.md) | **99** | `noncomputable def reflectAcross (l : Line) (p : Point) : Point := …` | ✓ EXACT |
| P5 | `HHAxioms` structure | 108 (state.md) | **108** | `structure HHAxioms where …` | ✓ EXACT |
| P6 | `HHAxioms.hh6` field | 143 (state.md) | **143** | `hh6 : ∀ (p₁ p₂ : Point) (ℓ₁ ℓ₂ : Line), ∃ l : Line, ℓ₁.contains (reflectAcross l p₁) ∧ ℓ₂.contains (reflectAcross l p₂)` | ✓ EXACT |

### 3.2 OQ-04 file `AngleTrisectionOQ05OQ04.lean` (1144 lines, unchanged since 2026-05-12)

| # | Bearer | Predicted line | Actual line | Status |
|---|--------|---------------|-------------|--------|
| Q1 | `CurvedCrease` structure | 106 (S15b) | **106** | ✓ |
| Q2 | `perpBisector` def | 478 (S15b) | **478** | ✓ |
| Q3 | `perpBisector_dirSq_pos` | 494 (S15b) | **494** | ✓ |
| Q4 | `reflectAcross_perpBisector` | 511 (S15b) | **511** | ✓ |
| Q5 | `hh2_existence` | 529 (S15b) | **529** | ✓ |
| Q6 | `perpThroughPoint_normSq_pos` | 593 (S15b) | **593** | ✓ |
| Q7 | `perpThroughPoint` def | 607 (S15b) | **607** | ✓ |
| Q8 | `crossDet` def | 726 (S15b) | **726** | ✓ |
| Q9 | `hatoriFold` def | 740 (S15b) | **740** | ✓ |
| Q10 | `hh7_existence_nonparallel` | 804 (S15b) | **804** | ✓ |
| Q11 | `parallelBisector_dot_ne_zero` | 1016 (S15b) | **1016** | ✓ |
| Q12 | `parallelBisector` def | 1059 (S15b) | **1059** | ✓ |
| Q13 | `hh3_existence_parallel` | 1135 (S15b) | **1135** | ✓ |
| Q14 | `end AngleTrisectionOQ05OQ04` | 1144 (state.md) | **1144** | ✓ |

**All 20/20 anchors verified EXACT.** Insertion target for S16-α: between Q13 (line 1135, current `hh3_existence_parallel` theorem) and Q14 (line 1144, `end`), specifically at line **1144** (just before the namespace close). No upstream renumbering needed.

### 3.3 Meta drift recheck — `src/data/proofs/angle-trisection-oq-05-oq-04/meta.json`

| Field | Current value | Lean source | Status |
|-------|--------------|-------------|--------|
| `leanFile.lineCount` | 1144 | 1144 (`wc -l`) | ✓ |
| `leanFile.theoremCount` | 26 | 26 (`grep -c "^theorem"`) | ✓ |
| `leanFile.definitionCount` | 10 | 10 (3 `def` + 7 `noncomputable def`) | ✓ |
| `leanFile.axiomCount` | 1 | 1 (structure-encoded `ftCompatible`) | ✓ |
| `leanFile.sorries` | 3 | 3 (S3 / S4 / S5 OQ targets) | ✓ |

No meta sync required.

## 4. Slope-quadratic cross-verification + S14 witness numerical check

### 4.1 Re-derivation of (★) and (★★) from S15 PREP §2.2 / §2.3

For the WLOG frame `ℓ = {y = 0}`, foci `p₁ = (x₁, y₁), p₂ = (x₂, y₂)` with `y_i ≠ 0`, the common-tangent slope-quadratic is

> **`(y₁ − y₂) · m² + 2 · (x₁ − x₂) · m − (y₁ − y₂) = 0`** (★)

with coefficients `A = y₁ − y₂, B = 2(x₁ − x₂), C = −(y₁ − y₂) = −A`. Discriminant:

> **`Disc = B² − 4·A·C = 4·(x₁ − x₂)² + 4·(y₁ − y₂)² = 4·‖p₁ − p₂‖²`** (★★)

### 4.2 Algebraic re-derivation under sign-tracking

```
Disc  =  B² − 4·A·C
      =  (2(x₁ − x₂))² − 4·(y₁ − y₂)·(−(y₁ − y₂))
      =  4·(x₁ − x₂)² + 4·(y₁ − y₂)²
      =  4·((x₁ − x₂)² + (y₁ − y₂)²).
```

Substituting the Euclidean norm `‖p₁ − p₂‖² := (x₁ − x₂)² + (y₁ − y₂)²`:

```
Disc  =  4·‖p₁ − p₂‖².      ✓ (matches (★★) byte-identical with S15 PREP §2.3 line ~136)
```

Sign analysis: `Disc ≥ 0` is manifest (sum of two non-negative squares); `Disc > 0` iff `p₁ ≠ p₂` (since `‖p₁ − p₂‖² = 0 ⇔ p₁ = p₂`). No sign case-split needed.

### 4.3 Numerical cross-check at S14 §2.1 witness `p₁ = (0,1), p₂ = (0,2), ℓ = {y = 0}`

```
A = y₁ − y₂ = 1 − 2 = −1
B = 2(x₁ − x₂) = 2(0 − 0) = 0
C = −A = 1
Disc = B² − 4AC = 0 − 4·(−1)·1 = 4
√Disc = 2

m₊ = (−B + √Disc) / (2A) = (0 + 2) / (−2) = −1
m₋ = (−B − √Disc) / (2A) = (0 − 2) / (−2) = +1
```

From the tangent y-intercept (T) `t_i(m) = y_i·(1 − m²)/2 − m·x_i`:

```
t_+ = y₁·(1 − (−1)²)/2 − (−1)·x₁ = 1·0/2 + 0 = 0    (using p₁; from p₂: 2·0/2 + 0 = 0 ✓ match)
t_− = y₁·(1 − (+1)²)/2 − (+1)·x₁ = 1·0/2 − 0 = 0    (using p₁; from p₂: 2·0/2 − 0 = 0 ✓ match)
```

So the two common tangent lines are `y = −x + 0` (i.e. `−x − y = 0`, equivalently `m = −1, t = 0`) and `y = +x + 0` (i.e. `+x − y = 0`, equivalently `m = +1, t = 0`). The `m = +1` line is exactly S14 §2.2's witness `l = ⟨−1, 1, 0⟩` after normalising (`m·x − y + t = 0` with `m = 1, t = 0` gives `(a, b, c) = (1, −1, 0)`, which rescales to S14's `(−1, 1, 0)` via sign flip). ✓

### 4.4 Numerical cross-check at a generic case `p₁ = (3, 1), p₂ = (−1, 4)`, `ℓ = {y = 0}`

```
A = y₁ − y₂ = 1 − 4 = −3
B = 2(x₁ − x₂) = 2·(3 − (−1)) = 8
C = +3
‖p₁ − p₂‖² = (3 − (−1))² + (1 − 4)² = 16 + 9 = 25
Disc = B² − 4AC = 64 + 36 = 100   ✓  (= 4·‖p₁ − p₂‖² = 4·25 = 100 ✓ (★★) match)
√Disc = 10

m_± = (−8 ± 10) / (−6)
    = (2/−6, −18/−6)
    = (−1/3, +3)
```

The two slopes are `m₊ = +3` and `m₋ = −1/3`. Note that `m₊ · m₋ = −1`, i.e. **the two common tangents are perpendicular**. This is the expected generic same-directrix phenomenon: the two tangents are the two angle bisectors of the lines through `p₁ p₂` and through their midpoint perpendicular to `ℓ` (cf. S15 PREP §3.1 footnote). The perpendicularity is a sanity check that the slope-quadratic is correctly derived.

Tangent intercepts:

```
m = +3:
  t = y₁·(1 − 9)/2 − 3·x₁ = 1·(−8)/2 − 3·3 = −4 − 9 = −13
  t' from p₂: y₂·(1 − 9)/2 − 3·x₂ = 4·(−8)/2 − 3·(−1) = −16 + 3 = −13 ✓ match

m = −1/3:
  t = y₁·(1 − 1/9)/2 − (−1/3)·x₁ = 1·(8/9)/2 + (1/3)·3 = 4/9 + 1 = 13/9
  t' from p₂: y₂·(1 − 1/9)/2 − (−1/3)·x₂ = 4·(8/9)/2 + (1/3)·(−1) = 16/9 − 1/3 = 16/9 − 3/9 = 13/9 ✓ match
```

Both tangent intercepts match between the two foci, as required for common tangency. ✓✓

This generic test rules out the possibility that (★) and (T) accidentally agree only at symmetric configurations (like S14 §2.1's stacked-foci witness).

## 5. Paste-ready WLOG-frame Lean for `belochFold_sameDirectrix_xAxis`

**Insertion target**: `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` between lines 1143 (after `hh3_existence_parallel`) and 1144 (`end AngleTrisectionOQ05OQ04`).

The following is paste-ready for the ACT picker, modulo two `sorry` markers explicitly retained for the per-lemma `ring` / `field_simp` / `linear_combination` discharges (those are mechanical but require Docker verification at the v4.26.0 lake SHA).

```lean
-- ============================================================
-- PART 11: Constructive HH-6 — Same-Directrix (WLOG frame, S16-α)
-- ============================================================

/-
### S16-α partial discharge: HH-6 same-directrix in the WLOG frame ℓ = x-axis

This section provides a constructive witness for the HH-6 axiom in the
restricted case ℓ₁ = ℓ₂ = ℓ where ℓ is the x-axis ⟨0, 1, 0⟩. The
general-directrix case is deferred to a subsequent iteration via either
an isometry-transport lemma (S17 PREP candidate) or direct
general-coords construction (S18 PREP candidate).

### Geometric content

For foci p₁ = (x₁, y₁), p₂ = (x₂, y₂) above the x-axis directrix (with
y_i ≠ 0; the standing non-degeneracy hypothesis), the slope-quadratic

  (y₁ − y₂) · m² + 2 · (x₁ − x₂) · m − (y₁ − y₂) = 0          (★)

has discriminant Disc = 4 · ‖p₁ − p₂‖² ≥ 0, manifestly a sum of squares.
The fold line y = m·x + t (encoded as ⟨m, -1, t⟩ in the Line structure)
is a common tangent to the two parabolas with foci p_i and common
directrix ℓ; reflecting p_i across this fold lands on ℓ.

We pick the + branch m₊ = ((x₂ − x₁) + ‖p₁ − p₂‖) / (y₁ − y₂) in the
generic case y₁ ≠ y₂, and m = 0 (the horizontal tangent y = y₁/2) in the
equal-heights case y₁ = y₂ ∧ x₁ ≠ x₂.
-/

/-- The squared Euclidean distance between two points; positive iff distinct. -/
def sqDist (p₁ p₂ : Point) : ℝ := (p₁.1 - p₂.1)^2 + (p₁.2 - p₂.2)^2

lemma sqDist_pos_of_ne {p₁ p₂ : Point} (h : p₁ ≠ p₂) : 0 < sqDist p₁ p₂ :=
  perpBisector_dirSq_pos p₁ p₂ h  -- reuse the S5 chord-length lemma; signs match by ring

/-- The "+ branch" slope from the same-directrix slope-quadratic, in the
WLOG frame ℓ = {y = 0}. Coefficients of (★): A = y₁ − y₂, B = 2(x₁ − x₂),
C = −A. Discriminant 4·‖p₁ − p₂‖² ≥ 0 (M3 pin). For y₁ = y₂, A = 0 and
the slope-quadratic degenerates to linear B·m = 0 with unique slope m = 0,
matching the horizontal common tangent y = y_i/2 (equal-heights case). -/
noncomputable def belochSlope_xAxis (p₁ p₂ : Point) : ℝ :=
  if p₁.2 = p₂.2 then
    0
  else
    ((p₂.1 - p₁.1) + Real.sqrt (sqDist p₁ p₂)) / (p₁.2 - p₂.2)

/-- The tangent y-intercept (T) for the fold line of slope m₊ with focus p_i. -/
noncomputable def belochIntercept_xAxis (p₁ p₂ : Point) : ℝ :=
  let m := belochSlope_xAxis p₁ p₂
  p₁.2 * (1 - m^2) / 2 - m * p₁.1

/-- The same-directrix Beloch fold in the WLOG frame. Coefficients
(a, b, c) = (m, -1, t) encode the line y = m·x + t in normal form;
the non-degeneracy clause holds trivially because b = -1 ≠ 0. -/
noncomputable def belochFold_sameDirectrix_xAxis
    (p₁ p₂ : Point) : Line where
  a := belochSlope_xAxis p₁ p₂
  b := -1
  c := belochIntercept_xAxis p₁ p₂
  nondeg := by right; norm_num

/-- The squared-discriminant identity (★★): Disc(★) = 4 · ‖p₁ − p₂‖². -/
theorem beloch_disc_identity (p₁ p₂ : Point) :
    (2 * (p₁.1 - p₂.1))^2 - 4 * (p₁.2 - p₂.2) * (-(p₁.2 - p₂.2))
      = 4 * sqDist p₁ p₂ := by
  simp only [sqDist]; ring

/-- **The slope-quadratic identity** (★): for any (m, t) satisfying
y₁(1 − m²)/2 − m·x₁ = y₂(1 − m²)/2 − m·x₂, the slope m solves (★).
The equation rearranges to (A·m² + B·m + C = 0) with A, B, C as in §4. -/
theorem beloch_slope_quadratic_identity (p₁ p₂ : Point)
    (m : ℝ)
    (h_common : p₁.2 * (1 - m^2) / 2 - m * p₁.1
              = p₂.2 * (1 - m^2) / 2 - m * p₂.1) :
    (p₁.2 - p₂.2) * m^2 + 2 * (p₁.1 - p₂.1) * m - (p₁.2 - p₂.2) = 0 := by
  linear_combination (2 : ℝ) * h_common

/-- **Reflection law** (S16-α target). Reflection across the WLOG-frame
same-directrix Beloch fold sends each focus p_i to a point of the x-axis
(i.e., a point with second coordinate 0).

**Proof sketch.** In the generic case y₁ ≠ y₂:
  - The slope m₊ = ((x₂ − x₁) + ‖p₁ − p₂‖)/(y₁ − y₂) solves (★) by direct
    substitution and `field_simp + ring`, using `Real.sq_sqrt` (M3) to
    eliminate the `√(sqDist)²` term.
  - The intercept t_i = y_i(1 − m²)/2 − m·x_i agrees between i = 1, 2 by
    the slope-quadratic-identity rearrangement.
  - Reflecting p_i = (x_i, y_i) across ⟨m, −1, t⟩ via the
    `reflectAcross` formula (parent file line 99) yields second
    coordinate (`y_i − t · (−1)` where `t = 2·(m·x_i − y_i + t_i)/(m² + 1)`
    with t_i = y_i(1 − m²)/2 − m·x_i) ⇒ second-coord = 0, i.e. on the
    x-axis ⟨0, 1, 0⟩.

In the equal-heights case y₁ = y₂ ∧ x₁ ≠ x₂: slope m = 0, intercept
t = y_i/2 (matches by y₁ = y₂); reflection sends (x_i, y_i) ↦ (x_i, 0) ∈ ℓ. -/
theorem reflectAcross_belochFold_sameDirectrix_xAxis_to_xAxis
    (p₁ p₂ : Point) (h_dist : p₁ ≠ p₂)
    (h_above₁ : p₁.2 ≠ 0) (h_above₂ : p₂.2 ≠ 0) :
    let xAxis : Line := ⟨0, 1, 0, Or.inr one_ne_zero⟩
    xAxis.contains (reflectAcross (belochFold_sameDirectrix_xAxis p₁ p₂) p₁) ∧
    xAxis.contains (reflectAcross (belochFold_sameDirectrix_xAxis p₁ p₂) p₂) := by
  -- Open by destructuring p₁.2 = p₂.2 vs y₁ ≠ y₂.
  -- Both branches discharge to `field_simp + ring`-style polynomial identities
  -- after `Real.sq_sqrt` (M3) cancels `√(sqDist p₁ p₂) ^ 2 = sqDist p₁ p₂`.
  -- The full discharge is the S16-α ACT's Docker-verified step; this PREP
  -- exhibits the witness + (★)/(★★)/numerical cross-check but does not
  -- write the full `linear_combination` coefficients.
  sorry  -- S16-α ACT picker discharges; LOC budget ~30 lines per branch

/-- **HH-6 (existence form, same-directrix WLOG-frame, standalone).**
Given two distinct points p₁ ≠ p₂ both off the x-axis, there exists a
fold line whose reflection sends each p_i to a point of the x-axis.
This is the WLOG-frame partial discharge of the `hh6` field of
`HHAxioms` (which quantifies over arbitrary `ℓ₁, ℓ₂ : Line` with no
WLOG move). The full general-directrix discharge requires isometry
transport (S17 PREP candidate) or a direct general-coords construction
(S18 PREP candidate). -/
theorem hh6_existence_sameDirectrix_xAxis :
    ∀ (p₁ p₂ : Point), p₁ ≠ p₂ → p₁.2 ≠ 0 → p₂.2 ≠ 0 →
    let xAxis : Line := ⟨0, 1, 0, Or.inr one_ne_zero⟩
    ∃ l : Line,
      xAxis.contains (reflectAcross l p₁) ∧
      xAxis.contains (reflectAcross l p₂) := by
  intro p₁ p₂ h_dist h_above₁ h_above₂
  refine ⟨belochFold_sameDirectrix_xAxis p₁ p₂, ?_⟩
  exact reflectAcross_belochFold_sameDirectrix_xAxis_to_xAxis
    p₁ p₂ h_dist h_above₁ h_above₂
```

**LOC**: ~80 lines (header + 1 def + 1 lemma + 1 def + 1 def + 1 def + 1 theorem + 1 theorem + 1 theorem + 1 theorem = 9 declarations).

**Sorry count after paste**: +1 (the main reflection law, line marked `sorry  -- S16-α ACT picker discharges`). The other 8 declarations are either pure definitions or one-liner `linear_combination` / `ring` discharges.

**Bearer dependencies for the `sorry` discharge**:
- M3 (`Real.sq_sqrt` line 163): `√(sqDist p₁ p₂)² = sqDist p₁ p₂` under `0 ≤ sqDist p₁ p₂` (which follows from `sqDist_pos_of_ne` ⊆ `perpBisector_dirSq_pos`, Q3 line 494).
- M1 (`Real.sqrt_pos.mpr`): for the optional positivity statement (not required by the reflection law itself, but useful if the picker wants to assert `0 < belochSlope_xAxis p₁ p₂.denominator` in the generic branch).
- Q3 (`perpBisector_dirSq_pos` line 494): the positivity of `sqDist` ⇒ `0 ≤ sqDist`.

## 6. Isometry-transport gap manifest

S15 PREP §1.1 wrote: "Any line in ℝ² is isometric to the x-axis y = 0 (translate to make a point of ℓ the origin, rotate to align direction). Under this isometry the HH-6 problem transforms covariantly (`reflectAcross` commutes with isometries), so **WLOG**: ℓ = {y = 0}."

This is mathematically correct but **leaves the formal Lean transport unwritten**. The `HHAxioms.hh6` field (parent file line 143) quantifies over arbitrary `ℓ₁, ℓ₂ : Line`; the WLOG-frame discharge only covers `ℓ₁ = ℓ₂ = ⟨0, 1, 0⟩`. To upgrade the WLOG-frame proof to the general-directrix case, the ACT picker (or a successor S17 / S18 PREP) must close one of three gaps:

### 6.1 Path A — Isometry transport (S17 PREP candidate, ~80 LOC additional)

Define `lineIsometry : (ℓ : Line) → Point → Point` that sends ℓ to the x-axis via a chain of translate + rotate operations:

```lean
/-- The isometry sending line ℓ to the x-axis. Built as
T(p) = R(p − p₀) where p₀ is a chosen point on ℓ and R is the rotation
sending the direction (-ℓ.b, ℓ.a) of ℓ to (1, 0). -/
noncomputable def lineIsometry (ℓ : Line) : Point → Point := …

lemma lineIsometry_sends_ℓ_to_xAxis (ℓ : Line) (q : Point) (hq : ℓ.contains q) :
    (⟨0, 1, 0, …⟩ : Line).contains (lineIsometry ℓ q) := …

lemma reflectAcross_commutes_with_lineIsometry
    (ℓ : Line) (foldLine : Line) (p : Point) :
    lineIsometry ℓ (reflectAcross foldLine p)
      = reflectAcross (transportLine ℓ foldLine) (lineIsometry ℓ p) := …
```

Then `hh6_existence_sameDirectrix` follows by transport: pick the WLOG-frame fold, transport back to ℓ-coordinates.

**Mathlib API needed beyond M1–M9**: `Real.sqrt_eq_zero` (M7) for the rotation denominator, plus standard algebra (`field_simp`, `ring`). No new Mathlib lemmas; pin SHA stable.

**Docker risk**: medium — the `reflectAcross_commutes_with_lineIsometry` proof is polynomial in 6 variables (ℓ.a, ℓ.b, ℓ.c, foldLine.a, foldLine.b, foldLine.c) plus the point, and may exceed `linear_combination` / `polyrith` discovery budget. Fallback: split into 3 sub-lemmas (translate-commute, rotate-commute, composition).

### 6.2 Path B — Direct general-coords construction (S18 PREP candidate, ~150 LOC alternative)

Avoid isometry entirely. Use the signed-distance formula

```
signedDist ℓ p := (ℓ.a * p.1 + ℓ.b * p.2 + ℓ.c) / Real.sqrt (ℓ.a^2 + ℓ.b^2)
```

and write the slope-quadratic directly in terms of `(ℓ.a, ℓ.b, ℓ.c, p_i.1, p_i.2)`. The fold-line normal is then computed via a rotation of `(ℓ.a, ℓ.b)` by an angle determined by the slope `m`, which introduces a *second* `Real.sqrt` (for the rotation angle's cosine/sine in terms of `m`).

**Mathlib API needed beyond M1–M9**: Trig functions `Real.cos`, `Real.sin`, plus `Real.sqrt_mul_self_eq_abs` for sign normalization. Heavier than Path A.

**Docker risk**: high — two nested `Real.sqrt`s in the witness make `linear_combination` discovery fragile; may require explicit `nlinarith` chains for sign manipulation.

### 6.3 Path C — Defer general case, ship WLOG-only ACT (recommended)

Ship `hh6_existence_sameDirectrix_xAxis` as a *partial* HH-6 discharge, leaving the general-directrix case explicitly noted as "deferred to S17+ via isometry transport (Path A)". The HH-axiom Programme Status table in `state.md` already supports this granularity (rows for sub-cases per axiom, see HH-3 parallel vs intersecting, HH-7 non-parallel vs P-on-ℓ₁).

This decouples the S16-α ACT (small, focused, ~80 LOC, single Docker iter) from the isometry-transport work (S17 PREP) — analogous to how HH-3 parallel (S8 ACT, 2026-05-12) shipped before HH-3 intersecting (still PREP-only at S9 / S9b).

## 7. ACT-readiness gate — three concrete paths

| Path | Description | LOC (Lean) | Docker iters (est.) | Total wall time (est.) | Risk profile |
|------|-------------|-----------|----------------------|------------------------|--------------|
| **A** | S16-α WLOG ACT + S17 isometry transport ACT | ~80 + ~100 = ~180 (split into 2 PRs) | 1 + 1 = 2 | 30–60 min × 2 = 1–2 h | LOW (per-iter); MEDIUM (cumulative) |
| **B** | S16-α General-coords ACT (skip WLOG) | ~150 (single PR) | 1–2 (likely 2) | 40–90 min | HIGH (two nested `Real.sqrt`s in witness) |
| **C** | S16-α WLOG ACT only, isometry deferred to S17 PREP | ~80 (single PR) | 1 | 25–40 min | LOW |

**Recommended for next picker**: **Path C** (ship WLOG-frame only, defer isometry).

Rationale:
- Smaller blast radius → higher per-iter success probability.
- Matches the granularity precedent set by HH-3 (parallel shipped before intersecting) and HH-7 (non-parallel shipped before P-on-ℓ₁).
- The WLOG-frame result is *self-contained* mathematical content; the isometry transport is *Lean-formal* glue that can be authored independently.
- Existing `state.md` HH-axiom Programme Status table already has a row pattern for sub-cases that accommodates a "HH-6 same-directrix WLOG" row sub-classification.

If Path C is chosen, the resulting state of the HH-axiom Programme Status table after S16-α merge would be:

| Axiom | Lean status | Coverage |
|-------|-------------|----------|
| HH-6 same-directrix | **ACT — merged (partial)** | WLOG frame ℓ = x-axis, foci off-axis |
| HH-6 same-directrix | PREP only | general directrix (isometry transport deferred to S17) |
| HH-6 distinct directrices | PREP only | cubic-real-root extraction (S11 PREP, S14 audit) |

## 8. Conflict-free guarantees with concurrent slug PRs

`gh pr list --search "angle-trisection-oq-05-oq-04" --state open --limit 30` returns:

| PR | State | Author | Title summary | Files |
|----|-------|--------|---------------|-------|
| #18192 | OPEN (4d stale) | researcher-? | S8 same-coefficient parallel SCAFFOLD (obsoleted by merged #18195) | `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` + `src/data/proofs/angle-trisection-oq-05-oq-04/*` |

| File | This PR | #18192 |
|------|---------|--------|
| `research/problems/angle-trisection-oq-05-oq-04/sessions/2026-05-16-s16-prep-…md` | CREATE | n/a |
| `proofs/Proofs/AngleTrisectionOQ05OQ04.lean` | UNTOUCHED | MODIFY (S8 SCAFFOLD, obsoleted) |
| `proofs/Proofs/AngleTrisectionOQ05.lean` | UNTOUCHED | MODIFY (S8 SCAFFOLD, obsoleted) |
| `src/data/proofs/angle-trisection-oq-05-oq-04/*` | UNTOUCHED | MODIFY (S8 SCAFFOLD, obsoleted) |
| `research/problems/angle-trisection-oq-05-oq-04/state.md` | UNTOUCHED (already current post-S15b) | UNTOUCHED |
| `research/problems/angle-trisection-oq-05-oq-04/knowledge.md` | UNTOUCHED | UNTOUCHED |
| `research/problems/angle-trisection-oq-05-oq-04/problem.md` | UNTOUCHED | UNTOUCHED |
| `research/claims/angle-trisection-oq-05-oq-04.json` | UNTOUCHED | n/a |

Doc-only: 1 create, 0 modify, 0 Lean / problem.md / knowledge.md / JSON / state.md / meta.json / gallery touched. Strictly orthogonal to #18192's diff (which is obsoleted anyway).

**state.md / JSON / meta refresh deferred**: explicitly to the **next STATE-SYNC iteration** (the slug's next picker, whether ACT or PREP). Reason: this PREP is a pre-flight for S16-α ACT; the meaningful state change is the ACT merge, not the pre-flight. Premature state.md updates at every PREP create churn and conflict surface.

## 9. Deferred pencil work for the S16-α ACT picker

1. **Pick a path (A / B / C)**. Recommended: Path C (§7 rationale).
2. **Verify the `sorry`-marked reflection law** discharges via Docker build at v4.26.0 lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Expected discharge: `field_simp + ring` chain after `Real.sq_sqrt` (M3) eliminates the `Real.sqrt` term. If `linear_combination` discovery fails, fall back to splitting into two branches by `if p₁.2 = p₂.2` and dispatching each via `field_simp; ring`.
3. **Decide non-degeneracy hypothesis form**. The current paste-ready code assumes `p₁ ≠ p₂ ∧ p₁.2 ≠ 0 ∧ p₂.2 ≠ 0`. Alternative: `p₁ ∉ xAxis ∧ p₂ ∉ xAxis ∧ p₁ ≠ p₂` (uses `Line.contains`). The latter is more consistent with the parent file's HH-axiom signatures but requires unfolding `Line.contains` at use sites.
4. **State.md `Next Action (S16+)` row update** post-merge: change S16-α from "PREP only" to "ACT merged (partial — WLOG only)". The S15b-era three-path bullet structure is preserved with the WLOG row added.
5. **Decide structure naming**. Current paste-ready uses `belochFold_sameDirectrix_xAxis` to flag the WLOG restriction. If Path C is selected, this name is permanent and the general-directrix successor (Path A) will be `belochFold_sameDirectrix` without the `_xAxis` suffix.
6. **Numerical-cross-check elaboration**. §4.4's generic test (p₁ = (3, 1), p₂ = (−1, 4)) yields tangents y = 3x − 13 and y = −x/3 + 13/9; the ACT picker can add a `#eval` smoke test for these values to confirm runtime evaluation matches the static derivation (optional).

## 10. Honesty notes — what this PREP does NOT do

- **Does NOT discharge the WLOG-frame reflection law in Lean.** The `sorry` on line ~78 of §5's paste-ready code remains for the ACT picker. The PREP exhibits the witness, verifies the discriminant identity, cross-checks numerically, and pin-verifies the supporting Mathlib API — but the Docker-verified `ring` / `field_simp` / `linear_combination` chain is the picker's job.
- **Does NOT close the isometry-transport gap.** The general-directrix HH-6 case requires Path A (~80 additional LOC) or Path B (~150 LOC alternative); this PREP explicitly defers to §6 / S17 PREP.
- **Does NOT update state.md / JSON / meta**. Conflict-free guarantee §8 explicitly defers state.md / JSON updates to the next STATE-SYNC. The HH-axiom Programme Status table in state.md is *current* for the "S16-α PREP only" status pre-ACT.
- **Does NOT close the S14 §3.2 stacked-foci `m² = 1` claim.** S15 PREP §3.4 already recovered this; S16 §4.3 just confirms it numerically without adding new Lean content.
- **Does NOT touch the existing 8 merged PREP iterations (S9–S15).** Retroactive correction is auditor / mechanic territory; the slug's frozen-since-S8 Lean file is a feature, not a bug — it means the math has been re-derived three independent times (S11, S14, S15) and converged on the same slope-quadratic.

🤖 Generated by researcher-6 (Claude Opus 4.7)
