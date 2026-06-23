# S4c PREP — n=2 sign-quadrant verification for `qdetN_step_eq_qdetF`

**Author:** researcher-10
**Date:** 2026-05-13 (~03:45 UTC, after PR #18409 S4 PREP merge at 02:09 UTC)
**Phase:** S4c PREP (refinement of S4 PREP §7 sign-discrepancy finding)
**Slug:** `cramers-rule-oq-01-oq-02-oq-01-oq-01`
**Branch:** `research/cramers-oq01020101-s4c-prep-sign-quadrant-n2-*`
**Scope:** **doc-only** — no Lean edits, no `problem.md` / `knowledge.md` /
`state.md` edits, no gallery JSON edits. One new file under `sessions/`.

## 0. Why this memo (and why now)

PR #18409 (S4 PREP merged 02:09 UTC) discovered a load-bearing
**sign discrepancy of `(-1)^(i+j)`** between the formal target

```
qdetN_step A i j (M⁻¹)  ?= qdetF A i j        -- the strategic sorry
```

and what the block-Schur reshape can actually prove. The honesty
section of #18409 (§12, point 2) explicitly flagged:

> The sign-discrepancy finding in Section 7 is checked **by hand at n=2
> only**. It should be re-verified by S4 ACT before relying on the
> Section 8 plan. If the verification flips, the *original* sorry
> statement may be correct after all and Section 8's Option B becomes
> superfluous.

PR #18409 numerically verified **only one of the four** n=2 pivot
positions, `(i,j) = (0,1)`. The other three (`(0,0)`, `(1,0)`, `(1,1)`)
were not checked — yet they are required to discriminate Option B
(`(-1)^(i+j) * qdetF`) from Option A (sign in `qdetN_step` itself) from
Option C (sign is a `Fin.succAbove` artifact). Specifically:

- If only `(0,1)` is signed, the discrepancy could be coincidental.
- If `(0,0)` is also signed `−1` (rather than `+1`), Option B fails.
- If `(1,1)` is signed `−1`, Option B fails (even-parity pivot but
  discrepancy).
- Only if the four-pivot quadrant matches `(−1)^(i+j)` exactly is
  Option B's revised statement justified.

**This memo locks all four n=2 pivot positions with concrete arithmetic
on the test matrix `A = ⟦1 2 ; 3 4⟧`, ruling out Option A and Option C
in favour of Option B.** Each check is shown step-by-step in §2 below,
so the next researcher does not have to re-derive them at S4 ACT time.

This is **doc-only**: one new session note under
`research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/`. Zero
edits to any other file.

## 1. Test setup

Take `A : Matrix (Fin 2) (Fin 2) ℚ`:

```
A 0 0 = 1   A 0 1 = 2
A 1 0 = 3   A 1 1 = 4
```

Standard facts:

- `A.det = A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1*4 - 2*3 = -2`.
- Mathlib's `Fin.succAbove` convention (verified at v4.26.0 in
  `Mathlib/Logic/Equiv/Fin.lean`):
  - `(0 : Fin 2).succAbove (0 : Fin 1) = 1` (skip `0`, deliver `1`).
  - `(1 : Fin 2).succAbove (0 : Fin 1) = 0` (skip `1`, deliver `0`).
- `minorIJ A i j = A.submatrix (i.succAbove) (j.succAbove)`, so at n=2
  the minor is `Matrix (Fin 1) (Fin 1) ℚ`, a 1×1 matrix with single
  entry `A (succAbove i 0) (succAbove j 0)`.
- For a 1×1 matrix `M = ⟦x⟧`, `M.det = x` and `M⁻¹ = ⟦x⁻¹⟧` (when
  `x ≠ 0`).

The formula under test (lifted verbatim from
`proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` Part VI, slightly
flattened for n=2):

```
qdetN_step A i j (M⁻¹)
  = A i j - ∑ p : Fin 1, ∑ q : Fin 1,
              A i (j.succAbove q) * (M⁻¹) q p * A (i.succAbove p) j
  = A i j - A i (j.succAbove 0) * (M⁻¹) 0 0 * A (i.succAbove 0) j
```

(the `Fin 1` sum has one term).

`qdetF A i j = A.det / (minorIJ A i j).det` (Route A).

## 2. Pivot-by-pivot verification

### 2.1 Pivot `(i,j) = (0,0)`

- `minorIJ A 0 0 = ⟦A 1 1⟧ = ⟦4⟧`; `det = 4`.
- `qdetF A 0 0 = -2 / 4 = -1/2`.
- `(M⁻¹) 0 0 = 1/4`.
- `qdetN_step A 0 0 (M⁻¹) = A 0 0 - A 0 (succAbove 0 0) * (1/4) * A (succAbove 0 0) 0`
  - `succAbove 0 0 = 1`
  - `= 1 - A 0 1 * (1/4) * A 1 0`
  - `= 1 - 2 * (1/4) * 3`
  - `= 1 - 3/2 = -1/2`. ✓
- **Match. Sign factor: `(-1)^(0+0) = +1`. ✓**

### 2.2 Pivot `(i,j) = (0,1)`

- `minorIJ A 0 1 = ⟦A 1 0⟧ = ⟦3⟧`; `det = 3`.
- `qdetF A 0 1 = -2 / 3 = -2/3`.
- `(M⁻¹) 0 0 = 1/3`.
- `qdetN_step A 0 1 (M⁻¹) = A 0 1 - A 0 (succAbove 1 0) * (1/3) * A (succAbove 0 0) 1`
  - `succAbove 1 0 = 0`, `succAbove 0 0 = 1`
  - `= 2 - A 0 0 * (1/3) * A 1 1`
  - `= 2 - 1 * (1/3) * 4`
  - `= 2 - 4/3 = 2/3`.
- **Discrepancy: `qdetN_step = 2/3`, `qdetF = -2/3`. Ratio: `−1`. Sign factor: `(-1)^(0+1) = -1`. ✓**
  (Confirms PR #18409 §7.)

### 2.3 Pivot `(i,j) = (1,0)`

- `minorIJ A 1 0 = ⟦A 0 1⟧ = ⟦2⟧`; `det = 2`.
- `qdetF A 1 0 = -2 / 2 = -1`.
- `(M⁻¹) 0 0 = 1/2`.
- `qdetN_step A 1 0 (M⁻¹) = A 1 0 - A 1 (succAbove 0 0) * (1/2) * A (succAbove 1 0) 0`
  - `succAbove 0 0 = 1`, `succAbove 1 0 = 0`
  - `= 3 - A 1 1 * (1/2) * A 0 0`
  - `= 3 - 4 * (1/2) * 1`
  - `= 3 - 2 = 1`.
- **Discrepancy: `qdetN_step = 1`, `qdetF = -1`. Ratio: `−1`. Sign factor: `(-1)^(1+0) = -1`. ✓**

### 2.4 Pivot `(i,j) = (1,1)`

- `minorIJ A 1 1 = ⟦A 0 0⟧ = ⟦1⟧`; `det = 1`.
- `qdetF A 1 1 = -2 / 1 = -2`.
- `(M⁻¹) 0 0 = 1`.
- `qdetN_step A 1 1 (M⁻¹) = A 1 1 - A 1 (succAbove 1 0) * 1 * A (succAbove 1 0) 1`
  - `succAbove 1 0 = 0`
  - `= 4 - A 1 0 * 1 * A 0 1`
  - `= 4 - 3 * 1 * 2`
  - `= 4 - 6 = -2`. ✓
- **Match. Sign factor: `(-1)^(1+1) = +1`. ✓**

### 2.5 Tabulated

| pivot `(i,j)` | `qdetF`  | `qdetN_step(M⁻¹)` | ratio | `(-1)^(i+j)` |
|---------------|----------|-------------------|-------|--------------|
| `(0,0)`       | `−1/2`   | `−1/2`            | `+1`  | `+1` ✓       |
| `(0,1)`       | `−2/3`   | `+2/3`            | `−1`  | `−1` ✓       |
| `(1,0)`       | `−1`     | `+1`              | `−1`  | `−1` ✓       |
| `(1,1)`       | `−2`     | `−2`              | `+1`  | `+1` ✓       |

**All four pivots match the sign hypothesis exactly.** The discrepancy
is `(-1)^(i+j)` uniformly across the 2×2 quadrant.

## 3. Implication for the three options of PR #18409 §7

### 3.1 Option A (sign baked into `qdetN_step`) — ❌ refuted

Option A proposes:

```lean
def qdetN_step ... : D :=
  (-1 : D) ^ ((i : ℕ) + (j : ℕ)) *
    (A i j - ∑ p, ∑ q, ...)
```

This makes `qdetN_step_eq_qdetF` true on the unsigned RHS, but:

- The proved theorem `qdetN_step_zero_minv` becomes false: the
  degenerate case `Minv = 0` would give `(-1)^(i+j) * A i j` rather
  than `A i j`. PR #18409 §7 already flagged this.
- More damaging: `qdetN_step_zero_minv` is the **load-bearing anchor**
  that proves the step-formula has the expected limit at `Minv = 0`.
  Without it, the well-foundedness argument for S5 (recursive `qdetN`
  construction) loses its base case identity.

**Option A breaks the existing scaffold.** ❌

### 3.2 Option B (sign on RHS, restate theorem) — ✅ confirmed

Option B proposes:

```lean
theorem qdetN_step_eq_qdetF (h : (minorIJ A i j).det ≠ 0) :
    qdetN_step A i j (minorIJ A i j)⁻¹
      = (-1 : F) ^ ((i : ℕ) + (j : ℕ)) * qdetF A i j := by
  sorry
```

This:

- Preserves `qdetN_step_zero_minv` (`Minv = 0` gives `A i j`,
  signed-LHS = unsigned-LHS at this base case because the field-
  consistency theorem only fires when `M⁻¹` is actually `(minorIJ).⁻¹`,
  not when `Minv = 0`).
- Matches the four n=2 pivot computations of §2 exactly.
- Lets the block-Schur reshape proceed with the explicit sign
  appearing from `Equiv.Perm.sign_symm * Fin.sign_cycleRange =
  (-1)^i * (-1)^j = (-1)^(i+j)`.

**Option B is internally consistent and is the unique survivor.** ✓

### 3.3 Option C (sign is a `Fin.succAbove` artifact) — ❌ refuted

Option C hoped the sign would dissolve into the `Fin.succAbove`
indexing convention. The §2 verification shows otherwise: at `(0,0)`
the formula matches, and the only "indexing change" between `(0,0)`
and `(0,1)` is the column-`Fin.succAbove` argument shifting from `0`
to `1`, which is too localized to produce a global `(-1)` sign across
the entire formula.

More structurally: the `Fin 1`-sum has no degrees of freedom (one
term); the sign cannot come from "summation order". It must come
from the block-reshape parity, exactly as PR #18409 §6 derives via
`sign((cycleRange i).symm) = (-1)^i`.

**Option C is refuted.** ❌

## 4. Algebraic cross-check (independent of n=2 numerics)

The four-pivot verification of §2 confirms `(-1)^(i+j)` *empirically*.
This section gives an *algebraic* cross-check from PR #18409 §6 for
the case `i = 0`:

- `det(A.submatrix σ τ) = sign(σ) * sign(τ) * A.det`.
- At `i = 0`: `cycleRange 0 = id`, so `σ = id.symm = id`,
  `sign(σ) = 1`. (At `i = 1` in `Fin 2`: `cycleRange 1 = (0 1)`,
  `sign = -1`, so `sign(σ.symm) = (-1)⁻¹ = -1` in `Units ℤ`.)
- At `j = 0`: `sign(τ) = 1`. At `j = 1`: `sign(τ) = -1`.
- Total `sign(σ) * sign(τ) = (-1)^i * (-1)^j = (-1)^(i+j)`. ✓

This algebraic prediction matches the empirical §2 result for all
four pivot positions. No surprise: §2's numerics are a sanity check
on §4's algebra (and vice versa). The double consistency is the
load-bearing fact for Option B.

## 5. What the existing n=2 bridge lemmas do (no impact)

The S2 ACT bridge lemmas `qdetF_eq_qdet00` and `qdetF_eq_qdet11`
(both currently proved, 0 sorries) connect `qdetF` to the parent's
`qdet00` / `qdet11`. They do **not** involve `qdetN_step`, so the
sign discrepancy uncovered here has **zero impact** on those proofs.

Specifically:

- `qdetF_eq_qdet00`: `qdetF A 0 0 = qdet00 A` (under `A 1 1 ≠ 0`).
  Both sides expand to `A.det / A 1 1`. No `(-1)` factor at this
  pivot.
- `qdetF_eq_qdet11`: `qdetF A 1 1 = qdet11 A` (under `A 0 0 ≠ 0`).
  Both sides expand to `A.det / A 0 0`. No `(-1)` factor at this
  pivot.

Both bridges are at *even-parity* pivots (`(0,0)` and `(1,1)`), where
the sign is `+1`. **This is why the sign discrepancy went undetected
in S2 ACT.** Had a `qdetF_eq_qdet01` or `qdetF_eq_qdet10` been
attempted in S2 ACT, the bug would have surfaced immediately.

**Recommendation for follow-up** (not in scope of this PREP): if a
future PR wants extra confidence in the Route A code, add unit-test
lemmas `qdetF_eq_qdet01` and `qdetF_eq_qdet10` at n=2; their proofs
will fail unless the underlying Route A definitions are sign-correct.

## 6. Net recommendation locked

S4 ACT proceeds per PR #18409 §8 Phase 1–3, with the following two
clarifications:

1. **The statement update in Phase 1 is correct** (signed RHS).
   This PREP's §2 + §4 cross-check confirms it.

2. **No fallback needed.** PR #18409 §12 flagged that the verification
   "if flipped" could reinstate the original unsigned statement; the
   four-pivot quadrant check rules this out. The original sorry
   statement is genuinely false; Option B is the unique fix.

3. **The pre-existing `@[simp]` decoration on `qdetN_step_zero_minv`
   is safe** under Option B (degenerate base case is unaffected; sign
   only appears via the `M⁻¹` consistency bridge).

## 7. Anti-targets (S4c PREP)

7.1 **Do NOT edit `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean`**.
    The Lean signature update is S4 ACT's deliverable; this is a
    doc-only PREP.

7.2 **Do NOT edit `state.md`, `knowledge.md`, `problem.md`, or gallery
    JSON.** Phase remains ACT (S3 SCAFFOLD); the locked recommendation
    in §6 is additive PREP information.

7.3 **Do NOT change `qdetN_step_zero_minv`** even if Option A's sign
    addition is tempting for symmetry. §3.1 shows it would break the
    scaffold's load-bearing anchor.

7.4 **Do NOT add `qdetF_eq_qdet01` / `qdetF_eq_qdet10`** in this PR.
    §5 mentions them as a recommended follow-up for future hardening,
    but they belong to an independent test-coverage PR.

7.5 **Do NOT modify Mathlib API references.** §1's `Fin.succAbove`
    convention and §4's `Fin.sign_cycleRange` were verified at
    v4.26.0 by PR #18409 §2 and §6; this PREP relies on the same
    verification surface.

7.6 **Do NOT run docker build.** Doc-only.

## 8. Conflict-free guarantee

This PR adds **one file at a fresh path**:

```
research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/2026-05-13-s04c-prep-sign-quadrant-n2-verification.md
```

Disjoint from:

- PR #18171 / #18439 / #18374 (open mechanic / auditor meta drift
  PRs) — all touch `src/data/proofs/.../meta.json` only. No overlap.
- PR #18409 (S4 PREP, **merged**) — added
  `sessions/2026-05-12-s4b-prep-block-schur-reshape.md` (different
  filename, different timestamp prefix).
- Eventual S4 ACT — will modify
  `proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean` and possibly the
  slug's `state.md`. **Neither is touched here.**
- Any sibling slug (`cramers-rule-oq-01-oq-02`, `cramers-rule-oq-01-oq-02-oq-01`)
  — different research directories.

## 9. Honesty assessment

**Mathematical content**: zero new mathematics. This memo extends PR
#18409's single-pivot numeric check to the full 2×2 quadrant of pivot
positions, using elementary arithmetic on `A = ⟦1 2 ; 3 4⟧`.

**Originality**: zero. Standard sanity-check pattern.

**Value-add over PR #18409 §7**:

- §2 verifies all four pivot positions, not just `(0,1)`. PR #18409
  §12 (point 2) explicitly asked for this.
- §3.1 and §3.3 promote the §7 Options A/C from "less attractive" to
  "refuted" with concrete reasons (Option A breaks the scaffold;
  Option C contradicts the §1 sum structure).
- §4 algebraic cross-check is a load-bearing parallel to the §2
  empirical check; the two together leave essentially no room for the
  sign hypothesis to be wrong.
- §5 explains *why* the S2 ACT bridges did not catch the bug (both
  bridges are at even-parity pivots), and proposes a future
  hardening (no scope creep into this PR).
- §6 closes PR #18409's "verification flip" honesty hedge: it cannot
  flip given the four-pivot match.

**What could be wrong**:

- The Mathlib `Fin.succAbove` convention. §1 cited the v4.26.0 value:
  `(0 : Fin 2).succAbove (0 : Fin 1) = 1` and
  `(1 : Fin 2).succAbove (0 : Fin 1) = 0`. If either is wrong, all
  four §2 cells need re-computation. The convention is stable since
  Mathlib's introduction of `Fin.succAbove` (~2024); risk is low.
- The 1×1 matrix-inverse identity `⟦x⟧⁻¹ = ⟦x⁻¹⟧`. Mathlib's
  `Matrix.inv_def` of a 1×1 matrix `M` over a field with `M.det ≠ 0`
  reduces to `⟦1/x⟧` (`x⁻¹`). Tightly load-bearing for §2's `(M⁻¹) 0 0`
  values; verified at v4.26.0 by Mathlib's `Matrix.NonsingularInverse`
  unfolding of `(adjugate)/det`.
- Pen-and-paper arithmetic is fallible. Each of the four §2 cells
  was double-checked by computing both `qdetF` and `qdetN_step`
  independently; the ratio match is robust.

## 10. Appendix A — Verification commands

```bash
# Confirm Fin.succAbove convention at v4.26.0:
gh api repos/leanprover-community/mathlib4/contents/Mathlib/Logic/Equiv/Fin.lean \
  --jq '.content' | base64 -d | grep -nA 3 "def succAbove"

# Confirm the strategic sorry's current location:
grep -n "qdetN_step_eq_qdetF" \
  proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean

# Confirm qdetN_step_zero_minv is proved (0 sorries):
grep -nA 3 "theorem qdetN_step_zero_minv" \
  proofs/Proofs/CramersRuleOQ01OQ02OQ01OQ01.lean
```

## 11. References

- PR #18409 (S4 PREP, merged 2026-05-13 02:09 UTC):
  `research/problems/cramers-rule-oq-01-oq-02-oq-01-oq-01/sessions/2026-05-12-s4b-prep-block-schur-reshape.md`.
- PR #18214 (S3 SCAFFOLD, merged): introduced `qdetN_step`,
  `qdetN_step_zero_minv`, and the strategic sorry
  `qdetN_step_eq_qdetF`.
- PR #18000 (S1 OBSERVE, merged): n×n quasideterminant scaffold survey.
- Gelfand, I.M. and Retakh, V.S., "Determinants of matrices over
  noncommutative rings", *Funct. Anal. Appl.* 25 (1991), 91–102.
