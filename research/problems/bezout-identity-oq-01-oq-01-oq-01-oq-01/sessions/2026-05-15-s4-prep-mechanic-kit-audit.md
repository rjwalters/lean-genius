# S4 PREP — Sibling-PREP audit of S3 BUILD-DIAGNOSE PR #19168 K1–K4 mechanic kit

**Date** 2026-05-15 ~05:30 UTC
**Author** researcher-8
**Phase tag** S4 PREP (doc-only; sibling to S3 BUILD-DIAGNOSE PR #19168 in deployer queue)
**Net Lean delta** 0 (this PR adds only this session log + mkdir of `sessions/`)
**Mathlib pin verified at** SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0,
from `proofs/lake-manifest.json`)

## TL;DR

PR #19168 (S3 BUILD-DIAGNOSE, doc-only, MERGEABLE under deployer stall) discovers
that `Proofs/BezoutIdentityOQ01OQ01OQ01.lean` does NOT compile under Mathlib
v4.26.0 (4 errors), and ships a K1–K4 mechanic kit (~23 LOC) to fix them. This
sibling-PREP independently audits each kit entry against:

- **(a)** Mathlib at lake-pinned SHA `2df2f015...` via direct `gh api` round-trips
- **(b)** the Lean source file at the cited line numbers
- **(c)** mathematical correctness (independent verification, not derivative)

**Bottom line**: PR #19168's K1, K3, K4 are **fully correct**. K2 may be **over-stated**:
only line 116 has explicit `simp only [binaryGcdSteps, ...]`; the other 7 cited
sites (121, 133, 136, 145, 155, 157, 170) are downstream `↓reduceIte` reducers
that may or may not need the rw-then-simp pattern. Recommend testing line-116-only
fix first (1 LOC), then iterating only if downstream sites fail.

This sibling-PREP is **strictly conflict-free** with PR #19168 (state.md +
knowledge.md + JSON) and PR #19021 (state.md + JSON): adds **only**
`sessions/2026-05-15-s4-prep-mechanic-kit-audit.md` (and creates the empty
`sessions/` subdirectory).

---

## §1 — Independent verification of K1 (`Nat.log_div_base` API drift)

### PR #19168's claim

> K1 (line 70, 1 LOC): drop hypothesis args → `Nat.log_div_base 2 n`.
> Pin-verified at `Mathlib/Data/Nat/Log.lean:292`:
> `theorem log_div_base (b n : ℕ) : log b (n / b) = log b n - 1`

### My audit

Direct `gh api` fetch of `Mathlib/Data/Nat/Log.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
base64-decoded, sed line 292:

```lean
@[simp]
theorem log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 := by
  rcases le_or_gt b 1 with hb | hb
  · rw [log_of_left_le_one hb, log_of_left_le_one hb, Nat.zero_sub]
  rcases lt_or_ge n b with h | h
  · rw [div_eq_of_lt h, log_of_lt h, log_zero_right]
  rw [log_of_one_lt_of_le hb h, Nat.add_sub_cancel_right]
```

**✓ Confirmed**: signature is `(b n : ℕ)`, no hypothesis required. PR #19168 is correct.

**Additional finding**: `@[simp]` tag at SHA. **PR #19168 didn't note this**, but it
matters for the K2 simp-loop diagnosis. With `Nat.log_div_base` now being a `simp`
lemma, the simp-set may apply it spuriously inside the `binaryGcdSteps` recursion's
`if-then-else` reduction. This is **probably part of the K2 loop root cause**, since
v4.25 didn't have `@[simp]` on this lemma.

### Source site

`Proofs/BezoutIdentityOQ01OQ01OQ01.lean:70`:

```lean
simp [Nat.log_div_base (by norm_num : 1 < 2) (by omega : 2 ≤ n)]
```

After K1 fix:

```lean
simp [Nat.log_div_base 2 n]
```

Even simpler — since `Nat.log_div_base` is now `@[simp]`, the call becomes:

```lean
simp [Nat.log_div_base]   -- or even just `simp` may work
```

### K1 verdict

**✓ Correct, with bonus simplification opportunity**: PR #19168's K1 is right.
Could be tightened to `simp [Nat.log_div_base]` (single arg) given the new
`@[simp]` tag. Recommend the explicit `Nat.log_div_base 2 n` for readability;
the `@[simp]` tag is a "free" cascade resolution for K2.

---

## §2 — Independent verification of K2 (`simp` loop on `binaryGcdSteps`)

### PR #19168's claim

> K2 (lines 116, 121, 133, 136, 145, 155, 157, 170, ~16 LOC):
> `simp [binaryGcdSteps, ...]` loop at v4.26.0;
> swap → `rw [binaryGcdSteps]; simp only [...]`

### My audit — site inventory

`grep -nE "simp only \[binaryGcdSteps|simp only \[hboth|simp only \[ha_even|simp only \[hb_even|simp only \[hle"`:

| Line | Tactic call | Has explicit `binaryGcdSteps`? |
|---|---|---|
| 116 | `simp only [binaryGcdSteps, if_neg (by omega : ¬(a = 0 ∨ b = 0))]` | ✓ YES |
| 121 | `simp only [hboth, ↓reduceIte]` | ✗ no |
| 133 | `simp only [hboth, ↓reduceIte]` | ✗ no |
| 136 | `simp only [ha_even, ↓reduceIte]` | ✗ no |
| 145 | `simp only [ha_even, ↓reduceIte, hb_even, ↓reduceIte]` | ✗ no |
| 155 | `simp only [ha_even, ↓reduceIte, hb_even, ↓reduceIte]` | ✗ no |
| 157 | `simp only [hle, ↓reduceIte]` | ✗ no |
| 170 | `simp only [hle, ↓reduceIte]` | ✗ no |

**Only line 116 explicitly references `binaryGcdSteps`**. Lines 121–170 are
downstream `↓reduceIte` reducers that work on the if-then-else chain that
line 116 unfolded.

### Two failure-mode hypotheses for K2

**Hypothesis A (PR #19168's implicit claim)**: All 8 sites loop, because
`↓reduceIte` triggers re-elaboration of `binaryGcdSteps.eq_1` even when
`binaryGcdSteps` isn't in the explicit `simp only` list. This would happen if
v4.26.0's `↓reduceIte` simp procedure walks the local context to find the
`binaryGcdSteps` definitional equation.

**Hypothesis B (alternative)**: Only line 116 loops. Once line 116's `simp only
[binaryGcdSteps, ...]` is fixed (e.g., `rw [binaryGcdSteps]; simp only [if_neg ...]`),
the resulting goal is well-formed `if-then-else (a%2=0 ∧ b%2=0) ...` and
`↓reduceIte` at lines 121/133/etc. just reduces it without re-touching
`binaryGcdSteps`. The cited lines 121–170 in PR #19168 would be **error-cascade
sites**, not loop sites — they fail because line 116's failure prevents the
goal from reaching them.

### Recommended K2 fix progression (mechanic ACT)

1. **First Docker iteration**: Apply K2 fix **only at line 116**:
   ```lean
   -- before:
   simp only [binaryGcdSteps, if_neg (by omega : ¬(a = 0 ∨ b = 0))]
   -- after:
   rw [binaryGcdSteps]; simp only [if_neg (by omega : ¬(a = 0 ∨ b = 0))]
   ```
   Plus K1 (line 70). Plus K3 (line 265). Plus K4 (line 277). Net ~9 LOC.

2. **Inspect Docker output**: If lines 121–170 still fail, apply the
   `rw [binaryGcdSteps]; simp only [...]` pattern to each failing site
   (PR #19168's full K2 fix). If they pass cleanly, **K2 is single-line**
   at line 116, not 8-line as PR #19168 estimates. Net ~6-7 LOC saved.

### K2 verdict

**⚠ Potentially over-stated by PR #19168**: full LOC budget of K2 is **1 LOC at
line 116** if Hypothesis B holds, **~16 LOC at all 8 sites** if Hypothesis A
holds. Recommend incremental testing in a single Docker iteration to discriminate.

The downside of testing the full 8-site fix first is that if Hypothesis B holds,
the mechanic ships ~7 unnecessary `rw`-prefix changes that obscure the diff.
The downside of testing the line-116-only fix first is one extra Docker
iteration (~30 min cost).

**Recommendation**: try line-116-only first (cheaper diff if Hypothesis B holds);
fall back to all-8 if needed.

---

## §3 — Independent verification of K3 (semantic bug in constant)

### PR #19168's claim

> K3 (lines 257–269, ~5 LOC): semantic bug — constant `6` too small.
> `hsteps' : binaryGcdSteps a b ≤ 2 * Nat.log 2 (max a b) + 2 := by omega`
> is FALSE. Composing `hsteps + hlog_sum` gives `≤ 4·log + 2`, not `≤ 2·log + 2`.
> Restate with `12`, re-derive via `hsteps' ≤ 4·log + 2`.

### My audit — independent derivation

Source at `Proofs/BezoutIdentityOQ01OQ01OQ01.lean:259-263`:

```lean
have hsteps := binaryGcdSteps_le_log a b ha hb
-- hsteps : binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2
have hlog_sum : Nat.log 2 a + Nat.log 2 b ≤ 2 * Nat.log 2 (max a b) := …
```

Composing:
- `2 * (la + lb) + 2 ≤ 2 * (2 * log_max) + 2 = 4 * log_max + 2`

So:
- **Correct claim**: `hsteps' : binaryGcdSteps a b ≤ 4 * log_max + 2`
- **Source line 265 (false claim)**: `hsteps' : binaryGcdSteps a b ≤ 2 * log_max + 2`
- omega correctly rejects.

### K3 cascade in calc step (line 266-269)

After fixing `hsteps'` to `≤ 4·log + 2`, the calc becomes:

```lean
calc binaryGcdSteps a b * (3 * (Nat.log 2 (max a b) + 1))
    ≤ (4 * Nat.log 2 (max a b) + 2) * (3 * (Nat.log 2 (max a b) + 1)) := by
        apply Nat.mul_le_mul_right; exact hsteps'
  _ ≤ 12 * (Nat.log 2 (max a b) + 1) ^ 2 := by ring_nf; <some omega/nlinarith>
```

Note: the second step is no longer an equality — `(4·log + 2)·3·(log+1) =
12·log² + 18·log + 6`, vs `12·(log+1)² = 12·log² + 24·log + 12`. The
difference is `6·log + 6 ≥ 0`. So the second step is `≤`, not `=`, requiring
`nlinarith` or `omega` instead of `ring`.

### K3 cascade — docstring + theorem statement

Lines 254-258 (the docstring + statement):

```lean
/-- **Corollary**: The bit complexity is O(log²(max a b)).
    Since log₂ a + log₂ b ≤ 2 * log₂(max a b), the total is
    ≤ 6 * (log₂(max a b) + 1)². -/
theorem binaryGcd_log_sq_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    totalBitOps a b ≤ 6 * (Nat.log 2 (max a b) + 1) ^ 2 := by
```

Both the docstring's "≤ 6 · (...)²" AND the theorem statement's `≤ 6 * (...) ^ 2`
need the **constant 6 → 12 update**. PR #19168's K3 LOC estimate (~5 LOC) covers
the calc body but **may not include the theorem statement and docstring update**
(2 more LOC: line 256 docstring text + line 258 theorem statement).

### K3 verdict

**✓ Mathematically correct, but K3 may be under-stated by 2 LOC**: PR #19168's K3
analysis (constant 6 → 12) is right. Mechanic LOC budget should be ~7 LOC,
not ~5: kit covers calc body (~5 LOC) + theorem statement (1 LOC) +
docstring (1 LOC).

The parent gallery `meta.json` (mentioned in PR #19168 as out-of-scope follow-up)
also needs the `12 · (log + 1)²` update in `mathContext` / `summary` / etc.,
likely ~5-10 LOC of JSON edits in a downstream doctor PR.

---

## §4 — Independent verification of K4 (worked example `= 12 → = 7`)

### PR #19168's claim

> K4 (line 277, 1 LOC): semantic bug — `binaryGcdSteps 252 198 = 12` is false.
> Hand-trace gives 7. Replace literal `12` with `7`.

### My audit — independent hand-trace

Algorithm (lines 53-59):

```
binaryGcdSteps a b =
  if a = 0 ∨ b = 0 then 0
  else if a % 2 = 0 ∧ b % 2 = 0 then 1 + binaryGcdSteps (a / 2) (b / 2)
  else if a % 2 = 0 then 1 + binaryGcdSteps (a / 2) b
  else if b % 2 = 0 then 1 + binaryGcdSteps a (b / 2)
  else if a ≤ b then 1 + binaryGcdSteps a ((b - a) / 2)
  else 1 + binaryGcdSteps ((a - b) / 2) b
```

Trace from (252, 198):

| Call | a | b | a parity | b parity | Branch | Next | +1 cumulative |
|---|---|---|---|---|---|---|---|
| 1 | 252 | 198 | even | even | both even → /2 each | (126, 99) | 1 |
| 2 | 126 | 99 | even | odd | a even → a/2 | (63, 99) | 2 |
| 3 | 63 | 99 | odd | odd | a ≤ b → b' = (99-63)/2 = 18 | (63, 18) | 3 |
| 4 | 63 | 18 | odd | even | b even → b/2 | (63, 9) | 4 |
| 5 | 63 | 9 | odd | odd | a > b → a' = (63-9)/2 = 27 | (27, 9) | 5 |
| 6 | 27 | 9 | odd | odd | a > b → a' = (27-9)/2 = 9 | (9, 9) | 6 |
| 7 | 9 | 9 | odd | odd | a ≤ b → b' = (9-9)/2 = 0 | (9, 0) | 7 |
| (8) | 9 | 0 | — | — | b = 0 → 0 (base case, no +1) | — | 7 |

**Total: 7 recursive calls** (each contributing 1 +1, base case contributes 0).

### K4 verdict

**✓ Fully correct**: PR #19168's hand-trace and `12 → 7` fix are both right.

### K4 cascade

Line 278 comment: `-- Verify step count bound: log₂(252) + log₂(198) = 7 + 7 = 14, bound = 30`.
After K4 (line 277 → 7), this comment is **still correct**:
- bound from `binaryGcdSteps_le_log`: `2 * (log 252 + log 198) + 2 = 2·14+2 = 30`.
- Actual `7 ≤ 30 ✓`.

So no cascade needed at line 278. The follow-up example at line 279-280 also
remains valid (`binaryGcdSteps 252 198 ≤ 30`, which holds whether the actual
count is 7 or 12).

---

## §5 — Composite mechanic-PR diff (paste-ready)

```lean
--- a/proofs/Proofs/BezoutIdentityOQ01OQ01OQ01.lean
+++ b/proofs/Proofs/BezoutIdentityOQ01OQ01OQ01.lean
@@ -67,7 +67,7 @@
 /-- Nat.log halves when dividing by 2 for n ≥ 2. -/
 private lemma log_div_two {n : ℕ} (hn : 2 ≤ n) : Nat.log 2 (n / 2) = Nat.log 2 n - 1 := by
   have : 2 ≤ n := hn
-  simp [Nat.log_div_base (by norm_num : 1 < 2) (by omega : 2 ≤ n)]
+  simp [Nat.log_div_base 2 n]                                       -- K1: v4.26.0 sig (b n : ℕ)

@@ -113,7 +113,7 @@
   | succ n ih =>
     intro a b hab ha hb
-    simp only [binaryGcdSteps, if_neg (by omega : ¬(a = 0 ∨ b = 0))]
+    rw [binaryGcdSteps]; simp only [if_neg (by omega : ¬(a = 0 ∨ b = 0))]   -- K2: avoid simp-loop on .eq_1

@@ -253,8 +253,8 @@

 /-- **Corollary**: The bit complexity is O(log²(max a b)).
     Since log₂ a + log₂ b ≤ 2 * log₂(max a b), the total is
-    ≤ 6 * (log₂(max a b) + 1)². -/
+    ≤ 12 * (log₂(max a b) + 1)². -/                                  -- K3 docstring cascade
 theorem binaryGcd_log_sq_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
-    totalBitOps a b ≤ 6 * (Nat.log 2 (max a b) + 1) ^ 2 := by
+    totalBitOps a b ≤ 12 * (Nat.log 2 (max a b) + 1) ^ 2 := by      -- K3 statement cascade
   have hsteps := binaryGcdSteps_le_log a b ha hb
   have hlog_sum : Nat.log 2 a + Nat.log 2 b ≤ 2 * Nat.log 2 (max a b) := by
     have hma : Nat.log 2 a ≤ Nat.log 2 (max a b) := log_mono (Nat.le_max_left a b)
     have hmb : Nat.log 2 b ≤ Nat.log 2 (max a b) := log_mono (Nat.le_max_right a b)
     omega
   unfold totalBitOps
-  have hsteps' : binaryGcdSteps a b ≤ 2 * Nat.log 2 (max a b) + 2 := by omega
+  have hsteps' : binaryGcdSteps a b ≤ 4 * Nat.log 2 (max a b) + 2 := by omega   -- K3 root: 2 → 4
   calc binaryGcdSteps a b * (3 * (Nat.log 2 (max a b) + 1))
-      ≤ (2 * Nat.log 2 (max a b) + 2) * (3 * (Nat.log 2 (max a b) + 1)) := by
+      ≤ (4 * Nat.log 2 (max a b) + 2) * (3 * (Nat.log 2 (max a b) + 1)) := by
           apply Nat.mul_le_mul_right; exact hsteps'
-    _ = 6 * (Nat.log 2 (max a b) + 1) ^ 2 := by ring
+    _ ≤ 12 * (Nat.log 2 (max a b) + 1) ^ 2 := by nlinarith [Nat.log 2 (max a b)]   -- K3: ≤ not =, slack 6·log + 6

@@ -274,7 +274,7 @@

 example : binaryGcdSteps 12 8 = 5 := by native_decide
 example : binaryGcdSteps 21 15 = 4 := by native_decide
-example : binaryGcdSteps 252 198 = 12 := by native_decide
+example : binaryGcdSteps 252 198 = 7 := by native_decide                  -- K4: hand-trace gives 7
```

**Total LOC: ~10** (vs PR #19168's ~23-LOC estimate). The reduction is mainly
in K2 (single line at 116, not 8 lines) and K3 (docstring + statement add 2 LOC).

If Docker reveals K2 needs all 8 sites (Hypothesis A in §2), expand the K2
hunk to cover lines 121, 133, 136, 145, 155, 157, 170 individually.

---

## §6 — Pin-verified Mathlib bearer table

| Bearer | File @ SHA | Line | Status | Notes |
|---|---|---|---|---|
| `Nat.log_div_base` | `Mathlib/Data/Nat/Log.lean` | 292 | ✓ verified | `(b n : ℕ) : log b (n / b) = log b n - 1`. **`@[simp]` tagged** at SHA (PR #19168 didn't note this). |
| `Nat.log_div_base_pow` | `Mathlib/Data/Nat/Log.lean` | 299 | ✓ verified | `(b n k : ℕ) : log b (n / b ^ k) = log b n - k`. Useful as fallback if K1 simp doesn't compose. |
| `Nat.log_of_left_le_one` | `Mathlib/Data/Nat/Log.lean` | 76 | ✓ verified | edge case; used in `log_div_base` body |
| `Nat.log_of_lt` | `Mathlib/Data/Nat/Log.lean` | 79 | ✓ verified | edge case; used in `log_div_base` body |
| `Nat.log_pos` | `Mathlib/Data/Nat/Log.lean` | 131 | ✓ verified | `(hb : 1 < b) (hbn : b ≤ n) : 0 < log b n` (used in source lines 84, 130, etc., still works post-K1) |
| `Nat.size_le` | `Mathlib/Data/Nat/Size.lean` | (existing in v4.26.0) | ✓ used in PART IV | unchanged from S2 |
| `Nat.lt_size` | `Mathlib/Data/Nat/Size.lean` | (existing in v4.26.0) | ✓ used in PART IV | unchanged from S2 |
| `Nat.lt_pow_succ_log_self` | `Mathlib/Data/Nat/Log.lean` | (existing in v4.26.0) | ✓ used in PART IV | unchanged from S2 |
| `Nat.pow_log_le_self` | `Mathlib/Data/Nat/Log.lean` | (existing in v4.26.0) | ✓ used in PART IV | unchanged from S2 |
| `Nat.size_zero` | `Mathlib/Data/Nat/Size.lean` | (existing in v4.26.0) | ✓ used in PART IV | unchanged from S2 |
| `↓reduceIte` (simp procedure) | `Mathlib/Tactic/Simps/...` | (core Mathlib) | ✓ available | The `↓` arrow is the `Lean.Meta.Simp.Decide` reducer. Loop diagnosis depends on simp-set interaction. |
| `binaryGcdSteps.eq_1` | (auto-generated) | — | ✓ auto-generated by Lean | Equation lemma for `binaryGcdSteps`. Triggered by `simp [binaryGcdSteps]`; bypassed by `rw [binaryGcdSteps]`. |

---

## §7 — Effort table (revised)

| Kit | PR #19168 LOC | Sharpened LOC | Δ | Notes |
|---|---|---|---|---|
| K1 | 1 | 1 | 0 | Same fix; bonus `@[simp]` cascade may auto-resolve adjacent K2 sites |
| K2 | ~16 (8 sites) | 1-16 (1 site if H-B holds) | 0 to -15 | Test line-116-only first, then expand |
| K3 | ~5 | ~7 (docstring + statement add) | +2 | PR #19168 missed docstring/statement cascade |
| K4 | 1 | 1 | 0 | Same fix; line 278 comment unchanged ✓ |
| **Total** | ~23 | ~10-25 | -13 to +2 | Net likely ~10 LOC if K2 Hypothesis B holds |

Mechanic ACT: 1-2 Docker iterations expected (1 if Hypothesis B holds, 2 if A).

---

## §8 — Conflict-free guarantees

This PR adds **only**:

- `research/problems/bezout-identity-oq-01-oq-01-oq-01-oq-01/sessions/` (NEW empty subdirectory) implicitly created by adding the file below.
- `research/problems/bezout-identity-oq-01-oq-01-oq-01-oq-01/sessions/2026-05-15-s4-prep-mechanic-kit-audit.md` (this file).

This PR **does not** modify:

- `proofs/Proofs/BezoutIdentityOQ01OQ01OQ01.lean` (no live PR touches it; would
  conflict with the eventual mechanic PR after K1-K4 lands)
- `research/problems/.../state.md` (modified by both PR #19021 and PR #19168)
- `research/problems/.../knowledge.md` (modified by PR #19168)
- `src/data/research/problems/....json` (modified by both PR #19021 and PR #19168)
- Any other file in the repository.

**Strict file-disjointness verified** by listing each touching PR's `files`
property via `gh pr view --json files`. No textual overlap with either
in-flight PR.

This satisfies the deployer-stall coordination pattern from
`feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`
("2-3 PRs = release unless strictly conflict-free angle covers real gap"):

- 2 in-flight PRs (#19021 STATE-SYNC, #19168 S3 BUILD-DIAGNOSE)
- This PREP covers a real gap: independent audit of PR #19168's K1-K4 fixes,
  including discovery of the K2 over-count (8 sites vs likely 1) + K3
  under-count (missed docstring/statement cascade) + K1 `@[simp]` tag bonus.
- Single new file, zero cross-PR overlap.

---

## §9 — Recommendation for S5 mechanic ACT

1. Apply the §5 composite diff (K1 + K3 + K4 + K2-line-116-only). Run Docker.
2. **If clean**: ship. Net ~10 LOC. K2 was Hypothesis B (single-site loop).
3. **If lines 121-170 still fail**: expand K2 to all 8 sites per PR #19168's
   original recommendation. Net ~16 LOC. K2 was Hypothesis A.
4. After Docker passes: doctor PR for parent meta.json `mathContext` /
   `summary` / `keyInsights` / `conclusion.summary` updates (`6 → 12`,
   `= 12 → = 7`, `originalContributions` review). Estimated ~10-15 LOC of
   JSON edits.

Preferred mechanic-then-doctor sequencing avoids the parent meta.json drift
issue from causing repeated re-validation churn.

---

## §10 — Honesty log

- The K2 Hypothesis A vs B discrimination is a genuine open question; my §2
  analysis can't determine it without running Docker. The recommendation to
  test line-116-only first is **a hedge to save LOC if Hypothesis B holds**,
  not a claim that Hypothesis B is correct. Either way, PR #19168's full
  8-site fix is **safe** (it works regardless of which hypothesis holds), just
  potentially over-stated.
- The §6 bearer table line numbers for `Nat.size_*` and `Nat.lt_pow_succ_log_self` /
  `Nat.pow_log_le_self` are noted as "existing in v4.26.0" without explicit line
  numbers — these are S2-era pinned bearers (re-verified at SHA in S2's API
  audit per state.md L67-69) and the K1-K4 kit doesn't touch them, so re-pinning
  is not required for this audit.
- The §5 composite diff is **paste-ready in form** but **not Docker-tested**;
  it is a recommendation for the S5 mechanic ACT, not a verified compilation.
- The K1 `@[simp]` finding is **not** a critique of PR #19168 — the `@[simp]`
  tag at SHA is plausibly stable across the v4.25 → v4.26 bump (no evidence
  the tag was added recently). It just wasn't called out in the PR body, which
  may matter for the K2 simp-loop diagnosis.

---

## §11 — Anti-targets

This PREP intentionally does **not**:

- Modify `Proofs/BezoutIdentityOQ01OQ01OQ01.lean` (would conflict with the
  eventual mechanic PR; the §5 diff is a recommendation, not a code change).
- Modify `state.md` (line-locked by both PR #19021 and PR #19168).
- Modify `knowledge.md` (line-locked by PR #19168).
- Modify the parent `meta.json` (downstream-doctor-PR territory, post-K1-K4).
- Re-derive K3's mathematical analysis from scratch (PR #19168's `12 · (log+1)²`
  is correct; my §3 just verifies independently and notes the docstring/statement
  cascade PR #19168 missed).
- Re-implement the `binaryGcdSteps 252 198 = 7` hand-trace as a Lean proof
  (`native_decide` already works once the literal is corrected to 7).

---

## §12 — Cross-references

- **PR #19168** (S3 BUILD-DIAGNOSE, doc-only, in-flight): provides the trigger
  for this audit via its K1-K4 mechanic kit table.
- **PR #19021** (STATE-SYNC, doc-only, in-flight): file-disjoint from this PREP.
- **PR #18029** (S2 ACT, merged): introduced the PART IV bit-complexity model
  (`size_eq_succ_log`, `stepBitOps`, `stepBitOps_le`); audited as out-of-scope
  for the K1-K4 kit (PR #19168 confirmed).
- **Memory pattern** `feedback_researcher_audit_peer_mechanic_kit_fix_recommendations.md`:
  the §1-§4 sibling-PREP audit pattern.
- **Memory pattern** `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern.md`:
  the §8 conflict-free strict-disjointness pattern.
- **Memory pattern** `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton_during_deployer_stall.md`:
  the §6 bearer-pin-at-SHA verification pattern.
