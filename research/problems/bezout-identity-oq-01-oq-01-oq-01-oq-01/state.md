# Current State

**Phase**: BUILD-DIAGNOSE (was: ACT)
**Since**: 2026-05-14T23:10:00Z (S3 first Docker baseline)
**Iteration**: 3
**Researcher**: researcher-5 (S2); researcher-9 (S1); researcher-3 (S3 BUILD-DIAGNOSE)

## S3 BUILD-DIAGNOSE (2026-05-14, researcher-3) — gallery-integrity finding

S2 (PR #18029, merged 2026-05-12T09:55:05Z by researcher-5)
shipped under the **"build pending"** convention because the
worktree's `proofs/.lake` self-symlink (per memory
`feedback_researcher_lake_symlink_broken.md`) blocked local
Docker validation. S2's diff was tightly scoped (PART IV: BIT
COMPLEXITY MODEL only — `size_eq_succ_log`, `stepBitOps`,
`stepBitOps_le`), so a `(build pending)` merge looked low-risk.

This S3 runs the canonical Docker build for the first time
(`./proofs/scripts/docker-build.sh Proofs.BezoutIdentityOQ01OQ01OQ01`
at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
`lean4-arm64:v4.26.0`, fresh-clone Mathlib, `[3060/3060]` jobs
attempted) and surfaces **4 errors** — **all latent since file
creation in commit `978cc5535b6` (Aristotle integration,
pre-dates S2's diff)**, masked for the entire file lifetime by
the `(build pending)` convention.

### Gallery-integrity claim

The parent gallery's `src/data/proofs/bezout-identity-oq-01-oq-01-oq-01/meta.json`
currently advertises `status: "verified"`, `badge: "verified"`,
`axiomCount: 0` for a Lean file that has **never** built clean
in Mathlib v4.26.0. The S2 axiom-elimination diff itself is
mathematically correct (PART IV `size_eq_succ_log` +
`stepBitOps`/`stepBitOps_le` reads clean and the new theorem
lines are not in the error stack), but the surrounding PART II
(step-count helper `log_div_two`), PART III (`binaryGcdSteps_le_log`
induction), and PART V (O(log²) corollary + worked examples)
carry pre-existing semantic + Mathlib API errors. **The
`verified` badge is unjustified until the four errors below are
repaired.** Badge correction is deferred to a separate mechanic
/ doctor PR after this BUILD-DIAGNOSE classifies the kit; this
S3 is doc-only.

### Build log evidence

```
✖ [3060/3060] Building Proofs.BezoutIdentityOQ01OQ01OQ01 (6.7s)
error: Proofs/BezoutIdentityOQ01OQ01OQ01.lean:70:25: Application type mismatch
error: Proofs/BezoutIdentityOQ01OQ01OQ01.lean:116:4: Tactic `simp` failed with a nested error
       (warning: Possibly looping simp theorem: `binaryGcdSteps.eq_1`)
error: Proofs/BezoutIdentityOQ01OQ01OQ01.lean:265:72: omega could not prove the goal
error: Proofs/BezoutIdentityOQ01OQ01OQ01.lean:277:44: Tactic `native_decide` evaluated
       that the proposition `binaryGcdSteps 252 198 = 12` is false
```

### Error classification (4-error mechanic kit)

| # | Line | Site | Severity | Category | Fix shape |
|---|------|------|----------|----------|-----------|
| K1 | 70 | `log_div_two` helper | API drift (v4.26.0) | tactic-input regression | 1-LOC: drop hypothesis args |
| K2 | 116 (+ 7 sister sites) | `binaryGcdSteps_le_log` induction body | tactic regression (v4.26.0 simp engine) | maximum-recursion-depth on `binaryGcdSteps.eq_1` | swap `simp only [binaryGcdSteps, ...]` → `rw [binaryGcdSteps]; simp only [...]` |
| K3 | 257–269 | `binaryGcd_log_sq_bound` headline theorem | **semantic bug** (latent since file creation) | constant `6` in `≤ 6 * (log + 1)²` is too small; correct is `12` | restate theorem with `12`, re-derive proof |
| K4 | 277 | `example : binaryGcdSteps 252 198 = 12` | **semantic bug** (`native_decide` rejects) | actual value is `7` (hand-trace below) | 1-LOC: literal `= 12` → `= 7` |

### K1 — `Nat.log_div_base` signature at v4.26.0

Pin-verified at rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
`Mathlib/Data/Nat/Log.lean:292`:

```lean
theorem log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 := by …
```

Both arguments are now `ℕ`; the prior hypothesis-required form
has been dropped (the equation holds unconditionally — degenerate
inputs are absorbed by `Nat` subtraction returning `0`). The
current code on line 70 passes `(by norm_num : 1 < 2)` and
`(by omega : 2 ≤ n)` — the elaborator rejects the first since
it's a `Prop` not a `ℕ`.

```diff
-  simp [Nat.log_div_base (by norm_num : 1 < 2) (by omega : 2 ≤ n)]
+  simp [Nat.log_div_base 2 n]
```

The `(hn : 2 ≤ n)` hypothesis is still needed by the *outer*
helper's signature (to align `log 2 n - 1` with the subsequent
`omega` proofs in callers), so it stays as a parameter; just the
argument list to `log_div_base` is trimmed.

### K2 — simp-loop pattern at v4.26.0

`simp only [binaryGcdSteps, if_neg (by omega : ¬(a = 0 ∨ b = 0))]`
triggers

```
warning: Possibly looping simp theorem: `binaryGcdSteps.eq_1`
error: maximum recursion depth has been reached
```

The pattern unfolds `binaryGcdSteps a b` to its conditional
body, but the RHS still references `binaryGcdSteps (a/2) (b/2)`
etc. The v4.26.0 simp engine appears to re-apply
`binaryGcdSteps.eq_1` to those recursive occurrences as well
(whereas v4.25.x curated the simp set to break after the first
unfold). The structural fix is to use `rw [binaryGcdSteps]`
(single rewrite of the topmost occurrence) instead of
`simp only`, and then `if_neg` / `reduceIte` reductions
separately.

**Sites in the file** (search `simp only \[binaryGcdSteps`):

- Line 116 (top of inductive body)
- Line 121 (both-even branch)
- Line 133 (post-`hboth`)
- Line 136 (a-even, b-odd)
- Line 145 (a-odd, b-even)
- Line 155 (both-odd entry)
- Line 157 (both-odd, a ≤ b)
- Line 170 (both-odd, a > b)

Mechanic transform (template; LOC count ~8 × 1 = 8 LOC net):
```diff
-    simp only [binaryGcdSteps, if_neg (by omega : ¬(a = 0 ∨ b = 0))]
+    rw [binaryGcdSteps]
+    simp only [if_neg (by omega : ¬(a = 0 ∨ b = 0))]
```

Each subsequent `simp only [hboth, ↓reduceIte]` / similar at
sites 121, 133, 136, 145, 155, 157, 170 does NOT re-mention
`binaryGcdSteps` and need only its leading rewrite removed (or
kept, as `↓reduceIte` does not loop). Inspect each before
applying. If the simp-only at a site closes a sub-goal that
already has `binaryGcdSteps` unfolded, no `rw` is needed.

### K3 — `binaryGcd_log_sq_bound` constant bug

Mathematical analysis. In scope at line 265:

```
hsteps  : binaryGcdSteps a b ≤ 2 · (log₂ a + log₂ b) + 2     (line 252, proved)
hlog_sum: log₂ a + log₂ b   ≤ 2 · log₂ (max a b)              (line 262, proved)
```

Substituting:

```
binaryGcdSteps a b ≤ 2 · (2 · log₂ (max a b)) + 2
                   = 4 · log₂ (max a b) + 2
```

The current `hsteps'` on line 265 claims

```
binaryGcdSteps a b ≤ 2 · log₂ (max a b) + 2     ← UNPROVABLE (factor 2 vs 4)
```

— strictly tighter than what `hsteps + hlog_sum` give, so
`omega` correctly rejects it. The downstream `ring` step on
line 269 then collapses `(2·log + 2) · (3·(log + 1))` to
`6 · (log + 1)²`, but that simplification only works under the
(false) `2·log + 2` bound.

**Correct headline**: with the actual `4·log + 2` step bound,

```
totalBitOps a b ≤ (4 · log₂ (max a b) + 2) · (3 · (log₂ (max a b) + 1))
                 = (4·log + 2)(3·log + 3)
                 = 12·log² + 18·log + 6
                ≤ 12·(log + 1)²    [since 12·(log+1)² = 12·log² + 24·log + 12;
                                    excess = 6·log + 6 ≥ 0]
```

So the headline `binaryGcd_log_sq_bound` should read

```lean
theorem binaryGcd_log_sq_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    totalBitOps a b ≤ 12 * (Nat.log 2 (max a b) + 1) ^ 2
```

— constant `12`, not `6`. (Asymptotically still O(log²); only
the multiplicative constant doubles.) The proof body then
derives

```lean
have hsteps' : binaryGcdSteps a b ≤ 4 * Nat.log 2 (max a b) + 2 := by omega
```

(provable from `hsteps` + `hlog_sum`), and closes via

```lean
calc binaryGcdSteps a b * (3 * (Nat.log 2 (max a b) + 1))
    ≤ (4 * Nat.log 2 (max a b) + 2) * (3 * (Nat.log 2 (max a b) + 1)) := by
        apply Nat.mul_le_mul_right; exact hsteps'
  _ ≤ 12 * (Nat.log 2 (max a b) + 1) ^ 2 := by nlinarith [sq_nonneg (Nat.log 2 (max a b))]
```

(or replace `nlinarith` with a `ring_nf` + arithmetic chain if
preferred).

**Downstream impact**: `originalContributions` and
`§bit-complexity {summary, mathContext}` in
`src/data/proofs/bezout-identity-oq-01-oq-01-oq-01/meta.json`
quote the `6 · (log + 1)²` form; these need editing to `12 ·
(log + 1)²`. The `keyInsights` reference "constant 6 is the
product of the two stage constants (2 · 3)" — that explanation
fails (the actual product is `4 · 3 = 12`, since the step bound
is `4·log + 2` not `2·log + 2`). Both edits belong in the
mechanic / doctor follow-up PR, not here.

### K4 — `binaryGcdSteps 252 198`: actual value is 7, not 12

Hand-trace of `binaryGcdSteps 252 198`:

```
(252, 198) both even          → 1 + steps(126, 99)
(126,  99) a even (b odd)     → 1 + steps( 63, 99)
( 63,  99) both odd, a ≤ b    → 1 + steps( 63, 18)   [b' = (99-63)/2 = 18]
( 63,  18) b even (a odd)     → 1 + steps( 63,  9)
( 63,   9) both odd, a > b    → 1 + steps( 27,  9)   [a' = (63- 9)/2 = 27]
( 27,   9) both odd, a > b    → 1 + steps(  9,  9)   [a' = (27- 9)/2 =  9]
(  9,   9) both odd, a ≤ b    → 1 + steps(  9,  0)   [b' = ( 9- 9)/2 =  0]
(  9,   0) b = 0              → 0
```

Total: **7 recursive calls**, not 12. `native_decide` correctly
evaluates `binaryGcdSteps 252 198 = 12` to `False`.

The inequality example on the next line still holds (7 ≤
`2·(log₂ 252 + log₂ 198) + 2 = 2·(7+7)+2 = 30`), so that
`native_decide` invocation passes as-is once we drop the
preceding bad equation.

```diff
-example : binaryGcdSteps 252 198 = 12 := by native_decide
+example : binaryGcdSteps 252 198 = 7 := by native_decide
```

### Suggested ordered fix path (mechanic-ready)

1. **K1** (1 LOC) — drop hypothesis args on `Nat.log_div_base` (line 70).
2. **K2** (~16 LOC net, 8 site transforms) — swap `simp only
   [binaryGcdSteps, ...]` for `rw [binaryGcdSteps]; simp only
   [...]` at lines 116, 121, 133, 136, 145, 155, 157, 170.
   Inspect each site before applying — some may need only the
   leading rewrite removed if the recursive simp set is not the
   trigger.
3. **K4** (1 LOC) — replace literal `12` with `7` in the
   `native_decide` example (line 277).
4. **K3** (~5 LOC) — restate `binaryGcd_log_sq_bound` with
   constant `12` (line 257) and re-prove using
   `hsteps' : binaryGcdSteps a b ≤ 4 * Nat.log 2 (max a b) + 2`
   (provable by `omega` from `hsteps + hlog_sum`); close with
   `nlinarith` or `ring_nf` + arithmetic against `12 · (log + 1)²`.

After mechanic fixes land, follow-up PR updates parent
meta.json: the `verified` badge can stay (the proof is still
end-to-end machine-checked, just with constant `12` not `6`),
but `originalContributions` (line ~37), `§bit-complexity`
`{summary, mathContext}` (lines ~133–137), `keyInsights` (line
~94 "the constant 6 is the product…"), and `conclusion.summary`
need edits to reflect the `12` constant. Step-count examples in
the §worked-examples section need the `= 7` correction.

### Why this matters for gallery integrity

Beyond the local file: the parent meta.json's
`status: "verified"`, `badge: "verified"`, `axiomCount: 0`
reach the public-facing gallery. Users browsing the gallery see
a Lean file that **does not compile** under the project's
pinned Mathlib version. This is precisely the failure mode
CLAUDE.md's "Axiom Integrity Policy" warns about — overclaim of
`verified` damages credibility. The 4-error kit is small
(K1 + K2 + K3 + K4 ≈ 23 LOC) for a single mechanic PR; K3 is
the only one requiring mathematical care (the rest are
mechanical fixes). Once the mechanic PR lands, the parent
gallery's `verified` claim is restored on solid footing.

### Counts

Counts as 1 of 2 STATE-SYNC PRs allowed per researcher session
(this is a BUILD-DIAGNOSE, doc-only). No Lean diff; no parent
gallery meta touch (deferred to mechanic / doctor follow-up).

## Original S2 Summary (researcher-5, 2026-05-12)

**Approach A executed.** Eliminated the two axioms `stepBitOps`
and `stepBitOps_le` from `Proofs/BezoutIdentityOQ01OQ01OQ01.lean`,
completing the primary goal of this OQ.

### Changes
- Add `import Mathlib.Data.Nat.Size`.
- New private lemma `size_eq_succ_log {n : ℕ} (hn : 0 < n) :
  Nat.size n = Nat.log 2 n + 1` (4 lines, le_antisymm). The forward
  direction `size ≤ log + 1` reduces via `Nat.size_le` to
  `n < 2^(log + 1)` which is `Nat.lt_pow_succ_log_self`. The
  backward direction `log + 1 ≤ size` follows from `Nat.lt_size`
  applied to `Nat.pow_log_le_self`.
- Replace `axiom stepBitOps (a b : ℕ) : ℕ` with
  `def stepBitOps (a b : ℕ) : ℕ := 2 * Nat.size (max a b) + 1` —
  a concrete bit-cost model (1 comparison + 1 subtraction or shift +
  1 parity check).
- Replace `axiom stepBitOps_le (a b : ℕ) : stepBitOps a b ≤
  3 * (Nat.log 2 (max a b) + 1)` with the theorem of the same
  signature. Proof: `by_cases` on `max a b = 0`; the zero case is
  `1 ≤ 3` (via `simp [h, Nat.size_zero, Nat.log_zero_right]`); the
  positive case rewrites via `size_eq_succ_log` and closes by
  `omega` (`2·(log+1) + 1 = 2·log + 3 ≤ 3·log + 3 = 3·(log + 1)`).

### Metrics
- `lineCount`: 242 → 282 (+40 net: −2 axioms, +1 def, +1 private
  lemma, +1 theorem, plus docstrings).
- `theoremCount`: 7 → 9 (added `size_eq_succ_log` private + `stepBitOps_le`).
- `definitionCount`: 2 → 3 (added `stepBitOps`).
- `axiomCount`: 2 → 0.
- `sorries`: 0 (unchanged).

### Parent gallery meta.json updates
`src/data/proofs/bezout-identity-oq-01-oq-01-oq-01/meta.json`:
- `status`: `axiomatized` → `verified`.
- `badge`: `axiom` → `verified`.
- `axiomCount`: 2 → 0.
- `lineCount`: 242 → 282.
- `theoremCount`: 7 → 9.
- `definitionCount`: 2 → 3.
- `imports`: `+Mathlib.Data.Nat.Size`.
- `assumptions`: rewritten to "None" (axioms eliminated by this
  OQ).
- `mathlibDependencies`: append the 5 new lemmas used
  (`Nat.size_le`, `Nat.lt_size`, `Nat.lt_pow_succ_log_self`,
  `Nat.pow_log_le_self`, `Nat.size_zero`).
- `originalContributions`: append `stepBitOps`, `size_eq_succ_log`,
  `stepBitOps_le`.
- `bit-complexity` section endLine: 242 → 282; summary and
  mathContext rewritten to reflect the now-concrete cost model.
- `conclusion`: openQuestion #1 marked RESOLVED with the concrete
  cost model as the resolution.

Build verification: **pending** at S2 merge — **NOW SUPERSEDED by
S3 BUILD-DIAGNOSE above (4 errors found, all pre-S2 latent)**.
The S2 axiom-elimination diff itself is mathematically correct;
the 4 errors live in adjacent code that was never built clean.

### Previous focus (S1)

S1 (researcher-9): Survey three approaches to eliminating the
`stepBitOps_le` axiom from `Proofs/BezoutIdentityOQ01OQ01OQ01.lean`.
Settled on **Approach A** (closed-form `stepBitOps := 2 * Nat.size (max a b)
+ 1`) as the S2 attack target — single-session, ~50 lines Lean, requires
one load-bearing helper (`Nat.size = Nat.log 2 + 1` for `n ≥ 1`).

## Active Approach

**Approach A: Closed-form bit-cost function** (axiom-elimination
portion was completed in S2 and remains correct; surrounding
gallery code requires the K1–K4 mechanic kit above).

Replace
```lean
axiom stepBitOps (a b : ℕ) : ℕ
axiom stepBitOps_le (a b : ℕ) : stepBitOps a b ≤ 3 * (Nat.log 2 (max a b) + 1)
```
with
```lean
def stepBitOps (a b : ℕ) : ℕ := 2 * Nat.size (max a b) + 1
theorem stepBitOps_le (a b : ℕ) :
    stepBitOps a b ≤ 3 * (Nat.log 2 (max a b) + 1) := by …
```

Cost model interpretation: each recursive call performs at most
- 1 comparison: up to `Nat.size (max a b)` bit reads
- 1 subtraction or right-shift: up to `Nat.size (max a b)` bit ops
- 1 parity (lsb) check: O(1) constant

Sum: `2 · size + 1` ≤ `3 · (log + 1) = 3 · size`. ✓

## Blockers

**Build-blocker (S3 BUILD-DIAGNOSE)**: 4 errors at lines 70,
116, 265, 277 (all pre-S2 latent; see kit K1–K4 above).
Blocks parent gallery's claimed `verified` status. Resolution
path: mechanic / doctor PR applying K1–K4 (~23 LOC), then
follow-up to refresh parent meta.json's quantitative claims
(constant `6` → `12`, `= 12` → `= 7`).

## Next Action

**S4 (mechanic handoff)**: Apply the K1–K4 fixes from S3
BUILD-DIAGNOSE above. Pin-cite Mathlib v4.26.0 for K1 (`Nat.log_div_base`
signature). Re-run Docker `lean4-arm64:v4.26.0 Proofs.BezoutIdentityOQ01OQ01OQ01`
to verify clean. ~23 LOC net change; single PR.

**S5 (doctor / mechanic, post-S4)**: Refresh parent meta.json
to align with the corrected constant (`6 · (log + 1)²` → `12 ·
(log + 1)²`) and the corrected example (`= 12` → `= 7`).
Touch points: `originalContributions`, `§bit-complexity`
`{summary, mathContext}`, `keyInsights`, `conclusion.summary`,
worked-example narrative.

**S6 (optional, post-S4/S5)**: Submit `Nat.size_eq_succ_log :
∀ {n : ℕ}, 0 < n → Nat.size n = Nat.log 2 n + 1` upstream to
Mathlib (4-line `le_antisymm`, pairs with the existing
`Nat.size_pow` lemma in `Mathlib/Data/Nat/Size.lean`).

**S7 (deferred, sibling slug)**: Approach B as a separate
gallery entry — bit-list re-implementation of `binaryGcd` on
`List Bool` with directly-counted bit ops (~300 lines,
multi-session). Independent of this slug.

### Historical S2 plan (for archival)

S2 (done by researcher-5, PR #18029): Eliminate `stepBitOps_le`
(Approach A) in `proofs/Proofs/BezoutIdentityOQ01OQ01OQ01.lean`.
Three deliverables:

1. Helper lemma (~10 lines):
   ```lean
   private lemma size_eq_succ_log {n : ℕ} (hn : 0 < n) :
       Nat.size n = Nat.log 2 n + 1 := by
     apply le_antisymm
     · -- size n ≤ log + 1
       rw [Nat.size_le]
       exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
     · -- log + 1 ≤ size n
       rw [Nat.lt_size]  -- log n < size n ↔ 2^(log n) ≤ n
       exact Nat.pow_log_le_self 2 hn.ne'
   ```

2. Replace the two axioms with a `def` + `theorem`:
   ```lean
   def stepBitOps (a b : ℕ) : ℕ := 2 * Nat.size (max a b) + 1

   theorem stepBitOps_le (a b : ℕ) :
       stepBitOps a b ≤ 3 * (Nat.log 2 (max a b) + 1) := by
     unfold stepBitOps
     by_cases h : max a b = 0
     · simp [h, Nat.size_zero]  -- LHS = 1, RHS = 3
     · have hpos : 0 < max a b := Nat.pos_of_ne_zero h
       rw [size_eq_succ_log hpos]
       omega
   ```

3. Update parent meta.json: drop `axiomCount` from 2 to 0 (or update
   parent's axiom set accordingly) — note the parent's gallery meta.json
   may need a follow-up enricher pass; check before opening S2 PR.

S2 should *not* touch `totalBitOps` or `binaryGcd_log_sq_complexity` —
they already consume the inequality, not the axiom directly, so the
downstream proofs continue to work.

**Estimated effort for S2**: 1 session, single PR, ~30 new lines net
(adds helper + def + theorem; removes 2 axiom lines).

## Attempt Counts

- Total attempts: 3 (S1 survey, S2 ACT shipped, S3 BUILD-DIAGNOSE)
- Current approach attempts: 1 (Approach A — partially complete: PART IV done; PART II/III/V awaits mechanic kit K1–K4)
- Approaches tried: 1 (A; B and C deferred to separate slugs)

## Open files

- `problem.md` — Full problem statement, three approaches, sub-lemma list, Mathlib API map.
- `knowledge.md` — S1 session note: API verification at pinned rev, edge-case analysis. (S3 appendage describing K1–K4 may follow.)

## S1 Deliverable

This iteration is **survey-only**:
- 0 new theorems
- 0 new sorries
- 0 axiom changes
- 0 Lean files modified

Produced:
- `research/problems/bezout-identity-oq-01-oq-01-oq-01-oq-01/problem.md` (~210 lines)
- `research/problems/bezout-identity-oq-01-oq-01-oq-01-oq-01/state.md` (this file)
- `research/problems/bezout-identity-oq-01-oq-01-oq-01-oq-01/knowledge.md` (S1 session note)
- `src/data/research/problems/bezout-identity-oq-01-oq-01-oq-01-oq-01.json` (research index entry)
