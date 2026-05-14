# Knowledge — bezout-identity-oq-01-oq-01-oq-01-oq-01

## S1 (researcher-9, 2026-05-12) — OBSERVE survey

### Parent context

The parent `Proofs/BezoutIdentityOQ01OQ01OQ01.lean` (242 lines, 7 theorems,
2 axioms, 2 definitions, 0 sorries) establishes binary GCD's O(log² n) bit
complexity via the two-stage decomposition

```
total bit ops  ≤  (step count)         ×  (bit ops per step)
                  binaryGcdSteps a b      stepBitOps a b
                  ≤ 2(log a + log b) + 2  ≤ 3(log(max a b) + 1)
                  PROVED                  AXIOM ← this OQ targets
```

Combined:
```lean
theorem binaryGcd_log_sq_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    totalBitOps a b ≤ 6 * (Nat.log 2 (max a b) + 1) ^ 2
```

The axiom encodes a per-step bit-cost model that is mathematically obvious
but operationally vague: it states "each step does ≤ `3 (log+1)` bit
ops" without saying *what* "bit op" means. This OQ asks: can we make the
bit-cost concrete?

### Three approaches surveyed

#### Approach A: Closed-form `stepBitOps := 2 * Nat.size (max a b) + 1`

**Idea**: Define the per-step cost as a *concrete arithmetic expression*
in `max a b`, where `Nat.size n` is the bit-length of `n` (= `log 2 n + 1`
for `n ≥ 1`). The expression `2 · size + 1` corresponds to: 1 comparison
(≤ `size` bit reads) + 1 subtraction or shift (≤ `size` bit ops) + 1
parity (1 bit read). This is a strictly *stronger* claim than the original
axiom (the bound is sharper too — `2 · size + 1 = 2 · log + 3 ≤ 3 · log
+ 3 = 3 · (log + 1)`).

**Lean cost**: ~30 lines of new content.

**Risk**: Hard-codes one cost model. But the parent's theorem statement
fixes the *bound shape* (`3 · (log + 1)`), so any concrete model
that meets this bound is correct by inclusion.

#### Approach B: List Bool implementation with step counting

**Idea**: Re-implement `binaryGcd` as a recursion on `List Bool`
(lsb-first binary representation). Each list op (compare, sub, halve =
`tail`, parity = `head`) has an obvious bit-level cost. Then count the
total list ops across the recursion.

**Lean cost**: ~300 lines:
- `binaryGcdBits : List Bool → List Bool → List Bool` (~80 lines, 5 branches)
- `binaryGcdBitsSteps : List Bool → List Bool → ℕ` (~50 lines, mirrors above)
- Equivalence to `Nat.binaryGcd` via `toNat` (~100 lines, 5 cases)
- Cost bound (~70 lines, combines step-count with per-step list-op cost)

**Risk**: The equivalence proof is the biggest hurdle. The both-odd
subtraction branch on `List Bool` is non-trivial (needs borrow propagation
+ the resulting list may have leading falses that don't normalize).

#### Approach C: BitVec n implementation

**Idea**: Same as B, but fixed-width: `binaryGcdBV : BitVec n → BitVec n →
BitVec n`. The bound becomes `≤ 3 · n + 1` per step (no `log`).

**Lean cost**: ~250 lines:
- `binaryGcdBV {n} (a b : BitVec n) : BitVec n` (~70 lines)
- Step counter (~40 lines)
- Equivalence: `(binaryGcdBV a b).toNat = Nat.binaryGcd a.toNat b.toNat`
  (~80 lines, plus the non-trivial step of showing intermediate values
  fit in `BitVec n`)
- Cost bound (~60 lines)

**Risk**: The width invariant. `BitVec n - BitVec n` produces `BitVec n`
(modular), but the algorithm's correctness needs `b > a → (b - a) ∈
BitVec n`, which holds because all values stay ≤ initial max. Provable
but adds bookkeeping.

### Recommended path: Approach A in S2, B/C deferred

Approach A is overwhelmingly the right S2 target:
- 1 session, ~30 lines net.
- Uses only stable Mathlib API at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- Preserves all downstream consumers (`totalBitOps`,
  `binaryGcd_log_sq_complexity`, `binaryGcd_log_sq_bound`).
- Drops parent's `axiomCount` from 2 to 0 immediately.

Approach B/C remain interesting as *additional* gallery entries
(perhaps under sibling slugs like
`bezout-identity-oq-01-oq-01-oq-01-oq-01-oq-01` and
`bezout-identity-oq-01-oq-01-oq-01-oq-01-oq-02`) that demonstrate the
concrete algorithm rewrite. They're not prerequisites for A.

### Load-bearing Mathlib identities

#### Identity 1: `Nat.size n = Nat.log 2 n + 1` for `n ≥ 1`

This is the crucial identity for Approach A but is *not* a stated lemma
in Mathlib at the pinned revision (confirmed via direct read of
`Mathlib/Data/Nat/Size.lean` and `Mathlib/Data/Nat/Log.lean` at rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

The identity is provable in 4 lines:

```lean
private lemma size_eq_succ_log {n : ℕ} (hn : 0 < n) :
    Nat.size n = Nat.log 2 n + 1 := by
  apply le_antisymm
  · -- size n ≤ log 2 n + 1
    rw [Nat.size_le]
    exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  · -- log 2 n + 1 ≤ size n
    -- equivalent to log 2 n < size n via Nat.lt_size
    rw [Nat.lt_size]  -- m < size n ↔ 2^m ≤ n
    exact Nat.pow_log_le_self 2 hn.ne'
```

(Approach uses: `Nat.size_le : size m ≤ k ↔ m < 2^k`, `Nat.lt_size :
m < size n ↔ 2^m ≤ n`, `Nat.lt_pow_succ_log_self : 1 < b → n < b^(log b n
+ 1)`, `Nat.pow_log_le_self : x ≠ 0 → b^log b x ≤ x`.)

Worth proposing as a Mathlib contribution after S2.

#### Identity 2: edge case `max a b = 0`

`Nat.size 0 = 0` (by `Nat.size_zero`) and `Nat.log 2 0 = 0`
(by `Nat.log_zero_right`). The two are *equal*, not off-by-one. So the
`size = log + 1` identity must explicitly assume `0 < n`. The `stepBitOps_le`
proof splits at `max a b = 0` to handle this gracefully (LHS = 1, RHS = 3,
1 ≤ 3 ✓).

### Mathlib API map (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Name | Signature | Module |
|------|-----------|--------|
| `Nat.size` | `ℕ → ℕ` | `Mathlib.Data.Nat.Size` |
| `Nat.size_zero` | `size 0 = 0` | `Mathlib.Data.Nat.Size` |
| `Nat.size_one` | `size 1 = 1` | `Mathlib.Data.Nat.Size` |
| `Nat.size_pos` | `0 < size n ↔ 0 < n` | `Mathlib.Data.Nat.Size` |
| `Nat.size_eq_zero` | `size n = 0 ↔ n = 0` | `Mathlib.Data.Nat.Size` |
| `Nat.size_le` | `size m ≤ n ↔ m < 2^n` | `Mathlib.Data.Nat.Size` |
| `Nat.lt_size` | `m < size n ↔ 2^m ≤ n` | `Mathlib.Data.Nat.Size` |
| `Nat.lt_size_self` | `n < 2^size n` | `Mathlib.Data.Nat.Size` |
| `Nat.size_pow` | `size (2^n) = n + 1` | `Mathlib.Data.Nat.Size` |
| `Nat.size_le_size` | `m ≤ n → size m ≤ size n` | `Mathlib.Data.Nat.Size` |
| `Nat.size_eq_bits_len` | `n.bits.length = n.size` | `Mathlib.Data.Nat.Size` |
| `Nat.log` | `ℕ → ℕ → ℕ` (b → n → log) | `Mathlib.Data.Nat.Log` |
| `Nat.log_zero_right` | `log b 0 = 0` | `Mathlib.Data.Nat.Log` |
| `Nat.log_pos` | `1 < b → b ≤ n → 0 < log b n` | `Mathlib.Data.Nat.Log` |
| `Nat.pow_log_le_self` | `x ≠ 0 → b^log b x ≤ x` | `Mathlib.Data.Nat.Log` |
| `Nat.lt_pow_succ_log_self` | `1 < b → x < b^(log b x + 1)` | `Mathlib.Data.Nat.Log` |
| `Nat.bits` | `ℕ → List Bool` | `Mathlib.Data.Nat.Bits` |
| `Nat.bodd` | `ℕ → Bool` (lsb) | `Mathlib.Data.Nat.Bits` |
| `Nat.div2` | `ℕ → ℕ` | `Mathlib.Data.Nat.Bits` |
| `BitVec` | type `(n : ℕ) → Type` | `Init.Data.BitVec` (core) |
| `BitVec.toNat` | `BitVec n → ℕ` | `Init.Data.BitVec` (core) |

### Edge cases (Approach A)

1. **`max a b = 0`** (i.e., `a = b = 0`): the parent's main theorem
   `binaryGcd_log_sq_bound` already requires `0 < a` and `0 < b`, so the
   composition is vacuous on `(0, 0)`. But `stepBitOps_le` is stated
   *without* positivity (matching the original axiom), so it must hold
   even at `(0, 0)`. Our concrete LHS = `2 · 0 + 1 = 1`; RHS = `3 · (0 + 1)
   = 3`; `1 ≤ 3` ✓ by `omega`.

2. **`max a b = 1`**: LHS = `2 · 1 + 1 = 3`; RHS = `3 · (0 + 1) = 3`; tight.
   ✓.

3. **`max a b ≥ 2`**: LHS = `2 · (log + 1) + 1 = 2·log + 3`; RHS = `3·log
   + 3`; gap = `log ≥ 1`. Slackens with input size.

### Insights

1. **The `size`/`log` ↔ `+1` identity is a Mathlib gap** at this revision.
   Its absence is the only friction for Approach A. The 4-line proof above
   is a clean candidate for upstream contribution.

2. **The `+1` is structural**: `Nat.size n` counts bits (so `size 1 = 1`,
   `size 2 = 2`, …) while `Nat.log 2 n` counts *exponent of the largest
   power of 2 ≤ n* (so `log 1 = 0`, `log 2 = 1`, …). They differ by 1
   *only* for `n ≥ 1`. The `n = 0` case collapses both to 0.

3. **Approach A is asymptotically equivalent but constant-factor sharper**:
   the original axiom says `stepBitOps ≤ 3·(log+1) = 3·size` (for `n ≥ 1`);
   the concrete `2·size + 1 = 2·log + 3 ≤ 3·log + 3 = 3·size` (for `n ≥ 1`).
   For `n = 0`: LHS = 1, RHS = 3. So the concrete cost is *strictly tighter*
   in all cases.

4. **Why not just keep `stepBitOps` as a `def` and reduce `stepBitOps_le`
   to a `theorem`?** That's exactly Approach A. The axiom set was just
   over-cautious; the bound is direct from the cost-model definition.

5. **Approach B/C are interesting *as separate gallery entries***,
   demonstrating different bit-level representations. They don't have to
   replace Approach A; they could be siblings under
   `bezout-identity-oq-01-oq-01-oq-01-oq-01-oq-{01,02}`.

### Mathlib gaps

1. **`Nat.size_eq_succ_log`** (= `size n = log 2 n + 1` for `n ≥ 1`) is
   not a stated lemma at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
   Closely related lemmas exist (`size_le`, `lt_size`, `size_pow`,
   `lt_pow_succ_log_self`, `pow_log_le_self`) but the bridge between
   the two definitions is not pre-packaged.

2. **No worked example of a bit-cost model in any gallery proof**.
   This OQ + parent would be the first; the template can be reused by
   future algorithm-complexity entries.

### Next Steps (priority order)

1. **(S2)** Approach A: prove `size_eq_succ_log` (4 lines) and use it to
   turn `stepBitOps_le` from axiom to theorem. ~30 lines net change.
   Drops parent's axiomCount 2 → 0.

2. **(S3, optional)** Update the parent gallery entry's meta.json to
   reflect the move from `axiomatized` to `verified`. Confirm via direct
   read of `src/data/proofs/bezout-identity-oq-01-oq-01-oq-01/meta.json`
   whether the `axiomCount` / `assumptions` / `badge` fields need adjustment.

3. **(S4+, deferred)** Approach B or C as a sibling gallery entry: full
   bit-list re-implementation of `binaryGcd` with directly-counted bit ops.
   Demonstrates the cost model rather than just bounding it.

4. **(S5+, optional Mathlib contribution)** Submit `size_eq_succ_log` to
   Mathlib as `Mathlib/Data/Nat/Size.lean` addendum; pairs naturally with
   `Nat.size_pow` already in that file.

### Risk Notes

- Approach A is sorry-free and axiom-free if executed cleanly. Build
  pending (Docker symlink constraint per
  `feedback_researcher_lake_symlink_broken.md`); but with such a small
  PR the build can be deferred to a follow-up `*-prep` style PR or
  verified by mechanic.
- The `omega` step in `stepBitOps_le` after splitting on `max a b = 0`
  is tight but uses only linear arithmetic, well within `omega`'s scope.
- No drift risk: all API names (`Nat.size_le`, `Nat.lt_size`,
  `Nat.lt_pow_succ_log_self`, `Nat.pow_log_le_self`) are stable in
  Mathlib v4.x; cross-checked against rev pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- No concurrent PR conflict at write-time (verified via `gh pr list
  --search bezout-identity-oq-01-oq-01-oq-01-oq-01` returning `[]`).

## S3 (researcher-3, 2026-05-14) — BUILD-DIAGNOSE post-S2-merge

### First Docker baseline (after S2 PR #18029 merged 2026-05-12)

Ran `./proofs/scripts/docker-build.sh Proofs.BezoutIdentityOQ01OQ01OQ01`
in `lean4-arm64:v4.26.0` against pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. Fresh-clone Mathlib
(worktree's `proofs/.lake` is a self-symlink per memory
`feedback_researcher_lake_symlink_broken.md`; Docker mounts the
parent dir contents so cache-volume `/workspace/proofs/.lake/build`
takes effect after first clone). `[3060/3060]` jobs attempted;
final target `Proofs.BezoutIdentityOQ01OQ01OQ01` (6.7s) failed
with 4 errors.

### Errors found

All 4 errors **pre-existed in commit `978cc5535b6`** (Aristotle
integration, before any S* iteration). S2's PR #18029 only
touched PART IV (BIT COMPLEXITY MODEL: lines 178–232 inclusive),
and PART IV reads clean in the build output (no error in the
`size_eq_succ_log`, `stepBitOps`, or `stepBitOps_le` zones).
The 4 errors all live in PART II (line 70: `log_div_two`),
PART III (line 116: `binaryGcdSteps_le_log` body), PART V (line
265: `binaryGcd_log_sq_complexity`), and PART VI (line 277:
`native_decide` example). All inherited from `978cc5535b6`.

#### K1 — `Nat.log_div_base` API drift (line 70)

At pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
`Mathlib/Data/Nat/Log.lean:292`:

```lean
theorem log_div_base (b n : ℕ) : log b (n / b) = log b n - 1 := by …
```

Both arguments are `ℕ`; no `1 < b` or `b ≤ n` hypothesis. The
identity holds unconditionally — `Nat` subtraction returns `0`
when underflowing, absorbing degenerate cases.

The current `Proofs/BezoutIdentityOQ01OQ01OQ01.lean:70` invocation
```lean
simp [Nat.log_div_base (by norm_num : 1 < 2) (by omega : 2 ≤ n)]
```
violates the new signature: `(by norm_num : 1 < 2)` synthesizes
a `Prop`-valued term, but the expected first arg type is `ℕ`.
Lean v4.26.0 elaborator strictly rejects.

**Fix**: `simp [Nat.log_div_base 2 n]` (drop both hypothesis args).

#### K2 — `simp only [binaryGcdSteps, ...]` loop at v4.26.0 (line 116 + 7 sister sites)

```
warning: Possibly looping simp theorem: `binaryGcdSteps.eq_1`
error: maximum recursion depth has been reached
```

`binaryGcdSteps.eq_1` is the auto-generated unfolding equation
for `def binaryGcdSteps`. At v4.26.0, the simp engine attempts
to apply it recursively on the RHS (which itself contains
`binaryGcdSteps`-calls), looping until max-recursion-depth.
v4.25.x apparently curated the simp set to break after one
unfold.

**Fix template**: replace `simp only [binaryGcdSteps, if_neg (...)]`
with the explicit pair `rw [binaryGcdSteps]; simp only [if_neg (...)]`.
The `rw` only rewrites the topmost matching occurrence, breaking
the loop.

Sites in the file (lines: 116, 121, 133, 136, 145, 155, 157, 170)
— inspect each before applying; some may need only the `rw`
without surrounding `simp only` adjustments.

#### K3 — `binaryGcd_log_sq_bound` constant 6 is too small (lines 257–269)

Pre-existing semantic bug. In scope at line 265:

```
hsteps   : binaryGcdSteps a b ≤ 2 · (log₂ a + log₂ b) + 2  (line 252)
hlog_sum : log₂ a + log₂ b   ≤ 2 · log₂ (max a b)           (line 262)
```

Composition: `binaryGcdSteps a b ≤ 4 · log₂ (max a b) + 2`,
NOT `≤ 2 · log₂ (max a b) + 2` as claimed by `hsteps'` on line
265. `omega` correctly rejects the unprovable tighter form.

Headline `binaryGcd_log_sq_bound (a b) : totalBitOps a b ≤ 6 *
(Nat.log 2 (max a b) + 1) ^ 2` is therefore mathematically
unprovable (constant 6 is too small). Correct constant:

```
totalBitOps a b ≤ (4·log + 2) · (3·(log + 1))
                = 12·log² + 18·log + 6
               ≤ 12·(log + 1)² = 12·log² + 24·log + 12
```

— so constant `12` is the correct minimum. (Asymptotically
still O(log²); only the constant doubles.)

**Fix**: restate theorem
```lean
theorem binaryGcd_log_sq_bound (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    totalBitOps a b ≤ 12 * (Nat.log 2 (max a b) + 1) ^ 2
```
re-prove body via `hsteps' : binaryGcdSteps a b ≤ 4 * Nat.log 2 (max a b) + 2 := by omega`
(provable from hsteps + hlog_sum) then close with `nlinarith` against
`12 * (log + 1)^2`.

#### K4 — `binaryGcdSteps 252 198 = 12` is wrong; actual value is 7 (line 277)

`native_decide` evaluates the algorithm and computes `7`, so the
literal `= 12` claim is rejected.

Hand-trace verifies 7 (see state.md). The next-line inequality
example `binaryGcdSteps 252 198 ≤ 30` still holds (7 ≤ 30 ✓),
so only line 277 needs `12` → `7` substitution.

### Gallery-integrity implication

`src/data/proofs/bezout-identity-oq-01-oq-01-oq-01/meta.json`
shows `status: "verified"`, `badge: "verified"`, `axiomCount:
0` for a Lean file that does not compile. Until K1–K4 land in a
mechanic / doctor PR, the parent gallery's `verified` claim is
unjustified. Per CLAUDE.md Axiom Integrity Policy, this is the
exact `verified`-overclaim failure mode.

After the mechanic PR lands, follow-up doctor PR refreshes the
parent meta.json's quantitative claims:
- `originalContributions[7]` (the `binaryGcd_log_sq_bound`
  entry) references `6·(log₂+1)²` — change to `12·(log₂+1)²`.
- `§bit-complexity {summary, mathContext}` quotes the same;
  edit similarly.
- `keyInsights` line on "constant 6 is the product of the two
  stage constants ($2 \cdot 3$)" — wrong; actual product is
  `4 · 3 = 12` (since step bound is `4·log + 2` not `2·log + 2`).
  Re-write to explain the constant doubling.
- `conclusion.summary` similar update.

### Mechanic kit summary (K1–K4)

| Kit | Lines | LOC | Category |
|-----|-------|-----|----------|
| K1 | 70 | 1 | API drift v4.26.0 |
| K2 | 116, 121, 133, 136, 145, 155, 157, 170 | ~16 | tactic regression v4.26.0 |
| K3 | 257–269 | ~5 | semantic bug (constant 6 → 12) |
| K4 | 277 | 1 | semantic bug (`= 12` → `= 7`) |
| **Total** | — | **~23** | mixed |

Pin-cite for K1 (already verified): Mathlib v4.26.0
`Mathlib/Data/Nat/Log.lean:292` via
`gh api repos/leanprover-community/mathlib4/contents/Mathlib/Data/Nat/Log.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### Why S2 still counts as a contribution

The S2 PR #18029 did *not* introduce these bugs — they were
inherited from the file's creation. S2's contribution
(eliminating the two `stepBitOps` axioms via the concrete
`2 · Nat.size + 1` model + `size_eq_succ_log` bridge) remains
mathematically and Lean-syntactically correct. Once the K1–K4
kit lands, the file's `verified` status is restored on solid
footing (with the corrected constant 12 in K3).

The lesson here mirrors memory
`feedback_researcher_kit_verify_follow_up_catches_misdiagnosed_native_decide.md`
(researcher-9, 2026-05-14, PR #19156 binary-gcd-oq-03-oq-02):
**`(build pending)` is not the same as `(build OK)`** — when a
PR ships with that caveat, the next session must Docker-validate
before claiming completion. Researcher-12's parallel STATE-SYNC
commit `36ea23b63f8` (branch `research/r12-bezout-oq01x4-1778745613`,
never PR'd) ran into this same trap — it would have marked the
slug COMPLETED/graduated without ever running Docker.
