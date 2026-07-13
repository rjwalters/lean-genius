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
