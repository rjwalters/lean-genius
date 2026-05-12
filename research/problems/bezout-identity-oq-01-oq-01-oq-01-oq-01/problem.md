# Problem: Eliminate `stepBitOps_le` axiom from Binary GCD bit-complexity proof

## Statement

### Plain Language

The parent gallery proof `bezout-identity-oq-01-oq-01-oq-01` (Binary GCD O(log² n)
Bit Complexity) establishes a complete bit-complexity bound for Stein's binary
GCD algorithm via a two-stage decomposition:

```
  total bit ops  ≤  (step count)   ×   (bit ops per step)
                    ──────────────     ──────────────────
                    (Part 1: proved)   (Part 2: axiom)
```

Part 1 is fully proved (`binaryGcdSteps_le_log : binaryGcdSteps a b ≤
2 * (Nat.log 2 a + Nat.log 2 b) + 2`). Part 2 is encoded as

```lean
axiom stepBitOps    (a b : ℕ) : ℕ
axiom stepBitOps_le (a b : ℕ) : stepBitOps a b ≤ 3 * (Nat.log 2 (max a b) + 1)
```

This OQ asks whether the second axiom can be *eliminated* by giving a concrete
Lean-level bit-cost model.

### Formal Statement

Replace the two `axiom` declarations in `Proofs/BezoutIdentityOQ01OQ01OQ01.lean`
with `def` declarations and a proved `theorem`. Possible target signatures:

```lean
-- Approach A (closed-form cost function)
def stepBitOpsConcrete (a b : ℕ) : ℕ := 2 * Nat.size (max a b) + 1
theorem stepBitOpsConcrete_le (a b : ℕ) :
    stepBitOpsConcrete a b ≤ 3 * (Nat.log 2 (max a b) + 1) := by sorry

-- Approach B (Bool-list algorithm with step counter)
def binaryGcdBits : List Bool → List Bool → List Bool := …
def binaryGcdBitsSteps (xs ys : List Bool) : ℕ := …
theorem binaryGcdBitsSteps_le_log_sq (xs ys : List Bool) :
    binaryGcdBitsSteps xs ys ≤ 6 * (xs.length.max ys.length + 1) ^ 2 := by sorry

-- Approach C (BitVec n algorithm)
def binaryGcdBV {n : ℕ} (a b : BitVec n) : BitVec n := …
def binaryGcdBVSteps {n : ℕ} (a b : BitVec n) : ℕ := …
theorem binaryGcdBVSteps_le {n : ℕ} (a b : BitVec n) :
    binaryGcdBVSteps a b ≤ 3 * n + 1 := by sorry
```

After elimination, the file's `axiomCount` should drop from 2 to 0, and the
parent gallery entry's `axiomatized`/`axiom` badge can be revisited (the parent
also exposes 2 axioms, both via `stepBitOps`/`stepBitOps_le`).

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - seeker-selected
  - binary-gcd
  - bit-complexity
  - axiom-elimination
  - mathlib-Nat.size
```

**Significance**: 6/10 — Eliminates the only axiom in the entire `bezout-identity`
formalization tree under `OQ-01`. The parent's O(log² n) result becomes
fully machine-checked in the `verified` track. Provides a template for
"bit-cost model elimination" in any algorithm-complexity proof.

**Tractability**: 7/10 — Approach A is a single rational-arithmetic theorem
(after deriving `size n = log 2 n + 1` for `n > 0` from existing Mathlib
lemmas). Approach B/C are multi-session structural rewrites of `binaryGcd`
itself.

## Why This Matters

1. **Axiom-free Binary GCD bound** — The parent's two axioms are the *only*
   assumption in the entire `O(log² n)` proof. Eliminating them moves the
   parent from `axiomatized` to `verified` and removes the asterisk on
   what is currently the gallery's best worked example of an explicit
   algorithm-complexity formalization.

2. **Template for cost-model elimination** — Many gallery proofs of
   algorithmic results (Schönhage–Strassen, FFT, sorting) will need
   bit-level cost models. Demonstrating one path here (Approach A in the
   simplest case; Approach B/C as deeper alternatives) sets the precedent.

3. **Connection to `Nat.size` / `Nat.bits`** — Mathlib's bit-level API
   (`Nat.size`, `Nat.bits`, `Nat.testBit`) is well-developed but rarely
   used in gallery proofs. This OQ surfaces it as a load-bearing dependency.

4. **Stein vs. Euclid trade-off** — The parent confirms binary GCD matches
   Euclid's asymptotic O(log² n). The axiom currently *assumes* the per-step
   cost; eliminating it would *prove* the matching constant 3 (1 compare + 1
   subtract/shift + 1 parity test, each ≤ `log` bit ops).

## Known Results

### Already Proven (in parent `BezoutIdentityOQ01OQ01OQ01.lean`)

- `binaryGcdSteps_le_log : binaryGcdSteps a b ≤ 2 * (Nat.log 2 a + Nat.log 2 b) + 2`
  — Step count bound (Part 1, fully proved, 0 sorries).
- `binaryGcd_log_sq_complexity` — Combined bound via `totalBitOps`.
- `binaryGcd_log_sq_bound : totalBitOps a b ≤ 6 * (Nat.log 2 (max a b) + 1)^2`
  — Final O(log² n) form.

### Available Mathlib Infrastructure (pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

| Need | Mathlib name | Module |
|------|--------------|--------|
| Bit-length of natural | `Nat.size : ℕ → ℕ` | `Mathlib.Data.Nat.Size` |
| Bit-length = `log 2 n + 1` for `n > 0` | derive from `Nat.size_le` + `Nat.lt_size` | `Mathlib.Data.Nat.Size` |
| Bit-length lower/upper bounds | `Nat.lt_size_self : n < 2^size n`, `Nat.size_le : size m ≤ n ↔ m < 2^n` | `Mathlib.Data.Nat.Size` |
| Bit list | `Nat.bits : ℕ → List Bool`, `Nat.size_eq_bits_len` | `Mathlib.Data.Nat.Bits` |
| Bit-vector type | `BitVec n` | `Init.Data.BitVec` (core) |
| Parity test | `n.bodd : Bool`, `n % 2 = 0` | `Mathlib.Data.Nat.Bits` |

### Open Sub-Questions

- **Q1**: Can `stepBitOps_le` be eliminated *without* rewriting `binaryGcd`,
  by giving a concrete `def stepBitOps := 2 * Nat.size (max a b) + 1`
  and proving the bound directly? (Approach A.)
- **Q2**: If we re-implement `binaryGcd` on `List Bool` (lsb-first),
  what is the cleanest induction principle for step counting?
  (Approach B.)
- **Q3**: Does a fixed-width `BitVec n` implementation simplify the
  bound (by replacing `log 2 (max a b)` with the literal width `n`)?
  (Approach C.)

### Our Goal

This S1 OBSERVE iteration: survey the three approaches; commit to
Approach A as the first attack target; produce the load-bearing
sub-lemma list and Mathlib API map. No Lean changes in this iteration.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `bezout-identity-oq-01-oq-01-oq-01` (parent) | Provides the algorithm + step-count bound; this OQ targets the parent's two axioms. |
| `bezout-identity-oq-01-oq-01` (grandparent) | Defines `binaryGcd` itself; specifies the algorithm whose cost we model. |
| `bezout-identity` (root) | Original Bézout identity proof via Euclid; provides comparative O(log²) bound. |
| `binary-gcd` (sibling gallery entry) | Companion of the parent; same algorithm, different result. |

## Initial Thoughts

### Potential Approaches

1. **Approach A — closed-form cost function (RECOMMENDED for S2)**.

   Replace
   ```lean
   axiom stepBitOps (a b : ℕ) : ℕ
   axiom stepBitOps_le (a b : ℕ) : stepBitOps a b ≤ 3 * (Nat.log 2 (max a b) + 1)
   ```
   with
   ```lean
   def stepBitOps (a b : ℕ) : ℕ := 2 * Nat.size (max a b) + 1
   theorem stepBitOps_le (a b : ℕ) :
       stepBitOps a b ≤ 3 * (Nat.log 2 (max a b) + 1)
   ```

   The proof reduces to: for `max a b ≥ 1`, `Nat.size (max a b) = Nat.log 2
   (max a b) + 1`, so `2 * size = 2 * log + 2`, and `2 * log + 2 + 1 ≤
   3 * (log + 1) = 3 * log + 3`. The edge case `max a b = 0` makes
   `Nat.size 0 = 0` so LHS = 1; RHS = `3 * (0 + 1) = 3`; 1 ≤ 3 ✓.

   **Why it might work**: The bound is concrete, computable, and the
   inequality is `omega`-discharged after the size/log identity.

   **Risk**: The mental model "stepBitOps = 2·size + 1" hard-codes one
   particular cost model. Future readers may want a different model
   (e.g., logarithmic addition / word-RAM). But this is a *strictly stronger*
   bound than what the axiom asserts, so it does what the parent needs.

   **Estimated effort**: 1 PR, ~30–50 lines of Lean, single session.

2. **Approach B — `List Bool` algorithm with explicit per-call cost**.

   Re-implement `binaryGcd` on lsb-first `List Bool` representations of
   `ℕ`. Provide:
   - `bitsCompare : List Bool → List Bool → Ordering` (counts bit reads)
   - `bitsSub : List Bool → List Bool → List Bool` (counts bit ops with borrow)
   - `bitsHalve : List Bool → List Bool` (tail; O(1))
   - `bitsParity : List Bool → Bool` (head; O(1))

   Then `binaryGcdBits xs ys` mirrors the original recursion, and a
   step counter tracks each bit-level call. The total cost is the sum
   over recursive calls of `bitsCompare + bitsSub + bitsHalve + bitsParity`.

   **Why it might work**: Direct, mechanistic match to a textbook
   complexity argument. Each list operation has an obvious linear
   recurrence in `xs.length + ys.length`.

   **Risk**: Need to prove `binaryGcdBits xs ys = Nat.binaryGcd (xs.toNat)
   (ys.toNat)` for the result to refer back to the parent's algorithm.
   This equivalence is non-trivial (especially the both-odd subtraction
   branch). 2–3 sessions minimum.

3. **Approach C — `BitVec n` algorithm**.

   Same as B but with fixed-width `BitVec n`. The advantage: `BitVec.toNat`
   is one of Mathlib's better-developed correctness layers, and the bound
   becomes `≤ 3·n + 1` per step (no `log` at all).

   **Why it might work**: Hard width parameter sidesteps the `size` vs
   `log` book-keeping. Aligns with hardware-oriented complexity literature.

   **Risk**: Requires a *non-decreasing-width* invariant: `binaryGcd
   (BitVec n) (BitVec n) → BitVec n`, but the both-odd branch produces
   `(b - a) / 2` which fits in `BitVec (n-1)` strictly. So either
   the algorithm widens to `BitVec n` always (with leading zeros) or
   uses a sigma type. The first is the natural fit but requires care
   with overflow proofs.

### Key Difficulties

- **The `Nat.size` ↔ `Nat.log 2 + 1` identity is not stated in Mathlib**.
  We need to prove it (≤ 4-line proof from `size_le` and `lt_size`)
  as a load-bearing helper. This is the single S2 hurdle in Approach A.

- **Edge case `n = 0`**: `Nat.size 0 = 0` and `Nat.log 2 0 = 0`, so the
  identity `size n = log 2 n + 1` *fails* for n = 0. The inequality
  `stepBitOps_le` must handle both `max a b = 0` and `max a b ≥ 1`.
  The original axiom doesn't care; the concrete version must split.

- **Approach B requires equivalence to `Nat.binaryGcd`**. The parent's
  `binaryGcd` is over `ℕ`; any list-based version needs a `toNat`
  bridge with `lemma binaryGcdBits_toNat : (binaryGcdBits xs ys).toNat
  = Nat.binaryGcd xs.toNat ys.toNat`. Each of the five recursive
  branches contributes one case to this proof.

### What Would a Proof Need? (Approach A)

- **Load-bearing helper**: `Nat.size_eq_succ_log_two : ∀ n ≥ 1, Nat.size n
  = Nat.log 2 n + 1`. Proof sketch:
  - From `lt_size_self : n < 2^size n` and `pow_log_le_self 2 n` (need
    `n ≠ 0`), we have `2^log < 2^size`, so `log < size`, i.e. `log + 1 ≤ size`.
  - From `size_le : size n ≤ k ↔ n < 2^k` applied at `k = log + 1`
    and `lt_pow_succ_log_self 2 n : n < 2^(log n + 1)`, we get
    `size n ≤ log n + 1`.
  - Antisymmetry: `size n = log n + 1`.
- **Main inequality** (`stepBitOps_le`):
  ```
  stepBitOps a b = 2 * size (max a b) + 1
  ```
  Case `max a b = 0`:
  ```
  LHS = 2 * 0 + 1 = 1
  RHS = 3 * (0 + 1) = 3
  1 ≤ 3 ✓ (omega)
  ```
  Case `max a b ≥ 1`:
  ```
  LHS = 2 * (log 2 (max a b) + 1) + 1 = 2 log + 3
  RHS = 3 log + 3
  2 log + 3 ≤ 3 log + 3 ↔ 0 ≤ log ✓ (omega)
  ```

## Tractability Assessment

**Difficulty**: Low (Approach A) | Medium (Approach B) | Medium-High (Approach C)

**Justification**:
- Approach A is a single S2 PR with ~30–50 lines of new Lean (1 helper +
  1 main theorem). All API names (`Nat.size`, `Nat.log`, `Nat.size_le`,
  `Nat.lt_size_self`, `Nat.lt_pow_succ_log_self`, `Nat.pow_log_le_self`)
  are stable in Mathlib v4.26.0.
- Approach B/C are multi-session efforts requiring an algorithm rewrite +
  equivalence proof.

**Estimated Effort**:
- Approach A: 1 session, single PR, ~50 lines Lean.
- Approach B: 3–4 sessions, ~300 lines Lean (algorithm + equivalence + cost).
- Approach C: 3–4 sessions, ~250 lines Lean (uses `BitVec` Mathlib API more directly).

## References

### Papers
- Stein, J. (1967). *Computational problems associated with Racah algebra*.
  J. Comput. Phys. — Original binary GCD algorithm.
- Knuth, D. E. *The Art of Computer Programming*, Vol. 2, §4.5.2 — Algorithm B
  and worst-case analysis.
- Sørenson, J. (1994). *Two fast GCD algorithms*. J. Algorithms — Step count
  asymptotic tightness.

### Mathlib
- `Mathlib.Data.Nat.Size` — `Nat.size`, `Nat.size_le`, `Nat.lt_size`, `Nat.size_pos`,
  `Nat.size_pow`, `Nat.size_eq_bits_len`.
- `Mathlib.Data.Nat.Log` — `Nat.log`, `Nat.log_pos`, `Nat.pow_log_le_self`,
  `Nat.lt_pow_succ_log_self`.
- `Mathlib.Data.Nat.Bits` — `Nat.bits`, `Nat.bodd`, `Nat.div2`,
  `Nat.size_eq_bits_len`.
- `Init.Data.BitVec` (Lean core) — `BitVec n`, `BitVec.toNat`, `BitVec.ofNat`.

## Metadata

```yaml
tags:
  - number-theory
  - binary-gcd
  - bit-complexity
  - axiom-elimination
  - seeker-selected
  - mathlib-Nat.size
related_proofs:
  - bezout-identity-oq-01-oq-01-oq-01
  - bezout-identity-oq-01-oq-01
  - bezout-identity
  - binary-gcd
difficulty: low
source: gallery-gap
created: 2026-05-12
```
