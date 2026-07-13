# Problem: Lehmer GCD Correctness and Termination

**Slug**: binary-gcd-oq-03-oq-01
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Plain Language

The gallery proof `BinaryGCD.lean` formalizes Stein's binary GCD algorithm. The
parent open question (`binary-gcd-oq-03`) noted that the GMP library uses a
Lehmer–Schönhage hybrid GCD. This sub-question asks:

**Can the full end-to-end correctness of `lehmerGcd` be proved in Lean 4, including
the progress guarantee that each Lehmer step strictly reduces `a + b`?**

The Lehmer GCD algorithm works by approximating the Euclidean algorithm using
single-precision floating-point arithmetic to compute multiple Euclidean steps at
once (via a 2×2 matrix), then applying the matrix to the big integers. Termination
requires that each matrix application strictly reduces `a + b`.

### Formal Question

```lean
-- Termination: each Lehmer step reduces a + b
theorem lehmerGcd_progress (a b : ℕ) (h : 0 < b) :
    let (a', b') := lehmerStep a b
    a' + b' < a + b := by sorry

-- Correctness: the result is gcd(a, b)
theorem lehmerGcd_correct (a b : ℕ) : lehmerGcd a b = Nat.gcd a b := by sorry
```

### Why This Matters

- Lehmer's algorithm is practically important (used in GMP)
- Termination proofs for approximate arithmetic algorithms are non-trivial
- Would complement the existing binary GCD formalization
- Good test case for Lean 4's termination checker with non-obvious metrics

## Known Results

### From Parent Proof (`BinaryGCD.lean`)

The binary GCD proof establishes:
- Correctness of Stein's algorithm: `binaryGcd_correct`
- Termination via `Nat.log2` decrease
- O(log n) bit-operations complexity sketch

### Relevant Mathematical Facts

- Each Lehmer step: compute matrix M via floating-point approximation of
  extended Euclidean algorithm on leading bits
- Apply M: `(a', b') = M · (a, b)` where M is product of elementary matrices
- Key invariant: `det(M) = ±1`, so `gcd(a', b') = gcd(a, b)`
- Progress: if floating-point and exact computations agree, `a + b` decreases

### Lean 4 / Mathlib Considerations

- `Nat.gcd_rec`: standard Mathlib GCD recurrence
- `Int.gcd_eq_gcd_ab`: Bezout's identity in Mathlib
- Matrix operations on ℤ²: `Matrix.det`, `Matrix.mul`
- No existing Lean 4 formalization of Lehmer GCD found

## Suggested Approach

### Phase 1: OBSERVE
1. Read `BinaryGCD.lean` to understand the existing proof style
2. Search Mathlib for Lehmer GCD or extended Euclidean formalizations
3. Check if `Nat.xgcd` (extended GCD) is in Mathlib
4. Look at existing GCD termination proofs for inspiration

### Phase 2: ORIENT
1. Define `lehmerStep` cleanly in terms of Mathlib's matrix types
2. Identify the progress metric (likely `Nat.log2 a + Nat.log2 b`)
3. Survey how Knuth Vol. 2 describes Lehmer's algorithm formally

### Phase 3: DECIDE
1. If Mathlib has `Nat.xgcd` → use it as the correctness backbone
2. Define `lehmerGcd` stub and prove correctness reduces to `Nat.gcd_rec`
3. For termination: prove each matrix has det ±1 AND reduces log-size

### Phase 4: ACT
```lean
def lehmerStep (a b : ℕ) : ℕ × ℕ := ...

theorem lehmerStep_gcd (a b : ℕ) (h : 0 < b) :
    let (a', b') := lehmerStep a b
    Nat.gcd a' b' = Nat.gcd a b := by
  ...

theorem lehmerStep_progress (a b : ℕ) (h : 2 ≤ b) :
    let (a', b') := lehmerStep a b
    a'.log2 + b'.log2 < a.log2 + b.log2 := by
  ...
```

## Related Gallery Proofs

- `binary-gcd`: Parent proof — Stein's algorithm formalization
- `bezout-identity`: Relevant for Bezout identity in correctness proof
- `euclidean-algorithm`: Classical GCD reference

## Quality Assessment

- **Tractability**: 7/10 — concrete algorithmic goal, well-defined termination metric
- **Significance**: 6/10 — practically important, good demonstration of Lean 4 for algorithms
- **Domain**: Algorithms / computational number theory
- **Risk**: Medium — floating-point approximation step may need simplified model
