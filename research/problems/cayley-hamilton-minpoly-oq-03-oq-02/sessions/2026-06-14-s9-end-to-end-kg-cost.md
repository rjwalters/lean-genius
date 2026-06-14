# S9 — End-to-end Keller-Gehrig matmul cost bound (researcher-3, 2026-06-14)

## Goal

Close the one remaining gap in the formalizable layers of
cayley-hamilton-minpoly-oq-03-oq-02: the file proved the squaring-phase and
assembly-phase matrix-multiplication bounds **separately** (and discussed the
combined `O(log j)` figure only in prose), but never stated the **total**
Keller-Gehrig cost as a theorem.

## Result

Added to `proofs/Proofs/CayleyHamiltonMinpolyOQ03OQ02.lean`:

```lean
def kellerGehrigCost (j : ℕ) : ℕ :=
  (Nat.size j - 1) + (j.bitIndices.length - 1)

theorem kellerGehrigCost_le_two_size (j : ℕ) :
    kellerGehrigCost j ≤ 2 * Nat.size j := by
  have h := squareKrylovProd_factor_count_le_size j
  unfold kellerGehrigCost
  omega
```

- **Squaring phase** `Nat.size j - 1`: one multiply per `T_{i+1}=T_i·T_i`
  step, up to the highest set bit of `j` (index `Nat.size j - 1`).
- **Assembly phase** `j.bitIndices.length - 1`: multiplies to combine the
  `popcount(j)` selected squared-Krylov factors.
- **Bound** `≤ 2·Nat.size j ≈ 2⌈log₂(j+1)⌉` = genuinely `O(log j)`, the
  exponential speed-up over the `O(j)` naive Krylov matrix-vector ladder.

This is the formalizable core of the problem's headline `O(n^ω)` claim. The
per-multiply `O(n^ω)` cost (Layer 3) remains genuinely blocked on Mathlib
having no complexity monad and no fast matmul — but the *count* of matrix
multiplications is plain `ℕ` arithmetic and fully machine-checkable.

File: 383 → ~430 LOC, 12 → 13 theorems (+1 def), 3 axioms unchanged,
0 sorries, no new imports/axioms.

## Build status

NOT machine-checked — Docker daemon down this cycle. Proof is elementary
(one prior-lemma rewrite + `omega`). Shipped as a build-pending draft for
deployer/CI verification before merge.

## State

Phase ACT, iteration 9. Tractable layers (1, 2, 2.5) now saturated: the
structural bridge, correctness product formula, vector forms, both
factor-count bounds, and the end-to-end cost bound are all formalized.
Layer 3 (`O(n^ω)` per-multiply count) stays axiomatized/blocked.
