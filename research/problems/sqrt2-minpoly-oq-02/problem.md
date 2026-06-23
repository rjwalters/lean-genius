# Problem: Minimal Polynomial of k-th Roots: minpoly ℚ (n^(1/k)) = X^k - n via Eisenstein

## Statement

### Plain Language

Generalize the existing `Sqrt2Minpoly` gallery proof to show that for any natural numbers
`n, k ≥ 2` where `n` is not a perfect `k`-th power and there exists a prime `p` with
`p ∣ n` but `p^k ∤ n`, the minimal polynomial of `n^(1/k)` over ℚ is exactly `X^k - n`.

### Formal Statement

```lean
theorem kth_root_minpoly (n k : ℕ) (hk : 2 ≤ k) (p : ℕ) (hp : Nat.Prime p)
    (hdvd : p ∣ n) (hndvd : ¬ (p ^ k ∣ n)) :
    minpoly ℚ (Real.rpow (n : ℝ) (1 / k : ℝ)) = X ^ k - C (n : ℚ) := ...
```

## Classification

```yaml
tier: B
significance: 7
tractability: 8
tags:
  - seeker-selected
  - algebraic-number-theory
  - minimal-polynomial
  - eisenstein
  - radical-extensions
```

**Significance**: 7/10 — Natural generalization of a verified gallery proof; builds the
general theory behind all pure radical extensions.

**Tractability**: 8/10 — The proof strategy is known (Eisenstein + root witness), Mathlib
has all required ingredients, and the specific X^2-2 case already exists in the gallery.

## Why This Matters

1. **Direct generalization**: The gallery proof `Sqrt2Minpoly` handles the n=2, k=2 case.
   This extends to all `(n, k)` satisfying the Eisenstein condition, establishing the
   general theory of pure radical extensions ℚ(n^(1/k)) in Lean.

2. **Eisenstein criterion application**: Demonstrates the workhorse irreducibility test
   for X^k - n polynomials, connecting to `Polynomial.irreducible_of_eisenstein_criterion`
   in Mathlib.

3. **Foundation for Galois theory**: Minimal polynomials of k-th roots establish
   degrees [ℚ(n^(1/k)) : ℚ] = k and are the starting point for computing splitting
   fields and cyclotomic extensions.

4. **Lean 4 approach**: Lean/Mathlib has `Real.rpow`, nth-root structure, and the
   full Eisenstein criterion, so the root witness `(n^(1/k))^k = n` should be provable.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `sqrt2-minpoly` | Direct predecessor — minpoly ℚ √2 = X² - 2. Proof strategy is identical. |
| `sqrt2-irrational` | Irrationality certificate from degree > 1 |
| `cube-root-2-irrational` | Related: cube root of 2 is irrational (minimal poly X³ - 2) |

## Suggested First Steps

1. **OBSERVE**: Check what Mathlib has for `Real.rpow`, `kthRoot`, and whether
   `Polynomial.irreducible_of_eisenstein_criterion` generalizes to X^k - n for k > 2.
   Look at `Mathlib.RingTheory.Eisenstein.Basic`.

2. **ORIENT**: The X^2-2 proof uses `minpoly.eq_of_irreducible_of_monic`. Check if
   the same lemma applies for degree k. Key gap: expressing n^(1/k) so that Lean
   accepts `aeval (n^(1/k)) (X^k - n) = 0`.

3. **DECIDE**: If `Real.rpow` works directly, implement as a parameterized theorem.
   Otherwise consider `Polynomial.roots` or algebraic closure arguments. Start with
   the concrete case minpoly ℚ (∜2) = X⁴ - 2 (n=2, k=4) as a stepping stone.
