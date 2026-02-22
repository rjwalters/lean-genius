# Problem: Is ζ(5) irrational

## Statement

### Plain Language
Is the value ζ(5) = 1 + 1/2^5 + 1/3^5 + 1/4^5 + ... = ∑_{n=1}^∞ 1/n^5 irrational?

### Formal Statement
```lean
-- OPEN CONJECTURE
theorem zeta_five_irrational : Irrational (∑' n : ℕ, 1 / (n : ℝ)^5) := by sorry
```

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - seeker-selected
  - extension
  - challenging
  - analysis
  - series
  - convergence
  - wiedijk-100
  - zeta-function
  - classic
```

**Significance**: 6/10
**Tractability**: 0/10 (OPEN: No proof currently known)

## Why This Matters

This is one of the central open problems in analytic number theory. Euler
computed ζ(2k) = rational × π^(2k) (hence transcendental), and Apéry
proved ζ(3) irrational in 1978. For odd zeta values ζ(5), ζ(7), ...,
almost nothing is known individually. The problem illustrates the gap
between what is known (Euler's formula for even values, Apéry's ζ(3))
and what remains mysterious.

## Known Results

| Result | By | Year | Status |
|--------|----|----|--------|
| ζ(2) = π²/6 | Euler | 1735 | In Mathlib |
| ζ(4) = π⁴/90 | Euler | 1735 | In Mathlib |
| ζ(3) is irrational | Apéry | 1978 | NOT in Mathlib (axiom) |
| Infinitely many ζ(2n+1) irrational | Rivoal | 2000 | NOT in Mathlib (axiom) |
| One of ζ(5),ζ(7),ζ(9),ζ(11) irrational | Zudilin | 2001 | NOT in Mathlib (axiom) |
| ζ(5) irrational | **OPEN** | — | **Unknown** |

## What Was Formalized (2026-02-22)

File: `proofs/Proofs/ZetaFiveIrrationality.lean`

**Proved from first principles:**
- Convergence: `Summable (fun n => 1/(n:ℝ)^5)` (p-series, p=5>1)
- Lower bound: `1 ≤ ζ(5)` (via hasSum_ite_eq + hasSum_le)
- Upper bounds: `ζ(5) ≤ π⁴/90` and `ζ(5) ≤ π²/6` (term-by-term via one_div_le_one_div_of_le)

**Stated as axioms (known proofs not yet in Mathlib):**
- `apery_theorem`: ζ(3) is irrational
- `rivoal_theorem`: infinitely many odd ζ values are irrational
- `zudilin_theorem`: one of ζ(5),ζ(7),ζ(9),ζ(11) is irrational

**Open conjecture (1 sorry):**
- `zeta_five_irrational`: ζ(5) is irrational (OPEN)

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| BaselProblem.lean | ζ(2) = π²/6 (proved) |
| RiemannHypothesis.lean | Related zeta function context |
