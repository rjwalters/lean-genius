# Problem: Complete Higher-Order Stirling Expansion (Work in Progress)

## Statement

### Plain Language
Prove the first correction term in Stirling's asymptotic expansion:

  n! ∼ √(2πn) · (n/e)^n · (1 + 1/(12n) + O(1/n²))

Specifically: prove `stirling_first_correction` in `proofs/Proofs/StirlingExpansion.lean`:

  ∃ C > 0, ∀ n ≥ 2, |stirlingSeq(n)/√π - (1 + 1/(12n))| ≤ C/n²

### Formal Statement
```lean
theorem stirling_first_correction :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n →
      |stirlingSeq n / Real.sqrt π - (1 + 1 / (12 * (n : ℝ)))| ≤ C / (n : ℝ) ^ 2
```

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - seeker-selected
  - wip
  - analysis
  - asymptotics
  - stirling
```

**Significance**: 6/10 — Eliminates the remaining `axiom` from StirlingFormula.lean;
  the correction term is foundational for probability error bounds.
**Tractability**: 6/10 — Mathlib has `log_stirlingSeq_diff_hasSum`; proof path is clear
  but requires careful remainder summation.

## Why This Matters

1. **Axiom elimination**: Proving this removes the remaining sorry from
   `StirlingExpansion.lean`, and via `error_bound_from_correction` eliminates
   `stirling_error_bound_ge_2` from `StirlingFormula.lean`
2. **Error quantification**: Gives explicit O(1/n²) error useful in CLT and
   combinatorial probability proofs in the gallery
3. **Infrastructure reuse**: `stirling_two_term_expansion` is already proved
   assuming this theorem — so proving this completes that chain immediately

## Key Lean File

`proofs/Proofs/StirlingExpansion.lean` (line 94: the sorry)

The file already provides:
- `stirlingCoeff` and `stirlingPartial` definitions
- `stirling_two_term_expansion` proved from `stirling_first_correction`
- `error_bound_from_correction` proved
- Numerical verification examples

## Proof Strategy

The file documents a clear path via Mathlib's existing Stirling infrastructure:

**Strategy A** (recommended): Use `log_stirlingSeq_diff_hasSum`

Mathlib has:
```
Stirling.log_stirlingSeq_diff_hasSum (m : ℕ) :
  HasSum (fun k ↦ 1 / (2 * k + 1) * (1 / (2 * ↑m + 3)) ^ (2 * k + 1))
    (Real.log (stirlingSeq (m + 1)) - Real.log (stirlingSeq (m + 2)))
```

This gives the exact telescoping series. The leading term is ≈ 1/(3(2m+3)²) ≈ 1/(12m²).
Summing from m=n to ∞ gives log(stirlingSeq(n)) - log(√π) = 1/(12n) + remainder.
Bounding the remainder tail gives the O(1/n²) error.

**Key steps**:
1. Show `stirlingSeq` is positive (already in Mathlib)
2. Take `log` of both sides: prove `|log(stirlingSeq(n)/√π) - 1/(12n)| ≤ C'/n²`
3. Exponentiate: use `|exp(x) - (1+x)| ≤ C·x²` near 0

**Strategy B**: Wallis product analysis
- `Stirling.wallis` gives `∏ Wallis factors → √π`
- Extract the rate of convergence via `HasSum` remainder bounds

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `stirling-formula` | Parent proof, imports StirlingFormula.lean |
| `stirling-formula-oq-01` | Gallery entry for this expansion (1 sorry) |
| `central-limit-theorem` | Uses Stirling bounds; would benefit from sharper error |
| `basel-problem-oq-01-oq-01-oq-02-oq-02` | Also uses Stirling in Apéry context |

## Suggested First Steps

1. **OBSERVE**: `grep -n "log_stirlingSeq_diff_hasSum\|stirlingSeq\|wallis" ~/.elan/toolchains/leanprover-lean4-v4.*/lib/lean4/library/ 2>/dev/null || grep -rn "log_stirlingSeq_diff_hasSum" $(lake env printenv LEAN_PATH 2>/dev/null | tr ':' '\n' | head -5)` — locate the Mathlib lemma
2. **ORIENT**: Check `Mathlib.Analysis.SpecialFunctions.Stirling` for `log_stirlingSeq_diff_hasSum` signature and available corollaries
3. **DECIDE**: Choose between Strategy A (log telescoping) and Strategy B (Wallis rate); A is preferred
4. **ACT**: In `StirlingExpansion.lean`, replace the `sorry` using `log_stirlingSeq_diff_hasSum` + geometric series tail bound
