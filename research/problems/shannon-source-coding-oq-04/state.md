# Research State: shannon-source-coding-oq-04

## Current State
**Phase**: ACT (statement audit; awaiting decision between Track A vs Track B)
**Since**: 2026-04-27T17:55:00Z
**Iteration**: 4

## Current Focus

`ShannonSourceCodingOQ04.lean` has 1 remaining sorry at line 386, in
`source_coding_achievability_mot`. Session 4 audit (2026-04-27) found that the **statement
of this theorem is trivially true** — it does not actually capture Shannon's achievability
claim because:

- `δ` does not appear in the conclusion
- `code_length = 0` always works (since `n * H(p) + n * ε ≥ 0`)
- The witness type `f = (n, 0, ..., 0)` has type class `{const 0}` (singleton, ≤ 2^0 = 1)

The supporting infrastructure is already proved:

| Lemma | Role |
|---|---|
| `type_class_size_eq_multinomial` | |T_f| = n!/∏(fᵢ!) (combinatorial identity) |
| `count_types_le` | distinct types ≤ (n+1)^k (polynomial in n) |
| `total_sequences_eq` | Total k^n sequences |
| `dominant_type_lower_bound` | Largest type class has ≥ k^n / (n+1)^k sequences |
| `type_class_size_le_entropy_pow` | |T_f| ≤ 2^{n H(Q)} (entropy upper bound) |

## Active Approach

Two tracks identified:

- **Track A** (Quick Win, ~30 lines): Prove the trivial form to eliminate the sorry.
  Mark statement as weak in description; status → `axiomatized` (with companion axiom for the
  real claim).
- **Track B** (Real Theorem, ~300-500 lines): Strengthen the statement to capture
  probability-mass coverage; prove via type-class size bounds + AEP / concentration.

## Attempt Count
- Total attempts: 4 (sessions 1-4)
- Current approach attempts: 4
- Approaches tried: 1 (combinatorial method-of-types infrastructure)

## Blockers

- **Disk pressure** (1.5 GiB free as of 2026-04-27) blocks Docker build verification.
- Track B requires AEP-like concentration: `∑_x ∏_j p(x j) → 1 - O(ε)` for sequences in the
  dominant type class. This needs LLN/concentration infrastructure (~300+ lines).

## Next Action

Decide between Track A and Track B (a human-level decision about formalization standards).

If Track A:
1. Prove the trivial form (~30 lines, see knowledge.md Session 4 for sketch)
2. Add `shannonEntropy_nonneg` lemma if not in scope
3. Add a clear note in the docstring/description that the statement is weak
4. Add `axiom source_coding_achievability_mot_strong` for the real claim
5. Update meta.json: status → `axiomatized`, badge → `axiom`

If Track B:
1. Replace the statement with the strong version (see knowledge.md)
2. Build product-measure-on-`Fin n → Fin k` infrastructure (~50 lines)
3. Prove dominant-type concentration via Chernoff or Hoeffding (~150 lines)
4. Assemble achievability (~100 lines)
5. Total: 1 sorry → 0 sorries with REAL achievability content

## Key Mathlib Lemmas (Session 4 reference)

- `shannonEntropy` (local, line 42): non-negative for probability distributions
- `Finset.sum_ite_eq'`: gives `∑ i, (if i = a then x else 0) = x` for the degenerate type
- `Real.exp_nonneg`: needed for the H + ε bound positivity
- (Track B only) `Mathlib.Analysis.SpecificLimits.Basic`, `Mathlib.Probability.IdentDistrib`

## Mathlib API Survey (Mathlib 4.26.0)

| Symbol | Use |
|---|---|
| `Mathlib.InformationTheory.KullbackLeibler.Basic` | KL divergence — useful for entropy continuity |
| `Mathlib.InformationTheory.KullbackLeibler.KLFun` | KL function and properties |
| `Mathlib.InformationTheory.Hamming` | Hamming distance (unrelated) |
| `Real.logb` | Used in `shannonEntropy` definition |
| `Real.exp_log` / `Real.rpow_logb` | Conversion between log and rpow |

Mathlib does **not** have a Shannon entropy function with the standard name (the
file's `shannonEntropy` is locally defined). It does have KL divergence, from which
H(p) = log(k) - D(p ‖ uniform) for finite alphabets — could be used as a bridge if
needed.

## Remaining Work

- 1 sorry: `source_coding_achievability_mot` (line 386) — trivially provable per audit
- For genuine achievability content: need product measure + AEP/concentration (Track B)
