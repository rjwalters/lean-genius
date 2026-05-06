# laws-of-large-numbers-oq-01-oq-02: SLLN Rate for Heavy-Tailed Distributions

**Problem**: What is the rate of convergence of the sample mean for heavy-tailed distributions (E[X²] = ∞)?

**Status**: COMPLETE — PR created 2026-05-06, 0 sorries, 3 axioms

---

## Session 2026-05-06 (Session 1) — Complete Formalization

**Mode**: FRESH  
**Outcome**: completed

### What I Did

1. Claimed problem, created branch `feature/researcher-4-lln-mz-rates`
2. Surveyed existing parent infrastructure (LawsOfLargeNumbersOQ01.lean, LawsOfLargeNumbersOQ01OQ01.lean)
3. Identified the Marcinkiewicz-Zygmund SLLN as the key result
4. Implemented `LawsOfLargeNumbersOQ01OQ02.lean` (344 lines, 10 theorems, 3 axioms, 0 sorries)
5. Created gallery entry `laws-of-large-numbers-oq-01-oq-02` with meta.json, annotations.json, index.ts
6. Created PR

### Key Mathematical Insights

- The M-Z theorem provides a **rate hierarchy** interpolating between Kolmogorov (r=1) and CLT (r=2)
- For r ∈ (1,2): the rate n^{1/r} lies strictly between n (Kolmogorov scale) and n^{1/2} (CLT scale)
- The proof uses a truncation argument: truncate at n^{1/r}, handle truncated part via Kolmogorov 3-series, tail via E[|X|^r]<∞ → Σ P(|X|>n^{1/r})<∞
- For Pareto(α) with α∈(1,2): the sharp rate is n^{1/α} from the stable CLT; M-Z gives o(n^{1/r}) for r < α approaching this from below
- Key formalization insight: `Memℒp.mono_exponent` gives L² ⊆ Lʳ for r≤2 in probability spaces

### Files Modified

- `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02.lean` (344 lines, 10 theorems, 3 axioms)
- `src/data/proofs/laws-of-large-numbers-oq-01-oq-02/meta.json`
- `src/data/proofs/laws-of-large-numbers-oq-01-oq-02/annotations.json`
- `src/data/proofs/laws-of-large-numbers-oq-01-oq-02/index.ts`

### Axioms Required

1. **`marcinkiewicz_zygmund_slln`**: The M-Z theorem itself — truncation argument not in Mathlib 4.26
2. **`pareto_in_lr_iff`**: E[Pareto(α)^r] < ∞ ↔ r < α — improper integral computation
3. **`stable_clt_attraction`**: n^{-1/α}(Sₙ−nμ) → 0 for Pareto(α) — requires characteristic function theory

### Follow-Up Questions

- Prove `marcinkiewicz_zygmund_slln` from Mathlib's 3-series theorem (Aristotle-suitable)
- State the distributional α-stable limit (requires Lévy continuity theorem formalization)
- Prove `pareto_in_lr_iff` from basic Mathlib integral calculus
