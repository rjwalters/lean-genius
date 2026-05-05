# SLLN Necessity: Kolmogorov's Converse Direction

**Problem**: laws-of-large-numbers-oq-01-oq-01  
**Question**: Can the converse (slln_necessity) be proved in Mathlib?  
**Parent proof**: laws-of-large-numbers-oq-01 (has `axiom slln_necessity`)

## Session 2026-05-05 (Session 1) — Proof Structure

**Mode**: FRESH  
**Outcome**: progress — proof structure complete, 2 sorries for BC2 lemmas

### What I Did

1. Examined parent `LawsOfLargeNumbersOQ01.lean` — found `axiom slln_necessity` (1 axiom, 0 sorries)
2. Examined `LawsOfLargeNumbersOQ01Aristotle.lean` — found proof of `slln_necessity_statement` by Aristotle, but with `exact?` compilation gaps in `borel_cantelli_of_pairwise_independent`
3. Wrote clean `LawsOfLargeNumbersOQ01OQ01.lean` with full proof structure
4. Created gallery entry `src/data/proofs/laws-of-large-numbers-oq-01-oq-01/`

### Key Findings

- **YES, the converse can be proved** — the mathematical structure is complete
- Proof: by contradiction using layer cake + pairwise BC2 + Cesàro
- The 2 remaining sorries (`variance_sum_indicator_le`, `borel_cantelli_pairwise_indep`) are well-defined L² arguments
- The `IndepFun → IndepSet` conversion uses `Kernel.indepFun_iff_measure_inter_preimage_eq_mul`
- The `hmeas` argument is extra vs the axiom signature but follows from `IdentDistrib.aemeasurable_fst`

### Files Modified

- `proofs/Proofs/LawsOfLargeNumbersOQ01OQ01.lean` (NEW, ~240 lines, 2 sorries)
- `src/data/proofs/laws-of-large-numbers-oq-01-oq-01/` (NEW gallery entry)
- `src/data/research/problems/laws-of-large-numbers-oq-01-oq-01.json` (knowledge updated)

### Next Steps

1. Submit `variance_sum_indicator_le` and `borel_cantelli_pairwise_indep` to Aristotle
2. Verify `Kernel.indepSet_iff_measure_inter_eq_mul` compiles in current Mathlib
3. After Aristotle returns proofs, run docker-build to verify
4. Update `LawsOfLargeNumbersOQ01.lean` to replace `axiom slln_necessity` with theorem (reduce axiom count from 1 to 0)
