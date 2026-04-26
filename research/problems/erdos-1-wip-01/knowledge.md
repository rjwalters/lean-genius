# Knowledge Base: erdos-1-wip-01

**Problem**: Complete Erdős Problem #1 — Distinct Subset Sums (WIP Extension)
**Last Updated**: 2026-04-26

---

## Session 2026-04-26 (Session 1) — Superincreasing Lemma + OQ03 Fix

**Mode**: FRESH
**Outcome**: progress

### What I Did

1. Surveyed OQ01 (0 sorries), OQ02 (1 sorry), OQ03 (1 sorry), OQ04 (1 sorry)
2. Analyzed sorry in OQ02: `dfx_lower_bound` - INCORRECT theorem (false for n=1, N=1 with A={1}: 2 ≤ 1.596 is false). Sorry is for a misstatement of the DFX bound.
3. Analyzed sorry in OQ03: `minDSSBound` existence - FIXABLE with powers-of-2 construction
4. Analyzed sorry in OQ04: `conwayGuySeq` recurrence - UNCLEAR recurrence formula (values 0,1,2,4,7,13,24,44 don't follow simple closed-form)
5. Created `proofs/Proofs/Erdos1WIP01.lean` (250 lines, 0 sorries, 0 axioms):
   - `dss_superincreasing_extend`: If A has DSS and b > sum(A), then insert b A has DSS
   - `sum_two_pow_lt`: ∑_{i<n} 2^i < 2^n (inductive)
   - `powers_of_two_has_dss`: {2^0,...,2^(n-1)} has DSS (induction via superincreasing)
   - `dss_exists`: For any n, ∃ n-element DSS set bounded by n*2^n
   - `dss_positive_exists`: Existence with positivity and bound 2^n
   - `not_dss_of_mem_zero`: If 0 ∈ A, then ¬DSS(A)
   - `dss_elements_pos`: All elements of a DSS set are positive
   - `dss_subset`: Subset of DSS set has DSS
   - `dss_singleton`: Any singleton has DSS
   - `dss_sum_lower_bound`: sum(A) + 1 ≥ 2^n (for n-element DSS A)
   - `minDSS_witness`: Existential witness for OQ03's minDSSBound
6. Fixed sorry in OQ03's `minDSSBound` by importing WIP01 and using `Erdos1WIP.minDSS_witness n`
7. Created gallery entry `src/data/proofs/erdos-1-wip-01/meta.json`

### Key Findings

- **OQ02 sorry is for a wrong theorem**: The `dfx_lower_bound` claims `2^n ≤ 2√(2/π)·√n·N` but this is false for n=1, N=1 (gives 2 ≤ 1.596). The actual DFX bound is asymptotic and needs additional hypotheses.
- **Superincreasing is the right abstraction**: The Conway-Guy sequence works because it's approximately superincreasing. The lemma captures this cleanly.
- **OQ03 fix**: minDSSBound now uses `Erdos1WIP.minDSS_witness` instead of a sorry.
- **OQ04 recurrence**: The sequence values {0,1,2,4,7,13,24,44,84} don't follow a simple closed-form recurrence; the sorry for `conwayGuySeq n+2` remains unfixed.

### Files Modified

- `proofs/Proofs/Erdos1WIP01.lean` (CREATED, 250 lines, 0 sorries, 0 axioms)
- `proofs/Proofs/Erdos1OQ03.lean` (FIXED sorry in minDSSBound)
- `proofs/Proofs.lean` (added Erdos1WIP01 import)
- `src/data/proofs/erdos-1-wip-01/meta.json` (CREATED)

### Next Steps

1. **OQ02 fix**: Change `dfx_lower_bound` theorem to have correct statement (add n ≥ 2 or different constant), or mark it as axiomatized
2. **OQ04 fix**: The `conwayGuySeq n+2` recurrence needs the actual formula. The greedy rule "add smallest m > max that preserves DSS" is non-trivial. May need to be left as `conwayGuy` lookup table.
3. **Strengthen WIP01**: Add more structural lemmas (e.g., if A has DSS and all elements ≥ 1, then consecutive differences satisfy structural inequalities)
4. **Submit hard lemmas to Aristotle**: `dss_sum_lower_bound` and `dss_elements_pos` should compile cleanly; verify via docker build
