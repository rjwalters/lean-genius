# Knowledge Base: combinations-formula-oq-03-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

### 2026-07-20 (researcher-1) — unimodality API + base cases k ≤ 1

- **Mathlib gap confirmed**: no `Unimodal` predicate for integer sequences. Introduced
  `IsCoeffUnimodal (p : ℤ[X])` = ∃ peak index m with coeffs weakly rising to m and weakly
  falling after, in `CombinationsFormulaOQ03OQ04Unimodal.lean`.
- **`isCoeffUnimodal_of_antitone`**: a globally non-increasing coeff sequence is unimodal
  (peak 0). The rising half is vacuous (only i=j=0 with i≤j≤0). Covers every flat/monotone
  base case cheaply.
- **Coefficient extraction that works**: `qBinom_one_right` (`[n,1]_q = qNumber X n`,
  general `R`) + an induction on `qNumber X (n+1) = 1 + X·qNumber X n` gives
  `qNumber_X_coeff n j = if j < n then 1 else 0`. Key simp lemmas: `coeff_add`, `coeff_one`,
  `coeff_X_mul` (for `(X·p).coeff (m+1) = p.coeff m`). Then both base cases reduce to
  `simp only [<coeff formula>]; split_ifs <;> omega`.
- **Base cases proved**: `qBinom_X_unimodal_zero` (k=0, coeff seq 1,0,0,…) and
  `qBinom_X_unimodal_one` (k=1, coeff seq 1,…,1,0,…). Both are antitone, so unimodal.

### Route to k = 2 (next, genuine content)
`[n,2]_q` coeffs count partitions in a 2×(n−2) box: `a_i = ⌊i/2⌋+1` for the rising half,
mirrored (peak interior). This is the first case where `_of_antitone` fails and the
rise-then-fall must be argued directly — the named tractable milestone in problem.md.

### Open crux (k ≥ 2 general)
Sylvester unimodality for general k needs sl₂-action / hard Lefschetz (Proctor 1982) or
O'Hara's (1990) combinatorial symmetric-chain decomposition — research-grade formalization,
not yet started.

---

## Dead Ends

[Approaches known not to work will be documented here]
