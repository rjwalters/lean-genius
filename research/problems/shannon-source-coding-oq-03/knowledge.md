# Shannon Source Coding OQ-03: Asymptotic Equipartition Property

**Problem**: Can the AEP be formalized using Mathlib's probability infrastructure for the discrete finite-alphabet case?

**Status**: NEAR-COMPLETE — gallery entry created, 1 sorry remaining

---

## Session 2026-05-03 (Session 1) - Gallery Entry Created

**Mode**: FRESH
**Outcome**: progress — key theorems proved, gallery created, 1 sorry remaining

### What I Did
- Claimed problem (RICH knowledge score 18, tractability 5)
- Proved `expVal_marginal` via `Fintype.prod_sum`: joint expectation factors into per-symbol marginal
- Proved `expVal_empEnt` using `expVal_marginal`: E[empEnt] = H(p)
- Fixed bug in `aep_concentration`: original incorrectly applied `rw [expVal_empEnt]` to variance goal; fixed to use `empEnt_variance`
- Proved `aep_concentration` (modulo `empEnt_variance` sorry)
- Proved `typical_set_size_upper` (no sorry)
- Created gallery entry: meta.json, annotations.json, index.ts
- Created `proofs/Proofs/ShannonSourceCodingOQ03.lean`

### Key Findings
- `Fintype.prod_sum` (in `Mathlib.Algebra.BigOperators.Pi`) is the algebraic core: it exchanges sum-over-functions with product-of-sums, formalizing i.i.d. independence
- `expVal_marginal` proof: rewrite joint product via `Finset.mul_prod_erase`, then apply `← Fintype.prod_sum`, then evaluate the product (j-th factor = ∑p·g, others = ∑p = 1)
- The original `aep_concentration` had a conceptual bug: it tried to rewrite `E[(empEnt - H)²]` using the mean equation `E[empEnt] = H`, which doesn't apply. The fix uses `empEnt_variance` to rewrite the variance term.
- One sorry remains: `empEnt_variance` (Var[empEnt] = logVar/n). This requires showing E[Z_i * Z_j] = E[Z_i]*E[Z_j] for i≠j (cross-term independence), which is a 2D version of `expVal_marginal`.

### Files Modified
- `proofs/Proofs/ShannonSourceCodingOQ03.lean` (created, ~260 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/shannon-source-coding-oq-03/` (created gallery entry)
- `src/data/research/problems/shannon-source-coding-oq-03.json` (updated knowledge)

### Next Steps
1. Prove `expVal_bilinear`: E[g(Xᵢ)·h(Xⱼ)] = E[g(Xᵢ)]·E[h(Xⱼ)] for i≠j (~50 lines, same Fintype.prod_sum technique)
2. Use `expVal_bilinear` to prove `empEnt_variance` and eliminate the last sorry
3. After all sorries resolved: badge upgrades to `verified`, 0 axioms, 0 sorries
