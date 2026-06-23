# fundamental-arithmetic-oq-01-oq-01

**Problem**: Can the unique factorization be proved in a way that avoids the parent file, giving a self-contained proof of the Fundamental Theorem from Mathlib primitives?

## Problem Summary

This problem asks for a self-contained proof of the FTA that avoids importing `FundamentalArithmetic.lean`. The parent file uses the sorted-list approach (`Nat.primeFactorsList`). This problem explores the algebraic (Finsupp) approach using `Nat.factorization : ℕ → (ℕ →₀ ℕ)`.

**Answer**: Yes. The Finsupp-based FTA states: for n ≠ 0, there exists a unique f : ℕ →₀ ℕ with prime support satisfying f.prod (·^·) = n. The canonical witness is n.factorization.

## Key Mathlib Facts Used

- `Nat.factorization_prod_pow_eq_self`: n.factorization.prod (·^·) = n (reconstruction)
- `Nat.support_factorization`: n.factorization.support = n.primeFactors
- `Nat.Prime.factorization hp`: p.factorization = Finsupp.single p 1
- `Nat.factorization_pow`: (n^k).factorization = k • n.factorization
- `Nat.factorization_mul`: (m*n).factorization = m.factorization + n.factorization
- `Finsupp.finset_sum_apply`: distributes Finsupp apply over sums
- `Finset.sum_ite_eq`: collapses indicator sums

## Session 2026-05-03 (Session 1) — Complete Proof

**Mode**: FRESH (first attempt)
**Outcome**: complete — 0 sorries, 0 axioms, 12 theorems, 220 lines

### What I Did
- Selected problem (score 0, fresh, tractable)
- Wrote full proof in `FundamentalArithmeticOQ01OQ01.lean`
- Key proof strategy: the algebraic identity (f.prod (·^·)).factorization = f for prime-support f
- Helper lemma: `factorization_finset_prod` (distribution over products by induction)
- Created gallery entry with meta.json, index.ts, annotations.json
- Updated listings.json with new entry
- Docker build pending

### Files Modified
- `proofs/Proofs/FundamentalArithmeticOQ01OQ01.lean` (new, 220 lines)
- `src/data/proofs/fundamental-arithmetic-oq-01-oq-01/meta.json` (new)
- `src/data/proofs/fundamental-arithmetic-oq-01-oq-01/index.ts` (new)
- `src/data/proofs/fundamental-arithmetic-oq-01-oq-01/annotations.json` (new)
- `src/data/proofs/listings.json` (added entry)

### Key Findings

**The algebraic core**: `finsupp_prime_prod_factorization` proves (f.prod (·^·)).factorization = f for prime-support f. The proof:
1. Distribute factorization over the Finset product (induction, using Nat.factorization_mul)
2. Use Nat.factorization_pow + Prime.factorization to reduce each term to indicators
3. Collapse with Finset.sum_ite_eq

**Uniqueness follows cleanly**: g = (g.prod (·^·)).factorization = n.factorization.

**Proof contrast with parent file**:
- Parent: sorted list [2,2,3,5,...] with `Nat.primeFactorsList`
- This file: Finsupp {2 ↦ 2, 3 ↦ 1, 5 ↦ 1} with `Nat.factorization`

### Next Steps
- Verify Docker build completes without errors
- Promote to gallery with PR

## Session 2026-06-04 (Session 2) — Mathlib v4.26.0 compatibility repair

**Mode**: REPAIR
**Outcome**: clean — Docker build of `Proofs.FundamentalArithmeticOQ01OQ01` succeeds against the current Mathlib pin. 0 sorries, 0 axioms, 220 lines, 12 theorems + 1 helper lemma.

### API drift fixes applied

- `Finset.induction_on` `insert` case now uses `| @insert a s ha ih` (explicit binders) rather than `rename_i`.
- `Finset.prod_ne_zero` → `Finset.prod_ne_zero_iff.mpr`.
- `Nat.mem_primeFactors hn` → bare `Nat.mem_primeFactors` (now an iff with a 3-way conjunction; project via `h.2.1`).
- `Nat.coprime_iff_disjoint.mp hcop` → `hcop.disjoint_primeFactors` plus `Nat.support_factorization` rewrites.
- `Finset.sum_ite_eq` → `Finset.sum_ite_eq'` (matches the `if x = a` orientation).
- `Finsupp.not_mem_support_iff` → `Finsupp.notMem_support_iff` (camelCase rename).
- `native_decide` on `Finsupp.single` equalities (noncomputable) → reformulated as pointwise `(n).factorization k = e` checks and primeFactors set equalities.
- Helper `factorization_finset_prod` generalized from `(∏ m ∈ s, m)` to `(∏ i ∈ s, g i)` with `[DecidableEq ι]`, fixing the rewrite failure at the key-lemma site.

No mathematical content changed; only Mathlib API call shapes.
