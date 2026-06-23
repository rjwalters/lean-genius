# Knowledge Base: borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02

**Problem**: Does the CRT compatibility for BU dimensions generalize to squarefree n = p₁·p₂·…·pₖ?

## Problem Summary

The semiprime case (n=pq, OQ03) proved buDim(pq,d) ≤ max(buDim(p,d), buDim(q,d)) using a CRT axiom, then OQ03-OQ01 derived it from the formula axiom. This problem asks whether the same result extends to k ≥ 3 prime factors.

---

## Session 2026-05-06 (Session 1) — Completed

**Mode**: FRESH
**Outcome**: completed (0 sorries, 0 axioms, gallery entry created)

### What I Did

1. Identified that `borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02` was the highest-knowledge available problem (after many stale pool entries were verified complete)
2. Discovered the key insight: `buDim_eq_sup_primeFactors` is trivially equivalent to `buDim_eq_formula` — the CRT is encoded in the definition of `buDimFormula`
3. Wrote `proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean` (247 lines, 13 theorems)
4. Resolved Mathlib API drift issues (Nat.primeFactors_prime unavailable in v4.26.0)
5. Created gallery entry in `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/`

### Key Findings

**Main insight**: The CRT compatibility holds for ALL n ≥ 2 (not just squarefree):
```
buDim n d = n.primeFactors.sup (fun p => buDim p d)
```
This follows trivially from `buDim_eq_formula` since `buDimFormula` is DEFINED as this sup.

**k-prime induction**: `primeFactors_prod_primes` proved by Finset induction:
- Base: {a}.primeFactors = {a} (via Nat.mem_primeFactors + Finset.eq_singleton_iff_unique_mem)
- Step: primeFactors(a * ∏S) = {a} ∪ S via Nat.primeFactors_mul

**API drift fix**: `Nat.primeFactors_prime` doesn't exist in Mathlib v4.26.0. Solution from Erdos367Problem.lean: use `Nat.mem_primeFactors` + `Finset.eq_singleton_iff_unique_mem` to prove `p.primeFactors = {p}` directly.

**Concrete cases**: buDim(30), buDim(210), buDim(2310) verified via native_decide for primeFactors computation.

### Files Modified

- `proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean` (new, 247 lines, 13 theorems)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/meta.json` (new)
- `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/annotations.json` (new)
- `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/index.ts` (new)
- Also fixed `proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02.lean`: removed bad import `Mathlib.Data.Finset.Lattice`

### Next Steps

None — proof complete.
