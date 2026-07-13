# Knowledge Base: sqrt2-minpoly-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Generalize `Sqrt2Minpoly` (gallery: minpoly ℚ √2 = X² - 2) to show that for any
natural numbers n, k ≥ 2 satisfying the Eisenstein condition (a prime p | n with p^k ∤ n),
the minimal polynomial of n^(1/k) over ℚ is X^k - n.

Key ingredients:
- `Polynomial.irreducible_of_eisenstein_criterion` in Mathlib
- `minpoly.eq_of_irreducible_of_monic` to conclude minimality
- `Real.rpow` for n^(1/k) and `aeval` evaluation to zero

---

## Session 2026-04-23 (Session 1) - Complete Proof File Created

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Found that `CubeRoot2IrrationalOQ03` already contains `minpoly_nthRoot_eq`
- Created dedicated `proofs/Proofs/Sqrt2MinpolyOQ02.lean` (202 lines, 0 sorries, 0 axioms)
- Added: squarefree corollary, degree theorems, non-perfect-power criterion, 12 concrete examples
- Updated meta.json: proofRepoPath → `Proofs/Sqrt2MinpolyOQ02.lean`, mainTheorems namespace

### Key Findings
- `Nat.squarefree_iff_prime_squarefree` + `rwa [sq]` closes the squarefree → Eisenstein condition gap
- `(minpoly_nthRoot_eq k m p hk hp hdvd hndvd hm).symm` converts X^k-m=minpoly to minpoly=X^k-m
- All new theorems are 1-2 line wrappers delegating to CubeRoot2IrrationalOQ03 infrastructure

---

## Insights

- The `CubeRoot2IrrationalOQ03` file is the right dependency for sqrt2-minpoly-oq-02
- Squarefree corollary via `Nat.squarefree_iff_prime_squarefree` → `rwa [sq]` for ¬ p^2 ∣ m

---

## Dead Ends

- Irrationality theorem attempt removed: `Rat.minpoly_eq_X_sub_C` approach was risky;
  irrationality follows trivially from degree = k ≥ 2 but not needed for gallery
