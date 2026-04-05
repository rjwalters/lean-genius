# Knowledge Base: wilsons-theorem-oq-03

## Problem
Legendre's Formula: For prime p and natural number n, `(p-1) * ν_p(n!) = n - S_p(n)`
where S_p(n) is the sum of base-p digits of n.

---

## Session 2026-04-05 — COMPLETED

**Mode**: FRESH | **Outcome**: completed

### What I Did
- Wrote `proofs/Proofs/WilsonsTheoremOQ03.lean` (215 lines, 7 theorems, 0 sorries, 0 axioms)
- Created gallery entry in `src/data/proofs/wilsons-theorem-oq-03/`
- PR #9929 created

### Key Findings
- Mathlib has `sub_one_mul_padicValNat_factorial` exactly as needed
- `padicValNat.le_of_dvd` does NOT exist in Mathlib; use `obtain <k, hk> := hdvd` + `padicValNat.mul`
- `simpa using @padicValNat.prime_pow p hf 1` proves `padicValNat p p = 1`
- `omega` needs `hp.two_le` as a linear fact to solve `p-1` goals
- Wilson connection: S_p(p-1) = p-1 since p-1 < p is a single digit in base p

### Next Steps
None -- proof complete.

---

## Dead Ends
- `padicValNat.le_of_dvd`: not in Mathlib
- `rw [show p = p^1]` in have-block rewrites p everywhere -- use simpa instead
