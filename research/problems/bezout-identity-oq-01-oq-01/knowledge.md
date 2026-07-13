# bezout-identity-oq-01-oq-01: Stein's Binary GCD Algorithm

**Status**: COMPLETED  
**Phase**: COMPLETED  
**Parent**: bezout-identity-oq-01 (Extended Euclidean Algorithm)

## Problem Summary

Can Stein's binary GCD algorithm — which computes gcd(a,b) using only subtraction and right-shifts, avoiding modular division — be formalized and proved equal to Nat.gcd in Lean 4?

**Answer**: Yes. The proof is complete and gallery entry was added 2026-05-03.

---

## Session 2026-05-03 (Session 1) - Gallery Entry Creation

**Mode**: REVISIT  
**Outcome**: completed

### What I Did

- Discovered that `proofs/Proofs/BezoutIdentityOQ01OQ01.lean` (188 lines, 0 sorries, 0 axioms) was complete but had no gallery entry
- Read the full Lean file and understood the proof structure
- Created gallery entry at `src/data/proofs/bezout-identity-oq-01-oq-01/`:
  - `meta.json`: full metadata with 6 theorems, 6 sections, 2 open questions
  - `annotations.json`: 7 pedagogical annotations covering key techniques
  - `index.ts`: TypeScript re-export
- Updated `src/data/research/problems/bezout-identity-oq-01-oq-01.json` with knowledge and completion status

### Key Findings

- The algorithm has 7 branches with termination by well-founded recursion on `a + b`
- `termination_by a + b` with `decreasing_by all_goals simp_wf; all_goals omega` closes all 7 termination goals automatically
- The key coprimality argument: if b is odd then gcd(2,b)=1, so gcd(2a,b)=gcd(a,b) via `Nat.Coprime.gcd_mul_left_cancel`
- Bézout corollary is immediate once correctness is established: use `Int.gcd_eq_gcd_ab` with a cast

### Files Modified

- `src/data/proofs/bezout-identity-oq-01-oq-01/meta.json` (created)
- `src/data/proofs/bezout-identity-oq-01-oq-01/annotations.json` (created)
- `src/data/proofs/bezout-identity-oq-01-oq-01/index.ts` (created)
- `src/data/research/problems/bezout-identity-oq-01-oq-01.json` (updated)

### Theorems Formalized

1. `binaryGcd`: Stein's algorithm, 7 branches, terminates by well-founded recursion on a+b
2. `binaryGcd_eq_gcd`: correctness, binaryGcd a b = Nat.gcd a b
3. `binaryGcd_comm`: symmetry, binaryGcd a b = binaryGcd b a
4. `binaryGcd_dvd_left` / `binaryGcd_dvd_right`: divisibility
5. `dvd_binaryGcd`: universality
6. `bezout_via_binaryGcd`: Bezout corollary

### Open Questions Generated

1. Can the O(log^2(max(a,b))) complexity bound be formalized using a bit-length measure?
2. Can binaryGcd be extended to integers via binaryGcd |a| |b|?

### Next Steps

- None (proof complete, gallery entry added)
