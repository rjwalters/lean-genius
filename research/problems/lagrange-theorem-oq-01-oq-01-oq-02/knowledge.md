# lagrange-theorem-oq-01-oq-01-oq-02 — Isomorphism uniqueness for groups of order pq

**Problem**: Upgrade the parent pq-classification (counting of isomorphism classes)
to genuine `MulEquiv` isomorphisms: "any two groups of order pq are isomorphic to
each other, for each of the two cases" (cyclic case `p ∤ q-1`; non-cyclic case
`p | q-1`).

## Summary of progress

- **Abelian case: SOLVED & verified.** Every abelian group of order `pq` (any
  distinct primes `p ≠ q`) is cyclic, hence any two are isomorphic, each ≅
  `Multiplicative (ZMod pq)`. Shipped in `Proofs/LagrangeTheoremOQ01OQ01OQ02.lean`
  (7 theorems, 0 sorries, 0 axioms, Mathlib-only, kernel-verified standard triple).
- **General cyclic case & non-abelian case: BLOCKED** on the parent Sylow
  classification.

## Session 2026-06-23 (Session 1) — Abelian uniqueness, FRESH

**Mode**: FRESH · **Outcome**: progress (verified partial)

### What I Did
- Claimed the problem (after bernoulli/cayley were taken by sibling agents).
- Planned the full upgrade: cyclic case via parent `pq_unique_when_coprime` +
  `mulEquivOfCyclicCardEq`; abelian case via Cauchy + coprime-order product law.
- Wrote and **kernel-verified all proof logic** against real Mathlib (clean
  `lake env lean`, EXIT 0).
- **Discovered a blocker**: the parent dependency chain
  `Proofs.SylowTheoremOQ01` → `Proofs.LagrangeTheoremOQ01OQ01` does **not compile**
  on Mathlib v4.26.0 — 14 deterministic errors including unknown constant
  `Nat.Prime.eq_of_dvd_of_prime` and unknown identifier `orderOf_eq_one_iff_eq_one`
  (both confirmed absent from the v4.26.0 Mathlib source). This is real API drift,
  not the transient olean-cache corruption that also plagued the session.
- **Pivoted** to a self-contained, Mathlib-only file delivering the abelian thread,
  which needs none of the parent infrastructure.

### Key Findings
- `pq_abelian_isCyclic`: an abelian group of order `pq` is cyclic for EVERY pair of
  distinct primes — squarefree order + the coprime-order product law
  `Commute.orderOf_mul_eq_mul_orderOf_of_coprime` force a generator `a·b` of order
  `pq`. No divisibility hypothesis, so the abelian class is pinned in BOTH branches.
- Mathlib's `mulEquivOfCyclicCardEq` (two cyclic groups of equal `Nat.card` are
  isomorphic) is exactly the count→isomorphism upgrade tool; `zmodCyclicMulEquiv`
  gives the canonical `Multiplicative (ZMod n)` model.
- Bridge `Fintype.card` ↔ `Nat.card` via `Nat.card_eq_fintype_card`.
- `Commute.orderOf_mul_eq_mul_orderOf_of_coprime` is in namespace `Commute` (dot
  notation `(Commute.all a b)....`), not the root namespace — first guess
  `orderOf_mul_eq_mul_orderOf_of_coprime` failed with unknown identifier.

### Files Modified / Added
- `proofs/Proofs/LagrangeTheoremOQ01OQ01OQ02.lean` (NEW, 163 lines, 7 thms)
- `src/data/proofs/lagrange-theorem-oq-01-oq-01-oq-02/{meta.json,annotations.json}` (NEW)
- `src/data/research/problems/lagrange-theorem-oq-01-oq-01-oq-02.json` (knowledge update)

### Next Steps
1. **Mechanic repair** of `Proofs/SylowTheoremOQ01.lean` (and dependent
   `LagrangeTheoremOQ01OQ01.lean`) for Mathlib v4.26.0 — the parent entry is marked
   `verified` but is stale. Until then `pq_unique_when_coprime` cannot be imported.
2. After repair: add the general cyclic case `pq_cyclic_case_iso` (for `p ∤ q-1`,
   any two order-pq groups isomorphic) and `pq_iso_zmod_of_coprime`. The proof logic
   was already drafted and verified against an axiom-stub of `pq_unique_when_coprime`.
3. Non-abelian uniqueness: recognize any non-cyclic order-pq group as the internal
   semidirect product `ℤ/q ⋊ ℤ/p`; reuse the sibling `oq-01-oq-01-oq-01`
   ApproachB `actionHom` infrastructure; show all nontrivial actions give isomorphic
   products. Mathlib has `SemidirectProduct.mulEquivSubgroup` for the internal
   recognition but lacks a normal-complement → semidirect lemma packaged for this.
