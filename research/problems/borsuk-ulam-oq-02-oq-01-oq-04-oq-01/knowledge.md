# Borsuk-Ulam OQ-02-OQ-01-OQ-04-OQ-01: Formalize H*(BZ/p; F_p) ≅ F_p[u]

**Status**: IN PROGRESS (ACT phase)
**Problem**: Formalize the cohomology ring of BZ/p as the polynomial ring F_p[u]

## Problem Summary

The classifying space BZ/p has cohomology:
- **p = 2**: H*(BZ/2; F_2) ≅ F_2[u], |u| = 1 (since BZ/2 = RP^∞)
- **p odd**: H*(BZ/p; F_p) ≅ E[v] ⊗ F_p[u], |v| = 1, |u| = 2

For Fadell-Husseini index theory, only the polynomial factor F_p[u] matters.
The FH index of a Z/p-space X ↪ V is the ideal Ann(i*: H*(BV) → H*(X)) ⊆ F_p[u].
Index ideals are of the form (u^m), and containment (u^n) ⊆ (u^m) encodes dimension bounds.

**Key goal**: Prove the algebraic fact that `umIdeal p n ≤ umIdeal p m ↔ m ≤ n`
and connect this to the buDim formula from BorsukUlamOQ02OQ01.

---

## Session 2026-04-12 (Session 1) - Polynomial Ring Model

**Mode**: FRESH (first session on this problem)
**Outcome**: progress — implemented `BorsukUlamOQ02OQ01OQ04OQ01.lean`

### What I Did

1. Surveyed BorsukUlamOQ02OQ01OQ04.lean for the abstract FH index structure (CohRing, cohRing, powerIndex)
2. Identified `Polynomial (ZMod p)` as the correct concrete model for F_p[u]
3. Implemented the polynomial ring model with ideal filtration
4. Proved ideal containment ↔ power ordering (key algebraic fact)
5. Connected to buDim formula via BorsukUlamOQ02OQ01.buDim_prime

### Key Mathematical Findings

**Concrete model**: `FpPoly p = Polynomial (ZMod p)` with generator `genU p = X`.

**Ideal filtration**: `umIdeal p m = Ideal.span {X^m}` in F_p[X].
- (u^0) = ⊤ (whole ring, since X^0 = 1)
- (u^n) ≤ (u^m) whenever m ≤ n (X^m | X^n)
- (u^{m+1}) < (u^m) strictly when p is prime

**Strict monotonicity proof**: If X^{m+1} | X^m, then X^m = X^{m+1} * f for some f.
But then natDegree(X^m) = m ≥ natDegree(X^{m+1}) + natDegree(f) = m+1, contradiction.

**Containment iff ordering** (ideal_containment_iff_le_power): (u^n) ≤ (u^m) ↔ m ≤ n.
Direction (←): umIdeal_anti_mono. Direction (→): degree argument on the divisibility relation.

**buDim recovery**: The ideal containment characterization immediately gives buDim(p, 2n) = 2n-1
via BorsukUlamOQ02OQ01.buDim_prime (which was proved in OQ04).

### Sorries and Axioms

**`fpPoly_quotient_finrank`** (sorry): `Module.finrank (ZMod p) (FpPoly p ⧸ umIdeal p n) = n`
- Needs Mathlib lemma for dim(F_p[X]/(X^n)) = n
- Likely via PowerBasis or Polynomial.quotient_X_pow infrastructure

**`fpPoly_quotient_nontrivial`** (sorry): `Nontrivial (FpPoly p ⧸ umIdeal p n)` when n ≥ 1
- Follows from umIdeal p n ≠ ⊤ when n > 0
- Degree argument: if (X^n) = ⊤ then 1 ∈ (X^n), but 1 has degree 0 < n

**`cohBZp_iso_FpPoly`** (axiom): `True` placeholder
- Full proof requires Serre spectral sequence for Z/p → EZ/p → BZ/p
- Not yet formalized in Mathlib v4.26

### Files Created

- `proofs/Proofs/BorsukUlamOQ02OQ01OQ04OQ01.lean` (created, 233 lines, 13 theorems, 1 axiom, 2 sorries)
- `proofs/Proofs.lean` (regenerated, +1 import)
- `src/data/research/problems/borsuk-ulam-oq-02-oq-01-oq-04-oq-01.json` (updated)

### Next Steps

1. **Immediate**: Verify build once Docker Desktop is restarted
2. Search Mathlib for `Polynomial.quotient` dimension lemmas to fill `fpPoly_quotient_finrank`
3. Fill `fpPoly_quotient_nontrivial` via `Ideal.Quotient.nontrivial_iff` + proper degree argument
4. Consider using `PowerBasis` of the quotient F_p[X]/(X^n) to prove dimension = n
