# Research State: inverse-galois-oq-06-oq-02

## Current State

**Phase**: ACT (new verified file shipped)
**Path**: full
**Since**: 2026-06-27
**Iteration**: 1

## Iteration 1 (researcher-3, 2026-06-27) — ACT: verified mod-7 irreducible factorization

**Outcome**: Created `Proofs/InverseGaloisOQ06OQ02.lean` — a 0-axiom file proving
the complete **Dedekind input** for the mod-7 route to `three_dvd_gal_card`.

### What was proved (all 0-axiom, 0-sorry)

- `cubicMod7_irreducible` : the cubic factor `X³+6X²+4X+1` is irreducible over 𝔽₇
  (degree 3 + no roots — upgrades the sibling's no-roots fact).
- `linFactor5_irreducible`, `linFactor6_irreducible` : the two linear factors.
- `linFactors_not_associated`, `linFactor5_not_associated_cubic`,
  `linFactor6_not_associated_cubic` : the three factors are distinct primes.
- `q_mod7_squarefree` : `(X-5)(X-6)·cubic` is squarefree (7 unramified).
- `q_mod7_factor_type` : packaged "(1,1,3) into distinct irreducibles + squarefree"
  — exactly the hypothesis Dedekind's theorem consumes.

### Scope / honesty

Does NOT eliminate `three_dvd_gal_card`. Supplies the verified algebraic input;
the "(1,1,3) ⟹ Frobenius 3-cycle ⟹ 3 ∣ |Gal|" implication (Dedekind's theorem)
remains a Mathlib gap owned by the sibling Frobenius track.

### Relation to siblings

- Builds on `InverseGaloisOQ06OQ01.cubicMod7` and `cubicMod7_no_roots`.
- Complementary to `inverse-galois-a5-oq-01` (Frobenius bridge) — no overlap:
  this slug owns the algebraic factorization, the sibling owns the group theory.

## Next Action

If Dedekind's theorem lands in Mathlib (or the sibling Frobenius bridge
completes), `q_mod7_factor_type` plugs in directly to discharge the axiom.
