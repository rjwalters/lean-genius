# lagrange-theorem-oq-02-oq-01: Burnside's Counting Lemma via Explicit Double-Counting

**Problem**: Formalize Burnside's counting lemma directly from orbit-stabilizer,
making the double-counting argument explicit (not just importing from Mathlib).

**Status**: COMPLETED (0 sorries, 0 axioms, PR submitted)

---

## Session 2026-05-04 (Session 1) - Proved

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Selected problem from available pool (highest knowledge among fresh problems)
2. Analyzed existing infrastructure: `LagrangeTheoremOQ02.lean` (orbit-stabilizer),
   `BurnsideCounting.lean` (Burnside from Mathlib), `LagrangeTheoremOQ05.lean` (chain proof)
3. Identified key gap: no proof with explicit double-counting bijection
4. Wrote `LagrangeTheoremOQ02OQ01.lean` (192 lines, 8 theorems + 2 defs, 0 sorries)
5. Created gallery entry with meta.json, annotations.json, index.ts

### Key Findings

- The double-counting bijection `(g,x,g•x=x) ↦ (x,g,g•x=x)` has `rfl` proofs for both
  left_inv and right_inv — it's a definitional isomorphism, not just a bijection
- `sigma_fixedBy_equiv_sigma_stabilizer` makes the counting argument machine-transparent
- Stabilizer conjugation `h ↦ g⁻¹hg` proves Stab(g•x) ≃ Stab(x) explicitly
- Each orbit contributes exactly |G| to Σ_x|Stab(x)| via orbit-stabilizer
- `burnside_from_orbit_stabilizer` = double-counting + orbit partition (Mathlib for latter)

### Files Modified

- `proofs/Proofs/LagrangeTheoremOQ02OQ01.lean` (new, 192 lines)
- `src/data/proofs/lagrange-theorem-oq-02-oq-01/meta.json` (new)
- `src/data/proofs/lagrange-theorem-oq-02-oq-01/annotations.json` (new)
- `src/data/proofs/lagrange-theorem-oq-02-oq-01/index.ts` (new)

### Next Steps

- PR submitted; awaiting deploy
- Follow-up: prove orbit partition sum without Mathlib's Burnside (oq-01 in meta)
- Follow-up: generalize to monoid actions (oq-02 in meta)
