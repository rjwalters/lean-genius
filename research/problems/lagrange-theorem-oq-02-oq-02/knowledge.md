# Class Equation (lagrange-theorem-oq-02-oq-02)

## Problem

Formalize the class equation |G| = |Z(G)| + Σ_{non-central conj classes [x]} [G : C_G(x)].

## Session 2026-05-05 (Session 1) - Class Equation Formalization

**Mode**: FRESH
**Outcome**: progress

### What I Did
- Selected problem (all 36 available had score 0; chose this as natural follow-up to oq-02)
- Confirmed Mathlib has `Group.nat_card_center_add_sum_card_noncenter_eq_card` in `Mathlib.GroupTheory.ClassEquation`
- Wrote `proofs/Proofs/LagrangeTheoremOQ02OQ02.lean` (257 lines, 13 theorems, 1 sorry)
- Created gallery entry `src/data/proofs/lagrange-theorem-oq-02-oq-02/`

### Key Findings
- Class equation is directly in Mathlib — can be wrapped cleanly
- `ConjAct.toConjAct_smul` reduces conjugation to `g * x * g⁻¹`
- `group` tactic handles all group arithmetic (g*x*g⁻¹ = x ↔ g*x = x*g)
- `conj_stabilizer_eq_centralizer` proved fully using forward/backward calc
- `card_conjClass_eq_one_iff_mem_center` proved via orbit uniqueness argument
- 1 sorry: `card_conjClass_eq_centralizer_index` — needs orbit Nat.card → centralizer index connection

### Files Modified
- `proofs/Proofs/LagrangeTheoremOQ02OQ02.lean` (new)
- `src/data/proofs/lagrange-theorem-oq-02-oq-02/meta.json` (new)
- `src/data/proofs/lagrange-theorem-oq-02-oq-02/annotations.json` (new)
- `src/data/proofs/lagrange-theorem-oq-02-oq-02/index.ts` (new)
- `src/data/research/problems/lagrange-theorem-oq-02-oq-02.json` (updated)

### Next Steps
- Prove `card_conjClass_eq_centralizer_index`: use `Nat.card_orbit_mul_card_stabilizer_eq_card_group` + index arithmetic
- Run Docker build to verify compilation
- If all compiles: update status to `verified` (0 sorries target)

## Session 2026-05-05 (Session 2) - Fix sorry: card_conjClass_eq_centralizer_index

**Mode**: REVISIT
**Outcome**: progress (pending Docker verification)

### What I Did
- Identified the 1 remaining sorry: `card_conjClass_eq_centralizer_index`
- Researched Mathlib API: `ConjAct.stabilizer_eq_centralizer`, `MulAction.orbitEquivQuotientStabilizer`, `Subgroup.index`
- Wrote proof using orbit-stabilizer equivalence + Mathlib's ConjAct stabilizer lemma

### Key Findings
- `ConjAct.stabilizer_eq_centralizer x : stabilizer (ConjAct G) x = centralizer {ConjAct.toConjAct x}`
- `MulAction.orbitEquivQuotientStabilizer (ConjAct G) x : orbit ≃ ConjAct G ⧸ stabilizer`
- `Subgroup.index H = Nat.card (G ⧸ H)` by definition — so quotient card = index
- `ConjAct.toConjAct x = x` definitionally (ConjAct G is type synonym for G)
- Full proof: `rw [← conj_orbit_eq_carrier, Nat.card_congr (orbitEquivQuotientStabilizer ...)]` then rewrite stabilizer to centralizer via `ConjAct.stabilizer_eq_centralizer`, close by `rfl`

### Files Modified
- `proofs/Proofs/LagrangeTheoremOQ02OQ02.lean` (sorry resolved)

### Next Steps
- Confirm Docker build succeeds with 0 sorries
- Update meta.json: sorries → 0, status → "verified"
- Create PR
