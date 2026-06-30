# Knowledge Base: platonic-solids-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-06-30 (Session 1) — Platonic↔Coxeter at the invariant level

**Mode**: FRESH
**Outcome**: progress (NEW Lean entry, VERIFIED 0-axiom)

### What I Did
- Created `proofs/Proofs/PlatonicSolidsOQ03.lean` (294L, 18 thm, 16 def, 0 sorry, 0 axiom).
- Formalized the correspondence "each Platonic solid's full symmetry group is a finite
  rank-3 reflection (Coxeter) group" at the level of the standard numerical invariants
  (NOT a full group isomorphism — that needs geometric symmetry groups absent from Mathlib).
- Added gallery entry `src/data/proofs/platonic-solids-oq-03` (meta + 9 annotations).

### Key Findings
- **Master bridge** `|W| = 4E`: tetra 4·6=24 (A₃), cube/octa 4·12=48 (B₃),
  dodeca/icosa 4·30=120 (H₃). Ties Coxeter orders to the parent's edge counts
  (flag-transitivity: 4 flags per edge).
- **Order = product of degrees** (Shephard–Todd/Chevalley): 2·3·4, 2·4·6, 2·6·10;
  equivalently ∏(exponent+1).
- **Reflections = sum of exponents = #mirror planes** (6, 9, 15); classical
  **N = n·h/2** verified as 2N = 3h (rank n=3, h = top degree = 4/6/10).
- **Exactly three symmetry classes**: duality (p↔q) preserves the group
  (`coxeter(dual s) = coxeter(s)`), so the duality orbits {tet},{cube,oct},{dod,ico}
  are the three groups A₃,B₃,H₃; `(allSolids.map coxeter).dedup = [A₃,B₃,H₃]`.
- **Index-2 rotation subgroups**, order 2E → rotation groups A₄(12), S₄(24), A₅(60).
- All discharged by kernel `decide`/`rfl` (deliberately no `native_decide`), so
  `#print axioms` on the capstone reports **no axiom dependence at all**.

### Files Modified
- proofs/Proofs/PlatonicSolidsOQ03.lean (new)
- src/data/proofs/platonic-solids-oq-03/{meta,annotations}.json (new)
- src/data/research/problems/platonic-solids-oq-03.json (knowledge)

### Next Steps
- Construct abstract A₃/B₃/H₃ in Lean; prove |W| = ∏degrees intrinsically.
- Define geometric Sym(P) of an embedded solid; prove Sym(P) ≅ W(Φ).
- Derive the rank-3 reflection classification from the Schläfli constraint alone.
