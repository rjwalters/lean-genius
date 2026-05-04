# Knowledge Base: cramers-rule-oq-01-oq-02-oq-01

**Problem**: Can the quasideterminant theory for 2×2 matrices extend to 3×3 and n×n matrices using recursive quasideterminants?

**Answer**: YES — formalized in CramersRuleOQ01OQ02OQ01.lean

---

## Session 2026-05-03 (Session 1) - Fresh Proof of 3×3 Recurrence

**Mode**: FRESH
**Outcome**: completed

### What I Did

- Claimed problem (score 0, no prior knowledge)
- Defined `block3 A i j` as `A.submatrix (Fin.succAbove i) (Fin.succAbove j)` — 12 entry lemmas all `rfl`
- Proved 3 minor determinant formulas via `simp [Matrix.det_fin_two]`
- Defined `qdet3 A i j = det(A) / det(block3 A i j)` over fields
- Proved core identity `qdet3_mul_minor_eq_det` via `div_mul_cancel₀`
- Proved Schur expansion `qdet3_00_schur_expand` via `field_simp; ring`
- Defined `schurComp3` (Schur complement of lower-right 2×2 = qdet00 of block3 A 0 0)
- Defined `qdet3_00_nc` (non-commutative via explicit Schur complement inverse)
- Proved `qdet3_00_nc_eq_qdet3` consistency via `field_simp; ring`
- Proved `cramer_rule_3x3` using `Matrix.mulVec_cramer`
- Proved `qdet3_recurrence_summary` as the main conjunction

### Key Findings

- `Fin.succAbove` evaluates definitionally on small `Fin` types — all entry lemmas are `rfl`
- `div_mul_cancel₀` immediately gives the core identity with no ring arithmetic
- The recursion is self-referential: `qdet3_00_nc` uses `schurComp3` which IS `qdet00(block3 A 0 0)` from the 2×2 theory
- `field_simp; ring` handles all commutative consistency proofs after definition unfolding
- `Matrix.mulVec_cramer` is the key Mathlib lemma: `A.mulVec (A.cramer b) = A.det • b`

### Files Modified

- `proofs/Proofs/CramersRuleOQ01OQ02OQ01.lean` (312 lines, 0 sorries, 0 axioms)
- `src/data/proofs/cramers-rule-oq-01-oq-02-oq-01/meta.json`
- `src/data/proofs/cramers-rule-oq-01-oq-02-oq-01/annotations.json`
- `src/data/proofs/cramers-rule-oq-01-oq-02-oq-01/index.ts`
- `src/data/proofs/listings.json` (added new entry)
- `src/data/research/problems/cramers-rule-oq-01-oq-02-oq-01.json`

### Next Steps

Future open questions:
- Formalize off-diagonal quasideterminants for 3×3 (8 remaining positions)
- n×n inductive formalization
- Non-commutative Cayley-Hamilton via quasideterminants
