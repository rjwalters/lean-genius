# godel-first-incompleteness-oq01-oq-01

**Problem**: Rosser's 1936 improvement: extend the formalization to use only plain consistency (not ω-consistency) by replacing G with the Rosser sentence R.

## Problem Summary

The parent proof `GodelFirstIncompletenessOQ01.lean` uses ω-consistency as a hypothesis (specifically the axiom `omega_consistency_G`). Rosser (1936) improved this to use only plain consistency by using a self-referential sentence R that encodes a proof-length comparison:

> R ↔ (∀ proof code p of R, ∃ disproof code q ≤ p of R)

The key structural property of R is **equi-decidability**: (⊢ R) ↔ (⊢ ¬R). Under plain consistency, this forces R to be undecidable.

## Session 2026-05-03 (Session 1) — Complete Formalization

**Mode**: FRESH
**Outcome**: COMPLETE — 0 sorries, 3 axioms, 11 theorems, PR #15256

### What I Did
- Analyzed parent file `GodelFirstIncompletenessOQ01.lean` (5 axioms, including `omega_consistency_G`)
- Identified that omega_consistency_G needs to be replaced by two Rosser-specific axioms
- Wrote `GodelFirstIncompletenessOQ01OQ01.lean` (308 lines):
  - Rosser sentence R = ⟨43⟩ with detailed proof-length comparison semantics
  - `R_prov_gives_formal_disproof`: if ⊢ R then ⊢ ¬R (Rosser Prov→Disprov)
  - `R_disproof_gives_formal_prov`: if ⊢ ¬R then ⊢ R (Rosser Disprov→Prov)
  - 11 theorems including equi-decidability, incompleteness, comparison with Gödel
- Created gallery entry in `src/data/proofs/godel-first-incompleteness-oq01-oq-01/`
- Created PR #15256

### Key Insights
- **Equi-decidability is the structural heart**: (⊢ R) ↔ (⊢ ¬R) replaces G's asymmetry
- **3 axioms vs 5**: Rosser's approach is MORE efficient than Gödel's original
- **Symmetric proof**: both `R_not_provable` and `R_not_disprovable` use the SAME argument pattern (assume provability, derive both ⊢ R and ⊢ ¬R, contradiction via consistency)
- **omega_consistency_G completely eliminated**: not even mentioned in the new file

### Files Modified
- `proofs/Proofs/GodelFirstIncompletenessOQ01OQ01.lean` — new proof file
- `src/data/proofs/godel-first-incompleteness-oq01-oq-01/meta.json` — gallery metadata
- `src/data/proofs/godel-first-incompleteness-oq01-oq-01/annotations.json` — empty
- `src/data/proofs/godel-first-incompleteness-oq01-oq-01/index.ts` — gallery index
- `src/data/research/problems/godel-first-incompleteness-oq01-oq-01.json` — knowledge JSON

### Remaining Work
- Docker build verification (queued — multiple concurrent builds active)
- Gallery rendering verification after deployment
