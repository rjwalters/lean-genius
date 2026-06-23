# angle-trisection-oq-02-oq-01-oq-01-oq-01

**Problem**: Does the theorem extend beyond CharZero? Separability is the key hypothesis — inseparable irreducibles in characteristic p have Gal group of smaller order than expected.

## Problem Summary

The parent theorem `natDegree_dvd_card_gal` (AngleTrisectionOQ02OQ01.lean) uses `[CharZero F]`. This problem asks whether the theorem extends to fields of other characteristics. The answer is: yes for separable irreducibles over any field; no for inseparable ones.

**Answer**: The CharZero hypothesis serves only to derive `p.Separable` from `Irreducible p` via `Irreducible.separable`. The tower-law proof itself is characteristic-free. Replacing `[CharZero F]` with `(p_sep : p.Separable)` gives the maximally general theorem.

---

## Session 2026-05-04 (Session 1) — Complete Proof

**Mode**: FRESH
**Outcome**: progress — 5 theorems, 0 sorries, 1 axiom (counterexample); Docker build pending

### What I Did
- Analyzed parent proof `natDegree_dvd_card_gal`: CharZero used only in `p_irr.separable` (line 33)
- Wrote `natDegree_dvd_card_gal_of_sep`: same tower-law proof, explicit `p_sep : p.Separable`
- CharZero corollary: `natDegree_dvd_card_gal_charZero` (one-liner via `Irreducible.separable`)
- 2-group Galois criterion: `galois_2group_implies_degree_pow2_sep` and `_is_pow2_sep` — work in any char
- Inseparable counterexample: documented X^p - t over F_p(t), axiomatized as `insep_gal_trivial`
- Proved consequence: `natDeg_notDvd_gal_of_insep` shows divisibility fails for insep irreds of degree > 1
- Created gallery entry with meta.json, annotations.json, index.ts
- Committed to branch `research/angle-trisection-beyond-charzero`

### Key Findings
- `Gal.card_of_separable p_sep` works with explicit Separable hypothesis — no CharZero needed
- The proof structure is identical to the parent; only one argument changes
- PerfectField corollary would need `PerfectField.separable_of_irreducible` or similar Mathlib API
- Inseparable irreducibles over function fields (char p) provide clean counterexamples

### Files Modified
- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ01OQ01.lean` (new, ~155 lines)
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01/` (new gallery entry)
- `src/data/research/problems/angle-trisection-oq-02-oq-01-oq-01-oq-01.json` (updated knowledge)

### Next Steps
- Await Docker build verification
- Push branch, create PR if build passes
- Optional: prove `insep_gal_trivial` using RatFunc/FractionRing over ZMod p

---

## Session 2026-05-04 (Session 2) — Recovery + Import Fix + PR Push

**Mode**: REVISIT (branch not pushed, work lost from previous session)
**Outcome**: progress — branch recovered from local git, import added, PRpushed

### What I Did
- Discovered branch `research/angle-trisection-beyond-charzero` was committed locally but never pushed to remote (previous session ended before push)
- Branch was checked out in `.loom/worktrees/researcher-7` worktree (PID was dead/stale)
- Created new worktree `.loom/worktrees/angle-trisection-beyond-charzero` from the branch
- Found missing `import Proofs.AngleTrisectionOQ02OQ01OQ01OQ01` in `Proofs.lean`
  — file existed on branch but was not registered for Lake compilation
- Added the import (alphabetically between OQ01 and OQ01OQ02)
- Fixed `lineCount: 155 → 165` in meta.json (both `meta` and `leanFile` sections)
- Pushed branch with 3 commits: original research + import fix + lineCount fix
- Docker build running: `Proofs.AngleTrisectionOQ02OQ01OQ01OQ01` (PID 48975, waiting for result)

### Key Findings
- Branch was never pushed because researcher session ended at commit stage
- `Proofs.lean` must always be updated with the new import for Lake to compile the file
- `listings.json` is untracked/generated — deployer handles it, no need to add in PR
- Docker build is waiting on busy Docker daemon (other concurrent builds)

### Files Modified
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/angle-trisection-oq-02-oq-01-oq-01-oq-01/meta.json` (lineCount fix)

### Next Steps
- Verify Docker build success
- Create PR once build confirms compilation
- Optional: prove `insep_gal_trivial` using RatFunc/FractionRing over ZMod p

