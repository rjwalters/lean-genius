# burnside-counting-oq-04-oq-01

**Status**: COMPLETED (verified, 0 axioms, 0 sorries)
**Answers**: parent burnside-counting-oq-04 open question #1

## Summary

Removes the `native_decide` (`Lean.ofReduceBool`) dependency from the headline count
|bracelets(4,2)| = 6 by computing the Burnside fixed-point total with ordinary kernel `decide`.

## Session 2026-06-23 (Session 1) — Completed

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Defined a concrete action `posAct`/`posMulAction` of `DihedralGroup 4` on positions `ZMod 4`
  (rotations `x ↦ x + i`, reflections `x ↦ -x - i`); both `MulAction` laws by kernel `decide`.
- Lifted to colourings `ZMod 4 → Fin 2` via Mathlib `arrowAction` (`colMulAction`), with a
  computable `DecidablePred` instance so each `fixedBy` set is a kernel-computable `Fintype`.
- `sum_fixedBy_eq`: total fixed colourings across the 8 group elements = 48, by kernel `decide`.
- `bracelet_count_4_2`: Burnside's lemma + |D_4| = 8 forces 6 orbits.
  `#print axioms` → only `propext, Classical.choice, Quot.sound` (no `Lean.ofReduceBool`).

### Key Findings
- **Atom-mismatch gotcha**: Burnside's lemma `sum_card_fixedBy_eq_card_orbits_mul_card_group`
  states its orbit side as `Quotient (orbitRel α β)` (a `local notation Ω`) with its own
  synthesised `Fintype` instance, while the goal uses the API name `orbitRel.Quotient α β`.
  These are *definitionally* equal but *syntactically* distinct, so `omega` saw them as two
  unrelated atoms and failed. Fix: route both through instance-independent `Nat.card`
  (`simp only [← Nat.card_eq_fintype_card]`) and bridge the two spellings with a `rfl` lemma.
- Kernel `decide` is entirely adequate here: carrier `k^n = 2^4 = 16` is tiny.

### Files Modified
- `proofs/Proofs/BurnsideCountingOQ04OQ01.lean` (131 lines, 2 thm / 2 def, verified)
- `src/data/proofs/burnside-counting-oq-04-oq-01/meta.json`

### Next Steps
- Generalise to a parametric kernel-verified |bracelets(n,k)| for small (n,k).
- Find the carrier-size threshold where kernel `decide` becomes infeasible and a structural
  per-symmetry closed form is needed instead.
