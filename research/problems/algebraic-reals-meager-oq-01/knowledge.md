# Package the Full Baire Category Theorem for Perfect Polish Spaces

**Problem ID**: algebraic-reals-meager-oq-01
**Status**: completed
**Phase**: SOLVED

## Summary

This open question asked to generalize the gallery's abstract uncountability lemma

    not_countable_of_perfect_t1_baire :
      X nonempty, T1, perfect, BaireSpace ⟹ ¬ Countable X

(`proofs/Proofs/AlgebraicRealsMeager.lean`) from the bespoke `ℝ` instance to the standard
descriptive-set-theory statement: **every nonempty perfect Polish space is uncountable**, with the
supporting "complete metric space is a Baire space" exposed as a reusable named result.

**Resolved (2026-06-19).** The packaging is a one-liner per the abstract lemma plus Mathlib's
instance chain — no new mathematics, but it lifts the result to the standard level of generality.
Build-verified GREEN, axiom-free (`[propext, Classical.choice, Quot.sound]`).

## Session 2026-06-19 — SOLVED

**Mode**: FRESH
**Outcome**: completed (6 new theorems, 0 sorries, 0 axioms)

### Key insight: the generality lift is free by instance resolution

Mathlib already supplies every instance along the chain that turns "perfect Polish space" into the
hypotheses of the existing abstract lemma:

    PolishSpace X                                  -- class, extends IsCompletelyMetrizableSpace
      → IsCompletelyMetrizableSpace X
          → MetrizableSpace X                      -- IsCompletelyMetrizableSpace.MetrizableSpace
              → T2Space X → T1Space X              -- t2Space_of_metrizableSpace
          → IsCompletelyPseudoMetrizableSpace X
              → BaireSpace X                       -- BaireSpace.of_completelyPseudoMetrizable

So a `[TopologicalSpace X] [PolishSpace X] [PerfectSpace X] [Nonempty X]` context discharges the
`T1Space` and `BaireSpace` hypotheses of `not_countable_of_perfect_t1_baire` automatically. The
headline theorem is therefore just the abstract lemma re-stated — `not_countable_of_perfect_t1_baire`
applies verbatim, and `not_countable_univ_iff.mp` repackages it as the `Uncountable` typeclass.

Relevant Mathlib references (paths under `proofs/.lake/packages/mathlib/Mathlib`):
- `Topology/MetricSpace/Polish.lean:62` — `class PolishSpace extends SecondCountableTopology,
  IsCompletelyMetrizableSpace`.
- `Topology/Metrizable/CompletelyMetrizable.lean` — `IsCompletelyMetrizableSpace.MetrizableSpace`
  (prio 90) and `.toIsCompletelyPseudoMetrizableSpace`.
- `Topology/Metrizable/Basic.lean:128` — `t2Space_of_metrizableSpace`.
- `Topology/Baire/CompleteMetrizable.lean:26` — `BaireSpace.of_completelyPseudoMetrizable` (prio 100).
- `Data/Set/Countable.lean:136,142` — `countable_univ_iff`, `not_countable_univ_iff`.

### What I added (`proofs/Proofs/AlgebraicRealsMeager.lean`)

- `baireSpace_of_completeMetricSpace` — complete metric space is a Baire space (the supporting
  "completeness half" of the BCT requested by the OQ), named wrapper over the Mathlib instance.
- `t1Space_of_polishSpace`, `baireSpace_of_polishSpace` — name the two implicit instance steps that
  feed the abstract lemma.
- `not_countable_univ_of_perfect_polishSpace` — `¬ (Set.univ).Countable` for a nonempty perfect
  Polish space.
- `uncountable_of_perfect_polishSpace` — the same in the `Uncountable X` typeclass form (the
  standard statement of the Baire Category uncountability theorem).
- `uncountable_real` — `ℝ` recovered as a corollary (`ℝ` is a perfect Polish space), a second route
  to Cantor's theorem subsuming the bespoke `not_countable_real`.

Added `import Mathlib.Topology.MetricSpace.Polish`. File 165 → 226 lines, 10 → 16 theorems.

### Verification

`./proofs/scripts/docker-build.sh Proofs.AlgebraicRealsMeager` — Build completed successfully
(3065 jobs). All theorems `#print axioms` ⟹ `[propext, Classical.choice, Quot.sound]` only (no
`sorryAx`, no `Lean.ofReduceBool`): verified / axiom-free. One pre-existing `simpa`→`simp` linter
warning at line 74 (in `isMeagre_of_isNowhereDense`, not introduced here).

### Files Modified
- proofs/Proofs/AlgebraicRealsMeager.lean (+61 lines, 6 new theorems)
- src/data/proofs/algebraic-reals-meager/meta.json (leanFile stats refreshed)
- research/problems/algebraic-reals-meager-oq-01/knowledge.md (this file)

### Next Steps
- None required for the OQ. Possible follow-ups: a perfect *compact* metric / `0`-dimensional
  perfect Polish (Cantor space) instance, or wiring `uncountable_of_perfect_polishSpace` into other
  gallery entries needing "perfect Polish ⟹ uncountable".

## References
- Kechris, A. S. (1995). *Classical Descriptive Set Theory*, §3 (Polish spaces, BCT).
- Baire, R. (1899). Sur les fonctions de variables réelles.
