# fodor-pressing-down-oq-04 — Solovay Splitting

## Question

> **Solovay's Splitting Theorem (1971).** Let κ be a regular uncountable cardinal and let S ⊆ κ be a stationary set. Then S can be partitioned into κ pairwise-disjoint stationary subsets.

The OQ asks for a Lean 4 formalization of this theorem in the framework of `Proofs/FodorPressingDown.lean`. The current file (385 lines, 0 sorries, 0 axioms) proves Fodor's pressing-down lemma itself; Solovay's theorem is the canonical first application that *strictly requires* Fodor and provides the foundational fact that "stationarity is not preserved under arbitrary partitions — but the partition into κ pieces is always possible".

## Why it matters

1. **Stationarity is genuinely large.** Solovay splitting is the canonical demonstration that a stationary subset of a regular uncountable cardinal carries enough largeness to be split into the maximum possible number of stationary pieces. Without it, one could only say "stationary sets are nonempty"; with it, the assertion becomes "stationary sets are κ-fat".

2. **First non-trivial corollary of Fodor.** Modern set-theoretic textbooks (Jech, Kunen) present Solovay splitting as the *paradigm* example of pressing-down applications: choose an auxiliary function on S, apply Fodor to a regressive variant, extract κ-many distinct constant values, partition.

3. **Foundation for ω₁-combinatorics.** Many later results (Σ-products, club guessing, ◇ at successor cardinals) build on Solovay splitting. Formalizing it unlocks a whole layer of forcing/large-cardinal infrastructure.

4. **Mathlib has no current proof.** A search of `Mathlib.SetTheory.Ordinal.*` shows definitions for `Cardinal.IsRegular` and `Ordinal.cof` but no stationary-set theory; the OQ-fileʼs `IsClubBelow`, `IsStationaryBelow`, `diagInter` infrastructure is, to the author's knowledge, the only Lean-4 stationarity setup in the gallery. Solovay splitting would be the second major theorem in that infrastructure.

## Scope of S1 OBSERVE

Documentation only. Specifically:

1. State the theorem precisely in the file's `IsStationaryBelow` framework.
2. Survey the standard proof structure (cof-based reduction + iterated Fodor).
3. Identify which existing lemmas in `FodorPressingDown.lean` are reusable directly.
4. Locate the Mathlib API gaps that would need to be filled (cofinality on ordinals, choice principles for κ-sized index sets).
5. Propose a graded S2/S3 plan with a tractable first deliverable.

No Lean code changes. No build. The S2 plan provides a concrete next-action.

## Anchoring file references

- `Proofs/FodorPressingDown.lean:48–60` — `IsUnboundedBelow`, `IsClubBelow`, `IsStationaryBelow` (the substrate for Solovay).
- `Proofs/FodorPressingDown.lean:87–94` — `diagInter`, `mem_diagInter`.
- `Proofs/FodorPressingDown.lean:240–246` — `diagInter_isClubBelow` (closure under intersection of κ clubs).
- `Proofs/FodorPressingDown.lean:259–313` — `fodor` (the load-bearing pressing-down result that Solovay invokes).
- `Proofs/FodorPressingDown.lean:343` — `IsStationaryBelow.of_subset` (passing to stationary subsets).
- `Proofs/FodorPressingDown.lean:334` — `IsStationaryBelow.nonempty` (the trivial-case sanity check).
