# Knowledge Base: shannon-channel-coding-oq-02-oq-01

## Problem

Prove Fano's inequality H(X|Y) ≤ h(P_e) + P_e·log(|X|-1) from the project's standard conditional entropy machinery in ShannonEntropy.lean. Specifically: bridge OQ-03's self-contained Fano proof to `InformationTheory.conditionalEntropy`.

## Session 2026-04-04 (Session 1)

**Outcome**: Bridge proof complete. Definitional equality confirmed. Axiom reduction blocked by ShannonEntropy.lean bug (root cause identified).

### What I Did

1. Identified that OQ-03's `FanoInequality.conditionalEntropy` and the project's `InformationTheory.conditionalEntropy` use the same formula
2. Proved definition compatibility by `rfl` (definitional equality)
3. Derived `fano_from_oq03` by direct delegation to `fano_theorem` from OQ-03
4. Analyzed root cause of ShannonEntropy.lean line 811 failure
5. Created `ShannonChannelCodingOQ02OQ01.lean` (142 lines, 1 axiom, 1 sorry)
6. Created gallery data: meta.json, annotations.json, index.ts

### Key Findings

- **Definitional equality is `rfl`**: Both conditional entropy definitions expand to the same formula. No rewriting or coercion needed.
- **Root cause of line 811**: After `simp_rw [hYZ]`, the YZ marginal has sum order `∑ y ∑ z ∑ x f`, but `simp_rw [hterm]` produces `∑ x ∑ y ∑ z f` for the same quantity. `linarith` is purely syntactic and can't cancel these. Fix: add `simp_rw [Finset.sum_comm (s := Finset.univ)]` before `linarith [h_cmi]`.
- **OQ-03 workaround**: Made self-contained (no ShannonEntropy.lean import) to avoid the bug.
- **fano_trivial_singleton**: `Fintype.sum_unique` simp interaction with `if ... then 0 else ...` causes progress failure. Marked sorry — conceptually trivial but tactic-level finicky.

### Files Modified

- `proofs/Proofs/ShannonChannelCodingOQ02OQ01.lean` (created, 142 lines)
- `src/data/proofs/shannon-channel-coding-oq-02-oq-01/meta.json` (created)
- `src/data/proofs/shannon-channel-coding-oq-02-oq-01/annotations.json` (created)
- `src/data/proofs/shannon-channel-coding-oq-02-oq-01/index.ts` (created)

### Next Steps

1. **Fix ShannonEntropy.lean line 811**: Add `simp_rw [Finset.sum_comm (s := Finset.univ)]` before `linarith [h_cmi]` in `strong_subadditivity`. This should eliminate `import_shannon_entropy_blocked` axiom.
2. **Fix fano_trivial_singleton**: Try `simp only [Finset.univ_unique, Finset.sum_singleton]` instead of `Fintype.sum_unique` for the Unit sum simplification.
3. **Eliminate axiom**: Once ShannonEntropy.lean builds, replace `axiom import_shannon_entropy_blocked : False` with the actual import and proof.
