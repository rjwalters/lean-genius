# Problem: Erdős #476 OQ5 — Complete Vosper's Theorem Inductive Step

**Slug**: erdos-476-oq-05-wip-01
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Vosper's Theorem (1956): Let p be prime and A, B ⊆ ℤ/pℤ with |A|, |B| ≥ 2 and
|A + B| < p. If |A + B| = |A| + |B| - 1, then A and B are arithmetic progressions
with the same common difference d.

The Lean formalization (`Erdos476OQ05Problem.lean`) has the full infrastructure proved
but contains 2 sorries in the inductive step:

```lean
-- SORRY 1/2: Key step: position analysis forces |A \ A.image(·+d)| = 1
sorry -- Key step: position analysis forces |A \ A.image(·+d)| = 1

-- SORRY 2/2: Case 1 existence: counting argument or iterative removal
sorry -- [SORRY 1/2] Case 1 existence: counting argument or iterative removal
```

### Plain Language

The proof infrastructure is complete:
- `IsArithmeticProgression` definition and key lemmas
- `vosper_base`: the base case |A| = 2 is fully proved
- `ap_of_near_periodic`: backward-shift induction lemma (proved)
- Translation invariance and singleton/pair AP lemmas

What remains: fill 2 sorries in the main inductive step `vosper_induction`. The first
sorry requires showing that if A is near-periodic (A \ A.image(·+d) has one element),
then a counting argument forces |A \ A.image(·+d)| = 1. The second sorry is a case
analysis existence argument.

### Why This Matters

- **Completion**: This is the most concrete gap — existing infrastructure means any
  progress directly upgrades the gallery proof from WIP to verified.
- **Cauchy-Davenport**: Vosper's theorem is the equality characterization of Cauchy-Davenport,
  a foundational result in additive combinatorics.
- **Erdős pipeline**: Completing this removes a sorry from the Erdős #476 family.

## Known Results

### What's Already Proven

In `Erdos476OQ05Problem.lean` (current):
- `IsArithmeticProgression p d A`: A is an AP with difference d in ℤ/pℤ
- `ap_iff_card_inter`: intersection characterization of APs
- `ap_of_near_periodic`: if |A \ A.image(·+d)| = 1, then A is an AP
- `vosper_base`: Vosper for |A| = 2 (fully proved)
- Line count: 407 lines, 2 sorries

### What's Still Open

1. **SORRY 1** (line 166): Inductive position analysis — if we're in the inductive case,
   a counting/shift argument shows the shift removes exactly one element
2. **SORRY 2** (line 407): Case 1 existence — finding the element that makes the shift
   argument work

### Our Goal

Fill both sorries to obtain a 0-sorry, verified Lean 4 proof of Vosper's theorem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-476-oq-05 | Parent WIP proof (has the sorries) | Cauchy-Davenport, ℤ/pℤ arithmetic |
| erdos-476 | Cauchy-Davenport theorem itself | Additive combinatorics, Finset |
| erdos-476-oq-05-incomplete-01 | Related incomplete formalization | Similar structure |

## Initial Thoughts

### Potential Approaches

1. **Direct case analysis**: For SORRY 2, enumerate cases based on whether the shift d
   moves A into itself or creates a new extremal element. The counting argument is:
   |A| + |A.image(·+d)| ≥ |A ∪ A.image(·+d)| = |A+{d}| = |A|, so |A ∩ A.image(·+d)|
   is determined.
   - Why it might work: Follows standard Vosper proof structure
   - Risk: Lean 4 Finset arithmetic may require non-trivial lemmas

2. **Adapt from Mathlib**: Check if Mathlib has Vosper or Cauchy-Davenport equality case
   that could be imported/adapted.
   - Why it might work: Saves proving from scratch
   - Risk: Mathlib's version may use different types/definitions

3. **Aristotle submission**: The sorries are theorem sorries (not defs), making them
   Aristotle-eligible. Submit the Aristotle companion file `Erdos476OQ05Aristotle.lean`
   for automated proof search.
   - Why it might work: Infrastructure is complete, Aristotle handles theorem sorries
   - Risk: Aristotle may time out on these combinatorial arguments

### Key Difficulties

- The inductive position analysis requires careful Finset arithmetic
- `Finset.card` API in Lean 4 can be verbose for inclusion-exclusion arguments
- The equality case of Cauchy-Davenport is delicate to formalize

### What Would a Proof Need?

- Finset inclusion-exclusion: `|A \ B| = |A| - |A ∩ B|`
- Shift invariance: `|A.image(·+d)| = |A|` for bijective shift
- Case analysis on whether extremal elements exist

## Tractability Assessment

**Difficulty**: Medium (Challenging, but WIP infrastructure exists)

**Justification**:
- All supporting lemmas are proved; only the main cases remain
- The proof strategy is known from the literature (Vosper 1956)
- The existing 407-line file provides the complete skeleton

**Estimated Effort**:
- Exploration: 1 day (read the existing proof, identify exact gaps)
- If tractable: 3-7 days (fill the two sorry cases)
- Alternatively: Try Aristotle submission first (may auto-close)

## References

### Papers
- Vosper, A.G., "The critical pairs of subsets of a group of prime order" (1956)
- Lev, V.F., "Restricted set addition in groups" (2000)

### Lean Files
- `proofs/Proofs/Erdos476OQ05Problem.lean` — the WIP proof with 2 sorries
- `proofs/Proofs/Erdos476OQ05Aristotle.lean` — Aristotle companion

### Mathlib
- `Mathlib.Combinatorics.Additive.CauchyDavenport` — Cauchy-Davenport theorem
- `Mathlib.Data.ZMod.Basic` — ℤ/pℤ arithmetic
- `Mathlib.Data.Finset.Card` — Finset cardinality lemmas

## Metadata

```yaml
tags:
  - additive-combinatorics
  - erdos
  - number-theory
  - arithmetic-progressions
  - cauchy-davenport
  - vosper-theorem
  - zmod
  - completion
  - wip
related_proofs:
  - erdos-476-oq-05
  - erdos-476
difficulty: challenging
source: gallery-gap
created: 2026-04-22
```

**Significance**: 7/10
**Tractability**: 6/10
