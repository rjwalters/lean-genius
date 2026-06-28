# lagrange-theorem-oq-01-oq-03-oq-01: Hall's theorem — Schur–Zassenhaus lifting step

## Problem
OQ-01 of the parent Hall entry: can the full proof of Hall's theorem be
formalized in Lean 4 without using Schur–Zassenhaus as a black box, building the
minimal normal subgroup induction from scratch?

## Session 2026-06-28 (Session 1) — FRESH
**Outcome:** progress (0-axiom verified contribution)

### Key findings
- The parent entry `lagrange-theorem-oq-01-oq-03` axiomatizes `hall_solvable`
  citing "Schur–Zassenhaus not yet in Mathlib 4.26". **This is false.** Mathlib
  4.26 has it: `Subgroup.exists_right_complement'_of_coprime`
  (`Mathlib/GroupTheory/SchurZassenhaus.lean`). Sibling entries
  `lagrange-theorem-oq-03` and `sylow-theorem-oq-03` already use it.
- Therefore the correct answer to OQ-01 is: do NOT rebuild Schur–Zassenhaus; it
  is available. The genuine remaining obstacle to a 0-axiom Hall's theorem is the
  minimal-normal-subgroup machinery (existence + elementary-abelian structure in
  the solvable case), which Mathlib lacks.
- Mathlib has Hall's *marriage* theorem (Combinatorics) but NOT Hall's theorem
  for solvable groups.

### What I built (0 axioms; #print axioms = propext/Choice/Quot only)
- `hall_lift_of_coprime` + `hall_lift_of_coprime_subgroup`: the inductive lifting
  step of Hall's theorem. If N ⊴ G, gcd(|N|, d) = 1, and G/N has a subgroup of
  order d, then so does G (and it lives inside the preimage of the quotient
  subgroup). Proof: L = π⁻¹(Q), show |L| = |N|·d via card_mul_index /
  index_eq_card / index_comap_of_surjective, then Schur–Zassenhaus on
  N.subgroupOf L (index d, order |N|, coprime) gives a complement of order d,
  pushed back along L.subtype. Mirrors Mathlib SZ's internal `step1` recursion.
- `schur_zassenhaus_available`: documents Mathlib's SZ.
- Corrected the parent's false justification (Lean docstring + meta.json).

### Files
- proofs/Proofs/LagrangeTheoremOQ01OQ03OQ01.lean (new, 169 lines, 0 axioms)
- src/data/proofs/lagrange-theorem-oq-01-oq-03-oq-01/meta.json (new)
- proofs/Proofs/LagrangeTheoremOQ01OQ03.lean (docstring correction)
- src/data/proofs/lagrange-theorem-oq-01-oq-03/meta.json (assumptions correction)

### Next steps
- Formalize existence of a minimal normal subgroup of a nontrivial finite group.
- Prove a minimal normal subgroup of a finite solvable group is elementary
  abelian; close the p | d branch.
- Assemble full 0-axiom Hall's theorem: lifting step (here) + abelian base case
  (lagrange-theorem-oq-03) + minimal-normal-subgroup structure.
