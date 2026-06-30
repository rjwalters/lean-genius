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

## Session 2026-06-28 (Session 2, researcher-2) — PROGRESS
**Outcome:** progress (0-axiom verified contribution) — closes BOTH minimal-normal
Mathlib gaps that Session 1 only pinpointed.

### Key findings / what I built (all 0 axioms; #print axioms = propext/Choice/Quot)
- `exists_minimal_normal` (+ `exists_minimal_normal_atom`): every nontrivial
  finite group has a minimal nontrivial normal subgroup. Proof: `Finite.exists_min`
  over the finite, nonempty (⊤ qualifies) subtype `{N // N.Normal ∧ N ≠ ⊥}`,
  minimizing `Nat.card`. Equality from a private antisymmetry lemma
  `eq_of_le_of_card_le` (`SetLike.coe_injective` + `Set.eq_of_subset_of_ncard_le`,
  bridged by `Nat.card_coe_set_eq`).
- `minimal_normal_abelian_of_solvable`: a minimal normal subgroup of a solvable
  group is abelian. KEY lemma found: `IsSolvable.commutator_lt_of_ne_bot`
  (Mathlib/GroupTheory/Solvable.lean) gives `⁅N,N⁆ < N` for N ≠ ⊥. `⁅N,N⁆` is
  normal in G via the `Subgroup.commutator_normal` instance, so minimality forces
  `⁅N,N⁆ = ⊥`; then `Subgroup.commutator_le` + `commutatorElement_eq_one_iff_mul_comm`
  give pairwise commutativity.
- `exists_abelian_minimal_normal`: assembles the two into the descent target Hall's
  induction needs — a nontrivial finite solvable group has an abelian minimal
  normal subgroup.
- Updated header docstring, meta.json (theoremCount 4→8, lineCount 169→288,
  contributions, sections, OQs, conclusion).

### GOTCHA (process)
- The Session-1 file `LagrangeTheoremOQ01OQ03OQ01.lean` is on origin/main (#31159)
  but the assigned `feature/researcher-2` branch predates it → file absent there.
  Worked on a fresh branch off `origin/main` (`research/hall-minimal-normal`) and
  symlinked `proofs/.lake` → main's for `lake env lean` verification.

### Remaining next steps (narrowed)
- Elementary-abelian sharpening: an abelian minimal normal subgroup is a p-group
  (p-torsion characteristic ⇒ normal ⇒ all of N by minimality). Now MEDIUM, not
  hard — abelianness is done.
- Thread lifting step + `exists_abelian_minimal_normal` + abelian base case through
  the induction on |G| for a 0-axiom `hall_solvable`.
