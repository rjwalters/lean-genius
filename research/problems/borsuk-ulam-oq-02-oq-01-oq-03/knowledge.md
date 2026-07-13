# Knowledge: borsuk-ulam-oq-02-oq-01-oq-03

## Summary

Gallery proof EXISTS at `proofs/Proofs/BorsukUlamOQ02OQ01OQ03.lean` (212 lines,
status: axiomatized, 8 axioms, 0 sorries). Research task: reduce axioms or extend
to upper bounds using Mathlib group theory.

## Key Facts

- **Lean file**: `proofs/Proofs/BorsukUlamOQ02OQ01OQ03.lean` — 212 lines, 14 theorems
- **Gallery proof**: `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-03/` — axiomatized, 8 axioms
- **Parent file**: `proofs/Proofs/BorsukUlamOQ02OQ01.lean` — `buDim`, `buDim_two`, `buDim_prime`, `buDim_mono`
- **Related**: `proofs/Proofs/BorsukUlamOQ02OQ01OQ04.lean` — Fadell-Husseini index (parallel direction)

## The 8 Axioms (as of gallery proof)

1. `dihedralBUDim (n d : ℕ) : ℕ` — existence of dihedral BU dimension
2. `dihedral_has_Z2 (n d hn) : buDim 2 d ≤ dihedralBUDim n d` — D_n contains Z/2
3. `dihedral_has_rotation_prime (n d p hp hdvd) : buDim p d ≤ dihedralBUDim n d` — D_n contains Z/p for p|n
4. `dihedralBUDim_one d : dihedralBUDim 1 d = buDim 2 d` — D_1 ≅ Z/2
5. `dihedralBUDim_two d : dihedralBUDim 2 d = buDim 2 d` — D_2 ≅ V_4
6. `symBUDim (n d : ℕ) : ℕ` — existence of symmetric BU dimension
7. `sym_has_cyclic_prime (p n d hp hpn) : buDim p d ≤ symBUDim n d` — S_n contains Z/p for p ≤ n
8. `sym_has_smaller_sym (n d) : symBUDim n d ≤ symBUDim (n+1) d` — S_n ≤ S_{n+1}

## Tractability Assessment

**Provable with Mathlib** (group structure, no topology needed):
- Axiom 2 (`dihedral_has_Z2`): Mathlib has `DihedralGroup n`. Reflections generate Z/2.
  `DihedralGroup.orderOf_sr` and `ZMod.orderOf_units` may help.
- Axiom 3 (`dihedral_has_rotation_prime`): Rotation subgroup is Z/n; Z/p ≤ Z/n for p|n.
  May use `DihedralGroup.r_pow_eq_one_iff` and `ZMod` embedding.
- Axiom 7 (`sym_has_cyclic_prime`): p-cycle `c = (1 2 ... p)` in `Equiv.Perm (Fin n)` has
  order p. `Equiv.Perm.orderOf_isCycle` and `Equiv.isCycle_swap` are related.
- Axiom 8 (`sym_has_smaller_sym`): S_n → S_{n+1} via extending permutations to fix n+1.
  `Equiv.Perm.extendDomain` or `Subgroup.map` embedding.

**Require equivariant topology (not in Mathlib)**:
- Axioms 1, 6 (existence of BU dimension): need Fadell-Husseini index or RO(G)-graded cohomology
- Axioms 4, 5 (D_1, D_2 exact values): need identification of small dihedral groups

## Key Structural Insight

Subgroup monotonicity (`buDim_mono` from parent): H ≤ G → buDim(H,d) ≤ buDim(G,d).
All proved theorems use this via axioms 2,3,7,8. If the structural axioms can be
replaced by Mathlib proofs, axiom count drops from 8 to 2 (just the BU dimension
existence axioms 1 and 6, which are genuinely topological).

## Open Questions (from gallery proof)

1. Are the dihedral lower bounds tight? Is dihedralBUDim n d = max(buDim 2 d, max_{p|n} buDim p d)?
   Requires RO(D_n)-graded equivariant cohomology for upper bounds.
2. Is symBUDim n d = buDim_{largest prime ≤ n} d = 2⌊d/2⌋-1?
   Bertrand's postulate gives a prime p > n/2, so lower bound is within factor 2 of d.
3. Can Fadell-Husseini index (BorsukUlamOQ02OQ01OQ04) prove matching upper bounds?
4. Wreath products G ≀ H (hyperoctahedral groups B_n = Z/2 ≀ S_n)?

## Research Strategy

**Phase 1 (tractable)**: Prove axioms 2, 3, 7, 8 using Mathlib DihedralGroup/Equiv.Perm.
This reduces axiom count from 8 to at most 4 (the BU dimension existence + exact value axioms).
This is a concrete, achievable improvement with clear Lean 4 paths.

**Phase 2 (hard)**: Upper bounds via equivariant cohomology — likely needs significant
new Mathlib infrastructure.
