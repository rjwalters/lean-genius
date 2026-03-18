# Knowledge Base: dissection-of-cubes-oq-03

Connections to packing problems for cube dissections.

---

## Session 2026-03-17 (Session 1) - Initial Formalization

**Mode**: FRESH
**Outcome**: completed

### What Was Done
Created `DissectionOfCubesOQ03.lean` formalizing the connection between cube dissection
impossibility and packing theory.

### Key Insight: The Packing/Covering Dichotomy
The main structural insight is that the COVERING requirement is what forces size repetition:
- **Packing** (containment + disjointness): all-different-sizes IS possible (constructive witness)
- **Dissection** (packing + covering): all-different-sizes is IMPOSSIBLE (Wiedijk #82)

### Proved Theorems
1. `dissectionToPacking`: CubeDissection -> CubePacking (forgetful functor)
2. `packing_all_different_exists`: constructive witness (one cube of side 1/2)
3. `packing_covering_dichotomy`: the key structural result combining both directions
4. `cube_side_le_one`: size bound from containment
5. `count_volume_bound`: n * eps^3 <= 1 (packing count bound)
6. `nonempty_packing_count_bound`: existential form with minimum side
7. `volume_dissection_bound`: dissection volume <= 1

### Axioms
1. `volume_packing_bound`: disjoint cubes in unit cube have total volume <= 1
   (requires measure theory for formal proof)

Plus 2 inherited axioms from DissectionOfCubes.lean (smaller_cube_above, long_chains).

### Files Created
- `proofs/Proofs/DissectionOfCubesOQ03.lean` (353 lines)
- `research/problems/dissection-of-cubes-oq-03/knowledge.md`
- `src/data/research/problems/dissection-of-cubes-oq-03.json`

### Assessment
Problem completed. The packing/covering dichotomy is the central result. Further work
could prove the volume bound from measure theory, but that's a separate BUILD task
requiring substantial Mathlib measure theory infrastructure.
