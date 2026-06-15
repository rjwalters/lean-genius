# erdos-57-oq-04: Bipartite characterization (odd cycles)

Erdős #57 (Liu–Montgomery 2020) main result is kept as the axiom `erdos_57`
(divergence of reciprocal odd-cycle lengths under infinite chromatic number).
This sub-problem concerns the elementary *bipartite characterization* lemmas in
`proofs/Proofs/Erdos57Problem.lean`:

- `bipartite_iff_no_odd_cycles : G.IsBipartite ↔ oddCycleLengths G = ∅`
- `colorable_two_no_odd_cycles : IsColorable G 2 → oddCycleLengths G = ∅`

## Session 2026-06-15 (Session 1) — FRESH, ACT

**Outcome**: progress (2 sorries → 1)

### What I Did
- Discovered Mathlib provides `SimpleGraph.Coloring.even_length_iff_congr`
  (`Mathlib/Combinatorics/SimpleGraph/ConcreteColorings.lean`): for a `Bool`
  coloring `c`, `Even p.length ↔ (c u ↔ c v)`. For a closed walk (`u = v`) the
  RHS is trivially true, forcing even length.
- Added reusable helper `noOddCycles_of_boolColoring (c : G.Coloring Bool) :
  oddCycleLengths G = ∅`, the parity argument (mirrors Mathlib's
  `Walk.three_le_chromaticNumber_of_odd_loop`).
- Fully proved `colorable_two_no_odd_cycles` (no sorry): build a `Coloring (Fin 2)`
  from the file's `IsColorable` witness via `SimpleGraph.Coloring.mk`, then apply
  the forward direction of the iff.
- Proved the forward direction (`→`) of `bipartite_iff_no_odd_cycles` by
  recoloring `Fin 2 → Bool` with `recolorOfEquiv G finTwoEquiv` and applying the
  helper.

### Key Findings
- `IsBipartite` is `abbrev` for `Colorable 2`; `obtain ⟨c⟩` extracts the
  `Coloring (Fin 2)`.
- The **reverse** direction (no odd cycle ⟹ bipartite) is a genuine Mathlib gap:
  `Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` lists exactly
  `IsBipartite ↔ ∀ n, (cycleGraph (2*n+1)).Free G` as *future work*. Only
  `IsAcyclic.isBipartite` / `IsTree.isBipartite` exist. For arbitrary (infinite)
  `V` it needs a component-wise distance-parity coloring + choice — substantial,
  build-gated.

### Files Modified
- `proofs/Proofs/Erdos57Problem.lean` (lines ~143–185)

### Next Steps
- Prove the reverse direction: per connected component, pick a base vertex, color
  by parity of `G.dist base v`; properness is exactly the no-odd-cycle hypothesis.
  Mathlib's `IsAcyclic.isBipartite` (Acyclic.lean:511) uses `dist u v % 2` and is
  a strong template. Estimated 200–400 lines; do under live Docker.
- Build-verify under Docker (this session was under a Docker/Aristotle blackout;
  proof is name-checked against pinned Mathlib v4.26 but not compiled).
