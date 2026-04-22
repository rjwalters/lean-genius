# Literature for szemeredi-regularity-oq-02

This directory contains:
- Related papers and their summaries
- Links to relevant Mathlib documentation
- References to similar problems and their solutions

## Related Gallery Proofs

- `szemeredi-regularity`: Parent proof — provides energy machinery, Mathlib Finpartition bridge,
  and ε-regular pair definitions
- `szemeredi-counting-oq-02`: Next step — hypergraph counting lemma formalization
- `szemeredi-full-oq-01`: Long-term — Furstenberg ergodic proof formalization
- `szemeredi-regularity-oq-04`: Harder sibling — Alon-Fischer strong regularity (2000)

## Key Papers

- **Frieze & Kannan (1999)**: "Quick approximation to matrices and applications" — the original
  weak regularity paper; introduces the cut-norm and exponential partition bound
- **Lovász (2012)**: "Large Networks and Graph Limits" — Chapter 9 covers cut-norm and
  Frieze-Kannan; provides clean proof via SDP relaxation
- **Conlon & Fox (2012)**: "Bounds for graph regularity and removal lemmas" — quantitative
  comparison between Szemerédi and Frieze-Kannan bounds

## Mathlib References

- `Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk`
- `Mathlib.Combinatorics.SimpleGraph.Regularity.Energy`
- `Mathlib.Combinatorics.SimpleGraph.Regularity.Equitise`
- `Mathlib.Order.Partition.Finpartition`

## External References

- Mathlib4 `szemeredi_regularity` theorem for ε-regularity definitions
- Lean 4 `⨆` (iSup) for defining the cut-norm supremum
