# Literature: sperner-ndim-oq-02

## Key References

- **Sperner (1928)**: Original Sperner's lemma paper
- **Freudenthal (1942)**: Freudenthal triangulation of the n-cube/simplex
- **Kuhn (1960)**: Simplicial approximation and fixed point algorithms
- **Scarf (1967)**: Approximation of fixed points; path-following algorithm

## Mathlib References

- `Mathlib.Combinatorics.SimplicialComplex.Basic` — simplicial complexes
- `Mathlib.Combinatorics.Colex` — combinatorics of finite sets
- `SpernerNDim.lean` — abstract SpernerTriangulation + parity theorem (this repo)
- `SpernerGrid.lean` — concrete Freudenthal grid (this repo, has sorries)

## Key Insight from Prior Session

The `GridSimplex` type in `SpernerGrid.lean` uses oriented simplices with a `miss`
direction. Each geometric simplex appears twice (two orientations). This means
`boundary_doors_odd` (counting oriented boundary doors) is ALWAYS EVEN, not odd.

The fix is to work with unoriented simplices (vertex sets, i.e., `Finset (Vertex d N)`)
and define a `SpernerTriangulation` instance for those.
