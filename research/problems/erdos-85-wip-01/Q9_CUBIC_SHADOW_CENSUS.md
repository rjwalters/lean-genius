# q=9 cubic-shadow census

For a vertex-transitive, C4-free, 9-regular graph on 80 vertices, the
triangle-free-edge shadow `F` is vertex-transitive and cubic.  It contains
neither a triangle nor a four-cycle, so it has girth at least five.

`F` need not be connected.  Vertex transitivity permutes its connected
components transitively, and the stabilizer of a component is transitive on
that component.  Consequently `F` is a disjoint union of isomorphic connected
cubic vertex-transitive graphs.  Their common order divides 80.

Filtering the complete Potočnik--Spiga--Verret census of connected cubic
vertex-transitive graphs gives the following candidates.  An ordinal means
the one-based position among census entries of that order.

| component order | copies | all census entries | girth-at-least-5 ordinals |
|---:|---:|---:|:---|
| 4 | 20 | 1 | none |
| 8 | 10 | 2 | none |
| 10 | 8 | 3 | 3 |
| 16 | 5 | 4 | 4 |
| 20 | 4 | 7 | 4, 6, 7 |
| 40 | 2 | 12 | 3, 4, 5, 6, 7, 8, 11 |
| 80 | 1 | 33 | 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19, 20, 21, 23, 24, 28, 29, 30, 32, 33 |

Thus the local and transitivity constraints reduce the shadow to exactly 37
unlabeled types: eight Petersen components; five copies of the unique
surviving order-16 graph; four copies of one of three order-20 graphs; two
copies of one of seven order-40 graphs; or one of 25 connected order-80
graphs.

This is a necessary-condition census, not an existence result.  A survivor
still needs a compatible vertex-transitive symmetric `80_3` linear
configuration whose point graph is edge-disjoint from `F` and whose union
with `F` is C4-free.

## Reproduction

The source is `cubicvt4-300g6.txt` from commit
`68c592d4790ab1737f04d86d3102c4999bbc6c09` of
<https://github.com/kguo-sagecode/cubic-vertextransitive-graphs>.  Its SHA-256
is `4bac89beec1465265318266117c38a2c1680e73a21efd322411207cef5313088`.

With NetworkX installed, run:

```text
python3 q9_cubic_shadow_census.py /path/to/cubicvt4-300g6.txt
```

The verifier checks the source digest, connectedness, cubicity, and the exact
survivor lists.  Its girth calculation is a direct repeated breadth-first
search.

## A first transitive orbit quotient

The smallest surviving shadow type is eight disjoint Petersen graphs.  The
script `q9_petersen_product_orbit_census.py` tests nine natural transitive
product actions on this shadow.  Internally it uses `F20`, `A5`, or `S5` on
the Petersen graph's model as the 2-subsets of five points.  On the eight
components it uses the regular action of `C8`, `C4 x C2`, or `C2^3`.

There are 56,000 possible triples whose points are pairwise at shadow distance
at least three.  The nine group actions reduce these to only 7 or 28 possible
invariant orbit unions of size 80.  None gives a compatible graph: every
union is non-linear, violates the definition of the triangle-free-edge
shadow, or creates a four-cycle.

This rules out those nine product actions, not every transitive subgroup of
the full wreath-product automorphism group of eight Petersen components.
That distinction matters: the census remains a necessary-condition reduction,
not a q=9 nonexistence proof.
