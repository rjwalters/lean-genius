# Independent H3 triple secondary-graph census

Direct enumeration of every three- or four-edge graph on eight labelled
vertices finds 3,450 admissible secondary graphs, in exactly 21 orbits. Each
production secondary-graph generator supplies exactly one representative of
each orbit. This independently checks the R-side normal-form coverage used by
the triple-profile searches. It does not repeat their U-side normalization,
terminal extension checks or singleton exact-cover rejection, and is not an
unconditional graph exclusion or a Lean theorem.

The input paper reductions are
`../Q7_H3_TRIPLE_SECONDARY_LEDGER_20260910.md` and the later sharpening summarized
in `../Q7_H3_TRIPLE_PROFILE_EXCLUSION_20260910.md`: R has eight vertices,
N consists of six neighbors of a distinguished root, T=R\N has two vertices,
e(R) is three or four, N induces a matching of size one to three, both T vertices
have an R-neighbor, and the graph with the root adjoined is C4-free. The census
assumes these graph-to-partition consequences; it does not derive them again.
In particular the earlier secondary ledger's preliminary r=2 boundary is
excluded using the later matching/cross-count sharpening, not by this census.

`census.py` uses a different input universe from the production generator:
it chooses all edge subsets of size three/four from the 28 possible R edges,
then tests the nine-vertex adjacency relation directly. It does not pre-fix a
matching or parameterize graphs by epsilon and the two far attachments. It
quotients by every one of the 1,440 permutations in S6 × S2, checking that each
whole orbit remains inside the surviving labelled set and that distinct
orbits are disjoint. Thus this independently recounts both the labelled set
and its quotient. The underlying paper reductions and symmetry group are
shared mathematical premises, not a second independent derivation.

| Matching size m | R edge count r | Labelled survivors | Orbits |
| --- | --- | ---: | ---: |
| 1 | 3 | 720 | 7 |
| 1 | 4 | 510 | 4 |
| 2 | 3 | 45 | 1 |
| 2 | 4 | 2,160 | 8 |
| 3 | 4 | 15 | 1 |
| Total | | 3,450 | 21 |

All 23,751 input graphs were examined. The original run took about 0.1 seconds.
The result contains each orbit representative, edges and cardinality; timings
may vary on replay. No SAT solver or Lean enumeration is launched.

`compare_production.py` runs the independent census first, then extracts only
the top-level R-enumeration loop from the three banked m1r3, m1r4 and m2 source
programs using the Python AST. It never runs those programs' U enumeration or
terminal search. Each extracted generator's representatives are joined to the
independent orbit assignment, requiring injectivity and surjectivity as well
as the same (m,r). The production m3 program's fixed matching plus far edge
joins the unique (3,4) class. Whole-source hashes, extracted-loop hashes and
line locations make the executed production snippets explicit. All three
comparisons pass. There is no claim that these three copies of the production
loop are independent of each other.

To replay from this directory, use fresh output paths:

```
python3 -B census.py --output /tmp/erdos85-secondary-census-new.json
python3 -B compare_production.py --output /tmp/erdos85-secondary-joins-new.json
```

Compare result content excluding elapsed time. The comparison script requires
the three banked production sources in the parent directory. Output creation
is exclusive; previous evidence is never overwritten by either CLI.
