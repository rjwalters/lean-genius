# Independent H3 triple U-domain census

An independent adjacency-matrix census reproduces the 29 full and 370 partial
U-domain classes used by the H3 triple searches. Every representative in all
four production programs joins exactly one independent class, with no missing
or duplicate classes and matching orbit cardinalities. This checks domain
generation and normalization only. It does not rerun any U-to-R extension,
singleton exact-cover search, or final exclusion, and adds no Lean theorem.

The shared paper premise is `../Q7_H3_TRIPLE_MATCHING_CAPACITY_20260910.md`:
U is partitioned into three five-vertex blocks A,B,C, each containing a
matching of two edges. The cross graphs are matchings with sizes either
5/5/5 or 5/5/4. In the partial case, name the unique block adjacent to both
perfect matchings A, so the deficient pair is B,C. Label along the two perfect
matchings to make A-B and A-C the identity matchings. This normalization does
not omit any graph furnished by the premise.

The new census then fixes A's internal matching to edges 0-1 and 2-3, leaving
vertex 4 unmatched. It enumerates each B and C matching by choosing two
vertex-disjoint edges directly (15 choices each). It generates the B-C map by
choosing a domain of size four/five and an ordered injective image. It builds
the full 15-vertex adjacency matrix and tests all vertex-pair intersections
for size at most one. There is no triangle-count or spectrum filter.

This differs from production, which leaves all 15 A matchings variable,
constructs partial maps by missing domain/image positions, checks C4s while
adding individual edges, and transports permutation/matching tuples. The new
census tests complete adjacency matrices and relabels actual vertices by
following their cross-neighbors.

| B-C size | B-C maps | Candidate matrices | C4-free with fixed A | All A matchings | Classes |
| --- | ---: | ---: | ---: | ---: | ---: |
| 5 | 120 | 27,000 | 670 | 10,050 | 29 |
| 4 | 600 | 135,000 | 5,310 | 79,650 | 370 |

Multiplication by 15 is exact: simultaneous S5 relabeling of the three blocks
preserves the identity A-B/A-C matchings and acts transitively on the 15
possible internal A matchings. It gives a bijection between every pair of
fibers. This applies within each color-isomorphism class as well, explaining
why every production orbit size is exactly 15 times the corresponding orbit
size in the fixed-A universe.

For orbit enumeration, consider all six color orders in the full case and
the two orders fixing A in the partial case. Choose any of the 120 orders of
the new A block. Its cross-neighbors force the new B/C labels uniquely.
Retain precisely transports whose new A matching equals the fixed matching.
These are all isomorphisms between two graphs in this normalized universe:
any such isomorphism chooses an allowed color order and an A labeling, and
its images on B/C are forced by the two identity cross-matchings. Each orbit
is checked to lie entirely in the remaining valid set, and all orbits are
removed disjointly until that set is empty.

`extract.py` parses a production source and executes only its top-level prefix
ending at the requested U-domain assignment. The four programs supply five
lists: m3/full, m1r4/full, m1r3/partial, and m2/full plus m2/partial. The final
R enumeration, extension search and all terminal rejections are excluded
from execution. Whole-source SHA256, boundary name and end line are retained.
The extracted source has no file-writing calls in that prefix. These runs
are comparison evidence; they are not part of the independent census.

`compare.py` reconstructs each production representative as an adjacency
matrix, enumerates all allowed transports into the fixed-A universe, and
joins its least image to the independently computed representatives. It
requires a bijection for each list, equality of raw domain sizes, and the
exact factor of 15 for every individual orbit. Thus agreement is stronger
than merely matching the numbers 29 and 370. The production programs share
code with each other; this comparison does not count them as independent
implementations.

Replay with a fresh output directory from the repository root:

```
python3 -B research/problems/erdos-85-wip-01/q7_h3_u_independent/replay.py \
  --output-dir /tmp/erdos85-u-census-new
```

Census/comparison stages have 60-second subprocess deadlines; each production
prefix has 90 seconds. A failed or timed-out subprocess fails the replay.
Output creation is exclusive. When comparing JSON, ignore elapsed seconds
and whitespace. The archived run completed the independent census in about
one second; production prefix timings are environment-dependent. No SAT
solver, proof replay, or Lean enumeration is launched.
