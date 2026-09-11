# Complete necessary F+U+V coupling on the saved order-24 parameter domain

The source domain is all 211 center-action/matching records from 2322, each with a=1 and a=4 as in accepted 2314. Its interpretation as covering every order-24 four-orbit action additionally requires the paper cover 2319 and finite parameter review 2322; no unaccepted input completeness is silently assumed.

For each action let lambda(g) label gH, let p be the matching partner of H, and let L be the five center labels other than p. Enumerate all inverse-closed subsets S of A minus identity of size a. Retain those with distinct labels contained in L and satisfying their own common-neighbor bound |S intersect gS|+1[lambda(g)=0]<=1 for g!=1. Use these as possible internal U and V connection sets.

For each S_U, enumerate T with one element in each of the remaining 5-a label fibers. Its inverse set T^-1 must also have distinct labels in L. Enumerate every S_V whose label set complements the labels of T^-1 in L. This covers exactly the allowed connection/coset parameterization; it never demands inverse closure of T.

Left translation reduces the necessary distinct-W-pair common-neighbor checks to three types:

    U1,Ug: |S_U intersect gS_U| + |T intersect gT| + 1[lambda(g)=0] <=1 (g!=1)
    V1,Vg: |S_V intersect gS_V| + |T^-1 intersect gT^-1| + 1[lambda(g)=0] <=1 (g!=1)
    U1,Vg: |S_U intersect gT^-1| + |T intersect gS_V| + 1[lambda(g)=0] <=1 (all g).

The inverse in the mixed expression is necessary because Vg has U-neighbors gT^-1. Fixed-center pairs introduce no extra obstruction under the coset/matching conditions. The source graph reconstruction independently verifies this for every survivor.

The original aggregate cap was 30 seconds. All 422 roots completed in 3.051 seconds, with no UNKNOWN or unvisited record. There were 515104 cross choices visited and 2688 coupled candidates reaching the final pair checks. Exactly 1344 configurations survive across 12 roots, all in the explicit S4 group (index22). The six action records involved are indices0..5, each at a=1 and a=4. Other recorded actions/groups have no surviving F+U+V configuration in this necessary model.

A separate direct set-based reconstruction of every survivor verifies the 54-vertex graph, all six center degrees nine, all 48 W degrees six, simplicity, symmetry, and all 1923264 distinct-endpoint common-neighbor checks. Complete adjacency lists are in witnesses.json. These checks certify positive partial graphs; independent review is needed for exhaustive negative coverage.

This stage leaves 1344 partial graphs and does not construct residual edges. It is a necessary coupling check, not a nine-regular graph solver, a four-orbit exclusion, or Lean formalization. Source coverage dependencies remain explicit; no timed-out attempt was retried.
