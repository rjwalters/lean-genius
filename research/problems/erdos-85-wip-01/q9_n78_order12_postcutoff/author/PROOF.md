# Excluding full automorphism order twelve at N78

Let G be a simple C4-free nine-regular graph on 78 vertices and A its full automorphism group. Accepted review2487 gives |A| in {1,2,3,4,6,8,12}. We exclude the last case by composing independently accepted proofs and complete finite domains. This composition itself is submitted for independent review.

Assume |A|=12. Reviews2489 and2494 give the exhaustive group disjunction C12, Dic12, C3 x V4, S3 x C2, A4. Their use of the full automorphism group matters: the accepted stabilizer bound rules out a globally fixed vertex. This argument does not claim that every subgroup of these types is excluded.

Review2555 excludes C12 and Dic12. Review2544 excludes C3 x V4. Review2627 independently composes all fourteen S3 x C2 action profiles and excludes that full group. It remains to exclude A4.

Write (a,b,c,d) for the multiplicities of A4 vertex orbits of sizes (3,6,4,12). Review2489 gives 3a+2b in {2,6}, c in {0,3}, and 3a+6b+4c+12d=78. These nonnegative integer equations give precisely the following six profiles; check.py independently inventories these elementary equations.

* (2,0,0,6) is excluded by2496.
* (2,0,3,5) is excluded by2491.
* (0,3,0,5) is excluded by2597, using the complete three-six-orbit cover.
* (0,3,3,4) is excluded by2602 with its explicit paper erratum, discussed below.
* (0,1,3,5) has exactly three attachment branches by2498: no exceptional orbit, an exceptional four-orbit, or an exceptional twelve-orbit. Review2498 excludes the first;2516, including accepted2512, excludes the entire exceptional-four branch;2520 excludes the exceptional-twelve branch.
* (0,1,0,6) has two attachment branches by2498. Review2501 excludes the no-exception branch. In the exceptional-twelve branch,2521 makes the exceptional orbit B independent, and2522 gives its degrees to the other five regular orbits as (2,2,1,1,1). There are two W orbits and three Y orbits. The locations of the two degree-two entries therefore give exactly three cases: both W, both Y, or one of each. Review2524 excludes both W,2528 excludes both Y, and2606 excludes the remaining mixed placement using the complete accepted upstream domains. Thus this last profile is impossible.

Every A4 profile is excluded. Hence none of the five possible full groups of order twelve occurs. Combining this with2487 yields

    |Aut(G)| in {1,2,3,4,6,8}, hence |Aut(G)| <= 8.

This is an upper cover, not a realizability assertion and not a divisibility-by-eight assertion. Smaller full automorphism groups, asymmetric graphs, N78 existence, N80 existence and Erdős85 globally remain open. This is a paper/computation composition, not a Lean formalization.

## Exact erratum and scope of the computational premises

Review2602 was accepted with the explicit reviewer erratum /tmp/erdos85-sol1-review2602/ERRATUM.md. The author PROOF.md is now corrected and accompanied by ERRATUM.json. For the three ordinary regular orbits, classes1/2 have diagonal degrees (1,3,1), with cross degree3 between ordinary orbits0 and2; the old uniform diagonal3/cross1 sentence is false and is not used. The actual enumerator and all1044 saved per-orbit rows always used the saved Q entries. This composition pins both the corrected author packet and the independent erratum.

Review2599 supplies only the complete induced-graph domain (973 cases after filtering), as explicitly scoped in its acceptance. Its separate capped incidence run, with UNKNOWN and unvisited cases, supplies no exclusion or exhaustive domain. Reviews2600,2601 and2602 instead use the complete induced cover and complete subsequent domains. This restriction is inherited here. No capped producer is resumed or enlarged, no positive existence witness is treated as an exhaustive domain, and no new graph search is run.

The machine-readable case map records every terminal branch and cover reference. check.py verifies current accepted review states and all files in their manifests, records exact source hashes, and binds the two erratum files. The script checks premise bookkeeping and the elementary profile inventory; the mathematical composition is the explicit exhaustive disjunction above and requires independent review.
