# Computational exclusion of the H3 stratum

Combined census/branch-union review #1685 PASS.

All universal H3 support profiles have been excluded by independently replayed finite computations. This statement depends on the reviewed paper graph-to-core reductions and Python enumerations. It is not yet a Lean kernel theorem and does not solve Erdős 85: the other outstanding strata and global obligations remain separate.

For a C4-free graph on 49 vertices with minimum degree 7 and exactly three degree-8 vertices, the high-support census has exactly two possibilities. The triple profile has 24 empty, 21 singleton, and one triple-support low vertex. The pair profile has 25 empty, 18 singleton, and three pair-support low vertices. These are exhaustive alternatives, not selected residual spectra. The census is recorded in `Q7_H1_H3_SQUEEZE_20260910.md` and already has Lean graph interfaces in `Erdos85OrderFortyNineThreeHighZeroFiber.lean` and `Erdos85OrderFortyNineThreeHighOneFiber.lean`.

In the pair profile, Ct=3 implies that a low vertex has at most one pair-support neighbor. The induced graph on the three pair vertices is therefore a matching with b=0 or b=1 edges. The core reductions and searches cover both values.

| Profile | Complete domain | Independent reviews |
| --- | --- | --- |
| Triple | All five (m,r) pairs; 3,337 induced U/R cases | 1664, 1666, 1668, 1673; union 1683 |
| Pair, b=0 | 36 normalized cores times 27 host choices = 972 cases | Core 1674; full completion 1679 |
| Pair, b=1 | 75 normalized cores times 48 host choices = 3,600 cases | Core 1680; full completion 1681 |

Every listed review resolved PASS. The full-completion reviews used unchanged-source, no-deadline replays and obtained exact agreement with the complete retained case JSON. No branch uses a triangle-count cutoff or a selected spectral polynomial.

The triple result is detailed in `Q7_H3_TRIPLE_PROFILE_EXCLUSION_20260910.md`. It exhausts the empty induced graphs and singleton exact covers, then rejects every cover failing a necessary high-color neighbor condition. The pair results are detailed in `Q7_H3_PAIR_B0_FULL_EXCLUSION_20260910.md` and `Q7_H3_PAIR_B1_FULL_EXCLUSION_20260910.md`. They regenerate the nonempty cores, enumerate all marked-empty host choices and remaining transversal singleton triples, and exhaust the empty-edge completions. There are zero completed full graphs in either pair branch.

The two pair searches together visit 13,582,750 incidence nodes, 286,306 incidence leaves, and 644 empty-edge recursion nodes, with zero completed empty-edge leaves. Their case counts and the triple case counts measure different stages; adding them does not count distinct graphs. No isomorphism-class claim is made for the pair cores.

Since every hypothetical H3 graph belongs to one row and every row is excluded, the paper and finite-computation argument excludes the H3 stratum. The outstanding formal task is to connect the exact core reductions and checked exclusions to the existing actual-graph interfaces. The conditional theorem `orderFortyNineStratumExcluded_three_of_representativeExclusions` already composes the two canonical support-profile exclusions, but the new Python results do not themselves discharge its Lean premises. The existing LRAT terminal is a separate certificate route; no new LRAT payload or campaign is claimed here.
