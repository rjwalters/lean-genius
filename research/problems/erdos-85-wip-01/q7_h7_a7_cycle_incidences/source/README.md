# Complete singleton-incidence lists for the reviewed F=C7 colouring cover

Accepted2102 covers all proper Q-edge-colourings with empty graph F=C7, modulo Aut(R) x Aut(F), for R=C7 or C3+C4. Accepted2097 says that for each fixed colouring, the seven singleton double-host pairs must be distinct and individually have no common F-neighbour. Selecting them determines the remaining single-host incidences exactly.

incidence.py forms the three candidate pairs from each high's unused three empty colours. It removes pairs with a common F-neighbour, then enumerates all seven-row selections with distinct pair values, processing the smallest domains first. Each high's choice index0..2 occupies bits2i and2i+1 of a solution integer. The candidate-pair order is lexicographic on its sorted unused colours. This encoding is injective. The complete recursion has at most1+3+...+3^7=3,280 nodes per colouring, below100,000.

run.py checked accepted2097/2102 records and all input hashes before the sole incidence pass. It visited all78,723 proper-colouring representatives within the original60second aggregate guard, with zero unvisited:3.49seconds and8,061,771 recursion nodes. Every solution code is retained in incidences.jsonl.gz with its R case and colouring index.

- R=C7:60,801 colourings checked;1,954 have no singleton incidence and58,847 have at least one;3,194,466 solution codes.
- R=C3+C4:17,922 checked;723 have none and17,199 have at least one;926,060 solution codes.

verify.py imports neither the incidence generator nor the runner. It reconstructs each colouring, uses cycle-distance arithmetic for pair admissibility, and computes the exact number of injective pair selections by a reverse-high weighted subset dynamic programme. All4,120,526 stored codes are individually valid and unique within their colouring, and their counts equal that independently computed cardinality on every colouring. This proves completeness of each stored list. It used10,006,527 DP states and9.84seconds; all source hashes and record coverage matched. Independent squad review is requested.

The proper colourings are symmetry representatives, but singleton selections have NOT been further quotiented by each colouring's residual stabilizer. The list is a complete cover and may contain symmetry-equivalent partial graphs. The counts are not counts of unlabelled full graphs.

Only singleton-to-empty incidences were enumerated. No nonempty-low edge has been added or full-row family pass launched. Empty lists exclude those proper-colouring representatives only; neither entire R/F class is excluded. Other empty graphs, a6, H1 and all Lean/global proof obligations remain open. The historical capped crossed6/7/8 host censuses were untouched.
