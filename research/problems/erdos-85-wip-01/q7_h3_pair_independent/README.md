# Independent re-implementation of the H3 pair-profile exclusion

Owner: claude (Fable). Date: 2026-09-10 (goal #48 Phase A, editor 46111 item (b), room 46138 caveat C1).
Status: second-implementation corroboration of `Q7_H3_PAIR_B0_FULL_EXCLUSION_20260910.md` (review 1679)
and `Q7_H3_PAIR_B1_FULL_EXCLUSION_20260910.md` (review 1681). Not a Lean theorem; does not touch the
triple profile; does not solve Erdős 85.

## What is independent

`h3_pair_independent.py` was written from the paper reductions only (support ledger, the two core-reduction
notes, the block identities BB^T = 7I + J, BC = J, C1 = 7 − t, Ct = 3, all re-derived by hand in room 46138).
It shares no code with `verify_q7_h3_pair_b{0,1}_*.py` and differs in three structural choices:

1. **No sol normalization of the core.** Every perfect matching consistent with BC = J is generated
   (special singletons fixed WLOG as the lowest indices of their colour; ordinaries only first-touch
   normalized) and pruned by an incremental C4 check; the surviving labelled cores are then reduced to
   orbit representatives under the exact symmetry group (colour permutations preserving the P–P edge set
   × relabelings of the ordinary singletons within each colour) by an invariant-refinement canonical
   form with brute force inside equal-invariant cells. The sol notes count *normalized configurations*
   (36 for b=0, 75 for b=1), not orbits; the orbit counts here are 14 and 35.
2. **Different incidence search.** Hosts of the P-adjacent empties are chosen as unordered subsets;
   the remaining empties' transversal triples are assigned exact-cover style by branching on the
   singleton with the fewest eligible triples (the sol verifier branches on a positive-demand singleton
   over subsets of its incident triples in a different order and with different pruning).
3. **Weaker, later empty-edge gates.** The empty–empty completion uses only the C4 admissibility test
   and residual-degree feasibility at each node (no star gate), so it visits far more empty-edge nodes
   than the sol verifier and rejects at the same final condition: no vertex may reach its residual
   degree.

Every rejection is one of: a C4 (two vertices with two common neighbours), a repeated singleton pair,
a singleton demand that cannot be met, or an empty vertex with fewer admissible partners than its
residual degree. No triangle count, spectral polynomial, timeout, or node cap is used.

## Result

| branch | labelled cores | orbit reps | host cases | incidence nodes | incidence leaves | empty-edge nodes | completed graphs | wall |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| b = 0 | 80 | 14 | 378 | 4,417,585 | 75,222 | 108,948 | **0** | 176 s |
| b = 1 | 456 | 35 | 1,680 | 1,155,223 | 18,594 | 29,466 | **0** | 46 s |

Both branches of the H3 pair profile admit no completion, in agreement with reviews 1679/1681
(which report 972 / 3,600 cases, 249,526 / 36,780 incidence leaves, zero completions). Case and node
counts are not comparable across the two implementations because the normalizations and branching
differ; the agreement that matters is the zero.

## Scope and limits

- The forced structure (special/ordinary singletons, per-colour matchings, host colours, demands
  4/3, residual empty degrees 5/4) is *derived*, not assumed; but it is the same derivation as the
  sol notes, so this corroborates the search, not the derivation. The derivation was checked by hand
  in room 46138.
- The WLOG placement of the special singletons and the first-touch rule are relabelings inside colour
  classes before any other structure exists; the orbit reduction uses only automorphisms of the fixed
  part of the problem (highs, P, specials) so every labelled configuration lies in the orbit of a
  representative that is searched exhaustively.
- Reproduce: `python3 h3_pair_independent.py 0` and `python3 h3_pair_independent.py 1` (standard
  library only; writes `result_b{0,1}.json`; the JSON output path inside the script is a scratchpad
  path and should be edited for a fresh run). Python 3.12 on the Mac Studio host.

## R-side (triple profile) secondary census recount — review 2004

`r_census_recount.py` is a third implementation of the triple-profile secondary graph census (sol-1 production loops, sol-2 `q7_h3_secondary_independent/`), written from the ledger constraints before reading sol-2's code. Result (`r_census_recount.json`): universe 23,751 three/four-edge subsets of the 28 R pairs, 3,450 labelled survivors, 21 orbits under S6 × S2 split 7/4/1/8/1 over (m,r) = (1,3)/(1,4)/(2,3)/(2,4)/(3,4) — identical to both other implementations. R-side only; the U-side reduction and terminal rejections are not touched.

## U-side (triple profile) census recount — review 2006

`u_census_recount.py` is a third implementation of the triple-profile U-domain census (sol-1 production, sol-2 `q7_h3_u_independent/`), using the identity-cross-matching normalization with all fifteen A matchings free and a re-normalizing transport for orbits. Results (`recount_full.json`, `recount_partial.json`): full 10,050 normalized labelled survivors / 29 orbits; partial 79,650 / 370 — identical to both other implementations. Lesson recorded in the review: a canonical form that applies a block permutation without re-normalizing leaves the universe and over-counts (53 instead of 29).
