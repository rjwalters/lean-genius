# 49-lab SAT instances (f(42) drop question, Erdős 85)

Question: does a C4-free graph on 49 vertices with minimum degree 7 exist?
Nonexistence ⟹ f(42) = R(C4, K_{1,42}) = 49 ⟹ first proven drop of the
Erdős-85 function. Any SAT model ⟹ f(42) = 50.

## Stratification (all Lean-verified on this branch)

Degrees are {7, 8}; h = #degree-8 vertices ∈ {1,3,5,7,9}; highs independent;
every high pair has a unique common low. The per-code profile theorem
(`orderFortyNine_highNeighborhood_general_profile`) parameterizes each stratum
by a **linear triple system** on the h highs (k=3 lows ↔ triples, k=2 lows ↔
non-internal pairs bijectively, k=1 multiplicity at w = t_w + 9 − h).

## Instance encoding (all generators in this directory)

Vertices 0..48. Highs first (0..h−1), then k3 lows (one per triple), k2 lows
(one per non-internal pair, lex order), k1 lows (grouped by attached high, in
high order), then k0 lows. All high-side edges are FIXED by the classification;
free variables are the low–low edges.

Variable semantics (certify_t34.py): the DIMACS variable for edge {i,j}, i<j,
is the 1-based index of (i,j) in the lexicographic enumeration of all
C(49,2) = 1176 vertex pairs. Variables > 1176 are sequential-counter
auxiliaries from pysat's CardEnc (EncType.seqcounter) and the partition-law
2-path auxiliaries.

Clause groups:
1. fixed edges (unit clauses): high-high absent, high-low per classification,
   in-code matchings absent/present are NOT fixed (implied by C4+degrees);
2. C4-freeness: for every pair i<j and every pair of potential common
   neighbors w<w': ¬e_iw ∨ ¬e_jw ∨ ¬e_iw' ∨ ¬e_jw';
3. degrees: CardEnc.equals(8) for highs, equals(7) for lows;
4. adjacency partition law (Lean:
   `orderFortyNine_low_neighborhood_partitions_highs` / support-partition form
   37f0c507ad): every low has ≥1 neighbor in N(w) for every high w
   (≤1 is implied by group 2).

## Results so far (2026-08-06/07)

- h=9: t=0,1 killed in Lean (parity / capacity). t=2: both cases UNSAT
  (Cadical 0.3/0.9s, DRAT archived; Z3 cross-check). t=3: all 60 prefix-fixed
  systems UNSAT. t=4: 921-system raw sweep (running, all UNSAT so far);
  canonical set = 11 iso classes (bipartite-iso reduction by Codex).
- h=7: full classified sweep t=0..7 running; every completed instance UNSAT.
- h=5: three classified reps (t=0,1,2) running; the census profile with n3=3
  is killed in Lean (`orderFortyNine_highIncidenceCount_three_le_two_of_five_high`).
- h=3: t-classification = dist-1/dist-2. Classes b1, b2, c1 killed (b2 by hand
  + Lean; b1/c1 propagation-UNSAT under the partition law). c2 and dist-2 running.
- h=1: clean sector killed uniformly in Lean
  (`false_of_squareOrder_uniqueHigh_clean`); dirty sector: 5 profile-pinned
  instances (pair-type multisets, matched sets WLOG-fixed) running.

Solver: CaDiCaL 1.9.5 via python-sat 1.9.dev7 (`Cadical195`, with_proof=True →
DRAT). Certificate path to Lean: DRAT → LRAT → Std bv_decide LRAT checker,
with the graph→CNF faithfulness bridge riding on the formalized layers.
