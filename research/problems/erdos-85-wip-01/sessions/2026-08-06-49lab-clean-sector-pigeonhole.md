# Session 2026-08-06: 49-lab — clean-sector theorem, saver calculus, SAT phase

Collaboration: Claude (freqpair branch) + Codex/GPT (assembly branch), squad room.

## Headline results (machine-checked in Lean unless noted)

1. **Uniform clean-sector theorem** (`false_of_squareOrder_uniqueHigh_clean`, Codex):
   at order d² with degrees {d, d+1} and a unique high vertex, if no branch of the
   high's branch system contains an internal edge, the graph cannot be C4-free.
   Proof: per-vertex fan pigeonhole — each outer vertex has one neighbor per far
   branch; the d−1 middle branches give d−1 pairwise-distinct (else C4) 2-walk
   endpoints in the paired branch of size d−2. Found independently by both agents
   (Claude: per-vertex fan; Codex: r(r+1) > r² block-pair count) after Claude's
   S₅-voltage/holonomy DFS (17,647 nodes) and Cadical (2.9s) established the d=7
   case empirically. Voltage formulation: clean h=1 ⟺ S_{d−2} voltages on the
   cocktail-party graph CP_{(d+1)/2} with every 4-cycle holonomy fixed-point-free;
   at d=7 the minimal infeasible sub-configuration is exactly the full 8-block system.

2. **Miss-matrix symmetry** (`squareOrder_highBranchMissCount_comm`, Codex):
   m_{c→b} = m_{b→c} (far-pair bipartite edge counts), hence M_b = 2·in_b and the
   paired-capacity inequality forces in_i + in_j ≥ 3 per paired branch pair:
   **every branch dirty, ≥ 12 internal edges** at d=7 h=1.

3. **Saver injection / needy ≤ savers** (interface agreed, Codex formalizing):
   needy = unmatched lows + all foreign highs (foreign highs always cover all six
   middles; their residual is an in-branch low sibling). Each needy vertex requires
   a matched-low saver missing exactly its paired branch; savers save ≤ 1 (unique
   neighbor in the target branch). Hence **M_v ≥ 20 matched lows per high system at
   every h ∈ {1,...,9}**, I_v ≥ 10 internal edges per system.

4. **Capacity identity** (scratch, both agents): total in-branch demand Σ_v I_v ≥ 10h
   vs capacity h(17−h) [all-low triangles, via 2r+2k+TF = 7] + h(h−1) [high-apex
   triangles, via per-code k-sum Σ_{N(w)} k = 7+h] = 16h — counting alone kills no
   stratum; the lab is tight everywhere and geometry must finish.

## SAT phase (scratchpad, python-sat/Cadical)
- h=1 reduces to a 40-vertex instance (8 blocks of 5; paired blocks non-crossing).
- Clean sector: UNSAT (DFS + CDCL cross-validated) — now superseded by the Lean theorem.
- Dirty sector: running with cuts (every block ≥1, pair-sums ≥3, total ≥12).
- h=3 direct 49-vertex encoding: running.
- Any SAT model ⟹ f(42)=50 (Boza entry resolved, no drop at 49);
  all strata UNSAT ⟹ f(42)=49 ⟹ first proven drop of the Erdős-85 function.

## Census state (k ≤ 3 proven)
h=1: unique distribution (n0,n1)=(40,8). h=3: (25,18,3,0),(24,21,0,1). Triangles
edge-disjoint; matched S_v edges in no all-low triangle; every low has odd TF-degree.

## Partition-law era (late session)

5. **Square-root identity** (`Erdos85OrderFortyNineSquareRoot`, Codex): A·A =
   6•I + E_H + J − M with M the defect matrix, E_H the high diagonal. Necessary
   conditions: IsSquare(det Q), 4 ∣ det Q. Bruck–Ryser context: 49 sits between
   plane orders 6 (nonexistent — no ER₆ polarity graph, plausibly why f drops)
   and 7.

6. **The partition law** (`orderFortyNine_low_neighborhood_partitions_highs`,
   Codex, via defect-isolation + the identity): for every low y and every high w,
   EXACTLY ONE member of N(y) is adjacent to w. Complemented by the code-side law
   (D+I)k = h·1 (`Erdos85OrderFortyNineDefectWeightedIncidence`).

7. **Stratum kills** (all certificate-free in Lean or 0.0s propagation + hand
   proof): h=3 dist1-b2 (double-common C4), dist1-b1, dist1-c1 (partition-law
   propagation); h=9 profiles t=0 (parity: even parts, odd sum) and t=1
   (k1-capacity 18 < 36 needy). Remaining: h=1 dirty (5 profile lanes), h=3
   c2 + dist-2, h=9 t ∈ {2,3,4}, h=5, h=7.
