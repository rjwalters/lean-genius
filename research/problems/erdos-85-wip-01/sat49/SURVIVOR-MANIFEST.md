# Survivor manifest — the remaining obligations for ¬C4FreeMinDegreeWitness 49 7

Target: `¬ C4FreeMinDegreeWitness 49 7` (no C4-free graph on 49 vertices with
minimum degree ≥ 7). Combined with the certified witnesses (48,7) and (49,6)
this closes `minDegreeForC4_fortyEight_fortyNine_exact` (f(48) = 8, f(49) = 7)
— the first proven drop of the Erdős-85 function, and f(41) = f(42) = 49 in
Boza's table.

Decomposition (all Lean-certified on this branch): any such graph has degrees
in {7,8}, h = #degree-8 vertices ∈ {1,3,5,7,9} (`orderFortyNine_card_high_…`),
and each stratum is parameterized by a linear triple system on the h highs
(general profile law). Status per stratum:

## CLOSED
- **h = 9** — `false_of_orderFortyNine_nine_high` (5a445a3545): full chain
  classification → witness table → aligned labeling → Boolean bridge →
  generated CNF → 18 include_str LRAT certificates. DONE, no hypothesis needed.

## OPEN HYPOTHESES (named, one per remaining instance family)

### SurvivorUNSAT_h7_t0, ..., SurvivorUNSAT_h7_t7
All eight h=7 triple-incidence cells remain formally open.  The earlier claim
that t=1..7 were certificate-closed was not backed by durable proof artifacts:
the artifact volume contains no DRAT, LRAT, verdict, or Lean semantic endpoint
for any h=7 cell.  The only durable h=7 inputs currently found are the seven
`h7t0_cube0..6.cnf` files in `deepsix-scout/`; these are CNFs, not exclusion
certificates.  Coverage of t=0..7 is Lean-certified by
`orderFortyNineStratumExcluded_seven_of_tripleCells`.

### SurvivorUNSAT_h5_t0, SurvivorUNSAT_h5_t1, SurvivorUNSAT_h5_t2
The three h=5 classified reps (unique triple systems (), (012), (012)(034);
censuses (14,20,10,0), (13,23,7,1), (12,26,4,2)). The fourth census profile
(n3 = 3) is Lean-dead (`orderFortyNine_highIncidenceCount_three_le_two_of_five_high`).
Coverage: h=5 classification complete in Lean (6f16f966ab). SAT: three
monoliths running (deep); code-law pilot variants running.

### SurvivorUNSAT_h3_dist2, SurvivorUNSAT_h3_c2
h=3 = t-classification {t=0 = dist-1, t=1 = dist-2} (6a3f27837b).
dist-1 classes b1, b2, c1 are dead (b2 by
`orderFortyNineDistOne_partner_forces_no_sibling_coincidence`; b1/c1 by
partition-law propagation — certificates to be regenerated through the
pipeline for the record). Remaining: c2 (non-partner + sibling coincidence)
and dist-2 (fully pinned high side, `orderFortyNineDistTwo_*` layers).
Coverage: coverage trichotomy + E4 split Lean-certified (40e5b02d7e,
d666b00e0e). SAT: both running (deep).

### SurvivorUNSAT_h1
No C4-free min-degree-7 49-graph with exactly one degree-8 vertex.
Structure fully certified in Lean: branch partition, induced matchings,
misses, saver injection, rigidity equalities (paired = M_s+M_t−5, far =
5−m−m′), disjoint miss sets, universal transversals, clean sector dead
(`false_of_squareOrder_uniqueHigh_clean`). Remaining = the dirty sector.
Two execution routes:
1. **Same-miss collapse** (open lemma; SAT tests deep/UNDECIDED at 200K
   conflicts): mates share their miss ⟹ all m-entries even ⟹ 102 role-free
   table cases across all five profiles (AAAB/ABBB die by handshake parity).
2. **Capacity-filtered orbit sweep**: 13,351 table orbits across the five
   in-profiles (1485/3617/4717/2693/839).  The graph-to-filter cover is
   Lean-certified by `oneHighRawV2OrbitCover_capacityInventory`; the cross-miss
   capacity filter removes 190 raw rows.  Of the filtered rows, 493 currently
   have Lean-accepted certificates and 12,858 remain pending.  The underlying
   authoritative enumerator is `enumerate_h1_miss_tables.py`; counts-only +
   per-branch D8 lex instances (timing: 17–90 s/table verified feasible);
   coverage obligations = profile exhaustiveness (in ∈ {1,2}, pair-sums ≥ 3 —
   Lean: `paired_highBranchMatchedCount_states`), orbit classification
   witness tables (h=9 style), and the D8-lex soundness lemma.
Calibration artifacts: C8-table 30-bracelet closure (running, all
UNSAT+verified so far); honest single-table kill verified (Glucose 433K-line
DRAT, `bbbb_table1b*`).

The exact theorem-backed integration socket is
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_verifiedFrontier`: filtered h=1,
the two h=3 cells, the three h=5 cells, and all eight h=7 cells.  The h=9
stratum is discharged internally.

## Discharge pipeline (identical to h=9)
Glucose 4.2 with proof → drat-trim verify → `emit_lrat_compact.py` →
`proofs/Proofs/Certificates/` → include_str + pure parse + `LRAT.check` via
native_decide → per-instance `False` theorem → conjunction closes the
hypothesis. CaDiCaL is the search workhorse but Glucose is the certificate
producer of record (pysat CaDiCaL proof capture truncates on some instances).

## Robustness
If any instance turns out SAT, its model is a 49-vertex witness: then
`C4FreeMinDegreeWitness 49 7` holds, f(42) = 50, and the same capstone
interface produces the no-drop resolution of Boza's entry instead.
