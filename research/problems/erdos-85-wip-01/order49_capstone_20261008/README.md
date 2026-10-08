# Order-49 integration capstone: receipt and note, 2026-10-08

Branch `erdos85/order49-capstone-20261008` = `erdos85/h5-formal-20261008`
@`717ff289137` (which contains `erdos85/h3-pair-formal-20261008` @`85d336bfbfe`)
merged with `erdos85/h7t0-formal-20261007` @`c95a89eced3`. Nothing from
`erdos85/h3-triple-formal-20261007` was merged beyond what the H5 branch already
contained. The only merge conflict was a comment block in
`proofs/scripts/docker-build.sh`; both sides were kept.

New modules:

- `proofs/Proofs/Erdos85OrderFortyNineCapstone.lean` (the theorems);
- `proofs/Proofs/Erdos85OrderFortyNineCapstoneAxiomAudit.lean` (no declarations,
  only `#print axioms` of the ingredients).

## What is proved

The capstone is a **conditional** theorem. It is not a Lean proof of
`f(49) = 7`: three hypotheses remain, and none of them is discharged in Lean.
No `sorry` in either module and no `sorryAx` in any printed axiom list.

```lean
theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence
    (hOne : ∀ (profile : Fin 5) table,
      table ∈ oneHighCapacityInventoryTables profile →
        OneHighFamilyV2CheckedUnsat profile.val table)
    (depth : Nat)
    (hSeven : ∀ edgeCount typeIndex,
      (edgeCount, typeIndex) ∈ sevenHighT0StructuralCubes →
        SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex)
    (hThreeOne : OrderFortyNineTripleCellExcluded 3 1) :
    ¬ C4FreeMinDegreeWitness 49 7
```

The same three hypotheses give the drop statements, using the checked Boza
order-48 graph and the checked order-49 degree-six graph for the lower sides:

```lean
theorem minDegreeForC4_fortyEight_fortyNine_exact_of_externalEvidence
    (hOne …) (depth : Nat) (hSeven …) (hThreeOne : OrderFortyNineTripleCellExcluded 3 1) :
    minDegreeForC4 48 = 8 ∧ minDegreeForC4 49 = 7

theorem minDegreeForC4_fortyNine_lt_fortyEight_of_externalEvidence
    (hOne …) (depth : Nat) (hSeven …) (hThreeOne : OrderFortyNineTripleCellExcluded 3 1) :
    minDegreeForC4 49 < minDegreeForC4 48
```

A fourth statement takes the whole three-high stratum instead of the triple
cell. It is the socket for codex's eventual stratum theorem:

```lean
theorem not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence_threeStratum
    (hOne …) (depth : Nat) (hSeven …)
    (hThree : OrderFortyNineStratumExcluded 3) :
    ¬ C4FreeMinDegreeWitness 49 7
```

All four are in namespace `Erdos85`. `depth` is a parameter, not a hypothesis;
the H7 campaign uses `depth = 3`.

### How the strata are covered

`not_c4FreeMinDegreeWitness_fortyNine_seven_of_strata` splits on the number `h`
of degree-eight vertices, `h ∈ {1, 3, 5, 7, 9}`.

| `h` | Source in the capstone | Status |
|---|---|---|
| 1 | `orderFortyNineStratumExcluded_one_of_capacityInventory_checked hOne` | hypothesis `hOne` |
| 3, `t = 0` | `Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero` | proved (24 native parts) |
| 3, `t = 1` | `hThreeOne` | hypothesis |
| 5 | `Erdos85.H5.orderFortyNineStratumExcluded_five` | proved (40 native parts) |
| 7 | `orderFortyNineStratumExcluded_seven_of_structuralHsbEvidence depth hSeven` | hypothesis `hSeven` for the 28 structural `t = 0` cubes; the other `t = 0` cubes and `t = 1..7` are proved inside that theorem |
| 9 | `orderFortyNineStratumExcluded_nine`, used inside `…_of_strata` | proved (18 LRAT certificate checks) |

The two three-high cells are combined by
`orderFortyNineStratumExcluded_three_of_tripleCells`.

### Plugging in the H3 triple cell

Once `OrderFortyNineTripleCellExcluded 3 1` is a theorem, say `h31`, the
two-hypothesis statement is one line:

```lean
theorem … (hOne …) (depth : Nat) (hSeven …) : ¬ C4FreeMinDegreeWitness 49 7 :=
  not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence hOne depth hSeven h31
```

With a proved stratum `h3 : OrderFortyNineStratumExcluded 3` instead, use
`…_of_externalEvidence_threeStratum hOne depth hSeven h3`. In that route the
24 pair-part axioms enter through codex's stratum theorem rather than through
this module.

## The remaining hypotheses and their external evidence

| Hypothesis | What it says | External evidence | State |
|---|---|---|---|
| `hOne` | every table in the 13,351-row one-high capacity inventory has `OneHighFamilyV2CheckedUnsat` | `cake_lpr` receipts for the 13,351 orbits (goal #48: bank 12,094 + census) | campaign done; the checks ran outside the Lean kernel and are not admitted into Lean |
| `hSeven` | for each of the 28 cubes in `sevenHighT0StructuralCubes`, a checked `hsb<depth>` cover plus a checked refutation of every generated leaf | the H7 hsb certificate campaign (`h7_hsb_campaign_20261008`, depth 3) | pending |
| `hThreeOne` | no order-49 witness with three high vertices and one triple support | codex's native campaign on `erdos85/h3-triple-formal-20261007` (384 buckets) | pending; not finished at the time of this receipt |

The emitter that ties the checked CNF files to the Lean formulas is compiled
code, not a kernel proof. That caveat is unchanged by this module.

## Axiom inventory

Printed by `#print axioms` in jobs 546872 and 559961; the two jobs print
identical sets for the four capstone statements. Exact names per theorem are in
`axioms_by_theorem.json`. All non-standard axioms are `native_decide` axioms
(`…._native.native_decide.ax_…`), so these statements are not kernel-only.

| Statement | Axioms |
|---|---|
| `not_c4FreeMinDegreeWitness_fortyNine_seven_of_externalEvidence` | 217 |
| `…_of_externalEvidence_threeStratum` | 193 (= 217 − 24 pair parts) |
| `minDegreeForC4_fortyEight_fortyNine_exact_of_externalEvidence` | 223 (= 217 + 6 witness) |
| `minDegreeForC4_fortyNine_lt_fortyEight_of_externalEvidence` | 220 (= 217 + 3 Boza) |

The 217 axioms of the main statement, grouped by the ingredient theorem that
prints them. The ingredient sets are pairwise disjoint apart from the standard
three, and their union is exactly the 217.

| Group | Count | Names |
|---|---|---|
| Standard | 3 | `propext`, `Classical.choice`, `Quot.sound` |
| H9 certificate checks (inside the case split) | 18 | `orderFortyNineT2RepA_check`, `…T2RepB_check`, `…T3Rep0..4_check` (5), `…T4Rep0..10_check` (11) |
| H1 reduction natives | 23 | `oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_{zero,one,two,three,four}` (5), `oneHighPrunedEnumeratorComplete`, `enumerateOneHighTableValues_complete`, `oneHighStandardMate_even_pair` (4), `oneHighRelevantPairList_complete`, `…_nodup`, `oneHighRelevantPair_mem_tablePairs`, `oneHighInventoryRows_relevant_lt_five`, `oneHighFamilyV2LowerTablePairs_mem_bounds`, `oneHighFamily_xor_one_lt_eight`, `oneHighBranchEdgeIndex_eq_iff`, `…_lt`, `card_filter_oneHighCanonicalBranchAdj`, `finFive_exists_canonical_lex_perm`, `finFive_matchingBits_canonical`, `finEight_standardMate_canonicalize_marked` |
| H3 pair parts | 24 | `H3Pair.pairPart_24_00` .. `_23` |
| H5 parts | 40 | `H5.cellPartF_0_4_16_00..15`, `H5.cellPartF_1_6_16_00..15`, `H5.cellPartF_2_12_8_00..07` |
| H5 graph covers | 18 | `fiveHighCanonicalFiberCover_{zero,one,two}` (1, 1, 2), `fiveHigh_t{0,1,2}_mask_key_fiber_card` (1, 1, 2), `fiveHigh_t2_local_triple_card` (10) |
| H7 positive-triple certificates | 13 | `sevenHighT1Rep0_check`, `…T2Rep0..1`, `…T3Rep0..2`, `…T4Rep0..2`, `…T5Rep0..1`, `…T6Rep0`, `…T7Rep0` |
| H7 orbit cover (`t = 0` empty cubes) | 2 | `sevenHighT0CanonicalEmptyPermutationAction_table`, `sevenHighT0CanonicalEmptyRepresentative_orbit_cover` |
| H7 graph covers | 66 | `sevenHighCanonicalFiberCover_{zero..seven}` (28), `sevenHigh_t{0..7}_mask_key_fiber_card` (14), `sevenHigh_t2_local_triple_card` (14), `sevenHighT{3..7}TripleSet_member_card` (10) |
| H7 triple-system canonical forms and CNF semantics | 10 | `extend_{four,five,six}_linear_triples_canonical` (3, 2, 1), `fixed_first_three_linear_triples_canonical`, `fixed_first_four_linear_triples_canonical_packed`, `orderFortyNineDegreeBlocks_seven_nonzero`, `orderFortyNineH7HighPairs_ne` |
| **Total** | **217** | |

Per ingredient: case split with H9 21; H1 cover 26; H3 pair cell 27; H5 stratum
61; H7 stratum 94 (each count includes the standard three). The H5 and H7
totals match the earlier stratum receipts (61 and 94).

The drop statements add the lower-side witness axioms: `boza48Graph`,
`boza48Graph_common_le_one`, `boza48Graph_degree` (3), and for the exact
values also `orderFortyNineDegreeSixGraph`, `…_common_le_one`, `…_degree_ge` (3).

## Build

Both builds ran on the erdos85 cloud builder through `e85-remote build`.
Nothing was built on the Mac.

| Job | Commit | Target | Exit | Result |
|---|---|---|---|---|
| `20261008T135640-erdos85__order49-capstone-20261008-546872` | `c955257fbd9a` | `Proofs.Erdos85OrderFortyNineCapstone` | 0 | `Build completed successfully (9076 jobs)`, about 17 min |
| `20261008T141633-erdos85__order49-capstone-20261008-559961` | `70bd08e71df2` | `Proofs.Erdos85OrderFortyNineCapstoneAxiomAudit` | 0 | `Build completed successfully (9077 jobs)` |

Files here: `job-546872-capstone-tail.txt` and `job-559961-axiom-audit-tail.txt`
(log from the last module to the end, with the full axiom lists),
`job-546872-module-actions.txt` (every `Built` / `Replayed` line of job 546872).

### Build cache reuse

The H5, H3 pair and H7 certificate modules were not recompiled. Before the first
job, the branch volume `lean-build-erdos85__order49-capstone-20261008` was
created as a reflink copy of the `h7t0-formal` volume, followed by no-clobber
overlays of the `h5-formal` and `h3-pair-formal` volumes. The source volumes
were only read. Two checks came first:

- neither branch modifies a shared Lean source relative to the merge base
  `95588b1cad7` (each side only adds files; the only modified files are
  `lakefile.toml` and `docker-build.sh`);
- every `.olean` present in two of the three source volumes is byte-identical
  (182, 182 and 188 common files compared).

Reuse was then decided by Lake's own input traces. Job 546872 compiled 29
modules: 28 in the H1 cover chain, which was in none of the three volumes, and
the capstone. The longest were `Erdos85OneHighV2InventoryOrbitCheck` (622 s) and
`Erdos85OneHighV2Enumerator` (241 s).

### Resource note

The launcher gave the first container a 16-CPU quota (`--threads 6` sets only
`LEAN_NUM_THREADS`). I lowered it to 8 CPUs with `docker update` about two
minutes after the start, at 13:59 UTC. The second job ran for a few seconds at
the default quota and ended before it could be capped. Memory cap was 48 GiB in
both; the largest process I observed was about 7 GiB.

## Notes on how the pieces fit

- **H9 is not axiom-free.** `orderFortyNineStratumExcluded_nine` carries 18
  `native_decide` axioms from the `orderFortyNineT{2,3,4}Rep*` LRAT certificate
  checks. They enter every use of `…_of_strata`, including the paper's Result A
  socket.
- **Cell and stratum shapes match.** H1, H5 and H7 arrive as
  `OrderFortyNineStratumExcluded`; H3 arrives as two `OrderFortyNineTripleCellExcluded`
  cells and is combined by the existing `…_three_of_tripleCells`. No transport
  lemma was needed.
- **`OrderFortyNineVerifiedCertificateFrontier` was not used.** That structure
  asks for the eight seven-high cells `7 0 .. 7 7` separately, while the H7
  development delivers the stratum directly. The capstone therefore goes
  through `…_of_strata`, not through the frontier structure.
- The Ramsey-plateau corollary (`consecutiveC4StarPlateauAt_fortyEight`) is not
  restated here; it follows from the main statement in one line.
