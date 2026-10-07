# Making the order-49 upper bound fully machine-checked: scoping (2026-10-07)

Goal (Robb): every step a Lean proof or a cake_lpr certificate. Desk estimate by a read-only scoping agent; nothing compiled.

I estimate H7 t=0 is the cheapest place to start, H3 is in the middle, and H5 is clearly the most expensive. I did not compile anything, so every effort figure below is a desk estimate.

Paths: R = `/Volumes/Stripe/lean-genius/erdos85-certpilot/research/problems/erdos-85-wip-01`, L = `/Volumes/Stripe/lean-genius/erdos85-certpilot/proofs/Proofs`.

## Key finding (H7)

The 14 certified cubes in `R/sat49/h7-empty-cube-certified-receipts.tsv` are F6 {0,1,3,4,6,7,9–13} and F7 {1,7,12}. All 14 lie among the 15 classes that the counting argument already excludes (`R/Q7_H7_UNIVERSAL_SINGLETON_CAPACITY_20260910.md`). So the 29 unsolved cubes are exactly the 28 structural roots plus one counting class, **F6_t2**. The solver closes the cubes the counting argument handles and stalls on the ones that need the structural arguments.

## H3 (2 cells)

**(a) Steps**
- **Triple profile.** The six neighbours N form a matching with m ∈ {1,2,3}. The secondary edge count r is 3 or 4, leaving 5 (m,r) branches. Exact covers by singleton neighbourhoods follow, then a check that each ordinary singleton has a neighbour of every high colour. Python: 3,337 U/R cases, 3.67e9 candidate extensions, 863,416 completed graphs, all rejected.
- **Pair profile.** The three pair vertices induce a matching with b = 0 or 1. Lemmas needed: the special singletons x_(i,a), the matching structure among the ordinary singletons, and the normalization (medium, mostly relabeling). Then 36 cores × 27 hosts = 972 cases and 75 × 48 = 3,600 cases, about 13.6M search nodes in total. That is fine for `native_decide`, far too big for `decide`.

**(b) Already in Lean**
- **Triple: the reduction is essentially finished.** About 90 `L/Erdos85OrderFortyNineThreeHighTriple*.lean` files (around 6.8k lines) plus about 110 `L/Erdos85ThreeHigh*` search files. The endpoint is `threeHigh_triple_excluded_of_terminal_certificates` in `L/Erdos85OrderFortyNineThreeHighTripleTerminalCertificate.lean`. Its only open premises are `hsound` plus two universal Boolean searches, `hfull` and `hdeficient`.
- Two single completions are already kernel-checked (`R/exact_cover_terminal_canary`, `R/joint_terminal_canary`).
- The orbit reductions (55 and 370 representatives) exist only in Python (`R/compact_u_orbits`).
- **Pair: nothing beyond the graph cover** (`...ThreeHighOneFiber.lean` / `ZeroFiber.lean`).

**(d) Effort**
- **Triple:** pick an `accept` function and prove `hsound` (the generic selected-cover theorem exists), roughly 300–600 lines. Then `native_decide` the two searches. Python finished these, so compiled Lean plausibly can too. Main risks are runtime and the missing Lean orbit transport.
- **Pair:** roughly 25–40 lemmas, 2.5–4k lines.

## H5 (3 cells)

**(a) Steps**
- The heavy-core census uses the BC=J, C1=7−t and Ct=5 identities. Cores have at most degree 2, no triangles and no C4. It gives 1,665 / 249 / 13 cores for T0 / T1 / T2 (`R/q7_h5_heavy_core/README.md`).
- **T0:** 1,665 → 761 host-compatible → 14 singleton-compatible. 13 of those fail an empty-layer search; the last needs a counting argument (20 incidences required, at most 19 allowed).
- **T1:** 249 → 211 → 10 → 0.
- **T2:** 12 cores fall to the census chain. The last, core44, splits into 92 branches handled by about 13 bespoke packages (`R/q7_h5_t2_core44_*`).
- Each finite stage is `native_decide`-sized, but each stage needs its own soundness proof.

**(b) Already in Lean:** only the labeling, triple normalization and CNF semantics (`L/Erdos85OrderFortyNineFiveHigh*.lean`). I found no heavy-core or census formalization.

**(d) Effort:** the largest of the three, roughly 60–100 lemmas and 6–10k lines. The 92-branch core44 accounting is the main risk.

## H7 t=0 (43 cubes)

**(a) Steps**
- The 15 counting exclusions use the bound |X| ≥ 35−4a, the per-vertex capacity c(v) = 7−2d(v), and one vertex-subset certificate per class.
- The 28 structural roots rest on long chains:
  - C7: 1.53M endpoints.
  - F14: 2.28M host leaves and 445,699 certificates.
  - a9: 2,640 + 480 cases.
  - a6/a7 depend on enumerator audits.
- Formalizing all of these is very large.

**(b) Already in Lean**
- `sevenHigh_t0_vertex_subset_exterior_capacity_inequality` (`...SevenHighT0ExteriorCapacityInequality.lean`) is the exact graph-side inequality the counting argument needs.
- Also present: the singleton/pair capacity files, `SixEdgeCubicBound`, `SevenEdgeCubicClique`, `EmptyEdgeNine`, and the stabilizer lex normal form (`...CanonicalEmptyStabilizerLex.lean`).

**(d) Effort:** F6_t2 by counting needs about 150–250 lines. The capstone currently accepts only LRAT evidence per cube, so it needs a variant that also accepts a semantic exclusion.

## (c) Hybrid route infrastructure

**Exists:**
- `cnfWithUnits` and the two-cube cover (`L/Erdos85CnfCubeCover.lean`).
- `cnfWithSignedUnit`, `cnf_unsat_of_binaryUnitSplit` and `CnfBinaryCheckedTree` (`L/Erdos85CnfBinarySplit.lean`).
- `SevenHighT0CanonicalEmptyCubeLratEvidence`, which accepts direct, binary-split or binary-tree evidence per cube.
- The 7×8 small-high grid (`...SmallHighCubeCover.lean`, `...SmallHighCubeGridTerminal.lean`).
- The Lean-exact emitters: `R/h35_probe_20261007/EmitCanonical.lean` and `...SevenHighT0CubeCnfEmit.lean`.

**Missing:** a generic "base CNF plus proven extra clauses" adapter. The adapter itself is easy (about 50 lines). Each fact also needs a proof that the graph-derived assignment satisfies its clauses, about 100–300 lines per fact, using the variable map in `...CanonicalCnfSatisfaction.lean`.

**Best candidate facts:**
1. Capacity bounds: each singleton has at most 2 empty neighbours, each pair vertex at most 1. These are plain clauses with no auxiliary variables, and are already proved in Lean.
2. The forbidden-pair rule (X ⊆ F).
3. Lex-leader symmetry breaking from StabilizerLex. Comparator clauses need auxiliary variables.
4. The bound |X| ≥ 35−4a. A cardinality encoding needs an extension lemma.

**Risk:** the base CNF may already imply facts 1 and 2. If so, adding them as clauses gains little, and the real speedup has to come from symmetry breaking or cubing. The H3/H5 cells (about 29.5k variables, 1.33M clauses) all returned UNKNOWN in the 30-minute probe (`R/h35_probe_20261007/README.md`).

## Ranked recommendation

1. **H7 F6_t2 plus the mixed-evidence capstone variant.** About 1–2 days of work, no new solver runs, and it brings H7 to 15 of 43 cubes closed.
2. **H7's other 28 cubes as cube-and-conquer binary trees checked by cake_lpr.** The 232-leaf adaptive queue already exists. If leaves stall, add the capacity and lex-leader clauses through the new adapter. All the plumbing exists except the adapter.
3. **H3 triple by `native_decide` on `hfull`/`hdeficient`.** The reduction is already proved, so this is mostly a runtime pilot plus the `hsound` proof.
4. **H3 pair by core normalization lemmas plus `native_decide`** (972 + 3,600 cases), or by SAT with symmetry-breaking clauses.
5. **H5 by SAT cubes** (the current `R/h35_pilot_20261007` plan, deeper than the 7×8 grid) with lemma clauses. A full structural formalization (the 92 branches) is the last resort.

If all of this works, the order-49 upper bound would rest only on Lean kernel proofs, `native_decide`, and cake_lpr checks of formulas produced by the Lean emitter.
