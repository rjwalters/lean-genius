# q9 semiregular CNF encoding audit (claude, 2026-09-11, board #39 / editor 50462 "audit")

Independent audit of the CNF instances the q=9 existence experiment solves (sol-1 generator
`/private/tmp/erdos85-sol1-q9-semiregular/generate.py`, sha cafc2195…; earlier semantic review 2138 by sol-2;
byte preflight by sol-2). Shares no code with the generator, the 2138 checker or the runner.

## What `encoding_audit.py` checks, per instance directory (graph.cnf + map.json)

1. sha256 of graph.cnf equals map.json's `cnf_sha256` and, when given, the launch ledger / preflight sha.
2. The orbit decomposition of the n(n−1)/2 unordered vertex pairs under residue translation
   t ↦ t+1 (vertex = block·m + residue) is re-derived from scratch and compared with map.json's
   orbit list: every pair exactly once, correct block pair and shift, within-block shifts d and −d
   merged, antipodal shift m/2 handled.
3. Every non-primary variable is recovered as a Tseitin gate z ↔ (a ∧ b) from the three clauses
   (¬z∨a), (¬z∨b), (z∨¬a∨¬b), any sign pattern (OR gates appear as ANDs of negated inputs); each
   non-primary variable has exactly one defining gate and gates are topologically ordered, so every
   assignment of the edge-orbit variables has a unique extension — the CNF is functional in the primaries.
4. Non-gate clauses are classified into the degree family (exactly one unit output clause per vertex
   block) and the C4 family (forced-false repeated conjunctions and the sequential at-most-one clauses).
5. Many primary assignments are evaluated through that extension and compared, per family, with an
   independent graph oracle (build the n-vertex graph from the true orbits; minimum degree ≥ d; no
   pair of vertices with two common neighbours): random assignments at densities 0.03–0.5,
   greedy maximal C4-free invariant graphs, ± one-orbit mutations of those, and the solver witness model
   when a solver.log is present. Any disagreement between a family's clauses and the oracle's verdict
   for that property is a MISMATCH.

## Results

See `pins.json` for the audited paths, CNF/map shas and per-log shas, and the `audit_*.log` files for
the full JSON report of each instance (all report `mismatches: 0`, `orbits_match_rederivation: true`,
`every_nonprimary_has_gate: true`, `degree_outputs_equal_block_count: true`). Both constraint
families are exercised positively in every instance (dense assignments satisfy the degree clauses;
greedy C4-free graphs satisfy the C4 clauses) and negatively (low-density and mutated assignments).
The N48/m24 control additionally: the kissat model satisfies all 13,047 clauses, decodes to the archived
adjacency.json, and that graph is 7-regular, C4-free, with a free Z24 residue action.

## Scope

This audit supports the ENCODING: an UNSAT verdict on one of these instances means "no C4-free graph on
N vertices with minimum degree ≥ d invariant under a free Z_m residue translation", and a SAT model
decodes to such a graph. It does not turn a proof-logging-OFF solver UNSAT into a checked certificate;
such a verdict remains a solver report. No solver was launched, no queue or ledger touched.
