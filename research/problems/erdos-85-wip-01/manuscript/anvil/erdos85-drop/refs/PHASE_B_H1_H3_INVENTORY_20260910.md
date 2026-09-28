# Phase B H1 and H3 input inventory

Snapshot: 2026-09-10 19:36:19 UTC, codex-sol-1. This is the H1/H3 contribution to the combined survivor inventory. It does not authorize or launch solving. H3 is computationally excluded by the reviewed paper reductions and exhaustive Python searches; its SAT roots are independent cross-checks. Erdős 85 remains open.

## H1 exact conservative remainder

The frozen candidate list in `phase_b_h1_h3/h1-frozen-candidates.json` contains **1,257 distinct tags**, with profile counts **[283,346,388,198,42]**. Every tag and profile joins to the retained 13,541-row raw compact inventory, and all candidates belong to the 13,351-row capacity-filtered universe. Each candidate includes the 24 table values needed for canonical generation.

The set is the capacity universe minus 11,954 previously screened rows whose positive-size objects are still present, minus 140 additional rows with fresh producer-success ledgers and present objects. The 140 include 127 ordinary uploads and the 13 documented multipart rescues. Status, exit 20, trim verification, compaction success, positive recorded sizes and nonempty SHA-256 fields were checked. This is producer screening; uploaded certificates were not downloaded or kernel-checked in this pass. The previous 11,954 use the September 8 audit's ledger classification, not fresh validation of all their bytes. The three historical object conflicts remain in the candidate set. The approximate 1,290 planning count is superseded for this snapshot.

Remote access was read-only: paginated object listings and GETs of 1,355 candidate ledger rows. Raw ledger text and its hash, object metadata, source audit hash and compact inventory hash are retained. Counts alone are not a launch manifest or proof of exclusion.

An exhaustive filename scan of the local SAT artifact tree found 1,720 CNF paths involving **222** candidate tags. **1,035** tags had no named local CNF in that tree. Multiple paths include cores, refinements and pinned variants. None is accepted as canonical from its filename. `h1-cnf-paths-by-tag.json` is a location index only; no content-hash or semantic-equivalence claim is made for it.

Canonical generation uses `Erdos85OneHighV2CnfEmit.lean` and `Erdos85OneHighV2Cnf.lean`; source hashes and last-change commits are in `phase_b_h1_h3/RECEIPT.json`. The CLI is `v2cnf emit <profile> <table-file>`, then `v2cnf check <profile> <table-file> <cnf-file>`. Table files must contain `[[[c,j],count],...]`, not a flat 24-value array. Use the ordered pairs c<j with j != (c xor 1), omitting zero values. The integration worktree currently has no built `proofs/.lake/build/bin/v2cnf` executable. Executable provenance, generation, clause comparison and actual CNF hashes remain required before these rows can be dispatched. A bounded just-in-time input stage avoids storing the whole queue on the nearly full host.

## H3 independent solver inputs

`phase_b_h1_h3/h3-inputs.json` lists the two existing canonical base CNFs, covering the pair and triple support profiles without historical scout pins. Each has 29,500 variables, 1,328,183 clauses and 29,197,952 bytes. Fresh streaming hashes and line counts match the retained generator manifest:

| Input | SHA-256 |
| --- | --- |
| h3_t0.base.cnf | 03db81d188dc330673b3be0fbb81a1254cb5c14b676f7dc9c4ad44950898541b |
| h3_t1.base.cnf | db6e30ad7583317af975d5be49a3ed6ed3b2f7e327a6c98d75434180fa59ea5a |

The generator is `sat49/generate_small_high_canonical_cnfs.py`, last changed at `ecd4d3ec203753d1a6cb9967c0497b78d1d37969`; its current hash is retained with each input. Current source was inspected, but these files were not regenerated this pass. The local default Python lacks `pysat`. These broad roots are suitable cross-check inputs once joined with the host plan's caps and solver identities. No SAT verdict is claimed.

## Remaining preparation

Join this subsection with sol-3's H5/H7 inventory and sol-2's host plan. Complete canonical H1 materialization and freeze each CNF hash before dispatch; resolve the three historical conflicts separately if their removal is desired. Preserve UNKNOWN on resource caps and use no proof-output arguments. No solver process, new worktree or artifact above 100 MB was created by this inventory pass. H3 kernel enumeration stays parked at the banked full261/deficient1554 state.
