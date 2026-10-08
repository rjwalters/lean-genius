# H5 stratum assembly: source review and completion inventory

The source assembly at `99bc3e3413008ca13d5efb29bee5e855af961976` has the
intended coverage. `prepare_inventory.py` checked all 44 source modules
against that Git pin and produced `inventory.json`. This is a static source
review, not a compilation or computational exclusion result.

| Representative | Prefix parameter | Modulus | Residues |
|---|---:|---:|---|
| T0 | 4 | 16 | 0 through 15 |
| T1 | 6 | 16 | 0 through 15 |
| T2 | 12 | 8 | 0 through 7 |

Each part contains exactly the expected `cellPartF c k m r = true` theorem
proved by `native_decide`. Each representative module imports all and only
its parts, exhaustively selects their theorems, and supplies the resulting
universal premise to the reviewed H5Fast soundness bridge. The impossible
remaining indices are discharged by their bounds.

The stratum module pairs each representative exclusion with
`fiveHighCanonicalGraphCover_all` at the same index, producing the three
`OrderFortyNineTripleCellExcluded 5 t` conclusions. Its final theorem supplies
all three representative exclusions to
`orderFortyNineStratumExcluded_five_of_representativeExclusions`. That theorem
uses the graph cover and existing five-high triple-count bound to conclude
`OrderFortyNineStratumExcluded 5`: there is no C4-free graph on `Fin 49` with
minimum degree at least seven and exactly five high vertices.

No assembly mismatch was found. The graph-side definitions and consumer
chain were inspected in `Erdos85OrderFortyNineSmallHighCanonicalCapstone`,
`Erdos85OrderFortyNineStrataCapstone` and
`Erdos85OrderFortyNineFiveHighTwoFiber`. This review does not independently
reprove all imported graph-cover lemmas.

## Completion audit still required

The producer is job
`20261008T112746-erdos85__h5-formal-20261008-455708`. At preparation time it
was still running. The inventory names every expected new native axiom and
the exact source hashes. It also records the required terminal checks:
authoritative success, all fresh objects, source/object provenance and the
printed axiom sets. It supplies no completion credit by itself.

The three representative conclusions should use precisely the standard
axioms plus their own 16, 16 or 8 search-part axioms. The four graph-side
conclusions additionally inherit native evaluation from the older graph
cover, including finite mask/fiber calculations. Those dependencies need
explicit review when their printed lists become available. Do not accept
arbitrary extra assumptions or equate “40 search parts” with “40 total native
axioms” for the stratum theorem.

The prior independent conditional reviews are in
`../h5_engine_review_20261008/` and `../h5_fast_review_20261008/`.
No H5 representative or stratum is marked complete by this directory.

To reproduce the static inventory (no Lean execution):

```sh
python3 -B prepare_inventory.py /path/to/erdos85-h5
```

The command checks the current files against the execution pin, validates
the generated proof shapes and assembly coverage, and refuses to overwrite
a different inventory.
