# H3/H5 cake_lpr feasibility probe (2026-10-07)

Question: can the five H3/H5 cell formulas consumed by
`not_c4FreeMinDegreeWitness_fortyNine_seven_of_smallHighLratChecks`
be certificate-checked by cake_lpr in a reasonable time on this Mac?

Answer: **not by monolithic solving.** All five Lean-exact cells and one h5 cube
returned UNKNOWN at a 30-minute CaDiCaL 3.0.1 cap. No proof-logged run was
started, so no cake_lpr certification exists and no paper claim changes.

## Lean-exact formulas

`EmitCanonical.lean` prints
`orderFortyNineGeneratedCanonicalSatCnf 3 (threeHighRepresentativeMasks i)` (i = 0, 1) and
`orderFortyNineGeneratedCanonicalSatCnf 5 (fiveHighRepresentativeMasks i)` (i = 0, 1, 2)
in Lean clause order, with Std.Sat variable v written as DIMACS v+1. This is the exact
inverse of `dimacsClauseToSatClause` and the same convention as
`artifacts/.../h3-lean-exact/EmitScout.lean`. `emit_lean_exact.sh` runs it with
interpreted `lake env lean --run` in the pinned image `lean4-arm64:v4.31.0`
(`sha256:a5ca6c4e…6dff6`), using the docker-build.sh mounts, `--network none`, 16 GiB
and 1 CPU. Each cell took about 25 s. The dependency modules were first built with
`docker-build.sh` (16 GiB).

| cell | vars / clauses | sha256 (Lean-exact) | relation to older files |
|---|---|---|---|
| h3 t0 | 29500 / 1328183 | `b5d073a8…5d327` | **byte-identical** to `small-high-canonical-audit/h3_t0.base.lean.cnf` |
| h3 t1 | 29500 / 1328183 | `70b66d68…738ba` | **byte-identical** to `small-high-canonical-audit/h3_t1.base.lean.cnf` |
| h5 t0 | 29632 / 1328618 | `02ccdc18…cebf9` | same clause multiset and IDs as `h3-lean-exact/h5_t0.lean-emitted.cnf` (Aug 16), different order |
| h5 t1 | 29632 / 1328618 | `078a3618…51e5` | same clause multiset as Aug-16 `h5_t?.lean-emitted.cnf`, different order |
| h5 t2 | 29632 / 1328618 | `186f6e20…c5df` | same clause multiset as Aug-16 `h5_t?.lean-emitted.cnf`, different order |

The Python `*.base.cnf` files use a different variable numbering. They are not the Lean
formula: 294,686 clauses differ between Python and Lean h3_t0 as sorted multisets.
An LRAT proof must be produced against the Lean-exact files above, because clause IDs
depend on clause order. Full hashes are in `receipts/lean_exact_SHA256SUMS`.
The CNFs themselves live at
`/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/h35-probe-20261007/lean/`.

## Plain difficulty probe (CaDiCaL 3.0.1, no proof, 1800 s cap, at most 2 concurrent)

| run | result | conflicts in 1800 s |
|---|---|---|
| h3 t0 (Lean-exact) | UNKNOWN | n/a (quiet log) |
| h3 t1 (Lean-exact) | UNKNOWN | n/a (quiet log) |
| h5 t0 (Lean-exact) | UNKNOWN | 22.6 M |
| h5 t1 (Lean-exact) | UNKNOWN | 20.4 M |
| h5 t2 (Lean-exact) | UNKNOWN | 18.8 M |
| h5 t0 + cube {232, 277} (one of the 56 positive cubes of `Erdos85OrderFortyNineSmallHighCubeCover`) | UNKNOWN | 19.3 M |

Receipts are in `receipts/plain_results.json`. The solver logs are in
`artifacts/.../h35-probe-20261007/plain/`.

Prior evidence agrees. In August, kissat ran for 12 h on each of the four Lean-exact
H3 scouts (b1, c1, c2, dist2) and returned UNKNOWN every time
(`artifacts/.../h3-lean-exact/search/*.kissat.log`). Those scouts are *more*
constrained than the H3 bases, because each carries 84 to 108 extra geometry pins.

## Recommendation

Do not certify now: no cell is within reach of a single solve-and-check on this host.
A cake_lpr upgrade for H3/H5 needs cloud cube-and-conquer that is deeper than the
existing Lean-proved 7x8 two-unit cover. At least one of those cubes is itself over
30 min. The cost cannot be estimated responsibly until a pilot finds a cube depth at
which leaves solve in minutes. The suggested next step is a bounded split pilot on one
h5 t0 cube, for example CaDiCaL/march lookahead to depth 8 to 12, with about 20 leaves
on one cloud box. Any resulting cubes would also need a Lean cover theorem, as the
7x8 grid has, before certificates could feed the `index ≤ 1` / `index ≤ 2` sockets.

`cert_cell.py` is the ready-to-use streamed CaDiCaL to FIFO to cake_lpr wrapper. It
reuses `h1_cert_full_20261001/cert_row.solve_and_check`, uses an 8000 MB heap, and
tolerates EPERM on unlink. It was not run.
