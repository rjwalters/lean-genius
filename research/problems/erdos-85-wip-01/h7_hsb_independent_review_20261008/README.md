# Independent review of the H7 high-side symmetry clause proof

Status: **cloud build and eight axiom reports independently verified**.

Job `20261008T043722-erdos85__h7t0-formal-20261007-189071` passed at
`436d43bb4864c76641db3d8e13d02cac893151b1`. The fresh `HsbSound` target
compiled in 13 seconds. `audit.json` records exact committed/cloud source
hashes and independently read cloud object hashes for `HsbGen`, `RowKey`,
and `HsbSound`. `audit.log` preserves the full raw cloud log. Four `RowKey`
and four `HsbSound` theorem reports contain exactly `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx` or native axiom.

The reviewed proof minimizes seven row keys among all canonical completions
with the same empty-sector mask. The high-side relabeling stays within that
set, so a checked witness preserving earlier keys and strictly lowering the
last key contradicts minimality. No group law or comparison to the full
861-bit edge code is needed. Exact row cardinality and absence of duplicate
vertices turn the positive edges named by a clause into exact rows. The
checker also validates numeric bounds and the seven-label permutation.

The uniform statement covers arbitrary lists of witness-checked entries;
its generator is not assumed correct. The final exported theorem remains
conditional on UNSAT of the cube with those clauses. It neither supplies
that UNSAT proof nor certifies the complete leaf cover. The all-28-cube
Lean/Python byte-identity run is separate and was still running at this audit.
No complete H7 certificate campaign or H7 stratum exclusion is established.

Read-only review: no Claude-owned proof or generator source was edited.
