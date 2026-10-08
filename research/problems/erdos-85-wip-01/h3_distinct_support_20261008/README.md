# Distinct-neighbor support pruning

The library module `Proofs.Erdos85ThreeHighDistinctSupportSearch` compiled in
the repository Docker environment with four exported theorems, each using
exactly `propext`, `Classical.choice`, and `Quot.sound`. `RECEIPT.json` pins the
source, compiler log, toolchain, manifest, command, and axiom lists;
`compile.log` is the complete successful build output.

The previous strong search enforces same-color distinctness only after a
resolution family is selected. The new support pass removes a triple unless
every color, including its own, still offers a different compatible triple.
The filter preserves every strong family witness. A cached table applies
bounded passes with early stopping on equality; the preservation theorem
holds for every fuel value, without assuming that equality is reached.

The new terminal and pair search are sound: a false result excludes the
supplied U/R pair under the cross-domain and external-cap hypotheses. The
module does not assert a concrete rejection or replace the existing search
in the queued census connection.

`Pilot.lean` tries full U representative 1, compact code `(6,6,15)`, with R
representative 15. Its separate local Docker run reached the 240-second
timeout with exit 124 at 8 GiB and one Lean thread. No axiom report or rejection
was produced. `PILOT.json` and `pilot.log` retain this negative execution
result. No speedup was established. The longer cloud baseline was left
running unchanged.

The pilot is intentionally outside the `Proofs` library glob. It is an
uncompiled research target containing `native_decide`, not a proof receipt.
