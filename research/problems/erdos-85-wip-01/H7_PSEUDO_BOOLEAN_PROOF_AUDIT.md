# H7 native pseudo-Boolean proof-system audit

Date: 2026-08-26.  Node: the 29 missing parents in the canonical H7/T0
finite terminal.  This was the bounded test selected independently by two
submissions in squad divergence round 72.

## Exact lift

`sat49/check_h7_t0_pseudo_boolean.py` emits the original graph constraints,
not a translation of the sequential-counter CNF:

- 861 Boolean variables, exactly the canonical low-low edge variables;
- 42 native degree equalities (targets 7, 6, and 5 by low-vertex role);
- 687,260 direct C4 inequalities, one for each surviving four-edge witness;
- 21 unit inequalities fixing the selected empty-sector graph.

Thus every OPB model is exactly a model of the corresponding canonical
parent and conversely.  The direct C4 count agrees with
`check_h7_t0_canonical_completion.build_cnf`; the edge order, fixed support,
and representative masks are imported from the reviewed canonical scripts.

The two emitted probes each have 861 variables and 687,323 input
constraints:

| parent | role | OPB SHA-256 |
|---|---|---|
| F7/t7 | independently certified UNSAT control | `0c1213209a8b41662b75d7b568d07fa9fb752bfece899e55e3c26b7aa5d3f5ee` |
| F6/t2 | missing hard parent | `39aa64bda1cfd93f7d0f0539e22f9054655158e24c27cd375603a423d8fbb1f2` |

The adapter's exhaustive four-variable clause test, five-variable equality
test, and full-parent shape test all pass.  RoundingSat also parses the
emitted control directly.

## Proof-producing solver probe

Solver: RoundingSat 2, master commit `5ade61f`, Docker image digest
`sha256:b037bed1249c0bc42cf7d77f64de8ddde40b33e066961f73cf6480b93cb13a4f`,
with `--proof-log`.  The decisive run used the exact hash-bound F7/t7 OPB
above, `--lp=0`, and a 60-second external limit.  The host is arm64 and the
published image is amd64, so the timing includes emulation; only the
qualitative control outcome is used.  It returned `UNKNOWN` after 413,520
conflicts, 528,626 decisions, and 10,721,544 propagations.  A separate native
arm64 build independently reached the same control verdict at 60 seconds
(914,287 conflicts, 1,315,000 decisions, about 19 million propagations),
leaving a 180 MiB unfinished proof log.

The hard F6/t2 parent was deliberately not run with the canonical adapter:
the predeclared gate required the certified control to solve and replay
first.  An earlier syntactically different but semantically equivalent
direct-OPB scratch encoding left both control and hard parent unknown; those
numbers are excluded here because they are not runs of the banked emitter.

Because the already-certified control did not finish, there was no completed
proof to replay with VeriPB.  Unfinished searches are not evidence and do
not enter the H7 manifest.

## Verdict

**CUT as an H7 root mechanism.**  Native cardinality/cutting-planes search
does not produce even the required qualitative control separation under the
bounded test.  There is no basis for a parent sweep or configuration search.
The emitter is retained as a reproducible exact proof-system boundary: a
future genuinely new PB inequality or symbolic cutting-planes derivation can
be tested without rebuilding the graph semantics, but running RoundingSat on
the raw system is not such a mechanism.  The certified baseline remains
14/43, with 29 parents missing.
