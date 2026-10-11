# H3 pair cell: independent completion audit

**PASS.** The native-backed pair cell `(h,t)=(3,0)` is excluded by the two
compiled exports:

- `Erdos85.H3Pair.threeHighCanonicalRepresentativeExcluded_zero`;
- `Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero`.

Both raw axiom reports contain exactly `propext`, `Classical.choice`,
`Quot.sound`, and the 24 generated axioms
`Erdos85.H3Pair.pairPart_24_NN._native.native_decide.ax_1_1` for NN=00..23.
There is no `sorryAx`. This is a proof relying on compiled native evaluation;
it is not a standard-axiom-only proof or a proof of the remaining triple
cell `(3,1)` or the full order-49 drop.

The evidence spans two producer jobs:

| Producer | Source | Outcome |
|---|---|---|
| `20261008T081713-erdos85__h3-pair-formal-20261008-331716` | `b3545ac16ae75faa072a66400bedb087544a03bf` | All 24 native parts built; job exit 1 because the final Cell composition tactic reached the recursion limit. Its failed Cell reports contain `sorryAx` and are rejected. |
| `20261008T100037-erdos85__h3-pair-formal-20261008-394958` | `dc7f78d47d7017dcb8da5cc4aa200f1432a0f5df` | Exit 0; repaired Cell built in 3.7 seconds, with no native part rebuilt. |

The repair replaces the tactic that tried every part theorem on every case
with explicit pattern cases 0..23 and an impossible `n+24<24` branch closed
by `omega`. The exported statements and all 24 imported parts are unchanged.
The doc comment now names the actual native trust dependencies. The source
review found no weakened premise or additional trust assumption.

`audit_cloud.py` ran read-only on the existing builder. It checked terminal
statuses, both exact source commits, all 24 fresh part objects within the
native producer interval, and the final Cell object within its successful
producer interval. Engine/Bridge/Split sources and objects match the earlier
independent conditional-chain audit. Their source bytes and all 24 part
sources are identical across the two producer commits. All 28 objects and
current sources were checked again for stability at the end of the audit.
The two final raw axiom reports have the exact expected sets.

`AUDIT.json` records source/object hashes and the audit program hash.
`evidence/` retains both raw job logs/specs/exits, the prerequisite audit,
and the exact 28 source files. The final Cell object SHA-256 is
`e9a79924cce61c34e9ce46b74537e23180ee0518b6c5e42edea0dfc33a8e6e20`.
Objects remain on the builder. Raw historical bytes are preserved unchanged.
Reproduce the read-only audit while those sources/objects remain available:

```sh
python3 -B research/problems/erdos-85-wip-01/h3_pair_completion_review_20261008/run_terminal_audit.py
```

`container-live.json` records the original native container configuration:
image `sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6`,
32 GiB memory/swap limits and 16 hard CPU units, with six Lean workers.
The 24 reported per-part build durations sum to 31,238 seconds (range
838..2005 seconds). These are build elapsed times, not independently measured
aggregate CPU usage; they must not silently be relabeled as CPU-hours.

A duplicate isolated repair was prepared while the peer repair was already
finishing. Its source commit `5ee31bfcaa9c0e841d05214d6d587bb721d503bf`
is not the accepted implementation. The direct compiler refused the source
path outside its configured root before elaboration; exit 1, no output
object, and all 27 prerequisite object hashes unchanged. The attempted
container had read-only source/cache mounts and ran no native search.
`duplicate-repair-failure/` preserves that attempt's source, command, logs,
container records and input/object inventories; its exited container was
removed after retention. The source branch is left as an explicit historical
attempt, not a candidate to integrate. The successful peer repair above is
the sole accepted Cell result.
