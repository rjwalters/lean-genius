# H1 input materialization pilot

The source-pinned interpreted command `lake env lean --run Proofs/Erdos85OneHighV2CnfEmit.lean emit 2 TABLE` reached its 120-second cap with zero output bytes for tag `003597af8a184e9f`. It did not produce a canonical CNF. PID70666 was independently checked absent after the runner returned; no orphan remains. The pilot created no solver process.

Source closure pins identify132 local Proofs modules and32 external imports, plus Lean toolchain and lake manifest; this is source inspection, not a fresh dependency build. The imported V2Cnf olean existed. No native v2cnf executable was found at standard build locations in the local worktrees. At the end of the interpreted attempt, a native emitter with verified provenance and a successful exact-byte pilot was still needed; the successful native attempt below resolves that pilot requirement. Do not dispatch the zero-byte result or infer an UNSAT verdict from this generation timeout.

## Successful native route

The existing ARM Linux emitter at `/Volumes/Stripe/lean-genius/artifacts/erdos85-sat49/campaign-20260825.noindex/h1fleet/v3freight-rebuild-20260905/stage/freight/v2cnf` hashes to `4bd9604c6d670ad65a8ca332a26dbf35132418634a3b0678c177c8b2cfff4bf6`, the previously pinned producer/conflict-check emitter identity. It was bind-mounted read-only into existing image `sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6`, with no network, read-only root, one CPU and8GiB limit. No binary/image copy or build occurred.

Emission returned0 in7.48s and produced12,454,143bytes. SHA256 `63ba3e99aa19f2ad56784f704afee5569808af699cd88d31a8ca54634e2e6f69` exactly matches the historical producer CNF for the selected unresolved tag. Native check returned0 in5.78s with `MATCH (610424 clauses, top 40944)`. Separate strict line parsing verified one header,610424 clauses,40944 variables, all literal bounds and terminators, and zero empty clauses. The header agrees with MATCH. The named container was independently confirmed absent after both runs.

The CLI parser ignores headers and empty clauses, so MATCH alone is insufficient for arbitrary historical files. The queue materializer must use strict DIMACS validation plus expected-count/header agreement and bind the actual emitted hash before dispatch. This single pilot establishes a working bounded route, not a throughput guarantee for every profile or a fresh rebuild of the binary from the current source closure. The12.5MB CNF remains in the private pilot directory; only small receipts/scripts are staged here. No SAT solver ran.

Review1992 independently passed the retained native input, tag/table/profile joins, emitter/image identities and strict clause framing. The native pilot script did not enforce a file-size cap:12.45MB is an observed output size, not a reusable99MB limit. The queue materializer must enforce its own output cap. This script records a one-input experiment only.
