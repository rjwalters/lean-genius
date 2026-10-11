# Concrete strong full-U block transport

The retained 55-entry block-permutation certificate now preserves
`ThreeHighDistinctJointWitness` at its 29 listed targets. Both new theorem
exports compile with only `propext`, `Classical.choice`, and `Quot.sound`:

- `FullUBlockOrbits.distinct_joint_transport` keeps the same specified target
  `target r`, cross-domain membership, and external block cap.
- `FullUBlockOrbits.distinct_joint_transport_to_targets` adds checked membership
  in the existing 29-element target set.

The check recompiles the retained `Full_3_3.lean` and `Certificate.lean`
byte-for-byte before compiling `StrongTransport.lean`. All eleven printed
exports (nine retained, two new) have standard axioms only. The three compiler
steps took approximately 11.0, 35.7, and 6.6 seconds, respectively, in Docker
with one Lean thread and an 8 GiB cap. `RUN.json` and the three full individual
compiler logs are retained; `RECEIPT.json` pins sources, toolchain, runner,
manifest, and command.

This is a concrete block-normalization result, not a finite exclusion or a
proof of full-U census coverage. The full and deficient coverage assemblies
still need to be connected to the strong actual-graph witness in their concrete
packages; full terminal/capacity pruning and all residual finite rejections
remain separate work. No H3 stratum exclusion is claimed.

## Reproduce

Use the repository Docker runner **with the cloud-builder command overrides**
(`LEAN_REPO_ROOT` and `LEAN_DOCKER_CMD`). The H3 branch's older runner does not
support those overrides; do not invoke that older script with the command below.
The exact runner used from the H7 worktree and its hash are in `RECEIPT.json`.
After the shared runner extension is integrated, that updated script can be
used from any checkout.

From the H3 repository root, set `runner` to the updated `docker-build.sh`, then:

```sh
LEAN_REPO_ROOT="$PWD" LEAN_NUM_THREADS=1 LEAN_MEMORY_LIMIT=8192 \
LEAN_BUILD_TIMEOUT=5m LEAN_SKIP_CACHE=true \
LEAN_DOCKER_CMD='lake build Proofs.Erdos85ThreeBlockCompactCodes Proofs.Erdos85ThreeHighBlockPermutationTransport Proofs.Erdos85ThreeHighDistinctBlockPermutationTransport && lake env python3 ../research/problems/erdos-85-wip-01/h3_strong_block_transport_20261008/check.py --output /workspace/research/problems/erdos-85-wip-01/h3_strong_block_transport_20261008/_build/recheck' \
"$runner"
```

The output directory must be new. Compilation is sequential; the script stops
on any compiler failure, unexpected export count, or nonstandard printed axiom.
The original measured run reused an already-built compact-code dependency;
the reproduction command lists that dependency explicitly for a fresh cache.
A cold dependency build may require a longer cap. Do not run the checker with
host Lean on the Mac.

The intended next full-branch integration uses this strong transport when the
U representative changes. Later terminal and capacity exclusions may consume
`hJoint.forget _` while retaining the strong `hJoint` at that representative.
