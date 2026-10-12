# Safe-subset verification for #43756

The final invocation selected **5,939 Linux targets** and completed with exit **1**. Its only source failures were the two existing legacy modules, `BallotProblemOQ03OQ01OQ02Helpers` and `KonigsbergOQ01OQ02`. The Ballot helper also blocks its two consumers, `BallotProblemOQ03OQ01OQ02` and `BallotProblemOQ03OQ01OQ02Aristotle`.

All seven repaired modules compiled: Brouwer, non-coprime CRT, Erdos967, Minkowski, the Pascal derangement companion, and the two corrected AM–GM/binary-GCD imports. The Erdos679 cascade passed. Erdos18WIP01 passed an isolated build, and its Erdos46 small-divisor consumer compiled in the final invocation.

The tested source is `898252bfa8fc59b4e3b62584065f1b6b95233edb`, based on main `9019cca651249bff7ba4d0308486f40b4a48ca88`. See [final-summary.json](final-summary.json) for the proof-source tree, job identifiers and exact outcomes. Both broad runs use retained Lake project and pinned Mathlib caches.

| Check | Source | Result |
|---|---|---|
| Initial broad run, 5,940 targets | `f84fbaf4932` | Exit 1: legacy failures, two import-case failures, two OOM kills |
| Direct import-repair checks, explicit `lean -j1` | `b3b160fb697` | Both exit 0 |
| Isolated Erdos18WIP01, 110 GiB cap | `b3b160fb697` | Exit 0; 8,577 jobs; compiler time 1,134 seconds |
| Final broad run, 5,939 targets | `898252bfa8f` | Exit 1; only the two legacy source failures |

The final command was `bash scripts/build-safe-subset.sh` inside the pinned Linux container, with a 96 GiB memory cap and a 16-CPU quota. It invokes Lake once and preserves its failure status. [final-environment.txt](final-environment.txt) records the command, source, image and exit receipt; [targets.txt](targets.txt) is the selected manifest. The dependency audit found 5,944 reachable project modules, no missing imports and no path into an excluded module.

Six modules are explicitly excluded by [the runner](../../scripts/build-safe-subset.sh): Erdos728FactorialDivisibility, SpernerGrid, SpernerGridAristotle, BirthdayProblemOQ03OQ01OQ01, the declaration-free AngleTrisection import-all artifact, and Erdos30WIP01. The Mac's case-insensitive filesystem lists one fewer target: Git tracks both byte-identical `Erdos1WIP01.lean` and `Erdos1Wip01.lean`.

Erdos30WIP01 is a new resource quarantine tracked in [#43846](https://github.com/rjwalters/lean-genius/issues/43846). During the initial batch, its compiler reached about 81.4 GiB anonymous RSS and the kernel killed it and Erdos18 under a 110 GiB container cap. Erdos18 later passed alone and remains included. The newly started Erdos30 isolated retry was deliberately stopped after the quarantine decision; it has no completed standalone proof verdict. Its log contains the wrapper's generic exit-137 memory message, while [retry-cancellation.txt](retry-cancellation.txt) records the actual manual stop.

The wrapper forwarded `LEAN_NUM_THREADS`, but observed compiler parallelism exceeded the requested value. The final run makes no compiler-thread-limit claim. [thread-setting-observation.txt](thread-setting-observation.txt) records the environment, command and observed CPU use. The memory cap and CPU quota were enforced by Docker.

Full logs are retained as `*.log.gz`. [archive-content.json](archive-content.json) records their decompressed hashes; [manifest.json](manifest.json) covers every receipt file except itself. [history.json](history.json) preserves the failed initial checkout, resource adjustment, isolated checks and collection notes. The original raw artifacts remain at `/Volumes/Stripe/lean-genius/artifacts/main-safe-subset-43756-20261012/`.

The runner's two stub-Lake tests pass, including quarantine selection, one invocation, nonzero-status propagation and list-only mode. Shell syntax and diff checks pass. No local Lean build was run.
