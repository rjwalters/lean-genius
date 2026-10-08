# H3 triple-cell completion engine

The conditional engine, bridge and split theorem compile with only
`propext`, `Classical.choice` and `Quot.sound`. This does not yet exclude the
triple cell: successful search results remain explicit premises.

Source commit: `8484794c2a96f41f6aee799c193a56c47bf8e292`.
Cloud build: `20261008T101350-erdos85__h3-triple-formal-20261007-402758`, exit 0.
Engine, Bridge and Split were freshly built in 9.7, 5.1 and 3.9 seconds.
`conditional-build/AUDIT.json` binds their exact sources, objects and four
axiom reports to the successful job. The read-only auditor checked the
objects twice, including modification times within the job interval.
Raw log/spec/exit and exact source snapshots are retained alongside it.

## Adaptation

The source is adapted from the completed pair engine at
`dc7f78d47d7017dcb8da5cc4aa200f1432a0f5df`. Namespace and module names are
separate. The support layout changes to the actual canonical representative
`threeHighRepresentativeMasks 1`: vertex 3 has mask 7; singleton supports
are 4–10, 11–17 and 18–24; empty supports are 25–48. Each colour fibre still
has eight vertices. All range guards and their supporting lemmas use the
new boundary 25. The rest of the search and soundness argument is unchanged.

The bridge proves the mask/colour equality directly with `decide +kernel`,
then derives an engine model and compatibility from the existing relation
constraints. `threeHighCanonicalGraphCover_one` transports representative
exclusion to `OrderFortyNineTripleCellExcluded 3 1`.

The unsplit interface is `tripleSearch = true`; the split interface requires
`0 < m` and every `triplePart m r = true` for `r < m`. Fuels are 70/30/40.
Fuel exhaustion and a completed candidate return false, so false alone is
not a satisfiability certificate. Neither hash injectivity nor balanced
parts is required by the composition theorem.

## Bounded diagnostic

`Probe384R0.lean` requests just `triplePart 384 0 = true` via `native_decide`.
It is outside the library's automatic module glob. `run_probe.py` stages it
under the Lean project root, checks the three prerequisite source/object
hashes, and limits its Lean process group to 300 seconds. Only the existing
cloud builder was used.

The diagnostic **timed out without a certificate**. Job
`20261008T101712-erdos85__h3-triple-formal-20261007-405471` ran at
`0be06607d7d5e176fa0c8f3abf040d191d4447ee`; its Lean child was killed and
reaped at 300.221 elapsed seconds, with 298.868 user seconds, 1.340 system
seconds and maximum RSS 6,451,688 KiB. Its compiler log is empty and no
`Probe384R0.olean` exists. The result remains unresolved.

The runner exits 124 after its five-minute timeout. The existing Docker
wrapper maps that to job exit 1 and prints its outer limit, “6m”, in the
timeout banner. That banner is not a six-minute runtime measurement.
`probe-evidence/` retains both layers' raw evidence and the read-only audit.
The audit verifies execution/source identity, absent certificate, removal of
the staged source, and unchanged prerequisite objects. The container and Lean
process were also observed absent after termination.

`probe-container-live.json` records the actual pinned image
`sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6`,
16 GiB hard memory limit, and two-CPU cgroup quota. The launch applied CPU
affinity `0,1` to `e85-host`, so its `nproc`-derived Docker quota was two.

This one censored sample does not estimate the whole route's cost or establish
that it improves on the census. No full campaign is authorized or launched by
this experiment, and the prior census route is unchanged.

## Phase-one-only follow-up

`PhaseOneOnly.lean` establishes `dfs1 (fun _ => true) 70 s0 = true` by
`native_decide`: every phase-one leaf is accepted without running phase two or
three. This is a traversal diagnostic and cannot imply graph exclusion.

Job `20261008T102436-erdos85__h3-triple-formal-20261007-410562`, execution
`94aab7d1b8baacb6e5b3c65c6ea319b65ebe89f6`, exited zero under a 60-second
inner cap. The compiler process finished in 4.970 seconds, including imports
and Lean startup, with 3.648 user seconds and 1.299 system seconds. Maximum RSS
was 6,485,932 KiB. The object hash is
`5f43898b6c353e3ed38c2c6c5d3006e85e212739b7d302c3a2672ba732076150`.
The theorem uses `propext`, `Quot.sound`, and its own
`phaseOneTraversal._native.native_decide.ax_1_1`; it is not standard-axiom-only.

`phase-one-evidence/` retains the exact source, runner, raw job records, inner
receipt, compiler log and read-only audit. The audit checks execution/source
identity, actual object hash, exact axiom set, unchanged prerequisite objects
and removal of the staged source. The job spec requests 16 GiB/two CPUs; no
live Docker inspection was captured for this short job. No isolation from
other workloads on this shared builder was enforced.

The result shows that the basic phase-one traversal can finish well within the
earlier cap. It suggests the expensive work is elsewhere, but the constant
callback also omits per-leaf hashing: this measurement alone does not isolate
hashing from phase-two/three search or measure bucket balance.
