# Exact first-column decomposition of the H3 native search

Status: **five structural/conditional exports cloud-verified; diagnostic pending**.

`Proofs.Erdos85ThreeHighFirstColumnSearch` expresses the existing native pair
search as the Boolean OR over its complete static-pruned first-column list.
Each branch retains the first prefix check, all seven remaining DFS levels,
and the original distinct-neighbor terminal. It caches U/R and fixed degree
data, as the original search does.

The assembly theorem requires rejection of **every** first-column candidate.
A subset of completed branches cannot establish a pair rejection. The final
consumer retains the cross-domain and external-cap hypotheses. No concrete
branch, pair, or stratum rejection is supplied by this module.

The equality proof and four associated exports passed in an isolated cloud
branch, with only `propext`, `Classical.choice`, and `Quot.sound` and no `sorry`.
The running U1/R15 and Full261 jobs are unchanged.
This module enables smaller parallel proof units; no runtime improvement is
claimed until measured.

`Inventory.lean` and `check_inventory.py` prepare a separate cloud diagnostic
for U1/R15 and the four cases selected in `h3_varied_pilot_20261008`. They
enumerate static first-column candidates and record the first prefix gate
result for every candidate, encoded as a 15-bit mask. They do not run the
remaining DFS. These diagnostic sources are **awaiting cloud verification**.
The runner requires a fresh output directory and retains the complete compiler
log, candidate list, and source/object hashes; its PASS is a diagnostic result,
not a rejection certificate.

The initial theorem build, job
`20261008T030527-erdos85__h3-first-column-20261008-127474`, reached its 15-minute
limit during dependency compilation (exit 124), before the target module.
`first-build.json` and `first-build.log` preserve that result.

Job `20261008T032226-erdos85__h3-first-column-20261008-138766` continues from
the same build cache at commit `34bb24f5fb1`, using 16 GiB, one Lean thread,
and a 30-minute limit. It runs `check_inventory.py`, which first builds the
theorem module and then evaluates the inventory only if dependencies pass.
That job reached the target and failed its proof elaboration (exit 1): a
partially applied branch was not unfolded by `simp`, the generic congruence
tactic exhausted its heartbeat budget, and `List.any_eq_false` expected
non-truth rather than a Boolean equality to false. Its complete dependency
log and receipt are retained in `failed-inventory-first/`. No diagnostic ran
and no theorem result is claimed from the failed module.

The revised source unfolds the branch explicitly, uses a direct `congrArg`
proof, and converts the Boolean rejection to non-truth. Job
`20261008T033506-erdos85__h3-first-column-20261008-147034`, execution commit
`bd597a87fc2`, verified all five exports (target build 3.7 seconds). The cloud
source hash matches the local source, and the compiled object's hash was
read independently from the cloud build volume. `proof-pass.json` records
the verified proof result; `proof-pass-inventory-failed/` retains the full
dependency log and the separate diagnostic failure.

That diagnostic could not compile its `Finset.toList` encoding because the
operation is noncomputable. The diagnostic now folds over `List.finRange 15`
and tests membership, leaving the verified theorem source unchanged. This
diagnostic-only fix awaits a further cloud check.

`audit.py` independently checks a completed run's commands, logs, source and
object hashes, all five theorem axiom reports (standard axioms only), and
the complete diagnostic candidate lists against the compiler output. It is
read-only and does not run Lean. A synthetic valid receipt passed, while
altered candidate counts and a changed diagnostic object were rejected.
The real artifact audit remains pending.
