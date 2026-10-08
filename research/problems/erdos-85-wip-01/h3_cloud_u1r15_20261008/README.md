# Cloud U1/R15 pilot, 8 October 2026 (UTC)

`launch.json` identifies the existing six-hour native-check job, pinned source
commit, exact pilot source hash, and verified resource settings. It is a launch
record, **not** a successful proof receipt. At the recorded initial inspection,
the Docker container and dependency compiler processes were running.

Poll this job before taking any further action:

```sh
e85-remote status
e85-remote logs 20261008T004436-erdos85__h3-triple-formal-20261007-42449
```

The cloud job is detached; a disconnected local log follower does not stop it.
Do not restart because a log observation times out. Inspect this same job and
its container. Once it actually terminates, retain its exit status, source
commit, complete relevant log, and printed theorem axioms as a separate result
record. The native rejection, if established, must be distinguished from the
standard-axiom structural lemmas. No full H3 exclusion follows from this one
pair alone.

The copied pilot exists only in the disposable remote worktree. The local
library's default build glob still contains no unchecked finite-pilot module.
