# Cloud U1/R15 pilot, 8 October 2026 (UTC)

Status: **first run failed in consumer elaboration; no passing proof receipt**.
The job exited 1 at 02:31:46 UTC. Lake reports 5,859 seconds for the target
module. Its native rejection declaration was printed, but `no_joint` at line
21 exceeded the recursion-depth limit, so the entire module failed.
`first-run.json` and the complete `first-run.log` preserve that outcome.
This was neither a timeout nor an out-of-memory termination.

`ConsumerBaseline.lean` and `Consumer.lean` isolate the consumer with the
rejection as an explicit hypothesis. The proposed fix makes
`threeHighCrossDomain` locally irreducible, matching the existing search
soundness module. `check_consumer.py` checks that the baseline reproduces the
error and the proposed consumer compiles with standard axioms. These probes
do not evaluate or prove the finite rejection. Their cloud validation is
pending; no expensive retry or larger finite campaign has been queued.

The 5,859-second measurement includes both declarations and does not isolate
native search time. If every one of the 1,815 remaining pairs cost that much,
the arithmetic scenario would be 2,953.9 serial hours (369.2 hours at eight
ideal workers, 184.6 at sixteen). One pair does not justify that average, and
these idealized figures omit overhead and memory constraints.

`launch.json` identifies the existing six-hour native-check job, pinned source
commit, exact pilot source hash, and verified resource settings. It is a launch
record, **not** a successful proof receipt. At the recorded initial inspection,
the Docker container and dependency compiler processes were running.

Inspect the original job record:

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
