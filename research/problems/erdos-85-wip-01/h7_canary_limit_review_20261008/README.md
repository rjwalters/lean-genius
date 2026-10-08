# H7 canary batch-limit race: reproduction and proposed patch

The worker at H7 commit `f995bd5f7a417dce8d7ea8d6e694b31f95120e45`
checks `done + len(active)` under a lock, then releases the lock before its
store calls. A slot is only added to `active` after it claims a batch. Multiple
slots can therefore pass the bound while their claims are still pending.

The retained test reproduces this using the exact `slot_loop` function AST and
a mocked delayed store: two slots with `max_batches=1` claim and complete two
batches. The proposed patch reserves the slot under the same lock as the bound
check, before store access, and releases the reservation in `finally` so STOP,
lifetime expiry, no claim and store errors cannot leak capacity. The same test
then claims and completes exactly one batch. Heartbeat `active` may temporarily
contain the explicit value `<claiming>` while a reservation awaits a store claim.

Five tests pass. Besides the original overshoot and corrected bound, they cover
early exits, a batch exception and unlimited mode. The test runs only the
extracted function with fake store and batch operations; it never imports the
campaign modules or calls AWS, Docker, Lean, a solver or a checker.

Files:

- `cert_worker.before.py`: exact reviewed source, SHA-256
  `5fb1c7adaf444375a18ced2e82b22eefac74e80f79b0600f4a607c5b0959273e`.
- `cert_worker.proposed.py`: proposed source, SHA-256
  `e159d9fe358488fbaf8c6f3095915b613beb895c7fff3c07e5b72cd5af2792d4`.
- `canary-reservation.patch`: patch against the normal campaign path.
- `test_reservation.py`, `tests.log`, `RESULT.json`: reproduction and validation.

`git apply --check` succeeded against the H7 worktree at the reviewed commit.
No patch was applied there, and no running job was changed. This fixes the
reservation race in the existing completed-plus-active accounting; it does not
add a lifetime cap on failed attempts, verify real S3 behavior, or replace the
required cloud canary and spending approval. Integration remains with the H7
owner, who was notified in the squad room before this proposal was prepared.

Reproduce locally (metadata and two mocked threads only):

```sh
python3 -B test_reservation.py
```
