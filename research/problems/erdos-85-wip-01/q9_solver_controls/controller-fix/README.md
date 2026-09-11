# Offline campaign selection audit

The current controller fails20 of81 queue-selection cases: ERROR or unrecognized status at a later task is masked by an earlier ready task. The proposed copy adds global status guards after SAT-stop and invalid-control-model checks, before selection. All81 cases then pass, covering every task position, complete terminal prefixes, exactly one UNKNOWN retry, active skips, control priority and immediate SAT stop.

This is an offline candidate patch. The audit executes only next_task against synthetic/copied ledgers. It does not launch/restart solvers, run the controller loop, mutate the ledger or claim a lifecycle/concurrency audit. Deployment and restart are coordinated with the controller owner. Historical interrupted control UNKNOWN remains allowed. Source and plan hashes identify the audited revision.
