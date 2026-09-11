# q=9 host solver/control lane

Owner: codex-sol-3. Scope: operator board39, 2026-09-11. This runner does not
encode graphs. The semiregular graph generator and variable map belong to
codex-sol-1. Its unrestricted minimum-degree encoding requires separate review.

`runner.py run --n 48 --d 7 --m 24 --cnf INPUT.cnf --metadata MAP.json --seed 0`
launches the first graph positive control. The second is N63/d8/m63 or m21.
The metadata file is copied and hashed verbatim; the runner does not interpret
its generator-specific schema. Both source and local CNF copies are pinned.
Kissat's complete SAT assignment is checked against every CNF clause. This
check does not replace graph decoding or independent graph validation.

The fixed solver is the local Homebrew kissat executable, resolved and hashed
per launch, with `--sat --strict --no-color`, recorded seed, and `--time` cap.
There is exactly one positional input filename: proof logging is OFF.
No cloud, proof generation, or Phase B/H7 solving is invoked here.

Runs are serialized by flock and durably recorded in ledger.json. A live or
unresolved PREPARED/RUNNING record prevents another launch. An observation
timeout is not evidence that the solver stopped. Inspect the recorded process
and its command/start time; never restart because a tool wait returned.
Unclean runner death requires explicit recovery of the existing run and
conservative accounting before further launches; no automatic recovery/retry
is implemented. The solver has its own time cap even if the Python wrapper dies.

Initial runs have a 3600-second wall limit. One explicit `--retry` is permitted
only for a terminal UNKNOWN initial run, using the identical CNF, variable-map
metadata and seed, with
a 14400-second limit. Runtime is charged as aggregate solver wall time,
including both graph controls. The cap is reduced near the 48-hour budget,
reserving five seconds for termination/reaping. Errors require investigation;
they do not automatically authorize retries. Any observed q9 SAT line stops all further launches, even when a timeout or
inconsistent exit leaves the terminal verdict UNKNOWN/ERROR. The durable
`sat_observed` flag is separate from that verdict, and model checking still
runs so a possible witness is preserved for investigation.

Before q9 launches, each control must have a second-seat PASS receipt registered:

```
python3 runner.py register-control /absolute/path/to/receipt.json
```

Receipt schema:

```json
{
  "run_id": 0,
  "status": "PASS",
  "reviewer": "codex-sol-2",
  "n": 48, "d": 7, "m": 24,
  "solver_output_sha256": "EXACT_HASH",
  "graph": {"path": "/absolute/adjacency.json", "sha256": "EXACT_HASH"},
  "verifier": {"path": "/absolute/check.py", "sha256": "EXACT_HASH"},
  "verification_output": {"path": "/absolute/result.json", "sha256": "EXACT_HASH"}
}
```

The second seat must independently check the decoded graph's order, symmetry,
simplicity, minimum degree, C4-freeness, semiregular action, and binding to the
exact solver assignment/variable map. N63 control must also be 8-regular.
Registration validates receipt bindings and hashes; it relies on that review
for the mathematical interpretation of the graph. It does not manufacture a
review from solver output. Receipt/artifact hashes are rechecked before q9 runs.

`python3 -m unittest -v test_runner` checks actual kissat on tiny SAT and UNSAT
CNFs, direct rejection of invalid models, scope/control/retry/budget/first-SAT
gates, wall termination/reaping of a deliberately sleeping test executable,
and SAT output followed by timeout or a contradictory exit code.
These temporary fixtures are software checks, **not either graph positive
control**, and never enter the experiment ledger or furnish a q9 verdict.

Current research status: no graph control instance has been run with this
runner, and no q9 verdict has been produced. Class UNSAT without proof logging
is a solver report about that encoded class; it is not a Lean theorem or a
global nonexistence conclusion. Class misses cannot show that 49 is sporadic.
