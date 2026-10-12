# Cold-build attempt 2: runner corrections

Attempt 1 (`20261011T215126-commit-8d4f59c82e40-9322`) failed after 460/893
modules; its receipts are on `erdos85/cold-build-evidence-20261011`
(`FAILURE.md`). Proof sources, the 32 include files and the accepted axiom
plan are unchanged; only the runner and plan limits differ.

1. **Plugin initializer.** `INIT` is now
   `initialize_Proofs_Erdos85H3TripleCompletionRuntime`, the symbol attempt 1's
   freshly built plugin exports (`attempt1-plugin-symbols.txt`). The old
   spelling came from the Lake-built campaign plugin, whose C carries the
   `proofs` package prefix; this runner compiles the Runtime C without a package.
   The runner now also refuses to continue if the generated C does not define
   `INIT`.
2. **Smoke gate by scheduling.** `Erdos85H3TripleCompletionPart000` and its
   ancestors are scheduled first, so the plugin is exercised in a real part about
   45 minutes in. Any failure there stops the run, as before.
3. **Critical-path order.** Attempt 1 scheduled ready modules alphabetically:
   the H7 certificate chain was ready at minute 45 but did not start until
   minute 300, behind 35-minute H3/H5 searches. Ready modules are now ordered by
   the longest estimated path to the endpoint (estimates only order work).
4. **No certificate memory reservation; 12 workers.** The Oct 7/8 builder compiled
   all 13 H7 certificate modules concurrently at a ~20 GB peak, and attempt 1's
   six searches left ~117 GiB available, so the 64 GiB reservation (which would
   have serialized the 13 certificates) is removed and the worker count is 12
   on the same 16-CPU / 110 GiB cgroup.

Simulated with attempt 1's measured durations (estimates for the rest): about
4.2 h total, smoke part at ~43 min, largest certificate done by ~3.1 h; the
580-minute outer cap is unchanged. Authorization: Robb, 2026-10-12, "diagnose and fix the bugs
and try again. let's keep doing this until we pass."
