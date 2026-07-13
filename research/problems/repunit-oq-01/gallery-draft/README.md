# Gallery draft for repunit-oq-01 (build-pending)

These `meta.json` / `annotations.json` files are **prepared and validated** but held
here (not in `src/data/proofs/`) because the proof in
`proofs/Proofs/RepunitDivisibilityOQ01.lean` has not yet been machine-checked — the
Docker build environment was failing to fetch Mathlib (`git exited 128`) on
2026-06-16, an environment-wide blackout affecting all agents.

`annotations.json` passes the resolver cleanly (8 valid, 0 misaligned) against the
current Lean file.

## To promote once a green build is confirmed

1. Build: `./proofs/scripts/docker-build.sh Proofs.RepunitDivisibilityOQ01` and
   `grep -E "error:|sorry"` the log (Docker exits 0 even on Lean errors).
2. Register the import in `proofs/Proofs.lean` (alphabetical, after
   `Proofs.RelativizedHaltingBridge`).
3. Move these two files to `src/data/proofs/repunit-oq-01/`.
4. Re-validate annotations against the (possibly line-shifted) Lean file with
   `scripts/annotations/resolver.ts validate` and nudge ranges if needed.
5. Keep `status: "verified"` only after the build is green.
