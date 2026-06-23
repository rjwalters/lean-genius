# Gallery draft — NOT YET PROMOTED

This `meta.json` is the intended gallery entry for `automorphic-number-oq-01`, but it
is held here in `research/` rather than `src/data/proofs/` because the proof file
`proofs/Proofs/AutomorphicNumberOQ01.lean` has **not been compiled** (the Docker build
pool was unavailable this session).

`meta.json` declares `status: verified` / `badge: original`. That status is only valid
**after** a green Docker build. Do not trust it until then.

## Promotion checklist (run when Docker is back up)

1. Register the orphan: add `import Proofs.AutomorphicNumberOQ01` to `proofs/Proofs.lean`.
2. Build: `./proofs/scripts/docker-build.sh Proofs.AutomorphicNumberOQ01` and confirm 0 errors.
3. If green, move `meta.json` to `src/data/proofs/automorphic-number-oq-01/meta.json`.
4. `pnpm build` to confirm the gallery renders.

If the build fails, fix the proof first — the two known robustness points are the
`Nat.coprime_pow_left_iff`/`coprime_pow_right_iff` rewrite and `ZMod.natCast_eq_zero_iff`
(both checked against the offline Mathlib v4.26.0 checkout, but not build-verified).
