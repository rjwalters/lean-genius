# Toolchain Upgrade Spike: Lean v4.26.0 → v4.31.0 / Mathlib → 9a9483a9

**Issue:** #37508 (epic) — first-PR spike scope.
**Branch:** `feature/issue-37508` (reference/spike branch — **not** merged to `main`).
**Date:** 2026-07-11
**Author:** Loom Builder

## TL;DR

The pin bump is mechanically clean (image builds, `lake update` resolves, mathlib
cache downloads). On a **231-file sample** of `proofs/Proofs/` (alphabetical prefix),
built individually against the new pin inside Docker:

| Result | Count | % |
|--------|-------|-----|
| PASS   | 145   | 62.8% |
| FAIL   | 86    | 37.2% |

Extrapolated to the full 5,745 `.lean` files, expect **~2,100 files needing repair**.
This confirms the epic classification: a big-bang merge is impossible; a staged,
proof-family-by-family migration on a long-lived branch is required. **The pins are
NOT flipped on `main` by this PR.**

## Target pin (and why)

- Lean: `leanprover/lean4:v4.26.0` → **`leanprover/lean4:v4.31.0`**
- Mathlib rev: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` → **`9a9483a92959bc92bd6a60176dd1fe597298c1f8`**

This is the exact pin `openai/cdc-lean` uses. Verified: the mathlib commit's
`lean-toolchain` is `leanprover/lean4:v4.31.0` (consistent pair). Matching it makes
the kernel-verified Cycle Double Cover proof (#37507) a near-verbatim drop-in,
discharging the axiom in the `cycle-double-cover` gallery entry (#37506).

## What was changed on the spike branch (config only)

| File | Change |
|------|--------|
| `proofs/lean-toolchain` | `v4.26.0` → `v4.31.0` |
| `proofs/lakefile.toml` | mathlib `rev` → `9a9483a92959bc92bd6a60176dd1fe597298c1f8` |
| `proofs/lake-manifest.json` | regenerated via `lake update mathlib` (inside Docker); all transitive deps re-resolved (aesop, batteries, Qq, proofwidgets, importGraph, LeanSearchClient, plausible, Cli) |
| `proofs/Dockerfile` | **both** `elan toolchain install` and `elan default` lines → `v4.31.0` (the curator-found gap: bumping only `IMAGE` in docker-build.sh would silently rebuild with the old toolchain) |
| `proofs/scripts/docker-build.sh` | `IMAGE="lean4-arm64:v4.26.0"` → `v4.31.0` |
| `proofs/scripts/spike-build-inventory.sh` | **new** instrumentation harness (per-file logging) — additive, does not modify the existing `build-safe-subset.sh` |

## How the spike was run (reproducible)

```bash
# 1. build image at new pin
docker build -t lean4-arm64:v4.31.0 proofs/

# 2. regenerate manifest + fetch mathlib cache inside the image
docker run --rm -v "$REPO:/workspace" \
  -v lean-mathlib-packages-v431:/workspace/proofs/.lake/packages \
  -v lean-mathlib-cache-v431:/workspace/proofs/.lake/build \
  -w /workspace/proofs lean4-arm64:v4.31.0 \
  bash -c "lake update mathlib"     # NOT lake build — allowed by the bin/lake wrapper

# 3. per-file inventory (LIMIT caps for time-budgeted runs)
docker run --rm ... lean4-arm64:v4.31.0 \
  bash -c "lake exe cache get; LIMIT=400 bash scripts/spike-build-inventory.sh"
```

Spike used **dedicated** volumes (`lean-mathlib-packages-v431`, `lean-mathlib-cache-v431`)
so the production `lean-mathlib-packages` / `lean-mathlib-cache` volumes (still on
v4.26.0) were **not** poisoned. `lake exe cache get` fetched 8,560 prebuilt mathlib
oleans — no multi-hour cold mathlib compile.

**Safety:** no `lake build` was ever run on the host; all builds were Docker-isolated
with a 16 GB memory cap. `Erdos728FactorialDivisibility` remained excluded and skipped.

## Failure-class breakdown (86 failing files in the sample)

Classified from retained per-file logs (`proofs/spike-logs/*.log`):

| Class | Count | Fix tier | Notes |
|-------|-------|----------|-------|
| `rename-unknown-name` (Unknown constant/identifier) | 25 | **Mechanic** (mechanical) | lemma/def renamed upstream |
| `rename-invalid-field` (Invalid field projection) | 20 | **Mechanic** (mechanical) | dot-notation field renamed |
| `signature-type-mismatch` (Application/Type mismatch) | 18 | Human/Doctor | lemma argument order/implicitness changed |
| `instance-synth-drift` (failed to synthesize instance) | 11 | Human/Doctor | typeclass hierarchy moved |
| `transitive-dep-failed` (no such file — imports a broken Proofs file) | 5 | auto-resolves | fixes when the imported file is fixed; not independent |
| `tactic-unsolved-goals` | 2 | Human/Doctor | simp-set / defeq drift leaves goals |
| `tactic-drift` (omega/simp/rewrite/unfold no longer close) | 2 | Human/Doctor | |
| `noncomputable-required` | 2 | Mechanic | add `noncomputable` marker |
| `namespace-ambiguous` | 1 | Mechanic | qualify the name |
| `other-uncategorized` | 1 | Human | |

**~52% of failures are pure renames** (`rename-unknown-name` + `rename-invalid-field` =
45/87 log files), i.e. batchable Mechanic-agent work. Many deprecations even self-document
the replacement, e.g.:

- `IsSolvableByRad` → `solvableByRad`
- `solvableByRad.isSolvable'` → `isSolvable_gal_of_irreducible`

Highest-frequency single rename in the sample: `alternatingGroup.isSimpleGroup_five`
(unknown constant, 15 files) — a Galois-theory prerequisite used across the AbelRuffini
family. One rename unblocks a whole cluster.

Other recurring rename targets observed: `div_le_div_iff`, `Finset.Nat.antidiagonal`,
`Countable.exists_surjective_nat`, `Cardinal.mk_real`, `pow_eq_zero`,
`Real.sqrt_eq_iff_sq_eq`, `IsPGroup.isSolvable`, `Filter.eventually_of_forall`,
`Complex.finrank_real_complex`, `set_integral_const`/`set_integral_congr`,
`integral_eq_sub_of_hasDerivAt`.

## Sampling caveat

The sample is the **alphabetical prefix** (`AMGM…` through mid-`A…`), not a uniform
random draw, so the exact 37.2% may shift for the full corpus. The early AbelRuffini
cluster (Galois theory, heavily dependent on the one `isSimpleGroup_five` rename) is
over-represented and inflates the rename share locally. A follow-up triage sub-issue
should run the full 5,745-file inventory (≈8 h at the observed ~5–11 s/file, or
parallelize across shards) to get exact per-family counts. This spike establishes the
method and the order-of-magnitude cost, which is what the epic needs to plan.

## Recommended epic decomposition (sub-issues, `loom:triage`)

1. **Full failure inventory** — run `spike-build-inventory.sh` over all 5,745 files
   (sharded/parallel), commit `results.tsv` + failure-class histogram.
2. **Mechanic batch: renames** — fix `rename-unknown-name` + `rename-invalid-field` +
   `deprecated` classes in family batches (the largest, most mechanical bucket).
3. **Doctor/Human batch: signatures + instances** — `signature-type-mismatch` +
   `instance-synth-drift` + `tactic-drift` (needs judgement).
4. **Infra flip** — once the safe subset is green on the new pin, flip
   `main`'s config (this PR's spike-branch changes) + refresh the shared
   `lean-mathlib-*` volumes + CI image tag.
5. **Gallery metadata sweep** — update `mathlib_version` in the ~3,508
   `src/data/proofs/*/meta.json` files (mechanical, do last).
6. **CDC full port (#37507)** — execute on the new pin.

Keep `main` green throughout: the migration lives on a long-lived branch with periodic
rebases; nothing merges to `main` until the safe subset builds clean at the new pin.

## Open item before infra flip

**Aristotle backend toolchain compatibility** — confirm the Aristotle proof-search
backend elaborates against v4.31.0 before flipping `main`'s pin. Aristotle-generated
proofs must build on our pin; a lagging backend would break the integration workflow.
Not verifiable from this spike (external service); flagged as a gate on step 4.
