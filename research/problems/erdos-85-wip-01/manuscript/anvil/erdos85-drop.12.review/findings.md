# Findings — erdos85-drop.12

## 1. Verification of the v12 additions at the pin

- **Pin.** `\repobase` is `fa2b41268df024128ed4738b3bb500637cf1ec12` ("erdos85: third-party-path cold rebuild ACCEPTED; objects byte-identical to attempt 2"). It is on `erdos85/release-assembly-20261011` and `erdos85/release-thirdparty-rebuild-20261012`, both present on `origin`, and it is an ancestor of the paper head `2fb3abe6abc`. All 80 `\repofile` uses (70 distinct targets) resolve at the pin.
- **Stated commit.** The availability paragraph names `92ff6248033c` instead. It is an ancestor of the pin, and `proofs/` is identical between the two. At `92ff6248033c` the three rebuild records do not exist: `release_cold_build_20261011/ACCEPTED.md`, `release_cold_build_20261011/FAILURE.md` and `release_thirdparty_rebuild_20261012/ACCEPTED.md`. This is major M1.
- **Capstone.** At the pin, `not_c4FreeMinDegreeWitness_fortyNine_seven_of_h1_h7Evidence` takes `hOne`, `depth` and `hSeven` and concludes `¬ C4FreeMinDegreeWitness 49 7`. Every `\lean` declaration name in the paper exists under `proofs/Proofs` at the pin. The exceptions are `hno49`, a binder in `Erdos85FiniteDropWitnesses.lean`, and `h1_81494a6ef36d3ec9`, an orbit identifier named in the cube-pilot module docstring; both are used correctly.
- **Cold rebuild, attempt 2** (`release_cold_build_20261011/ACCEPTED.md`). Job `20261012T042927-...`. 893/893 modules compiled from source. Capture gave `COLD_PROJECT_BUILD_ACCEPTED`, and the audit gave `COLD_PROJECT_BUILD_AUDIT_PASS` with axiom counts 601/607/604. The recorded scope matches the paper: a fresh project closure, pinned Lean/Mathlib package caches, and no external SAT replay. The record also says "independent re-audit of the bundle is open for Codex" (minor m4).
- **Third-party-path rebuild** (`release_thirdparty_rebuild_20261012/ACCEPTED.md`). It started from a fresh worktree with no `strata-lrat/` directory. The fetch script retrieved all 13 files, each `OK` against the manifest, and 893/893 modules compiled. "All 893 compiled `.olean` objects are byte-identical (same SHA256)" to attempt 2, and all axiom exports match. The record's limitation, a fetch under the bucket-owner account, is disclosed in the paper at L280. The paper does not use the phrase "third party" in prose. It describes the run accurately as "starting from a checkout without the certificate files and obtaining them with the published download script".
- **Attempt 1** (`FAILURE.md`). Exit 1 after 460/893 modules, caused by a runner initializer-name defect. The paper says "An earlier attempt failed in the build runner before completion", which is accurate. The record's closing instruction, "The manuscript must not claim a completed cold project rebuild", predates attempt 2 and is superseded but has no banner (minor m2).
- **Toolchain.** `proofs/lean-toolchain` at the pin is `leanprover/lean4:v4.31.0`, which matches "Lean 4.31.0".

## 2. Scope rules, full sweep

Every occurrence of "theorem", "decide(s/d)", "proved", "settled", "establish*" and "unconditional" was checked:
- Result A is never called a theorem. L87 says "not an unconditional theorem of Lean" and "separates Result A from a Lean theorem", both negations.
- The upper side is "derived in Lean ... from exactly two hypotheses" (L78) and "Lean thus derives the upper side from two explicit unsatisfiability hypotheses" (Abstract).
- `native_decide` is disclosed with counts in the abstract (598), §2.2 (601/607/604) and Table 2.
- cake_lpr is outside the Lean kernel in every mention.
- The new rebuild text does not promote anything: "That rebuild still lists the `native_decide` axioms, as any rebuild would" (L232), and Table 2 keeps "the two hypotheses" as the open item for the upper side.
- Nothing is claimed about Erdős Problem 85: "A single drop therefore decides nothing about the problem" (L73), and "Nothing is claimed about Erdős Problem 85 itself" (L87).
- A-REG is not asserted: "A-REG is not asserted" (L87), and "We hold A-REG as a hypothesis whose truth the finite data do not decide" (L246).
- "Settled" occurs once, at L147, for the superseded verdict-only census that the paper says it does not rely on.

**No critical flag.**

## 3. Cross-section consistency after the edits

- The publication status agrees across L87 ("are published with a hash-verified download recipe"), L121, Table 2, L232 and L280. The "Not published" list at L286 no longer includes the 13 files.
- The rebuild facts agree across §2.2, §2.3 ("The cold rebuild replayed all thirteen certificate checks from the published files"), Table 2 and L232.
- One inconsistency: the commit printed at L272 does not match `\repobase` at L32 (M1).
- The two kinds of cold build, September and October, are not distinguished at L93 and L236 (minor m6).

## 4. Release-level observations (outside the rubric)

- Separate-account access to the Requester Pays bucket is still untested (disclosed). One fetch from a non-owner account before the tag would remove the caveat at L280.
- The fetch-script comment at the pin still says "any AWS credentials work". The fix is on the paper branch only, so the final pin should include it.
- The 2.39 GB rebuild output bundles are retained outside Git, with committed per-file hash manifests (disclosed at L280).
- The version-dir changelog and `_progress.json` cite superseded pins (`92ff6248033c`, `87e58b130b5`). This is bookkeeping only.
