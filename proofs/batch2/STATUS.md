# Batch 2/3/4/5 + Doctor verification state (updated Doctor increment 2, #38065, 2026-07-12)

## DOCTOR INCREMENT 2 NUMBERS (#38065)

Ledger `verify-results.tsv` (full 2,659-file inventory-FAIL baseline):

- **651 GREEN / 1,984 RESIDUAL / 24 PRE-EXISTING** (increment start: 484 GREEN /
  2,151 RESIDUAL). **+167 GREEN this increment.**
- Fix waves DR6 (660-target touched-closure re-verify: mechanical sweeps +
  hub fixes, +118 green), DR7 (234 safe-set fix targets, +32 green),
  DR8 (two-pass follow-ups + revert re-verify, +17 green).
- **Regression gate: 119 GREEN modules with edited (transitive) deps ALL
  re-verified by exit-code (runner4): 119/119 PASS** after one true regression
  (Erdos895CounterexampleFin18, broken by the symm.symm field sweep hitting an
  already-migrated multiline `symm := by / constructor` block) was root-caused
  and reverted repo-wide (36 files).
- Mechanical sweeps this increment (`dr6_fix.py`, `dr7_noprogress.py`,
  `dr7_natdegree.py`, map §7f): Std.Symm/Irrefl use-sites + structure fields,
  umbrella `import Mathlib` for 298 unknown-const/import-loss rows, verified
  renames, `open scoped Classical` on 107 new candidates + noncomputable
  second pass, NormedSpace.exp scalar drops, no-progress tactic neutralization
  (132 sites), maxRecDepth inserts, Option.noConfusion eta-form fixes,
  hdvd factorial simpa fixes, ZsqrtdNegTwo EuclideanDomain `where __ :=` form.

## Verification infrastructure (CHANGED — read before next session)

- **lake 5.0 has NO `-j` flag** — `lake build -j4` dies instantly with
  "unknown short option '-j'" swallowed by `>/dev/null || true` (this silently
  no-opped runner4's bulk phase). Parallelism = container CPU count; limit
  with `docker --cpuset-cpus 0-5` (6 CPUs ≈ ≤6 lean procs ≈ fits in 11g).
- **runner5.sh** (preferred): chunked bulk (25 targets) with per-chunk LOGS to
  `batch2/logs/`, `pkill -9 lean` after each chunk (orphaned leans from a
  timed-out bulk otherwise starve everything), then **mtime-based PASS/FAIL**
  (olean newer than .lean). Validated 289/289 against runner4 exit codes.
  ⚠ mtime check is ONLY sound for RESIDUAL targets (no olean unless built) —
  for GREEN targets (stale olean + git-reset mtimes) use runner4 exit codes.
- Diags come from chunk logs via `batch2/extract_diags.py <results> <diag-out>
  <log-prefix>...` (import-closure attribution for dep failures).
- Wave sequence this increment: DR6a/b(seq, partial) → DR6mt+DR6ra/rb →
  DR7a/b → DR7reg2 (runner4, GREEN regression) → DR8a/b.

## Residual classes after Doctor increment 2 (1,984 total) + dispositions

| class | count | disposition |
|---|---|---|
| type-mismatch | 537 | per-file signature bridges; freshest diags diag-DR6r*/DR7*/DR8* are chunk-log based |
| proof-drift | 421 | per-file tactic repair; `dr7_noprogress.py` neutralized the no-progress subset — remaining are real goal drift |
| unknown-const singletons | 389 | umbrella-import already applied where useful; leftovers = true removals + project-local names (halasz_theorem, white_lower, …) — harvest §batch-5 style, else route disposition |
| instance-synth | 266 | classical recipe applied to 107 more files (two-pass done); remainder = cyclotomic mystery (48 rows), Fintype edgeSet/neighborSet shapes, decide×classical catch-22s |
| rewrite-drift | 111 | per-file rw pattern updates |
| parse-error | 77 | hand-inspect |
| signature-drift | 55 | Function-expected/app-type-mismatch |
| elab-drift | 49 | incl. FourierSeries `No applicable extensionality theorem for AddCommMonoid ℝ` family |
| dot-notation-drift | 27 | mostly REAL import-loss now umbrella'd; leftover = true field renames (IsMulCommutative.comm, HasFDerivAtFilter.div, …) |
| no-diag-captured | 13 | chunk logs lost their error lines (dep-attribution miss) — re-verify with runner4 in increment 3 |
| noncomputable | 9 | fix_noncomputable two-pass done; these need per-file judgement |
| duplicate-decl | 8 | project-local double declarations (never-compiled tier) |
| slow-timeout | 7 | need >300s or single-file runs |
| partenat-removal | 5 | ℕ∞/emultiplicity rework — deep-rework |
| decide-maxrecdepth | 5 | set_option applied; these 5 still exceed (incl. SetLike-recursion shape) |
| lambda-token / uses-sorry / termination-drift / oom-killed | 5 | per-file |

**Known deep-rework items (unchanged dispositions):** cyclotomic-instance
synthesis mystery (InverseGalois*/AngleTrisection* — biggest single synth shape,
48 rows); `Set.Finite.ncard_biUnion` finsum rework (Ballot family);
native_decide×noncomputable catch-22 (AbelRuffiniOQ10, Erdos968, Picks);
24 PRE-EXISTING never-compiled rows → separate cleanup issue.

## Backlog → Doctor increment 3 (routing)

1. **type-mismatch 537** — largest class; start from diag-DR8*/DR7* (freshest);
   the `simpa using hdvd`-style shared shapes are catalogued in map §7f.
2. **unknown-const 389** — mechanical harvest of multi-module names first
   (Function.nmem_support.mp ×8, Complex.abs shim-downstream ×12,
   div_add_div_same ×9 → `← add_div`, Nat.find_eq_iff/le_pow_iff_clog patterns).
3. **proof-drift 421** — hub-first (check `import Proofs.*` fan-out before
   per-file work; this increment's hub flips: GraphCore, ShannonChannelCodingOQ04OQ01
   (13-module fan-out), SpernerMathlib4, DerangementsConvergence, ZsqrtdNegTwo).
4. **instance-synth 266** — attack Fintype edgeSet/neighborSet shape;
   cyclotomic mystery needs dedicated in-container debugging session.
5. Re-verify the 13 no-diag-captured rows with runner4.

## Verification recipe (updated)

docker run --rm --memory 11g --cpuset-cpus 0-5 \
  -v "<worktree>:/workspace" \
  -v lean-mathlib-packages-v431:/workspace/proofs/.lake/packages \
  -v lean-mathlib-cache-v431:/workspace/proofs/.lake/build \
  -w /workspace/proofs lean4-arm64:v4.31.0 \
  bash batch2/runner5.sh batch2/targets-X.txt batch2/results-X.txt batch2/logs/X 900

Diags: `python3 batch2/extract_diags.py batch2/results-X.txt batch2/diag-X.txt batch2/logs/X`
Merge: `cd proofs/batch2 && python3 merge_results.py --results ... --diag ...` (idempotent).
Reclassify: `python3 reclassify.py` (ORDER extended through DR8).
≤2 containers concurrently (use disjoint --cpuset-cpus). NEVER lake build on host.
GREEN-module verification: runner4.sh (exit codes), never runner5 mtimes.


---

# HISTORY: Doctor increment 1 close-out (superseded 2026-07-12)

## DOCTOR BATCH NUMBERS (#38065, first increment)

Ledger `verify-results.tsv` now covers the **full 2,659-file inventory-FAIL
baseline** (verified: `comm -23 <(inventory FAILs) <(ledger rows)` = 0):

- **484 GREEN / 2,151 RESIDUAL / 24 PRE-EXISTING** (session start: 973 tracked,
  294 GREEN / 655 RESIDUAL).
- Wave 0 (required first acceptance criterion, COMPLETE): zero-edit re-verify of
  the 1,687 untracked inventory FAILs in 8 shards
  (`targets-W0smoke/aa..ah`, results/diag files on branch) using
  `runner3.sh` — like runner2 but keeps 2 context lines per error so
  instance-synth diags record WHICH instance failed.
- Doctor fix waves: DR1 (64 targets, 17 green), DR2 (282 targets, 43 green),
  DR5 (250 targets incl. 40-row regression sample, 82 green).
  (Doctor waves are `DR*` — plain `D1/D2` are the Mechanic's earlier artifacts.)
- Regression gate: 40 previously-GREEN modules re-verified in DR5 — **40/40
  still PASS**, no regression from any repo-wide edit.
- Zero `unclassified`/`doctor-unclassified` rows: classifier extended
  (signature-drift, elab-drift, duplicate-decl, oom-killed, slow-timeout,
  instance-synth-stuck, …) + `reclassify.py` recomputes classes from the
  freshest diag per module.

## Residual classes after Doctor increment 1 (2,151 total) + dispositions

| class | count | disposition |
|---|---|---|
| type-mismatch | 572 | per-file signature bridges; next Doctor session — start from diag-W0*/diag-DR5 (fresh, context-aware) |
| unknown-const singletons | 500 | wave-0 unmasked ~350 new names; harvest with the §batch-5 procedure; import-loss subset → umbrella `import Mathlib` |
| proof-drift | 407 | per-file tactic repair (linarith/omega/simp drift); hub-first (see hub table in map §7) |
| instance-synth | 328 | classical recipe (§7a) applied to 141 pattern rows; remainder = cyclotomic-instance mystery (see below) + stuck-instance shapes |
| rewrite-drift | 99 | per-file `rw` pattern updates |
| signature-drift | 74 | Function-expected / application-type-mismatch; many are `Std.Symm`-adjacent (recipe §7c) |
| parse-error | 70 | remaining hand-inspect (mostly wave-0 new) |
| elab-drift | 32 | universe/metavariable/anonymous-constructor drift; per-file |
| dot-notation-drift | 30 | recipes in map §7d (max?, flatMap, primeFactorsList, …) |
| decide-maxrecdepth | 9 | `set_option maxRecDepth 40000` recipe validated (TwinPrimes/SophieGermain green) |
| duplicate-decl | 8 | project-local double declarations (never-compiled tier, route with PRE-EXISTING follow-up) |
| noncomputable | 7 | `fix_noncomputable.py` on next wave's diag |
| slow-timeout | 6 | need >300s per-target or 600s retry (incl. HurwitzTheoremOQ04) |
| partenat-removal | 4 | ℕ∞/emultiplicity rework (ChebyshevPNTBridgeOQ01 + 3) — deep-rework |
| lambda-reserved-token | 2 | rename λ binders (recipe §7e) |
| uses-sorry / termination-drift / oom-killed | 3 | per-file |

**Known deep-rework items** (dispositions, not bugs in this batch):
- `IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ)` fails to synthesize in
  InverseGalois/AngleTrisectionEmbedding although v4.31 has the `[CharZero K]`
  instance (Cyclotomic/Basic.lean:702) — needs in-container debugging.
- `Set.ncard_biUnion` → `Set.Finite.ncard_biUnion` with finsum RHS
  (BallotProblemOQ01OQ02OQ01 family) — proof rework, not a rename.
- AbelRuffiniOQ10 / Erdos968: `native_decide` × noncomputable catch-22 (map §6.5).
- 24 PRE-EXISTING never-compiled rows: route to a separate cleanup issue.

## Doctor recipes catalog

See `research/toolchain-v4.31-rename-map.md` **section 7** for the full
verified recipe catalog added by this batch (classical decidability loss,
Subgroup.normalizer Set-argument, Std.Symm/Std.Irrefl SimpleGraph fields,
NormedSpace.exp, Complex.abs shims, notation-scope losses, parse repairs, …)
and `batch2/add_open_classical.py` / `batch2/fix_noncomputable.py` /
`batch2/reclassify.py` for the sweep tooling.

## Backlog → next Doctor session

1. Re-diagnose + fix hub files first: each hub flip cascades (this session:
   CayleyHamiltonOQ02OQ01 '-/'-docstring fix flipped 5, AmgmInequalityOQ02
   flipped 7, AreaOfCircleOQ01OQ02OQ02 flipped 12, Step4 flipped 3).
2. unknown-const harvest over diag-W0* (500 rows, many mechanical).
3. type-mismatch bridges (572) — largest class.
4. Remaining classical-recipe candidates among the 328 instance-synth rows.

## Verification recipe (unchanged)

docker run --rm --memory 8g \
  -v "<worktree>:/workspace" \
  -v lean-mathlib-packages-v431:/workspace/proofs/.lake/packages \
  -v lean-mathlib-cache-v431:/workspace/proofs/.lake/build \
  -w /workspace/proofs lean4-arm64:v4.31.0 \
  bash batch2/runner3.sh batch2/targets-X.txt batch2/results-X.txt batch2/diag-X.txt [bulk-timeout-s]

Merge: `cd proofs/batch2 && python3 merge_results.py --results results-X.txt --diag diag-X.txt`
(idempotent). Reclassify: `python3 reclassify.py`.
≤2 containers concurrently. NEVER lake build on the host.
All edits are applied ONLY to files already FAIL in proofs/spike-logs-full/results-full.tsv,
so no previously-passing file can have regressed (regression sample re-checked
40 GREEN rows in DR5: 40/40 PASS).
