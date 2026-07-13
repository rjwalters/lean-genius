## Session 2026-06-05 (S8 ACT) — lindemann_theorem axiom discharge via Hermite-Lindemann bridge

**Mode**: REVISIT (extending S7 ACT axiom-reduction pattern to sibling file)
**Outcome**: progress (1 axiom discharged in PiTranscendental.lean; 2 pre-existing build errors repaired)
**Researcher**: researcher-11
**HEAD entered**: 5407e6f00be (rebased to 0795b5fd at session start)
**PR #28013 status**: head SHA 5abb7c68488 (unchanged since 2026-05-29; mergeable_state blocked)

### What I Did

1. **Selected nth-root-irrational-oq-03** from available pool (knowledge score 22 = RICH; selected per DEPTH OVER BREADTH rule).
2. **S7 sibling-pattern recognition**: noticed that `axiom lindemann_theorem` in PiTranscendental.lean:125 has nearly the same signature as `axiom hermite_lindemann` in HermiteLindemann.lean:147 — they differ only in `IsAlgebraic ℤ α` vs `IsAlgebraic ℚ α`. The S7 ACT (yesterday) discharged `e_transcendental` via a similar `halg.algebraMap` bridge from `hermite_lindemann`; the same orthogonal path applies here.
3. **Drafted bridge proof** (3 lines):
   ```lean
   theorem lindemann_theorem (α : ℂ) (hα_ne : α ≠ 0) (hα_alg : IsAlgebraic ℤ α) :
       Transcendental ℤ (Complex.exp α) :=
     HermiteLindemann.hermite_lindemann α hα_ne
       ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp hα_alg)
   ```
   This pattern is used 10+ times in adjacent files (HermiteLindemann.lean:228 uses the exact identical `(IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp halg` call to extend ℤ to ℚ).
4. **Diagnosed 2 pre-existing Mathlib v4.26.0 regressions** flagged in S7's `nextSteps` ("PT:228,285 unknown irrational_pi/type mismatch"):
   - Line 228: `irrational_pi` undeclared. ETranscendentalOQ01.lean:11 imports `Mathlib.Analysis.Real.Pi.Irrational` to access it; PiTranscendental.lean only imports `Mathlib.Data.Real.Irrational` which used to transitively re-export but no longer does in v4.26.0.
   - Line 285: `isAlgebraic_algebraMap (1 : ℚ)` type-mismatch. Identical to S5b Fix #2 at eTranscendental.lean:225 (newer Mathlib elaborator does not auto-bridge `algebraMap ℚ ℝ 1` to `(1 : ℝ)`). Fix is `isAlgebraic_one`.
5. **Applied 3 edits to PiTranscendental.lean**:
   - Imports (lines 6-7): `+ Mathlib.Analysis.Real.Pi.Irrational` (for `irrational_pi`) and `+ Proofs.HermiteLindemann` (for the bridge). Confirmed no circular dependency — HermiteLindemann.lean has no `import Proofs.*`.
   - Line 125 axiom → line 129 theorem (3-line bridge body).
   - Line 285 (now 291) `isAlgebraic_algebraMap (1 : ℚ)` → `isAlgebraic_one`.
6. **Build verification (initial attempts)**: two `docker-build.sh` runs failed with cache I/O errors (`os error 5` / `Read-only file system os error 30`) and docker daemon crash. Root cause: host disk at 84% capacity, 2.3 GB free, Docker disk usage 30+ GB. Ran `docker system prune -f` → reclaimed 8.155 GB; disk dropped to 49% capacity.
7. **Build verification (post-prune)**: re-ran build → surfaced real Lean errors at `pi_transcendental` (line 149):
   - `error: Proofs/PiTranscendental.lean:158:7: failed to synthesize Algebra ℝ ℤ`
   - `error: Proofs/PiTranscendental.lean:161:13: Unknown identifier I_algebraic`
   - `error: Proofs/PiTranscendental.lean:149:56: unsolved goals`
8. **Root cause diagnosed**: `pi_transcendental` was a long-standing pre-existing bug — its proof body referenced `I_algebraic` and `neg_one_algebraic`, both defined LATER in the file (lines 209+ and 213+). Forward references are invalid in Lean 4. The file had presumably been broken since these definitions were placed below the theorem; nobody noticed because no caller was building it directly.
9. **Final fix**: replaced the entire `pi_transcendental` proof body with a one-line alias to `HermiteLindemann.pi_transcendental_real` (already proven, post-S7). This removes the forward-reference bug AND avoids the broken `Polynomial.aeval_algebraMap_apply` API call.
10. **Build verification (final)**: `docker-build.sh Proofs.PiTranscendental` → **3092/3092 jobs ✓ (build succeeded, 81s)**. Only output warnings are deprecation linter notices for old import names (`Mathlib.Data.Real.Irrational`, etc.) — same as S7's recorded HermiteLindemann.lean state.

### Key Findings

- The two axioms `hermite_lindemann` and `lindemann_theorem` differ only in base ring (ℚ vs ℤ); the local axiom is redundant — a 3-line bridge from the transitive Hermite-Lindemann axiom suffices. Same orthogonal pattern as S7's `e_transcendental` discharge.
- PiTranscendental.lean had **3 pre-existing build failures** (S7 nextSteps mentioned only 2):
  1. Line 228: missing `Mathlib.Analysis.Real.Pi.Irrational` import for `irrational_pi` (per ETranscendentalOQ01.lean:11 pattern).
  2. Line 285: `isAlgebraic_algebraMap (1 : ℚ)` → `isAlgebraic_one` (S5b Fix #2 pattern).
  3. **NEW finding**: `pi_transcendental` had invalid forward references to `I_algebraic` (line 161) and `neg_one_algebraic` (line 173), both defined later in the file. This long-standing bug was masked because no caller imported the file. Fix: replace proof body with one-line alias to `HermiteLindemann.pi_transcendental_real` (proven post-S7).
- Net effect: PiTranscendental.lean `leanFile.axiomCount` 1→0; file builds clean (3092/3092 jobs ✓). Transitive axiom count still 1 (hermite_lindemann remains gated on Mathlib PR #28013).
- ETranscendentalOQ01.lean transitively depends on PiTranscendental.lean; this S8 fix unblocks its build too.
- Host Docker infrastructure was rescued by `docker system prune -f` (reclaimed 8.155 GB).

### Files Modified

- `proofs/Proofs/PiTranscendental.lean` (+2 imports, axiom → theorem, isAlgebraic_one fix, pi_transcendental alias to HermiteLindemann.pi_transcendental_real; 457 → 432 lines, net −25)
- `src/data/proofs/pi-transcendental/meta.json` (leanFile.lineCount 457→432, axiomCount 1→0, theoremCount 18→19; meta.assumptions reworded to reflect transitive-only axiom)
- `src/data/research/problems/nth-root-irrational-oq-03.json` (insights, builtItems, nextSteps, progressSummary)

### Next Steps

- **S9 (passive watch, primary)**: PR #28013 head SHA `5abb7c68488` unchanged since 2026-05-29 (7 days). Continues passive watch through ~2026-06-26 grace period end.
- **S5d.A/B/C (deferred)**: CF expansion of e remains the only avenue to discharge `e_not_liouvilleWith_gt_two` axiom (280-480 LOC).
- **S8 follow-up** (low priority): `pi_transcendental_over_rationals` (line 179) now has a cleaner ℚ-direct path via the new theorem; current proof routes through ℤ. Not on critical path.
- **Mechanic scope**: ETranscendentalOQ02.lean still has pre-existing build error at line 708 ("no goals"). Out of researcher scope.

### Honesty Statement

This session's deliverable (axiom discharge + 3 build repairs) is identical-pattern follow-up to S7 ACT, not a creative breakthrough. The Hermite-Lindemann axiom remains the load-bearing assumption for pi-transcendence; this session reduces local-axiom surface without changing the proof's transitive trust assumption. The `pi_transcendental` alias to `HermiteLindemann.pi_transcendental_real` is the cleanest path given the forward-reference bug — it does not invent a new proof, just delegates to the already-proven sibling. Build verified locally (3092/3092 jobs ✓).
