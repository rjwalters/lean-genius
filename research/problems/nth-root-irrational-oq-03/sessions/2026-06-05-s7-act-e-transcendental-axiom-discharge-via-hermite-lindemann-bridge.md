# S7 ACT — Discharge `axiom e_transcendental` via Hermite-Lindemann bridge

**Researcher**: researcher-5
**Date**: 2026-06-05T09:30Z
**Phase**: ACT (axiom reduction)
**Iteration**: 8
**Scope**: Lean code change + 2 meta.json edits + state docs

## 1. Mission

Per S6 PREP (2026-06-01), Mathlib PR #28013 threshold-crossing (168h) would
trigger promotion of S5d.A (CF-of-e formalization). On 2026-06-05, the threshold
was indeed crossed (169.8h vs 168h), but only by 1.8h — within normal weekly
variance — and the S6 PREP explicitly extended the grace period to "another
~3-4 weeks". The proper S5d.A promotion is therefore still deferred to
~2026-06-26.

This session pursued an **orthogonal axiom-reduction path** identified during
the dependency audit: discharging `axiom e_transcendental` in
`eTranscendental.lean` by deriving it from the existing `axiom hermite_lindemann`
in `HermiteLindemann.lean`. Setting α = 1 in Hermite-Lindemann gives
transcendence of `Complex.exp 1`, which transfers to `Real.exp 1` via the ℝ↪ℂ
embedding. This is a structural reduction unrelated to the CF-of-e arc.

## 2. Discoveries

### 2.1 Stale knowledge in slug JSON

`src/data/research/problems/nth-root-irrational-oq-03.json` claimed "4 sibling
sorries across eTranscendental.lean, ETranscendentalOQ01.lean,
ETranscendentalOQ02.lean, PiTranscendental.lean" (Insight 1, S1). Direct grep
at 2026-06-05 confirms **0 sorries** across all 5 sibling files. The sorries
were discharged in intervening enrichment/research work; the JSON insight is
stale (S7 leaves it as historical record but no longer actionable).

### 2.2 HermiteLindemann.lean broken on origin/main

Docker-build of `Proofs.HermiteLindemann` at HEAD `da53bdc3c9e` fails with **5
errors + 4 cascade parse errors** at v4.26.0:

| line | issue | category |
|------|-------|----------|
| 216 (orig) | `Complex.ofRealHom.toAlgHom` — `RingHom.toAlgHom` removed v4.26.0 | API regression |
| 244-246 (orig) | `Complex.ofReal_cos_ofReal_re`/`_sin_ofReal_re` — removed v4.26.0 | API regression |
| 258 (orig) | `Complex.ofRealHom.toAlgHom` — same as 216 | API regression |
| 277/297/309 (orig) | cascade parse errors after 258 | parser confusion |
| 150-155/173-183/185-192 (orig) | dangling `/--` docstrings with no attached declaration | parser strict |
| 200-203 / 268-277 / 287-309 (orig) | aspirational "Axiom: ..." docstrings, never declared | parser strict |
| 225 (orig) `pi_transcendental` | `by decide` on `(X^2 + 1 : ℚ[X]) ≠ 0` fails — `Decidable` got stricter v4.26.0 | tactic regression |

S6 PREP (2026-06-01) verified `Proofs.ETranscendentalOQ03` builds clean (3072
jobs) but did **not** check `Proofs.HermiteLindemann` — OQ03 doesn't import
HermiteLindemann. This session's bridge requires `import Proofs.HermiteLindemann`
in `eTranscendental.lean`, so the file must build. All 5+4 errors fixed in §3.

### 2.3 Mathlib API audit at lake-pinned SHA

Confirmed at `gh api repos/leanprover-community/mathlib4/...` (v4.26.0 tag,
manifest rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

- `IsAlgebraic.algebraMap` (Mathlib/RingTheory/Algebraic/Basic.lean:174) —
  `{a : S} → IsAlgebraic R a → IsAlgebraic R (algebraMap S A a)`. Provides
  the ℝ → ℂ algebraicity transfer in 1 line.
- `Complex.ofReal_exp` — `((Real.exp x : ℝ) : ℂ) = Complex.exp ↑x`. Used `←`
  direction to rewrite `Complex.exp ↑(1 : ℝ)` to `↑(Real.exp 1)`.
- `Complex.ofReal_cos` and `Complex.ofReal_sin` — `↑(Real.cos x) = Complex.cos ↑x`
  etc. Replace the removed `_ofReal_re` variants.
- `isAlgebraic_one` — `IsAlgebraic R (1 : A)` (Basic.lean:138). Replaces
  `isAlgebraic_int 1` which failed to elaborate (`?A` ambiguous).
- `IsFractionRing.isAlgebraic_iff A K x` — `IsAlgebraic A x ↔ IsAlgebraic K x`
  (Localization/Integral.lean:135). So `.mp : ℤ→ℚ`, `.mpr : ℚ→ℤ`. Matches the
  S5b "flip `.mp` to `.mpr`" recorded fix at `eTranscendental.lean:152`.

## 3. Lean changes

### 3.1 `proofs/Proofs/HermiteLindemann.lean`

**`e_transcendental_int` (new theorem, replaces broken `e_transcendental_rationals`
proof)**

```lean
theorem e_transcendental_int : Transcendental ℤ (Real.exp 1) := by
  have h_complex : Transcendental ℤ (Complex.exp (1 : ℂ)) :=
    hermite_lindemann 1 one_ne_zero isAlgebraic_one
  rw [show (1 : ℂ) = ↑(1 : ℝ) from by simp, ← Complex.ofReal_exp] at h_complex
  exact fun halg => h_complex halg.algebraMap

theorem e_transcendental_rationals : Transcendental ℚ (Real.exp 1) :=
  fun halg => e_transcendental_int ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr halg)
```

Down from 17 lines (broken) to 7 lines (working). `IsAlgebraic.algebraMap`
substitutes for the entire `Polynomial.aeval_algHom_apply ... Complex.ofRealHom.toAlgHom`
machinery.

**`pi_transcendental` (repaired)**

Replaced broken `Complex.ofReal_cos_ofReal_re` chain with `Complex.exp_mul_I`
+ `← Complex.ofReal_cos` + `← Complex.ofReal_sin` + `Real.cos_pi` + `Real.sin_pi`
+ `push_cast; ring` for Euler identity. Replaced `by decide` for polynomial
nonzero with explicit `eval (0 : ℚ)` discharge (`(X^2 + 1).eval 0 = 1`, so if
the polynomial were zero we'd have `0 = 1`).

**`pi_transcendental_real` (repaired)**

```lean
theorem pi_transcendental_real : Transcendental ℤ Real.pi :=
  fun halg => pi_transcendental halg.algebraMap
```

Same 1-line `IsAlgebraic.algebraMap` shortcut. Down from 6 lines to 2.

**Dangling docstring cleanup**

7 `/-- ... -/` docstrings (for "Axiom: ..." entries never declared) converted
to `/-! ... -/` doc blocks. No semantic content lost; aspirational axioms
clearly marked as commentary rather than parse-failed code.

### 3.2 `proofs/Proofs/eTranscendental.lean`

- Added `import Proofs.HermiteLindemann`.
- Replaced `axiom e_transcendental : Transcendental ℤ (Real.exp 1)` (16 lines
  of axiom + docstring) with:

```lean
theorem e_transcendental : Transcendental ℤ (Real.exp 1) :=
  HermiteLindemann.e_transcendental_int
```

eTranscendental.lean **local axiom count: 1 → 0**. The downstream
`e_transcendental_over_rationals`, `e_irrational_axiom`, `e_inv_transcendental_axiom`,
etc. all continue to use the same name `e_transcendental` (now a theorem) with
no signature change.

## 4. Build verification

```
LEAN_BUILD_TIMEOUT=20m ./proofs/scripts/docker-build.sh Proofs.eTranscendental
→ ⚠ [3079/3079] Built Proofs.eTranscendental (4.5s)
→ info: e_transcendental : Transcendental ℤ (rexp 1)
→ Build completed successfully (3079 jobs).

LEAN_BUILD_TIMEOUT=20m ./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ03
→ ⚠ [3085/3085] Built Proofs.ETranscendentalOQ03 (8.1s)
→ Build completed successfully (3085 jobs).
```

Both targets build clean. `e_transcendental` is now a **theorem** at line 144
(was axiom at line 147 pre-change), as confirmed by the `info:` line from
`#check e_transcendental` at the bottom of the file.

### 4.1 Out-of-scope build state (pre-existing failures, not regressed)

`Proofs.PiTranscendental` fails at lines 228 (`Unknown identifier irrational_pi`)
and 285 (type mismatch on `isAlgebraic_algebraMap 1`). `Proofs.ETranscendentalOQ02`
fails at line 708 (`No goals to be solved`). These were already broken on
origin/main at HEAD `da53bdc3c9e` and are unaffected by S7 changes. Flagged
as mechanic-class follow-up.

`Proofs.ETranscendentalOQ01` transitively fails because it imports
`Proofs.PiTranscendental`. Fixing PT unblocks OQ01.

## 5. Meta.json updates

### `src/data/proofs/e-transcendental/meta.json`

| field | before | after |
|-------|--------|-------|
| `leanFile.axiomCount` | 1 | **0** |
| `leanFile.theoremCount` | 12 | **13** |
| `leanFile.lineCount` | 305 | 304 |

`meta.status` and `meta.badge` stay `"axiomatized"` / `"axiom"` per Axiom
Integrity Policy: the slug still **transitively** depends on
`axiom hermite_lindemann` in the upstream file. The reduction is local-file
only; total project-wide axiom count is unchanged at 1 (now solely
`hermite_lindemann`).

### `src/data/proofs/hermite-lindemann/meta.json`

| field | before | after |
|-------|--------|-------|
| `leanFile.theoremCount` | 4 | **5** (added `e_transcendental_int`) |
| `leanFile.lineCount` | 390 | 373 |

## 6. Value assessment

Per the value hierarchy in the research prompt:

1. **Structural theorem** — yes. `e_transcendental` is now a direct consequence
   of `hermite_lindemann`, making the axiom dependency explicit and shared
   rather than duplicated. This is exactly the "one reduction > 1000 cases"
   pattern the prompt highlights.
2. **Decidable instance** — n/a.
3. **Lemma on critical path** — `e_transcendental_int` is a reusable bridge
   for ℂ→ℝ transcendence transfer; will be used again whenever a sibling
   slug needs `Transcendental ℤ x` from a Hermite-Lindemann-style consequence.
4. **Side benefit**: HermiteLindemann.lean restored to clean build state.
   `pi_transcendental` and `pi_transcendental_real` now actually work (was
   pure decoration before — fail-silent because no caller imported the file).

Non-trivial gain: the discovery that "4 sibling sorries" was stale (0 actual
sorries), prompting this dependency audit which surfaced the redundant axiom.

## 7. Next steps

1. **S8 (passive watch, primary)**: re-check PR #28013 at next claim of this
   slug. Threshold crossed 2026-06-05 by 1.8h; S6 grace period ends ~2026-06-26.
2. **S5d.A/B/C (deferred)**: CF-of-e formalization (280–480 LOC, 3 sub-tasks).
   Activation criterion: PR #28013 still not merged at 2026-06-26.
3. **S7 follow-up** (low priority): use `pi_transcendental_real` (now working)
   to discharge `axiom lindemann_theorem` in `PiTranscendental.lean`. Same
   `halg.algebraMap` bridge pattern. Would reduce another redundant axiom but
   requires first fixing PiTranscendental.lean's pre-existing v4.26.0 build
   errors (out of researcher scope — mechanic-class repair).
4. **Mechanic flag**: 3 deprecation-linter warnings (Mathlib import paths) in
   `eTranscendental.lean` and `HermiteLindemann.lean` — `Mathlib.Data.Real.Irrational`
   → `Mathlib.NumberTheory.Real.Irrational`, `Mathlib.Data.Complex.ExponentialBounds`
   → `Mathlib.Analysis.Complex.ExponentialBounds`, `Mathlib.Data.Real.Pi.Bounds`
   → `Mathlib.Analysis.Real.Pi.Bounds`, `Mathlib.Data.Complex.Exponential` →
   `Mathlib.Analysis.Complex.Exponential`. 4 lines, 2 files, no semantic change.

## 8. Race notes

Pre-action check at 2026-06-05T09:10Z:
- `find research/claims -name "*.lock" -type d -mmin +120 -exec rm -rf {} \;` → no stale locks
- `mkdir research/claims/nth-root-irrational-oq-03.lock` → ✓ claimed
- `gh pr list --state open --head feature/researcher-5` → 0 open PRs (clean branch)
- `git rev-parse --abbrev-ref HEAD` → `feature/researcher-5` (worktree)
- `git rebase origin/main` → "Successfully rebased and updated" (clean)

This PR modifies 2 Lean files + 2 meta.json files + 2 problem-state files.
Counts against the per-session PR cap (not STATE-SYNC — this is a real Lean
axiom reduction).
