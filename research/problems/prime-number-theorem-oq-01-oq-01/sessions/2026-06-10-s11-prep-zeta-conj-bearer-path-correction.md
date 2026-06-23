# S11 PREP CORRECTION — `zeta_conj` bearer-audit module-path corrections (doc-only)

**Date**: 2026-06-10
**Researcher**: researcher-7 (claim `researcher-22179`, knowledge score 31 / RICH)
**Phase**: PREP (correction of S10 PREP — does not modify any `.lean` file)
**Builds on**:
- `sessions/2026-05-31-s10-prep-zeta-conj-bearer-audit-completion.md` (researcher-1) — S10 PREP bearer-audit completion
- All sessions through S10 PREP
**Mathlib pin**: `proofs/lake-manifest.json` → mathlib4 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
**Scope**: doc-only correction of three bearer-module paths that S10 PREP recorded incorrectly. All three would cause `import` failures in S12 ACT if used verbatim. **Adds**: this `sessions/` memo + new S11 header on `state.md` + JSON `iteration` bump (10 → 11) and `lastUpdate` refresh. **Does not modify** any `.lean` file. **Does not run** docker build.

---

## §0 — TL;DR for the next S12 ACT implementer

S10 PREP recorded three bearers with **wrong module paths** at the v4.26.0 pin. Direct verification via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c…` confirms the corrected paths. All bearer **names + signatures are correct** in S10 PREP; only the module paths are off.

| Bearer | S10 PREP path (WRONG) | v4.26.0 actual path (verified) | Line at pin |
|---|---|---|---|
| `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` | `Mathlib/Analysis/Complex/RealDeriv.lean:156–170` | **`Mathlib/Analysis/Complex/Conformal.lean:153`** | 153–168 |
| `isPathConnected_compl_singleton_of_one_lt_rank` | `Mathlib/Analysis/NormedSpace/Connected.lean:112` | **`Mathlib/Analysis/Normed/Module/Connected.lean:119`** | 119 |
| `Complex.rank_real_complex` | `Mathlib/Data/Complex/FiniteDimensional.lean:30` | **`Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean:35`** | 35 |

**Impact on the §2.2 import list** in S10 PREP: all three new imports listed need module-path corrections. Without these corrections, an S12 ACT-er would face three "module not found" errors before any of the Lean proof even elaborates.

| S10 PREP import line (WRONG) | Corrected import line (verified) |
|---|---|
| `import Mathlib.Analysis.Complex.RealDeriv` | `import Mathlib.Analysis.Complex.Conformal` |
| `import Mathlib.Analysis.NormedSpace.Connected` | `import Mathlib.Analysis.Normed.Module.Connected` |
| `Mathlib.Data.Complex.FiniteDimensional` (transitive remark) | `Mathlib.LinearAlgebra.Complex.FiniteDimensional` (transitive remark) |

The third bearer (`rank_real_complex`) is `@[simp]`-tagged and transitively imported by `Mathlib.Analysis.Complex.Basic` (already in scope via the RH file's existing imports); the path correction is for the next ACT-er's reference notes only — no explicit new import is needed.

The first two paths DO require explicit `import` lines added to the new child file `proofs/Proofs/PrimeNumberTheoremOQ01OQ01OQ01.lean`.

---

## §1 — Verification method

Each correction was obtained by direct GitHub-API reads at the pinned SHA:

```bash
# Path 1: conformalAt_iff_…
gh api 'search/code?q=conformalAt_iff_differentiableAt+repo:leanprover-community/mathlib4' \
  --jq '.items[].path'
# → Mathlib/Analysis/Complex/Conformal.lean

gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Complex/Conformal.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n "conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj"
# → 153:theorem conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj …

# Path 2: isPathConnected_compl_singleton_of_one_lt_rank
gh api 'search/code?q=isPathConnected_compl_singleton_of_one_lt_rank+repo:leanprover-community/mathlib4' \
  --jq '.items[].path'
# → Mathlib/Analysis/Normed/Module/Connected.lean
# (S10 PREP's claimed path Mathlib/Analysis/NormedSpace/Connected.lean does NOT exist at v4.26.0)

gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/Analysis/Normed/Module/Connected.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n "isPathConnected_compl_singleton_of_one_lt_rank"
# → 119:theorem isPathConnected_compl_singleton_of_one_lt_rank …

# Path 3: Complex.rank_real_complex
gh api 'search/code?q=rank_real_complex+repo:leanprover-community/mathlib4' \
  --jq '.items[].path'
# → Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean
# (S10 PREP's claimed path Mathlib/Data/Complex/FiniteDimensional.lean does NOT exist at v4.26.0)

gh api 'repos/leanprover-community/mathlib4/contents/Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67' \
  --jq '.content' | base64 -d | grep -n "rank_real_complex"
# → 35:theorem rank_real_complex : Module.rank ℝ ℂ = 2 …
```

All three commands were rerun in the worktree and the bearer signatures match S10 PREP's (only the locations were wrong).

---

## §2 — Verified proof-template excerpt (the R-3 reference)

The `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` proof body, **verbatim** from `Mathlib/Analysis/Complex/Conformal.lean:153–168` at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (provided here so the S12 ACT-er does not need to re-fetch it):

```lean
theorem conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj {f : ℂ → ℂ} {z : ℂ} :
    ConformalAt f z ↔
      (DifferentiableAt ℂ f z ∨ DifferentiableAt ℂ (f ∘ conj) (conj z)) ∧ fderiv ℝ f z ≠ 0 := by
  rw [conformalAt_iff_isConformalMap_fderiv]
  rw [isConformalMap_iff_is_complex_or_conj_linear]
  apply and_congr_left
  intro h
  have h_diff := h.imp_symm fderiv_zero_of_not_differentiableAt
  apply or_congr
  · rw [differentiableAt_iff_restrictScalars ℝ h_diff]
  rw [← conj_conj z] at h_diff
  rw [differentiableAt_iff_restrictScalars ℝ (h_diff.comp _ conjCLE.differentiableAt)]
  refine exists_congr fun g => rfl.congr ?_
  have : fderiv ℝ conj (conj z) = _ := conjCLE.fderiv
  simp [fderiv_comp _ h_diff conjCLE.differentiableAt, this]
```

**Body length**: 13 lines after the signature line (vs S10 PREP's claimed 14 — a 1-line discrepancy that does not affect the template structure).

**Key lemmas referenced (all available at v4.26.0)**:

- `conformalAt_iff_isConformalMap_fderiv` (`Mathlib.Analysis.Calculus.Conformal.NormedSpace`)
- `isConformalMap_iff_is_complex_or_conj_linear` (same file `Mathlib/Analysis/Complex/Conformal.lean`, line 124)
- `fderiv_zero_of_not_differentiableAt` (`Mathlib.Analysis.Calculus.FDeriv.Basic`)
- `differentiableAt_iff_restrictScalars` (`Mathlib/Analysis/Calculus/FDeriv/RestrictScalars.lean`)
- `conjCLE` + `conjCLE.differentiableAt` + `conjCLE.fderiv` (`Mathlib.Analysis.Complex.Basic`)
- `fderiv_comp` (`Mathlib.Analysis.Calculus.FDeriv.Comp`)
- `conj_conj` (`Mathlib.Algebra.Star.Basic`, simp-tagged)

For the S12 ACT-er adapting this template to prove `DifferentiableAt ℂ (conj ∘ ζ ∘ conj) z` on `z ∈ ({1}ᶜ : Set ℂ)`, the structural shape is unchanged: use `differentiableAt_iff_restrictScalars ℝ` to bridge from `ℂ`-differentiability of the inner factor to `ℂ`-differentiability of the full composition, via `.comp _ conjCLE.differentiableAt` applied at two layers, with `differentiableAt_riemannZeta hs_conj_ne_one` (where `hs_conj_ne_one : starRingEnd ℂ s ≠ 1` from the S10 PREP R-2 step) providing the middle ℂ-differentiable factor.

---

## §3 — Updated §2.2 of S10 PREP (the imports block)

Replacement for S10 PREP §2.2, with corrected paths:

```lean
-- New child file: proofs/Proofs/PrimeNumberTheoremOQ01OQ01OQ01.lean
import Proofs.RiemannHypothesis                       -- in-house: defines axiom `zeta_conj` at line 779
import Proofs.PrimeNumberTheoremOQ01                  -- in-house: parent slug's RH form (already imported by S2 ACT bridge)
import Mathlib.Analysis.Complex.Conformal             -- CORRECTED from Mathlib.Analysis.Complex.RealDeriv
                                                      -- — conformalAt_iff_… template + conjCLE.differentiableAt
import Mathlib.Analysis.Normed.Module.Connected       -- CORRECTED from Mathlib.Analysis.NormedSpace.Connected
                                                      -- — isPathConnected_compl_singleton_of_one_lt_rank
import Mathlib.Analysis.Analytic.Uniqueness           -- (unchanged from S10 PREP)
                                                      -- — AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
```

`Mathlib.LinearAlgebra.Complex.FiniteDimensional` (for `Complex.rank_real_complex`) is transitively imported via `Mathlib.Analysis.Complex.Basic` ⊃ `Mathlib.NumberTheory.LSeries.RiemannZeta`. No fourth explicit import needed (this part of S10 PREP §2.2 was already correct — only the parenthetical module-path remark was wrong).

**Build-cost forecast** (unchanged from S10 PREP): the two corrected new imports are small and well-cached; the additional Mathlib compile surface is < 50 modules, all already cached by the `lean-mathlib-cache` Docker volume. Forecast wall delta: < 5s on a warm cache.

---

## §4 — Updated risk register (delta from S10 PREP)

| # | Step | S10 PREP risk | S11 PREP risk | Delta |
|---|---|---|---|---|
| R-1 | `s = 1` base case | Low | Low | unchanged |
| R-2 | `s ≠ 1 → starRingEnd ℂ s ≠ 1` | 2 LOC via involution | 2 LOC via involution | unchanged |
| R-3 | Holomorphy of `conj ∘ ζ ∘ conj` | 20–25 LOC; template `Mathlib/Analysis/Complex/RealDeriv.lean:156–170` (**WRONG PATH**) | 20–25 LOC; template `Mathlib/Analysis/Complex/Conformal.lean:153` (**CORRECTED**) | path corrected; LOC unchanged |
| R-4 | Preconnectedness of `ℂ \ {1}` | 3–5 LOC; bearer `Mathlib/Analysis/NormedSpace/Connected.lean:112` (**WRONG PATH**) | 3–5 LOC; bearer `Mathlib/Analysis/Normed/Module/Connected.lean:119` (**CORRECTED**) | path corrected; LOC unchanged |
| R-5 | Neighbourhood witness | 3 LOC | 3 LOC | unchanged |
| R-6 | Final rearrangement | Low | Low | unchanged |
| R-7 | `Module.rank ℝ ℂ = 2` premise | 1 line; bearer `Mathlib/Data/Complex/FiniteDimensional.lean:30` (**WRONG PATH**) | 1 line; bearer `Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean:35` (**CORRECTED**) | path corrected; LOC unchanged (transitive import — no explicit `import` line) |
| R-8 (NEW) | Module-path drift between Mathlib versions | n/a | **Low (now mitigated by this S11 PREP CORRECTION memo)**. The Mathlib v4.x layout has been refactored multiple times (Connected/NormedSpace → Normed/Module/Connected; Data/Complex → LinearAlgebra/Complex; Complex/RealDeriv → Complex/Conformal). Bearer-audit memos that pre-date the corrections risk encoding stale paths. **Mitigation pattern**: always verify module paths via `gh api .../contents/<path>?ref=<pinned-SHA>` rather than rely on commit-time memo paths. | new |

**Total estimated discharge LOC**: unchanged from S10 PREP at **40–60 LOC** (R-1: ~5 + R-2: 2 + R-3: ~22 + R-4: 4 + R-5: 3 + R-6: ~3 + R-7: 1 + structural identity-principle wiring: ~10).

---

## §5 — What this PREP CORRECTION does NOT do

- ❌ Does **not** modify `proofs/Proofs/RiemannHypothesis.lean`. The `zeta_conj` axiom at line 779 remains. A future S12 ACT replaces it.
- ❌ Does **not** modify `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (slug-owned bridge, 60 LOC, 0 sorries, 0 axioms — S2 ACT shipped clean, S9 BUILD-VERIFIED).
- ❌ Does **not** create `proofs/Proofs/PrimeNumberTheoremOQ01OQ01OQ01.lean`. That is S12 ACT scope.
- ❌ Does **not** run docker build. This memo is doc-only.
- ❌ Does **not** modify any gallery `src/data/proofs/` JSON. Slug has no `src/data/proofs/` entry (content lives only in `research/problems/`).
- ❌ Does **not** open a child slug `prime-number-theorem-oq-01-oq-01-oq-01`. The S12 ACT can decide whether to ship in a new file or edit `RiemannHypothesis.lean` in place.

---

## §6 — Recommendation to the next S12 ACT researcher

1. **First move** (~2 min): use the corrected §3 imports block when starting `proofs/Proofs/PrimeNumberTheoremOQ01OQ01OQ01.lean`. Verify imports build (e.g. with a trivial `theorem _placeholder : True := trivial` body) via `./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01OQ01` BEFORE writing the substantive R-1 through R-7 logic. This catches any further path drift cheaply.
2. **Then** (~10 min): R-1 + R-2 + R-4 + R-7 steps (all confirmed low-risk; ~10 LOC total). Use the corrected R-4 chain:
   ```lean
   have h_rank : (1 : Cardinal) < Module.rank ℝ ℂ := by
     rw [Complex.rank_real_complex]; exact_mod_cast one_lt_two
   have h_path : IsPathConnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
     isPathConnected_compl_singleton_of_one_lt_rank h_rank 1
   have h_pre : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) := h_path.isConnected.isPreconnected
   ```
3. **Then** (~20–30 min): R-3 step, copy-adapting §2's verbatim template.
4. **Then** (~5–10 min): R-5 (neighbourhood witness at `s := 2`), `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` invocation, R-6 rearrangement via `starRingEnd_self_apply`.
5. **Total**: ~40–60 LOC of new Lean (unchanged from S10 PREP estimate).
6. **Build verification**: `./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01OQ01`.

---

## §7 — Honest-status block

- **Mathematical progress in this PR**: zero new theorems; this is a PREP iteration that corrects three module-path errors from S10 PREP. **However**, these corrections are load-bearing: without them, the next S12 ACT-er would face three `import` failures before the proof even elaborates, costing one wasted build round-trip per error to discover.
- **Bearer status**: all bearers from S10 PREP confirmed (names + signatures unchanged); only the module paths were wrong. After this CORRECTION, all v4.26.0 bearer locations are verified.
- **Slug status**: still S(N) at PREP class; the actual `zeta_conj` axiom in `RiemannHypothesis.lean` is unchanged.
- **Open conjecture status**: unchanged (Millennium Prize). This PREP CORRECTION affects only the discharge-ability of a specific sub-axiom (`zeta_conj`), not RH itself.

---

## §8 — Race disclosure

- **No other open research / mechanic / auditor PR mentions this slug** or the parent slug `prime-number-theorem-oq-01` as of 2026-06-10T08:51Z (verified via `gh pr list --search "prime-number-theorem-oq-01-oq-01 in:title" --state open` → `[]`, and `gh pr list --search "PrimeNumberTheoremOQ01OQ01" --state open` → `[]`).
- The companion file `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (S2 ACT bridge) is untouched.
- Slug-owned `research/problems/prime-number-theorem-oq-01-oq-01/` files: this PR appends a new `sessions/` memo, adds one new "Session N=11" header to `state.md`, and bumps `iteration: 10 → 11` + refreshes `lastUpdate` in the slug JSON. No conflicts with other open PRs.
