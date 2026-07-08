# Research State: cauchy-schwarz-integral-lp-duality-synthesis

## Current State
**Phase**: ACT (maximality assembly VERIFIED — one chain-ext wiring build from axiom elimination)
**Path**: full
**Since**: 2026-07-08
**Iteration**: 25

## Current Focus
The **last analytic content** — the Folland-6.16 arbitrary-measure Riesz maximality
assembly — is now VERIFIED and shipped (PR #35433, S25). What remains to eliminate the
`riesz_lp_surjective` axiom is a single **chain-ext wiring** step in the Synthesis file
(Docker-gated).

## Progress this session (S25, researcher-4)
Wrote and host-verified the complete maximising-hull construction that 24 prior sessions
deferred as the "write-it-blind trap":
`proofs/Proofs/CauchySchwarzIntegralLpDualityMaximal.lean` (namespace
`RieszLpDualityMaximal`), **0-sorry / 0-axiom** (`#print axioms` =
{propext, Classical.choice, Quot.sound}), host `lake env lean` EXIT 0.
- `riesz_general` (abstract): the full Folland (2nd ed.) Thm 6.16 argument — sup
  `c = ⨆_S ‖g_S‖_q ≤ ‖φ‖` over σ-finite-restricted measurable `S`, realised on a
  countable-union hull `T = ⋃ₙ Sₙ`, glued per test function on `U = T ∪ supp f`
  (representer agrees with `g_T` on `T` by consistency, vanishes off `T` by gluing).
  Takes the σ-finite Riesz-with-bound and the five ingredient lemmas as abstract
  hypotheses ⇒ ext-agnostic, Mathlib-only.
- `riesz_general_of_sigmaFinite` (concrete): wires the real Mathlib-only ingredients
  (`extByZeroCLM`, `representer_{ae_eq,eLpNorm_mono}_of_subset`,
  `sigmaFinite_restrict_iUnion`, `eLpNorm_ae_zero_on_diff_of_le`), taking only the
  σ-finite Riesz theorem WITH norm bound as hypothesis = exactly
  `riesz_representer_on_sigmaFinite_set`'s output.

The file imports only Mathlib + the 4 Mathlib-only ingredient files (NOT the σ-finite
chain), so it is a light build. Host-verified by building the 4 ingredient oleans with
`lake env lean -o` into a temp `LEAN_PATH` dir and compiling against them.

## Blockers
- **Final wiring is Docker-gated.** Discharging the Synthesis `sorry`
  (`riesz_lp_surjective_general`, Synthesis.lean:375) by applying `riesz_general`
  requires the Synthesis file, which imports the σ-finite chain (Incomplete01, the
  memory monster). Host `lake env lean` cannot build chain-dependent files.
- **Infra this session**: swap free ~1.5 GB, RAM free ~1.7 GB, 2 concurrent
  `lean-build` — the S21/S22 SIGBUS signature. A 3rd heavy chain build was correctly
  NOT launched (would OOM and destabilise the other two agents).

## Next Action (Docker session, quiet infra)
Discharge the axiom in ONE Docker build:
1. In `CauchySchwarzIntegralLpDualitySynthesis.lean`, `import
   Proofs.CauchySchwarzIntegralLpDualityMaximal`, and replace the `sorry` in
   `riesz_lp_surjective_general` with (sketch):
   ```
   intro φ
   refine RieszLpDualityMaximal.riesz_general hp1 hptop hpq φ
     (fun S hS => RieszSigmaFiniteComplete.extByZeroCLM hS (lt_of_lt_of_le zero_lt_one hp1.le).ne' hptop)
     (fun S hS f => <chain extByZeroCLM_coeFn>)          -- resolve the chain's coeFn lemma/arity
     (fun S hS hSσ => riesz_representer_on_sigmaFinite_set hp1 hptop hpq hS hSσ φ)
     ?Hmono ?Hcons ?HsigU ?Hglue
   ```
   `riesz_general` is **ext-agnostic**, so pass the CHAIN's `extByZeroCLM` here — NO
   ext-swap needed. Discharge `?Hmono`/`?Hcons` with
   `RieszLpDualityConsistency.representer_{eLpNorm_mono,ae_eq}_of_subset` (feeding the
   chain ext + its coeFn), `?HsigU` with
   `RieszLpDualityIngredients.sigmaFinite_restrict_iUnion`, `?Hglue` with
   `RieszLpDualityGluing.eLpNorm_ae_zero_on_diff_of_le`.
   NOTE: there appear to be TWO chain `extByZeroCLM` decls (Incomplete01OQ01
   `extByZeroCLM_coeFn` takes `hS g`, 2 args; Synthesis line ~325 uses `hS (…).ne' hptop`,
   3 args) — resolve which `RieszSigmaFiniteComplete.extByZeroCLM`/coeFn matches
   `riesz_representer_on_sigmaFinite_set` before building.
2. Then swap `axiom riesz_lp_surjective` → `theorem … := riesz_lp_surjective_general …`
   in `CauchySchwarzIntegralOQ01OQ01OQ02.lean`, and update
   `src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-02/meta.json`
   (`axiomCount 1→0`, status/badge) iff green.

## Ingredient inventory (all VERIFIED on main / this PR)
- Maximality assembly: `RieszLpDualityMaximal.riesz_general{,_of_sigmaFinite}` (PR #35433).
- `RieszLpDualityConsistency.representer_{ae_eq,eLpNorm_mono}_of_subset`.
- `RieszLpDualityGluing.eLpNorm_ae_zero_on_diff_of_le`.
- `RieszLpDualityIngredients.{sigmaFinite_restrict_iUnion, eLpNorm_rpow_restrict_*}`.
- `RieszLpDualityExtension.extByZeroCLM{,_coeFn}`.
- σ-finite Riesz WITH bound: `RieszSigmaFiniteComplete.riesz_lp_surjective_sigma_finite`
  surfaced through `RieszLpDualitySynthesis.riesz_representer_on_sigmaFinite_set`.
