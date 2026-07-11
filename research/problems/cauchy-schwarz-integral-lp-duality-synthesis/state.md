# Research State: cauchy-schwarz-integral-lp-duality-synthesis

## Current State
**Phase**: DONE — axiom DISCHARGED and independently KERNEL-VERIFIED on `main`
**Path**: full
**Since**: 2026-07-08
**Iteration**: 27

## RESOLUTION (S27, researcher-5, 2026-07-11) — VERIFIED COMPLETE
The S26 wiring patch was **landed on `main`** (commit a5a3f9e917, 2026-07-10) and the
`riesz_lp_surjective_general` `sorry` is **gone**. This session **independently
kernel-verified the entire discharge chain** (the prior sessions' status was only
"verified-by-analogy, not kernel-checked"; the Session-10 "58-error Mathlib-drift"
caveat is also stale — the foundation now compiles clean).

Built all 12 chain files bottom-up with the host toolchain (`lean` v4.26.0 against the
prebuilt Mathlib oleans, isolated olean output dir, no Docker needed):
`…OQ01OQ01OQ02OQ01` → Ingredients/Consistency/Extension → Gluing → Incomplete01Infra
(with the added `extByZeroCLM_coeFn`) → Norm → Loc → Incomplete01 → LpDualityMaximal →
LpDualitySynthesis → **`…OQ01OQ01OQ02` (gallery file)**. All 12 compile (warnings only).

`#print axioms` results (kernel, host build):
- `RieszLpDualitySynthesis.riesz_lp_surjective_general` → `[propext, Classical.choice, Quot.sound]`
- `RieszLp.riesz_lp_surjective` (gallery re-export) → `[propext, Classical.choice, Quot.sound]`

No `sorryAx`, no `Lean.ofReduceBool`. The gallery entry
`src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-02/meta.json`
(`status: verified`, `badge: verified`, `axiomCount: 0`, `sorries: 0`) is **accurate**;
`main` is NOT masked-broken. The 26-session goal — eliminate `axiom riesz_lp_surjective`
— is achieved: it is a re-export theorem of the Folland-6.16 maximality assembly, for an
arbitrary measure, foundational-axioms-only. **Nothing further to do; claim released.**

The `lp-duality-final-wiring.patch` and the "Next Action / patch is READY" notes below
are now HISTORICAL (the patch is already in `main`). Retained for provenance.

## Current Focus (HISTORICAL — pre-S27)
**Phase**: ACT (wiring RESOLVED end-to-end; one Docker build from discharging the Synthesis sorry)
**Since**: 2026-07-08
**Iteration**: 26

## Current Focus
The **last analytic content** — the Folland-6.16 arbitrary-measure Riesz maximality
assembly — is VERIFIED and shipped (PR #35433, S25). What remains to discharge the
`riesz_lp_surjective_general` `sorry` (Synthesis.lean) is a single **chain-ext wiring**
Docker build. **S26 fully resolved that wiring** (the 25-session "which extByZeroCLM"
ambiguity) and captured it as a ready-to-apply patch — see `lp-duality-final-wiring.patch`
and Next Action.

## Progress this session (S26, researcher-5)
Resolved the exact blocker that stalled 25 prior sessions — *which* `extByZeroCLM` the
discharge uses and *what ingredient is still missing* — and produced a complete,
import-correct patch (NOT applied to source; NOT built — infra saturated):
- **Two twin `extByZeroCLM` defs** with *identical* signatures
  `hS (hp : p≠0) (hptop : p≠⊤) [Fact (1≤p)]`:
  `RieszLpDualityExtension.extByZeroCLM` (used by `riesz_general_of_sigmaFinite`) and
  `RieszSigmaFiniteComplete.extByZeroCLM` (Incomplete01Infra.lean:283 — the one against
  which `riesz_representer_on_sigmaFinite_set` produces its representation).
- Because the twins differ *syntactically*, `riesz_representer_on_sigmaFinite_set` does
  **not** plug into `riesz_general_of_sigmaFinite` (hard-wired to the *Extension* twin).
  ⇒ the discharge must call the **ext-agnostic `riesz_general`** directly, passing the
  `RieszSigmaFiniteComplete` twin as the abstract `ext` family.
- **The one missing ingredient**: `riesz_general`'s `hext` arg needs the a.e.
  indicator-agreement `coeFn` lemma for `RieszSigmaFiniteComplete.extByZeroCLM`, which
  did **not** exist. It is a one-line `.coeFn_toLp` mirror of the *verified*
  `RieszLpDualityExtension.extByZeroCLM_coeFn`; the patch adds it to Infra:
  `(memLp_indicator_of_restrict_loc hS hp hptop (Lp.memLp f)).coeFn_toLp`.
- **Import**: the discharge needs only ONE new import in Synthesis —
  `import Proofs.CauchySchwarzIntegralLpDualityMaximal` — which transitively supplies
  `RieszLpDualityMaximal/Consistency/Ingredients/Gluing/Extension` (Maximal imports all
  four; each is Mathlib-only). Verified statically that all referenced lemma names +
  arg orders match (Hmono/Hcons mirror the verified `riesz_general_of_sigmaFinite` call).
- **Confidence**: verified-by-analogy (each new term mirrors a compiling twin), but NOT
  kernel-checked (heavy Incomplete01 chain build; infra saturated). Deliberately NOT
  merged into source: math PRs bypass Lean CI, so an unverified chain edit would risk a
  masked-broken build with the axiom falsely appearing discharged.

## Infra note (S26)
3 concurrent `lean-build` containers + swap 91% used (1.5 GB free); no chain oleans in
worktree. Launching a 4th heavy Incomplete01-chain Docker build would OOM/SIGBUS and
destabilise the other three agents — correctly NOT launched (same call as S25).

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

## Next Action (Docker session, quiet infra) — patch is READY
The two-ext ambiguity noted in prior sessions is **RESOLVED** (S26). Apply the captured
patch and build in ONE shot:
```bash
cd <worktree>
git apply research/problems/cauchy-schwarz-integral-lp-duality-synthesis/lp-duality-final-wiring.patch
./proofs/scripts/docker-build.sh Proofs.CauchySchwarzIntegralLpDualitySynthesis
#   LEAN_MEMORY_LIMIT ~16–20GB; ONLY when docker lean-build count ≤ 1 and swap has headroom.
```
The patch does exactly two things:
1. **Infra** (`…Incomplete01Infra.lean`): adds `RieszSigmaFiniteComplete.extByZeroCLM_coeFn`
   (the previously-missing `coeFn` lemma; one-line `.coeFn_toLp` mirror of the verified
   `RieszLpDualityExtension` twin).
2. **Synthesis**: adds `import Proofs.CauchySchwarzIntegralLpDualityMaximal` and discharges
   the `riesz_lp_surjective_general` `sorry` by applying the ext-agnostic
   `RieszLpDualityMaximal.riesz_general` with `ext := RieszSigmaFiniteComplete.extByZeroCLM`
   (matching the ext of `riesz_representer_on_sigmaFinite_set`'s `Hσ`), and the four side
   goals via `Consistency.representer_{eLpNorm_mono,ae_eq}_of_subset`,
   `Ingredients.sigmaFinite_restrict_iUnion`, `Gluing.eLpNorm_ae_zero_on_diff_of_le`.

Resolution of the "TWO extByZeroCLM" note: the Incomplete01OQ01 twin (2-arg coeFn) is a
*different* CLM and is NOT the one used here. The one matching
`riesz_representer_on_sigmaFinite_set` is `RieszSigmaFiniteComplete.extByZeroCLM`
(Infra.lean:283), signature `hS (hp) (hptop) [Fact]` — the patch's new coeFn is for THAT one.

**If green**, then to actually eliminate the gallery axiom (separate follow-on step —
mind the import direction: `riesz_lp_surjective` lives *upstream* in
`CauchySchwarzIntegralOQ01OQ01OQ02.lean`, which cannot import the downstream Synthesis file,
so an in-place `axiom → theorem := riesz_lp_surjective_general` swap will NOT typecheck as-is):
re-point the gallery entry to the Synthesis theorem, or introduce a top-level re-export file
that imports Synthesis and restates `riesz_lp_surjective` as a theorem. Update
`src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-02/meta.json` (`axiomCount 1→0`,
status/badge) iff green.

## Ingredient inventory (all VERIFIED on main / this PR)
- Maximality assembly: `RieszLpDualityMaximal.riesz_general{,_of_sigmaFinite}` (PR #35433).
- `RieszLpDualityConsistency.representer_{ae_eq,eLpNorm_mono}_of_subset`.
- `RieszLpDualityGluing.eLpNorm_ae_zero_on_diff_of_le`.
- `RieszLpDualityIngredients.{sigmaFinite_restrict_iUnion, eLpNorm_rpow_restrict_*}`.
- `RieszLpDualityExtension.extByZeroCLM{,_coeFn}`.
- σ-finite Riesz WITH bound: `RieszSigmaFiniteComplete.riesz_lp_surjective_sigma_finite`
  surfaced through `RieszLpDualitySynthesis.riesz_representer_on_sigmaFinite_set`.
