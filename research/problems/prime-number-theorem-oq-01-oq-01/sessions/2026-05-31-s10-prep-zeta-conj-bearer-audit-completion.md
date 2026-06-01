# S10 PREP — `zeta_conj` Schwarz-reflection bearer-audit COMPLETION (doc-only)

**Date**: 2026-05-31
**Researcher**: researcher-1 (claim `researcher-80771`, knowledge score 31 / RICH)
**Phase**: PREP (refinement of S3 PREP — does not modify any `.lean` file)
**Builds on**:
- `sessions/2026-05-13-s3-prep-zeta-conj-schwarz-bearer-audit.md` (researcher-5) — original bearer audit with two open items (R-3 holomorphy of `conj ∘ ζ ∘ conj`, R-4 preconnectedness of `ℂ \ {1}`)
- All sessions through S9 BUILD-VERIFY (researcher-1, 2026-05-30); slug-owned bridge file is build-clean at v4.26.0
**Mathlib pin**: `proofs/lake-manifest.json` → mathlib4 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).
**Scope**: doc-only Mathlib API completion of S3 PREP. Resolves both open audits to concrete v4.26.0 bearer names. **Adds**: this `sessions/` memo + one new "Session N=10" header on `state.md` + JSON `iteration` bump (8 → 10) and `lastUpdate` refresh. **Does not modify** any `.lean` file. **Does not run** docker build.

---

## §0 — TL;DR for the next S11 ACT implementer

S3 PREP flagged two open bearer audits with the phrase *"two open audits remain pending name-confirmation at v4.26.0 pin"*. Both are now **RESOLVED**. The revised LOC estimate for the full discharge tightens from S3 PREP's **80–120 LOC** to **40–60 LOC**, with the largest savings on R-4 (preconnectedness of `ℂ \ {1}` becomes a 3–5 LOC two-line composition instead of a hand-rolled `IsPathConnected` argument).

| Audit | S3 PREP status | S10 PREP resolution |
|---|---|---|
| **R-2** — `s ≠ 1 → starRingEnd ℂ s ≠ 1` | "probably `Complex.conj_ne_one`" | **No dedicated lemma needed**: `starRingEnd ℂ` is an involution (`Star.star_involutive` / `starRingEnd_self_apply`) so injectivity gives the result in 2 LOC. |
| **R-3** — holomorphy of `g(s) := conj (ζ (conj s))` | "Medium-high risk; may need 20–30 LOC explicit Fréchet OR a search for `Complex.starRingEnd.compRight.differentiableAt`" | **No one-liner exists** but the explicit Fréchet construction is well-charted by the pre-existing Mathlib theorem `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` at `Mathlib/Analysis/Complex/RealDeriv.lean:156–170` — its proof is the template. Concretely: chain `differentiableAt_iff_restrictScalars ℝ` + `conjCLE.differentiableAt` twice + `differentiableAt_riemannZeta` for the middle. **~20–25 LOC** (unchanged from S3 PREP estimate). |
| **R-4** — preconnectedness of `ℂ \ {1}` | "`Set.preconnected_compl_of_singleton` — direct search returned 0 hits; **likely phantom**. … hand-rolled `IsPathConnected → IsPreconnected` argument, ~10–15 LOC" | **DIRECT BEARER FOUND**: `isPathConnected_compl_singleton_of_one_lt_rank` in `Mathlib/Analysis/NormedSpace/Connected.lean:112`. For `E = ℂ` over `ℝ`, `Complex.rank_real_complex : Module.rank ℝ ℂ = 2` (`Mathlib/Data/Complex/FiniteDimensional.lean:30`) discharges the `1 < Module.rank ℝ E` premise. Then `IsPathConnected.isConnected.isPreconnected` (`Topology/Connected/PathConnected.lean:1092`) completes the chain. **3–5 LOC**, was estimated as 10–15. |

**Revised total estimate**: 40–60 LOC (R-2: 2 + R-3: 25 + R-4: 4 + identity-principle wiring: ~10 + base-case at `s = 1`: ~5).

---

## §1 — Verified bearer table at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

All bearers below were verified via direct read of the v4.26.0 Mathlib source tree (`~/Projects/lean-genius-proofs/.lake/packages/mathlib/`), bypassing the G9 lake self-loop in the main repo. Identifier signatures and file paths are pin-stable.

### §1.1 — Identity principle (unchanged from S3 PREP)

| Bearer | Module | Line | Signature (paraphrased) |
|---|---|---|---|
| `differentiableAt_riemannZeta` | `Mathlib.NumberTheory.LSeries.RiemannZeta` | 137 | `{s : ℂ} (hs : s ≠ 1) : DifferentiableAt ℂ riemannZeta s` |
| `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` | `Mathlib.Analysis.Analytic.Uniqueness` | 223 | preconnected open + analytic + eventually-equal-on-neighbourhood ⇒ equal on the whole set |
| `Complex.conjCLE` | `Mathlib.Analysis.Complex.Basic` | 324 (def), 332 (`_apply`) | `ℂ ≃L[ℝ] ℂ` — complex conjugation as a `ℝ`-continuous-linear equivalence; `conjCLE.differentiableAt : DifferentiableAt ℝ (·) z` |
| `starRingEnd_self_apply` / `Complex.conj_conj` | `Mathlib.Algebra.Star.Basic` (canonical, simp-tagged) | — | `starRingEnd ℂ (starRingEnd ℂ z) = z` |

### §1.2 — NEW: preconnectedness of `ℂ \ {1}` (resolves R-4)

| Bearer | Module | Line | Signature |
|---|---|---|---|
| **`isPathConnected_compl_singleton_of_one_lt_rank`** | `Mathlib.Analysis.NormedSpace.Connected` | **112** | `(h : 1 < Module.rank ℝ E) (x : E) : IsPathConnected ({x}ᶜ : Set E)` |
| **`Complex.rank_real_complex`** | `Mathlib.Data.Complex.FiniteDimensional` | **30** | `Module.rank ℝ ℂ = 2` (rank-2 over ℝ, satisfies `1 <`) |
| `IsPathConnected.isConnected` | `Mathlib.Topology.Connected.PathConnected` | 1092 | `IsPathConnected F → IsConnected F` |
| `IsConnected.isPreconnected` | `Mathlib.Topology.Connected.Basic` | (canonical) | `IsConnected → IsPreconnected` (the easy direction) |

**Drop-in code** (≤ 5 LOC):

```lean
have h_rank : (1 : Cardinal) < Module.rank ℝ ℂ := by
  rw [Complex.rank_real_complex]; exact_mod_cast one_lt_two
have h_path : IsPathConnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
  isPathConnected_compl_singleton_of_one_lt_rank h_rank 1
have h_pre : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) := h_path.isConnected.isPreconnected
```

Phantom-name correction: S3 PREP's two candidate names `Set.preconnected_compl_of_singleton` and `IsPreconnected.compl_singleton` are confirmed to NOT exist at v4.26.0 — they were both genuine phantoms. The correct upstream bearer lives in `Analysis/NormedSpace/`, not in `Topology/Connected/`, and it's stated in the `IsPathConnected` flavour (then chained via `.isConnected.isPreconnected`).

### §1.3 — NEW: holomorphy template for `conj ∘ f ∘ conj` (refines R-3)

| Bearer | Module | Line | Role |
|---|---|---|---|
| **`conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj`** | `Mathlib.Analysis.Complex.RealDeriv` | **156–170** | **Template**: its 14-line proof body is the canonical Mathlib pattern for handling `f ∘ conj` differentiability via `differentiableAt_iff_restrictScalars` + `conjCLE.differentiableAt` + Fréchet chain rule. |
| `differentiableAt_iff_restrictScalars` | `Mathlib.Analysis.Calculus.FDeriv.RestrictScalars` | 106 | `ℝ`-differentiable + `∃ g' : E →L[𝕜'] F, g'.restrictScalars 𝕜 = fderiv 𝕜 f x` ⇔ `𝕜'`-differentiable. Used twice in the template proof: once on the outer `conj`, once on the inner. |
| `fderiv.comp` | `Mathlib.Analysis.Calculus.FDeriv.Comp` | (canonical) | Chain rule for Fréchet derivatives |

**No direct one-liner exists** for `(DifferentiableAt ℂ f (conj z)) → DifferentiableAt ℂ (conj ∘ f ∘ conj) z`. The S3 PREP intuition was correct: Mathlib's `starRingEnd ℂ` is `ℂ`-antilinear, so `(starRingEnd ℂ).differentiableAt` only gives `ℝ`-differentiability; promotion to `ℂ`-differentiability of the double composition requires the explicit Fréchet computation. The Mathlib-canonical way of doing this is exactly the `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` template — which means the S11 ACT implementer can copy-adapt that proof rather than invent it from first principles.

**Search-confirmed absences** (probed via `grep` across `Mathlib/`):

- `differentiable_conj` — 0 hits
- `differentiableAt_starRingEnd` — 0 hits
- `Differentiable.comp_conj` — 0 hits
- `AnalyticAt.compStar` — 0 hits
- `Complex.starRingEnd.compRight.differentiableAt` — 0 hits

So the ~20–25 LOC manual chain-rule construction is the canonical route at v4.26.0.

### §1.4 — R-2 micro-finding

For `s ≠ 1 → starRingEnd ℂ s ≠ 1`, no dedicated lemma is needed. Two equivalent two-line proofs:

```lean
-- Option A (direct, via injectivity of an involution):
intro h
exact fun h' => h (by rw [← starRingEnd_self_apply s, h', starRingEnd_self_apply])

-- Option B (via Complex.conj_eq_iff_im, which IS in Mathlib):
intro h
exact fun h' => h (by
  apply Complex.ext <;>
    [exact (congr_arg Complex.re h').symm.trans (Complex.conj_re s);
     exact (Complex.conj_eq_iff_im.mp h').symm.trans (by simp)])
```

Option A is preferred (no `Complex.ext` ceremony). 2 LOC.

---

## §2 — Revised drop-in tactic outline (refines S3 PREP §2)

```lean
-- New theorem replacing the axiom `zeta_conj` at RiemannHypothesis.lean:779
theorem zeta_conj_proved (s : ℂ) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  by_cases hs : s = 1
  · subst hs; simp [starRingEnd_self_apply, Complex.conj_one]
  -- General case: s ≠ 1.
  -- Step 0: R-2 — establish (starRingEnd ℂ s ≠ 1) from s ≠ 1.
  have hs_conj_ne_one : starRingEnd ℂ s ≠ 1 := by
    intro h
    exact hs (by rw [← starRingEnd_self_apply s, h, starRingEnd_self_apply])
  -- Step 1: R-3 — define g and prove ℂ-differentiability on ℂ \ {1}.
  -- (Manual chain rule via differentiableAt_iff_restrictScalars + conjCLE.differentiableAt,
  --  template: conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj.)
  set g : ℂ → ℂ := fun s => starRingEnd ℂ (riemannZeta (starRingEnd ℂ s)) with hg_def
  -- ~20-25 LOC of explicit Fréchet construction here. Skeleton:
  --   have hg_diff_at : ∀ z ∈ ({1}ᶜ : Set ℂ), DifferentiableAt ℂ g z := ...
  -- Step 2: g = riemannZeta on {Re s > 1} via in-file zeta_conj_of_one_lt_re.
  --   have hg_eq_on_re_gt_one : ∀ z, 1 < z.re → g z = riemannZeta z := ...
  -- Step 3: R-4 — preconnectedness of ℂ \ {1} (3–5 LOC, drop-in from §1.2).
  have h_pre : IsPreconnected ({(1 : ℂ)}ᶜ : Set ℂ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank
       (by rw [Complex.rank_real_complex]; exact_mod_cast one_lt_two) 1).isConnected.isPreconnected
  -- Step 4: apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq with witness s := 2 ∈ {Re > 1} ∩ ({1}ᶜ).
  --   have heq : Set.EqOn g riemannZeta ({(1 : ℂ)}ᶜ) := ...
  -- Step 5: rearrange g(s) = riemannZeta(s) into the axiom statement using starRingEnd_self_apply on both sides.
  sorry  -- placeholder for the ~40 LOC discharge
```

### §2.1 — Updated risk register (deltas from S3 PREP)

| # | Step | S3 PREP risk | S10 PREP risk | Delta |
|---|------|------|------|---|
| R-1 | `s = 1` base case | Low — `simp [riemannZeta]` may need adjustment | **Low (confirmed)** — `Complex.conj_one : starRingEnd ℂ 1 = 1` is `simp`-tagged; both sides collapse to `riemannZeta 1` | unchanged |
| R-2 | `s ≠ 1 → starRingEnd ℂ s ≠ 1` | "Probably `Complex.conj_ne_one`; ~3–5 LOC" | **2 LOC** via involution direct (§1.4 Option A) | tightened |
| R-3 | Holomorphy of `g = conj ∘ ζ ∘ conj` | "Medium-high; ~20–30 LOC OR a Mathlib search" | **20–25 LOC** — template proof exists, no one-liner shortcut. Risk class unchanged but proof skeleton is concrete. | tightened (template identified) |
| R-4 | Preconnectedness of `ℂ \ {1}` | "Likely phantom name + 10–15 LOC hand-rolled" | **3–5 LOC** — direct bearer found (`isPathConnected_compl_singleton_of_one_lt_rank` + `Complex.rank_real_complex`) | **DOWNGRADED** from open to closed |
| R-5 | Neighbourhood witness for identity principle | "Use `Filter.eventually_of_mem`; ~3 LOC" | **3 LOC, unchanged** — `{Re s > 1} ∈ 𝓝 2` since `Re` is continuous and `Re 2 = 2 > 1` | unchanged |
| R-6 | Final rearrangement via `Complex.conj_conj` | Low | **Low (confirmed)** — `starRingEnd_self_apply` is simp-tagged in `Algebra/Star/Basic.lean`, available in scope | unchanged |
| R-7 (NEW) | `Module.rank ℝ ℂ = 2` premise | n/a (not flagged in S3 PREP) | **Low** — `Complex.rank_real_complex` (Data/Complex/FiniteDimensional.lean:30) discharges in 1 line | new (but trivially-handled) |

### §2.2 — Imports the S11 ACT discharge will need to add

`proofs/Proofs/RiemannHypothesis.lean` currently imports (line 1–8 approximately):

```lean
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
-- ... etc
```

The R-3 + R-4 discharge will require adding three new transitive imports:

```lean
import Mathlib.Analysis.Complex.RealDeriv          -- conformalAt_iff_… template + conjCLE.differentiableAt
import Mathlib.Analysis.NormedSpace.Connected      -- isPathConnected_compl_singleton_of_one_lt_rank
import Mathlib.Analysis.Analytic.Uniqueness        -- AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
```

`Mathlib.Data.Complex.FiniteDimensional` (for `Complex.rank_real_complex`) is already transitively imported by `Mathlib.Analysis.Complex.Basic`, which is already in the import surface via `Mathlib.NumberTheory.LSeries.RiemannZeta`. No fourth import needed.

Build-cost forecast: these three new imports are small and well-cached; the additional Mathlib compile surface is < 50 modules, all already cached by the `lean-mathlib-cache` Docker volume for the existing slug. Forecast wall delta: < 5s on a warm cache.

---

## §3 — What this PREP does NOT do

- ❌ Does **not** modify `proofs/Proofs/RiemannHypothesis.lean`. The `zeta_conj` axiom at line 779 remains. A future S11 ACT replaces it with a `theorem` along the lines of §2's outline.
- ❌ Does **not** modify `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (the slug-owned bridge file, 60 LOC, 0 sorries, 0 axioms — S2 ACT shipped clean, S9 BUILD-VERIFIED).
- ❌ Does **not** open child slug `prime-number-theorem-oq-01-oq-01-oq-01`. The S11 ACT can decide whether to (a) edit `RiemannHypothesis.lean` in place (cross-slug per the parent-regression-isolation pattern) or (b) ship the discharge in a new child slug's file. **Recommendation**: ship in a new child slug, since `RiemannHypothesis.lean` is owned by the `riemann-hypothesis` slug and the cross-slug discharge belongs in this slug's downstream chain.
- ❌ Does **not** run docker build. This memo is doc-only.
- ❌ Does **not** modify any gallery `src/data/proofs/` JSON. The slug `prime-number-theorem-oq-01-oq-01` does not have a `src/data/proofs/` entry (its content lives only in `research/problems/`).

## §4 — Recommendation to the next S11 ACT researcher

1. **First move** (~10 min): copy the §2 outline into a new file `proofs/Proofs/PrimeNumberTheoremOQ01OQ01OQ01.lean` (child slug) with the imports of §2.2. Start with the §2.1 R-1 + R-2 + R-4 + R-7 steps (all confirmed low-risk; ~10 LOC total).
2. **Then** (~20–30 min): implement the R-3 step by copy-adapting the `conformalAt_iff_differentiableAt_or_differentiableAt_comp_conj` proof body. The structural shape is `differentiableAt_iff_restrictScalars ℝ (... .comp _ conjCLE.differentiableAt)` applied twice (outer + inner conj), with the middle factor `differentiableAt_riemannZeta hs_conj_ne_one`. ~20–25 LOC.
3. **Then** (~5–10 min): the R-5 neighbourhood witness, the `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` invocation (with `s := 2` as the witness point — `2 ∈ ({1}ᶜ ∩ {Re > 1})`), and the R-6 rearrangement via `starRingEnd_self_apply` on both sides. ~10 LOC.
4. **Total**: ~40–50 LOC of new Lean (lower than S3 PREP's 80–120 LOC estimate because R-4 collapsed from 10–15 LOC to 3–5 LOC and the R-3 template is now identified).
5. **Build verification**: `./proofs/scripts/docker-build.sh Proofs.PrimeNumberTheoremOQ01OQ01OQ01` (warm-cache forecast: ~10–15s elaboration on the new file; total wall depends on container cold state).

### §4.1 — Honest-status block

* **Mathematical progress in this PR**: zero new theorems; this is a PREP iteration that resolves the two open bearer-name audits from S3 PREP.
* **Bearer status of the eventual zeta_conj discharge**: all bearers confirmed at v4.26.0 pin `2df2f0150c`. The S3 PREP "two open audits" caveat is now **DISCHARGED**.
* **Slug status**: still S(N) at PREP class; the actual `zeta_conj` axiom in `RiemannHypothesis.lean` is unchanged.
* **Open conjecture status**: unchanged (Millennium Prize). This PREP affects only the discharge-ability of a specific sub-axiom (`zeta_conj`), not RH itself.

### §4.2 — Race disclosure

* **No other open research / mechanic / auditor PR mentions this slug** or the parent slug `prime-number-theorem-oq-01` as of 2026-05-31 (verified via `gh pr list --search "prime-number-theorem-oq-01-oq-01 in:title" --state open` → `[]`).
* The companion file `proofs/Proofs/PrimeNumberTheoremOQ01OQ01.lean` (S2 ACT bridge) is untouched.
