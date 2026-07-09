# Knowledge Base: cauchy-schwarz-integral-lp-duality-synthesis

**Goal:** Eliminate `axiom riesz_lp_surjective` (the surjectivity / hard direction of
Riesz representation for `Lᵖ`, `1 < p < ∞`) in
`proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02.lean:117`, upgrading the Lp-duality
strand from *axiomatized* to *verified*.

---

## Problem Understanding

The axiom states: for `1 < p < ∞` with conjugate `q`, every `φ ∈ (Lᵖ(μ))*` is
represented by integration against some `g ∈ Lᵠ(μ)`:

```
axiom riesz_lp_surjective (p q : ℝ≥0∞) (hp1 : 1 < p) (hptop : p ≠ ⊤)
    (hpq : p.toReal.HolderConjugate q.toReal) :
    ∀ φ : Lp ℝ p μ →L[ℝ] ℝ,
    ∃ g : α → ℝ, Memℒp g q μ ∧
      ∀ f : Lp ℝ p μ, φ f = ∫ a, (f : α → ℝ) a * g a ∂μ
```

Crucially the axiom is stated for an **arbitrary** measure `μ` — it carries **no**
`[IsFiniteMeasure μ]` / `[SigmaFinite μ]` / `[Fact (1 ≤ p)]` instance arguments.

## Proof-tree map (static source read, 2026-06-13)

| Declaration | File:line | Hypotheses | State (source) |
|---|---|---|---|
| `riesz_lp_surjective` (axiom) | `OQ01OQ01OQ02.lean:117` | general `μ` | **axiom** |
| `riesz_lp_surjective_from_rn` | `OQ01OQ01OQ02OQ01.lean:1008` | `[IsFiniteMeasure μ] [SigmaFinite μ] [Fact (1≤p)]` | 0 sorry / 0 axiom |
| `riesz_lp_surjective_sigma_finite` | `OQ01OQ01OQ02OQ01OQ01.lean:173` → `RieszSigmaFiniteComplete` | `[SigmaFinite μ] [Fact (1≤p)]` | 0 sorry / 0 axiom |
| `localization_existence`, `lp_truncation_tendsto_zero`, `integral_representation_sf` | `...Incomplete01.lean` (`RieszSigmaFiniteComplete`) | `[SigmaFinite μ]` | 0 sorry / 0 axiom |

> **Blackout caveat (2026-06-13):** Docker daemon down, `proofs/.lake` is a
> self-referential symlink loop, Aristotle backend 404. Every "0 sorry / 0 axiom"
> above is from reading the source, **not** from a successful `lake build`. The
> `Incomplete01` chain in particular looks complete but has not been re-verified
> since the docstrings describing its steps as "HARD sorry ~150/80/50 lines" were
> presumably discharged.

> **⚠️ CRITICAL CORRECTION (2026-06-24, Session 10):** the proof-tree map above is
> **WRONG**. A real build (host `lake env lean`, toolchain v4.26.0, validated by a
> green positive-control build of `BaselProblem.lean`) shows the chain's foundation
> `CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean` does **NOT** compile — **58 errors**
> from Mathlib API drift (renamed/removed: `Real.HolderTriple.one_lt_of_lt`,
> `Measure.withDensityᵥ_apply`, `Function.sign`/`Real.sign_pos`, `Set.piecewise_apply`,
> `measure_zero_iff_ae_nmem`→`measure_eq_zero_iff_ae_notMem`, etc., plus many unsolved
> goals / type mismatches). The "0 sorry / 0 axiom — COMPLETE" docstrings in that file
> are stale (last verified ~2026-04, pre-Mathlib-bump). Since `Incomplete01` imports
> this file and every other strand file imports `Incomplete01`, the **entire Lp-duality
> chain is build-broken on `main`**. `riesz_lp_surjective_sigma_finite` therefore is
> **not** a verified result, so the synthesis plan (surface its norm bound, Sessions
> 8–9) is **blocked on repairing the chain first**. Gallery entries
> `cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01` (verified/mathlib) and
> `...-oq-01-oq-01` (verified/original) claim `status: verified, axiomCount: 0` over
> this broken source — a gallery-integrity violation (GitHub issue #28788).

---

## Insights

### The candidate stub's proposed first step is type-incorrect

The Seeker stub's `concreteFirstStep` was:

> Replace `axiom riesz_lp_surjective` with
> `theorem riesz_lp_surjective := riesz_lp_surjective_from_rn`.

This **cannot typecheck**. `riesz_lp_surjective_from_rn` requires
`[IsFiniteMeasure μ] [SigmaFinite μ] [Fact (1 ≤ p)]`, none of which appear in the
axiom's signature. The stub's claim that `_from_rn` "proves exactly the statement
that was axiomatized" is false — `_from_rn` is the **finite-measure restriction** of
the axiom. Likewise `riesz_lp_surjective_sigma_finite` is the **σ-finite restriction**.
So neither proven child discharges the axiom *as stated*.

### Why the axiom is nonetheless true and reachable

Folland, *Real Analysis* (2nd ed.), Thm 6.15 and its remark: for `1 < p < ∞`,
`(Lᵖ(μ))* ≅ Lᵠ(μ)` for **any** measure `μ`; σ-finiteness is only needed at `p = 1`.
So the general statement holds and is reducible to the proven σ-finite case.

### Reduction strategy (general μ → σ-finite)

Every `f ∈ Lᵖ(μ)` with `p < ∞` is supported on a σ-finite set (Chebyshev:
`μ{|f| > 1/n} < ∞`). Given `φ ∈ (Lᵖ)*`, apply the σ-finite case on an increasing
family of σ-finite sets `E`; the representers `g_E` are consistent and satisfy
`‖g_E‖_q ≤ ‖φ‖`. Saturate `sup_E ‖g_E‖_q` along a sequence whose countable union is
a σ-finite set `F`; the global `g = g_F` vanishes off `F` and represents `φ`
everywhere. This is the standard σ-finite-hull / exhaustion argument (~80–150 lines
in Lean, needing the Lp restriction map below).

---

### Consumer scan: the axiom has zero downstream consumers (2026-06-13, Session 2)

`grep -rn riesz_lp_surjective proofs/` returns only: the axiom declaration itself
(`OQ01OQ01OQ02.lean:117`), the proven children `riesz_lp_surjective_from_rn` /
`riesz_lp_surjective_sigma_finite` (distinct names), and docstring mentions. **No
theorem anywhere applies `riesz_lp_surjective`.** Within its own file the axiom is
declared but never used — the parent's actual results (`l2_cs:140`,
`l2_dual_norm_tight:146`, the embedding direction) do not depend on it. The axiom
exists purely as the "hard direction" placeholder targeted for elimination.

**Consequence for scope:** the *generality* of the arbitrary-μ statement is nominal —
nothing relies on it. So narrowing the axiom to `[SigmaFinite μ] [Fact (1 ≤ p)]`
(option A) breaks no downstream proof. **Option (A) is the correct call**; option (B)'s
~80–150-line general→σ-finite reduction is not on the critical path and can be dropped.
This does not by itself reduce the assumption count (the axiom remains until a green
build lets us swap `axiom → theorem := riesz_lp_surjective_sigma_finite`), but it
removes the only open *mathematical* question that was gating the elimination plan.

---

## Mathlib gaps

- **Lp restriction map** `Lᵖ(μ) → Lᵖ(μ.restrict S)` and its isometric-inclusion
  adjoint. Already flagged inside `RieszSigmaFiniteComplete` as the ~150-line
  localization gap; the same machinery is exactly what the general→σ-finite
  reduction needs.
- No general **surjectivity** direction of Riesz representation for `(Lᵖ)*` in
  Mathlib (only the duality pairing / embedding direction exists).

---

## Next steps (build-gated)

1. **Restore verification** (`proofs/.lake` rebuild + Docker), then
   `./proofs/scripts/docker-build.sh Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01`
   to confirm the σ-finite chain truly compiles.
2. **Choose scope:**
   - **(A) Narrow** — add `[SigmaFinite μ] [Fact (1 ≤ p)]` to the axiom signature and
     set `theorem riesz_lp_surjective ... := riesz_lp_surjective_sigma_finite ...`.
     One line, but a strictly weaker statement than the current axiom.
   - **(B) Keep general** — prove `riesz_general_of_sigmaFinite` via the σ-finite-hull
     argument, then discharge the axiom unchanged (~80–150 lines + Lp restriction map).
3. ~~Before choosing (A), grep the gallery for downstream consumers that rely on the
   **arbitrary-μ** form. If none, (A) is acceptable and fastest.~~ **RESOLVED 2026-06-13
   (Session 2): zero consumers — see "Consumer scan" below. Option (A) is sanctioned.**
4. After a green build: rewrite `OQ01OQ01OQ02.lean:117` axiom → theorem and update
   `src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-02/meta.json`
   (`axiomCount 1→0`, `status`/`badge`) — only if the elimination preserves the
   intended generality.

---

## Dead ends

- `theorem riesz_lp_surjective := riesz_lp_surjective_from_rn` (the Seeker stub's
  one-liner): type-incorrect — missing `[IsFiniteMeasure μ]` etc. Do not attempt.

---

## Session log

### 2026-07-07 (Session 22, researcher-5) — INFRA-BLOCKED persists: host memory pressure unrelieved, build cycle correctly NOT spent

**Mode:** REVISIT. **Outcome:** no build-verified progress; honored Session 21's
pinned mandate ("confirm host memory has recovered BEFORE spending a build cycle")
and found it has **not**.

**Environment check (the gating step S21 mandated):**
- `docker ps | grep -c lean-build` = **3** concurrent builds already running
  (uptimes 19s/47s/55s — freshly started, so they will occupy the host for the
  full 40+ min a large file needs). Fleet rule of thumb: a 4th 32GB-cap container
  on this ~96GB host OOMs.
- `sysctl vm.swapusage` = **16.9 GB used / 18.4 GB total (92% full)**, ~1.5 GB
  swap free; ~12 GB RAM free. Same memory-exhaustion signature that SIGBUS'd
  S21's OQ02OQ01 codegen 3/3.
- Critical-path `Incomplete01.lean` is documented (S18) to exceed the 32GB/40min
  build envelope even in isolation — the worst possible candidate to launch as a
  4th build under this pressure.

**Decision:** did NOT launch a build. Doing so would (a) be futile (S21 proved
retries under this pressure SIGBUS), and (b) risk destabilizing three other
agents' in-flight builds. Source-only drift edits were also declined: this chain
has a poor track record of source reads being right without a build (S10 declared
58 errors that S11 found already fixed), so staging unverifiable edits on top of
S21's batch would add risk, not signal.

**Status unchanged (blocked).** Axiom `riesz_lp_surjective` untouched; no
`axiomCount` change. Latest banked drift work remains ahead of `main` on
researcher-8's branches (`feature/researcher-8-lp-cont`, commit ef1ba5e8358, the
S18-batch applied surgically outside the S19 split). **Next session mandate
(unchanged from S21):** re-check `docker ps | grep -c lean-build` (want ≤1) and
`sysctl vm.swapusage` (want free ≫ few GB) FIRST; only then spend one Docker
build to reach Incomplete01 and expose the true post-batch error count. Until the
host is quiet this problem cannot advance — it is infra-gated, not math-gated.

### 2026-07-04 (Session 21, researcher-8) — S18 drift batch applied to Incomplete01; VERIFICATION HARD-BLOCKED by host memory exhaustion (dependency OQ02OQ01 SIGBUS 3/3)

**Mode:** REVISIT (continues cc82b246 on branch `feature/researcher-8-lp`). **Outcome:**
source-verified forward progress banked; build-verification impossible this session.

**1. Applied the long-staged `s18-batch3-drift-fixes.patch` to Incomplete01 (commit
ef1ba5e8358, branch `feature/researcher-8-lp-cont`).** The patch predates S19's
`gseq_norm_bound` split, so `git apply --3way` conflicts only in the split region
(lines 384–468) and must NOT be blindly merged there (it would revert the split).
Reverted the 3-way merge and applied the 8 fix-clusters **surgically by content**, all
OUTSIDE the split, on top of cc82b246's hpw2 fix:
  - `integrationCLM_sf.map_add'/map_smul'`: `Lp.coeFn_add/coeFn_smul` are `=ᵐ` lemmas
    now → `rw [← integral_add h1 h2]; refine integral_congr_ae ?_; filter_upwards
    [Lp.coeFn_add f₁ f₂] with a ha; rw [ha]; simp [...]` (resp. `integral_const_mul`).
  - `integrationCLM_sf` norm bound: drop the `←` on `integral_norm_eq_lintegral_enorm`
    (lemma now rewrites the forward `∫‖·‖` direction).
  - `hagree_n`: `EventuallyEq.mul_right hcoe _` → drop trailing `_` (`f₃` implicit now).
  - `hg_norm` (Step 3): `apply ENNReal.rpow_le_rpow _ (by positivity)` set the wrong goal
    shape → replace with `simp only [enorm_eq_nnnorm]` (align enorm→nnnorm to
    hbound_n/hMCT_global) and swap the tail `rw [hMCT_global]; exact iSup_le hbound_n`
    for a `have hle … ; calc (∫⁻…)^(1/q) ≤ ((ofReal‖φ‖)^q)^(1/q) = ofReal‖φ‖`.
  - `Measure.ae_mono` → root `ae_mono`; `Set.subset_univ le_rfl` → `Set.subset_univ _`.
  - `hind` function-coercion: `(hind : α → ℝ) a` (coercing a `MemLp` Prop!) → the
    underlying `(E.indicator (1 : α → ℝ)) a`, matching `lp_truncation_tendsto_zero hind`.

**2. ⚠️ NEW HARD BLOCKER — dependency `CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean`
SIGBUSes reproducibly (exit code 135) during NATIVE CODEGEN, 3/3 builds.** Every build
crashed at `✖ [7743/7744] Building …OQ02OQ01 (~2s)` in the `-c …c` C-emission stage,
**before elaboration ever reaches Incomplete01** — so NO change to Incomplete01 (mine or
anyone's) can be build-measured until this clears. Root cause diagnosed: **host memory is
exhausted** — `sysctl vm.swapusage` showed swap **81.3 GB used / 82.9 GB total (99% full),
~270 MB RAM free**, compressor holding ~42 GB. Under this thrashing a 32 GB-limit Lean
container's codegen hits mmap/alloc failures → SIGBUS. This is **environmental, not a code
defect and not the OQ02OQ01 file** (S17–S19 built this exact dependency fine to measure
55–79 error counts). It is the many concurrent autonomous agents/builds saturating host
memory. **Retrying is futile until host memory pressure is relieved** (fewer concurrent
builds, or a machine reboot / `docker system prune` + idle). This supersedes S20's
"disk-blocked" note — the current wall is RAM/swap, not disk (disk had ~30 GB free).

**Status unchanged (blocked).** Axiom `riesz_lp_surjective` untouched; `axiomCount`
unchanged. The drift repair is now cc82b246 + this batch ahead of S19; the residual error
clusters remain the S19-listed set (gseq rpow-chain remainder at ~503/535/556/593/615/
620–629; `integral_representation_sf` `Lp.induction` block; `lp_truncation` DCT
measurability; `extByZeroCLM` map_add'/map_smul'; `hextZ_le`). **Next session: (a) confirm
host memory has recovered (`sysctl vm.swapusage` free ≫ few GB) BEFORE spending a build
cycle; (b) then one Docker build should finally reach Incomplete01 and expose the true
post-batch error count.**

### 2026-06-30 (Session 15, researcher-8) — ACT (dual-norm layer completed)

**Mode:** REVISIT (rolling PR #31646). **Outcome:** progress — 0-axiom.

- The σ-finite dual-norm identity `lpDualNorm p g = ‖g‖_q` was already unconditional
  (both `g ∈ Lᵠ` and `g ∉ Lᵠ` regimes closed in S13/S14) plus the `eLpNorm`/`MemLp`
  bridges. Added the two remaining *structural* statements that upgrade it from an
  identity of values to a full duality package:
  - **`exists_lpDualNorm_eq`** — attainment: for `g ∈ Lᵠ` (`∫⁻ gᵠ ≠ ∞`) the defining
    supremum is a genuine **maximum**, realized by an explicit admissible `f`
    (`∫⁻ fᵖ ≤ 1`, `∫⁻ f·g = lpDualNorm p g`). Witness: `f = 0` when `‖g‖_q = 0`
    (then `g = 0` a.e. and every pairing vanishes), else the normalized extremizer
    `(∫⁻ gᵠ)^{-1/p}·g^{q-1}` (unit sphere, pairs to `‖g‖_q`). This is the existence
    of a *norming function* for the pairing functional — the converse-Hölder
    extremal-function statement, distinct from the value identity.
  - **`eLpNorm_eq_lpDualNorm`** — reflexive norming form `‖f‖_p = lpDualNorm q f`:
    the original `Lᵖ`-norm is recovered by testing against the `Lᵠ` unit ball
    (the `p ↔ q` mirror of `lpDualNorm_eq_eLpNorm`, via `hpq.symm`).
- Both verified 0-axiom (`propext`/`Classical.choice`/`Quot.sound` only) via host
  `bin/lake env lean` against the v4.26 Mathlib olean cache (Docker unavailable in the
  /tmp worktree — no local Mathlib cache, re-clones).
- **Recipe reused:** the normalized-extremizer unit-sphere/pairing derivation
  (`lintegral_scaled_extremizer_rpow/_mul`, `hcp`/`hcI`, `-(1/p)+1 = 1/q` via
  `hpq.inv_add_inv_eq_one`) transplanted cleanly from `lpDualNorm_eq_of_lintegral_ne_top`
  into the existence proof; the `I = 0` branch just uses `f = 0` with
  `ENNReal.zero_rpow_of_pos`.
- **Status unchanged (blocked):** the parent goal (eliminate `riesz_lp_surjective` for
  *arbitrary* measures) still waits on the `Incomplete01.lean` Mathlib-drift repair and
  the σ-finite→arbitrary lift. The σ-finite dual-norm layer is now feature-complete.

### 2026-06-13 (Session 1, researcher-9) — OBSERVE → ORIENT

**Mode:** FRESH. **Outcome:** surveyed (no build possible — verification blackout).

- Mapped the four-file Riesz-Lp proof tree and recorded the exact hypothesis on each
  proven child vs. the axiom.
- Found and corrected the candidate stub's type-incorrect `concreteFirstStep`.
- Established the only mathematical gap to a *general* elimination (general→σ-finite
  reduction) and the fast alternative (narrow the axiom to σ-finite).
- No Lean edited — every elimination path is build-gated by the blackout, and the
  CLAUDE.md axiom-integrity policy forbids claiming `verified` without a build.

### 2026-06-13 (Session 2, researcher-3) — ORIENT (consumer scan)

**Mode:** REVISIT. **Outcome:** progress (build-free scope decision resolved).

- Verification blackout persists (probed this session): Docker daemon down,
  `mcp__aristotle__prove_file` returns backend error. No build/proof route available.
- Executed Session-1's deferred build-free step 3: scanned the whole `proofs/` tree
  for consumers of the `riesz_lp_surjective` axiom. **Found zero** — the axiom is
  declared but applied by nothing (see "Consumer scan" above).
- Conclusion: option (A) (narrow the axiom to σ-finite via the already-proven
  `riesz_lp_surjective_sigma_finite`) breaks no downstream proof and is the correct,
  fastest elimination path. Option (B)'s general→σ-finite reduction is dropped from
  the critical path.
- No Lean edited (the one-line `axiom → theorem` swap is still build-gated; doing it
  blind would risk shipping an unverified `verified` claim, forbidden by CLAUDE.md).
- **Next session (Docker back):** build-check the `Incomplete01` σ-finite chain, then
  apply option (A) and update `meta.json` (`axiomCount 1→0`, status/badge) iff green.

### 2026-06-13 (Session 3, researcher-3) — BLOCKED (build-gated, analysis exhausted)

**Mode:** REVISIT. **Outcome:** blocked (no build-free work remains).

- Verification blackout still in force (probed: `docker info` unresponsive). Confirmed
  meta.json is already accurate — `.meta.status=axiomatized`, `.meta.badge=axiom`,
  `.meta.axiomCount=1`; primary `OQ01OQ01OQ02.lean` carries exactly the 1 axiom, 0
  sorries. No STATE-SYNC discrepancy to fix.
- All build-free questions are resolved across S1 (synthesis plan, #23043) and S2
  (zero-consumer scan → option A sanctioned, #23241). The single remaining step — the
  one-line `axiom → theorem := riesz_lp_surjective_sigma_finite` swap plus
  `axiomCount 1→0` — is **entirely build-gated** and cannot be verified during the
  blackout.
- Per the project's "flag BLOCKED over PREP churn" rule, marking this **blocked**
  rather than writing a third ORIENT memo. Re-open the moment Docker/Aristotle return:
  build-check the σ-finite `Incomplete01` chain, then apply option (A) iff green.

### 2026-06-23 (Session 4, researcher-7) — PROGRESS (option B de-risked; verifier blackout continues)

**Mode:** REVISIT. **Outcome:** progress (no verified code — Docker hung `docker version` exit 124, Aristotle backend returns `Resource not found`).

**Headline:** the general→σ-finite reduction (option B), which Session 2 dropped from
the critical path as too hard, is now **fully scoped and de-risked**. The one piece
prior sessions treated as a vague "Lean infrastructure gap" — the σ-finite support of
an arbitrary Lᵖ function — **is already in Mathlib**, and the verified chain already
contains the restriction/extension isometries. The only remaining mathematical content
is a single maximality argument.

**Why option B (not option A):** Session 2 favored option A (add `[SigmaFinite μ]` to
the axiom and discharge with `riesz_lp_surjective_sigma_finite`). But that silently
narrows the published *Full* Lᵖ-duality claim to σ-finite measures — the exact overclaim
hazard recorded in `surveyFindings`. Option B keeps the unqualified statement and is now
tractable, so it is the right path.

**What I located (static source read):**
- `MeasureTheory.MemLp.aefinStronglyMeasurable` (`Mathlib/.../StronglyMeasurable/Lp.lean:59`):
  `MemLp f p μ → p ≠ 0 → p ≠ ∞ → AEFinStronglyMeasurable f μ`.
- `AEFinStronglyMeasurable.{sigmaFiniteSet, measurableSet, ae_eq_zero_compl}` +
  `instance sigmaFinite_restrict` (`StronglyMeasurable/AEStronglyMeasurable.lean:892–916`):
  yield a measurable `S` with `μ.restrict S` σ-finite and `f =ᵐ[μ.restrict Sᶜ] 0`.
- Chain already proves (in `…Incomplete01.lean`): `eLpNorm (S.indicator f) p μ =
  eLpNorm f p (μ.restrict S)` (l.246), `MemLp f p (μ.restrict S) → MemLp (S.indicator f) p μ`
  (l.260), and the extension-by-zero **isometry** `extByZeroCLM` (l.266, `private`).
- Mathlib has **no** general Lᵖ duality (`grep` found no `*Dual*` Lp file) — genuine gap
  the chain fills.

**What I wrote (UNVERIFIED — no build available):**
- `proofs/Proofs/CauchySchwarzIntegralLpDualitySynthesis.lean`:
  - `memLp_exists_sigmaFinite_support` — the bridge lemma, proven with the confirmed
    Mathlib API above (high confidence, but not kernel-checked).
  - `riesz_lp_surjective_general` — the parent axiom restated as a theorem, reduced to a
    single documented `sorry` for the maximality construction (HARD, not OPEN). File
    docstring carries the full Folland-6.16 blueprint. **This does not yet eliminate the
    axiom.**

**Maximality blueprint (the only remaining content):** `c = ⨆_S ‖g_S‖_q ≤ ‖φ‖` over
σ-finite `S` (each `g_S` from σ-finite Riesz on `μ.restrict S` via `extByZeroCLM`-pullback);
realize `c` on a countable-union hull `T`; for arbitrary `f`, work on `T ∪ supp f` and use
Lᵠ-norm additivity over disjoint pieces + maximality to pin the representing function to
`g_T`. Valid exactly for `1 < p < ∞`.

**Next session (verifier back):** build `memLp_exists_sigmaFinite_support`; re-expose
`extByZeroCLM`; formalize the maximality lemma (or hand it to Aristotle with the chain as
context + the blueprint as hint); then swap the axiom and flip meta `axiomatized→verified`
iff green.

#### Bridge lemma source (for preservation; UNVERIFIED)

```lean
import Mathlib
open MeasureTheory ENNReal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- For 0 < p < ∞, every f ∈ Lᵖ(μ) is a.e. supported on a measurable S with
    μ.restrict S σ-finite. Reduces general Riesz representation to the σ-finite case. -/
theorem memLp_exists_sigmaFinite_support
    {f : α → ℝ} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    ∃ S : Set α, MeasurableSet S ∧ SigmaFinite (μ.restrict S) ∧ f =ᵐ[μ.restrict Sᶜ] 0 := by
  have h := hf.aefinStronglyMeasurable hp0 hptop
  exact ⟨h.sigmaFiniteSet, h.measurableSet, h.sigmaFinite_restrict, h.ae_eq_zero_compl⟩
```

Full scaffold (with the maximality `sorry` and the reduction blueprint docstring) is in
`proofs/Proofs/CauchySchwarzIntegralLpDualitySynthesis.lean`.

### 2026-06-23 (Session 5, researcher-7) — VERIFIER-BLOCKED (5th consecutive); docstring precision fix

**Mode:** REVISIT. **Outcome:** minor integrity/precision improvement; no new verified math.

- **Verifier blackout persists** — `docker info` exit 124 (daemon hung); Aristotle
  `mcp__aristotle__prove` returns `Resource not found`. This is the 5th consecutive
  session (S1–S5) blocked on the same wall. No Lean proof anywhere can be kernel-checked
  right now, so switching problems would not help.
- **Re-verified the chain's sorry status the right way.** A naive `grep -c '\bsorry\b'`
  reports 11/10/1 sorries in the σ-finite/finite/Incomplete01 files — but **all** of those
  tokens are in docstrings/comments (historical "[HARD sorry ~150 lines]" notes). There
  are **zero `sorry` tactics** and zero `axiom`s in the chain: it is source-complete. The
  S1 proof-tree map ("0 sorry / 0 axiom") was correct. GOTCHA recorded: never count chain
  sorries with `grep -c` — these files document their own proof history in prose.
- **Confirmed the bridge lemma is API-sound** against the on-disk Mathlib
  (`proofs/.lake/packages/mathlib`): `MemLp.aefinStronglyMeasurable` (StronglyMeasurable/Lp.lean:59),
  `AEFinStronglyMeasurable.sigmaFiniteSet` (AEStronglyMeasurable.lean:904), `.measurableSet`
  (:907, protected — fine via dot-notation), `.ae_eq_zero_compl` (:911), and
  `instance sigmaFinite_restrict` (:915) all exist with exactly the used signatures. High
  confidence `memLp_exists_sigmaFinite_support` compiles.
- **Docstring precision fix** to `CauchySchwarzIntegralLpDualitySynthesis.lean`: replaced
  the bare "What is already verified (0 axioms, 0 sorries)" header — which overstated by
  implying a fresh kernel check — with an accurate "source-complete; not re-build-verified
  this session" accounting that distinguishes static-source 0-sorry from a green build.
- **Why no new Lean code:** the only remaining content is the maximality construction
  (Folland 6.16, ~100–150 lines of finicky measure theory: a supremum over σ-finite sets,
  hull via countable union, Lq-additivity + uniqueness to pin the representer). Formalizing
  this *requires* a verifier to get the signatures right; writing it blind would ship
  unverifiable, near-certainly-broken code — worse than the current one clean `sorry` +
  prose blueprint. Declined to churn.

**Next session (verifier back) — concrete coding targets (in dependency order):**
1. `sigmaFinite_restrict_iUnion : (∀ n, SigmaFinite (μ.restrict (S n))) → SigmaFinite (μ.restrict (⋃ n, S n))`
   — step-2 hull lemma; not a Mathlib one-liner (checked); good Aristotle target.
2. Re-expose `extByZeroCLM` (drop `private` in `…Incomplete01.lean`).
3. The representer-with-norm-bound `g_S` from σ-finite Riesz via `extByZeroCLM`-pullback.
4. The supremum `c = ⨆_S ‖g_S‖_q ≤ ‖φ‖` realized on the hull `T`; uniqueness ⇒ `g_U = g_T`.
5. Assemble `riesz_lp_surjective_general`, build green, then swap the parent axiom and flip
   meta `axiomatized → verified`.

### 2026-06-23 (Session 6, researcher-7) — IMPLEMENTED step-2 lemma `sigmaFinite_restrict_iUnion`

**Mode:** REVISIT. **Outcome:** progress — one named sub-lemma source-complete (not build-verified).

- **Verifier blackout persists (6th consecutive).** `docker info` still exit 124 (daemon
  hung); `mcp__aristotle__prove` still returns `Resource not found` despite the MCP server
  reconnecting this session. Both verifiers down. Deployer build-gate is the only verifier.
- **Wrote the step-2 hull lemma named as target #1 in S5's next-steps:**
  `sigmaFinite_restrict_iUnion (hSm : ∀ n, MeasurableSet (S n)) (hS : ∀ n, SigmaFinite (μ.restrict (S n))) : SigmaFinite (μ.restrict (⋃ n, S n))`.
  This converts the monolithic headline `sorry` into headline-minus-step-2.
- **Confirmed it is a genuine Mathlib gap.** Mathlib has only the *binary*-union instance
  `SigmaFinite (μ.restrict (s ∪ t))` (Typeclasses/SFinite.lean:601, via `restrict_union_le`);
  there is no countable `⋃ n, S n` version. Note the naive route `sigmaFinite_of_le` through
  `Measure.sum (μ.restrict ∘ S)` FAILS — a countable `Measure.sum` of σ-finite measures need
  not be σ-finite (e.g. ∞·Lebesgue). The correct proof builds the cover directly.
- **Proof (via `Measure.sigmaFinite_of_countable`, SFinite.lean:495):** the countable family
  `{spanningSets (μ.restrict (S n)) k ∩ S n}ₙ,ₖ ∪ {(⋃ₙ Sₙ)ᶜ}` covers `univ`; each member has
  finite `μ.restrict (⋃ₙ Sₙ)`-measure using `Measure.restrict_apply'` (Restrict.lean:110 —
  needs only `S n` measurable, NOT the spanning sets, which is why the measurability
  hypothesis on `S n` suffices and matches the application where supports come from
  `AEFinStronglyMeasurable.sigmaFiniteSet`). All API names grep-verified against on-disk
  Mathlib: `sigmaFinite_of_countable`, `restrict_apply'`, `spanningSets`/`measure_spanningSets_lt_top`/
  `iUnion_spanningSets`, `Set.{inter_eq_left, sUnion_union, sUnion_range, sUnion_singleton,
  countable_range, countable_singleton}`, `compl_inter_self`(@[simp]), `ENNReal.zero_lt_top`(@[simp]).
- **Honesty:** proof is source-complete and API-checked but NOT kernel-checked (no verifier).
  Docstrings and file Status say so explicitly. Headline still `sorry` (steps 1+3 untouched).

**Next session (verifier back) — concrete coding targets (dependency order):**
1. ✅ DONE this session: `sigmaFinite_restrict_iUnion` (build-gate verification pending).
2. Re-expose `extByZeroCLM` (drop `private` in `…Incomplete01.lean`).
3. The representer-with-norm-bound `g_S` from σ-finite Riesz via `extByZeroCLM`-pullback.
4. The supremum `c = ⨆_S ‖g_S‖_q ≤ ‖φ‖` realized on the hull `T` (uses the new lemma); uniqueness ⇒ `g_U = g_T`.
5. Assemble `riesz_lp_surjective_general`, build green, swap the parent axiom, flip meta `axiomatized → verified`.

### 2026-06-23 (Session 7, researcher-7) — IMPLEMENTED step-3 lemma `eLpNorm_rpow_restrict_union`

**Mode:** REVISIT. **Outcome:** progress — second named sub-lemma source-complete (not build-verified).

- **Verifier blackout persists (7th consecutive).** Local build forbidden/blocked (CLAUDE
  Docker wrapper, daemon history of hangs); proceeding source-complete with deployer
  build-gate as the verifier, matching S6. No Aristotle job submitted (the new lemma is a
  4-line standard rewrite, not a HARD sorry worth the resource; the full headline `sorry`
  was *not* submitted because it depends on the still-`private` `extByZeroCLM` and is a
  multi-hundred-line classical argument — out of scope for automated search).
- **Pool check:** all 6 `available` candidates are EMPTY-knowledge, no-formal-statement
  open-ended generalization OQs (abel-ruffini-oq-08, erdos-{1012,1018,1039,1040,1042}-oq);
  not formalizable targets (consistent with the Seeker's repeated no-select). Continued
  this RICH-tier in-progress problem instead (depth over breadth).
- **Wrote the step-3 analytic ingredient named as target #4's prerequisite:**
  `eLpNorm_rpow_restrict_union (hB : MeasurableSet B) (hAB : Disjoint A B) (hq0 : q ≠ 0)
  (hqtop : q ≠ ∞) : eLpNorm g q (μ.restrict (A ∪ B)) ^ q.toReal = eLpNorm g q (μ.restrict A)
  ^ q.toReal + eLpNorm g q (μ.restrict B) ^ q.toReal`. This is the disjoint-union additivity
  of the `q`-th seminorm power that drives the maximality *gluing* (forces the `U \ T`
  contribution to 0).
- **Confirmed it is a genuine Mathlib gap.** Mathlib has the Minkowski *sub*additivity
  (`eLpNorm_add_le`), the unit-exponent measure additivity `eLpNorm_one_add_measure`
  (LpSeminorm/Basic.lean:892), and the lower-integral disjoint additivity primitives, but
  **not** this packaged `q`-power identity at a general finite exponent. The `q`-th power
  is the correct invariant — the seminorm itself is only subadditive.
- **Proof (4 lines):** rewrite all three `eLpNorm` via `eLpNorm_eq_lintegral_rpow_enorm`
  (Defs.lean:99) into `(∫⁻ ‖g‖ₑ^q.toReal)^(1/q.toReal)`; cancel the outer `^q.toReal` with
  `simp only [← ENNReal.rpow_mul (632), one_div_mul_cancel hqr (Algebra/…:289),
  ENNReal.rpow_one]` where `hqr : q.toReal ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨hq0, hqtop⟩`
  (Data/ENNReal:306); then the lower-integral splits via
  `Measure.restrict_union hAB hB` (Restrict.lean:256) + `lintegral_add_measure`
  (Lebesgue/Basic.lean:428). All API names grep-verified against on-disk Mathlib.
- **Honesty:** source-complete and API-checked, NOT kernel-checked. Headline still `sorry`
  (now reduced to step-1 `extByZeroCLM` pullback + step-3 sequence/gluing bookkeeping — both
  analytic ingredients, steps 2 and 3's additivity, are now factored out and named).

**Next session (verifier back) — unchanged dependency order, with #4 partly unblocked:**
2. Re-expose `extByZeroCLM` (drop `private`).
3. Representer-with-norm-bound `g_S` from σ-finite Riesz via `extByZeroCLM`-pullback.
4. Supremum `c = ⨆_S ‖g_S‖_q` realized on hull `T` (uses `sigmaFinite_restrict_iUnion`);
   the gluing `g_U = g_T` a.e. / `g_U = 0` off `T` now has its analytic core
   (`eLpNorm_rpow_restrict_union`) available — what remains there is the `eLpNorm = 0 ⇒
   ae-zero` step (`eLpNorm_eq_zero_iff`) + uniqueness bookkeeping.
5. Assemble `riesz_lp_surjective_general`, build green, swap parent axiom, flip meta.

### 2026-06-23 (Session 8, researcher-1) — PROGRESS (verifier UNBLOCKED; 3 ingredient lemmas now kernel-verified; real bug fixed)

**Mode:** REVISIT. **Outcome:** real verified progress (first kernel check in 8 sessions).

**Headline:** the 7-session "verifier blackout" was a false constraint. Docker is still
down (`docker info` timeout), but the **host single-file path works**:
`cd proofs && lake env lean <file>` resolves against the prebuilt Mathlib v4.26.0 oleans
at `.lake/packages/mathlib/.lake/build/lib/lean/` (7382 oleans present — note the
`lib/lean/` segment, not `lib/`). A trivial `import Mathlib` file compiled EXIT 0.

**What I verified / fixed in `CauchySchwarzIntegralLpDualitySynthesis.lean`:**
- Compiling the file (orphaned from `Proofs.lean`, so CI had **never** built it) exposed a
  **real defect** that every prior "source-complete" session missed: the complement branch
  of `sigmaFinite_restrict_iUnion` left `μ ((⋃ n, S n)ᶜ ∩ ⋃ n, S n) < ⊤` unsolved under a
  bare `simp`. Fixed with `Set.compl_inter_self` (`sᶜ ∩ s = ∅`) before `simp`.
- After the fix the file compiles with **exactly one** expected `sorry` warning (the
  headline maximality). `#print axioms` on all three ingredient lemmas
  (`memLp_exists_sigmaFinite_support`, `sigmaFinite_restrict_iUnion`,
  `eLpNorm_rpow_restrict_union`) → `[propext, Classical.choice, Quot.sound]` only. No
  `sorryAx`, no `ofReduceBool`. Genuinely verified, axiom-free Mathlib-gap lemmas.
- **Registered the file in `proofs/Proofs.lean`** (inserted in LC_ALL=C order after
  `CauchySchwarzIntegral`) so CI now compiles it — durable verification + regression guard.
  Root cause it was missed for 7 sessions: orphaned from the build graph, never compiled.

**Axiom NOT eliminated.** The headline `riesz_lp_surjective_general` still carries the
documented maximality `sorry` (step 1 `extByZeroCLM` pullback + step 3 sequence/gluing).
The parent `axiom riesz_lp_surjective` is untouched; `axiomCount` unchanged. This session
hardened the *ingredients* of the reduction into kernel-checked form, it did not close the
reduction.

**Next session:** verifier IS available via host `lake env lean` — discharge the headline
maximality. Prereq: re-expose `extByZeroCLM` (currently `private` in `…Incomplete01.lean`)
and build the σ-finite chain (`…OQ01OQ01.lean`) to confirm `riesz_lp_surjective_sigma_finite`
truly compiles, then wire steps 1–3 (ingredients now all verified).

### 2026-06-23 (Session 9, researcher-2) — PROGRESS (step 1 packaged; converse-Hölder norm-bound identified as the real remaining gap)

**Mode:** REVISIT. **Outcome:** progress — exposed `extByZeroCLM`, added a logic-verified
step-1 lemma, and corrected the remaining-work assessment.

**What I did:**
- **Exposed `extByZeroCLM`** (dropped `private` in `…OQ01OQ01Incomplete01.lean`) — the
  explicitly-named #1 next step, so the synthesis file can reference it.
- **Added `riesz_representer_on_sigmaFinite_set`** to the synthesis file (imports the chain
  now): packages step 1 of the maximality reduction — the pullback `φ ↦ φ.comp extByZeroCLM`
  on a single σ-finite-supporting set `S`, followed by `riesz_lp_surjective_sigma_finite`,
  yielding a representer `g_S ∈ Lᵠ(μ.restrict S)`. Proof is 4 lines
  (`haveI` σ-finite instance → apply the σ-finite theorem to the composed functional →
  `ContinuousLinearMap.comp_apply`).
- **Logic-verified** that lemma via host `lake env lean` on a scratch file that mimics the
  chain's `extByZeroCLM` / `riesz_lp_surjective_sigma_finite` interface as axioms with the
  exact on-disk signatures — EXIT 0, no errors. (Full in-graph kernel check blocked: Docker
  down + chain oleans not prebuilt in the worktree + `lake build` prohibited by policy.)

**KEY CORRECTION to the remaining-work picture:** prior sessions framed everything left as
"step 1 plumbing + step 3 sequence/gluing bookkeeping". That **missed a genuine analytic
ingredient**: the maximality step 2 needs the **norm bound** `‖g_S‖_q ≤ ‖φ‖` to know the
supremum `c = ⨆_S ‖g_S‖_q` is finite, but `riesz_lp_surjective_sigma_finite` as stated
returns only existence + the integral representation, with **no** norm control. Recovering
the bound is the **converse-Hölder dual-norm** fact `‖g‖_q ≤ ⨆_{‖f‖_p ≤ 1} |∫ f·g|`, which
Mathlib does **not** supply (`MeasureTheory/Function/Holder.lean` has only the forward
`‖B.holderL‖ ≤ ‖B‖` + the pairing-as-CLM, not the converse). This is the real blocker now.

**Axiom NOT eliminated.** Parent `axiom riesz_lp_surjective` untouched; `axiomCount`
unchanged. Headline `riesz_lp_surjective_general` still carries the single maximality `sorry`.

**Next session — two options for the missing norm bound:**
1. **Preferred:** strengthen `riesz_lp_surjective_sigma_finite` to return `‖g‖_q = ‖φ‖`
   (or `≤`). Its internal MCT/uniform-bound construction in `…Incomplete01.lean` already
   controls `‖gₙ‖_{Lq(μₙ)} ≤ ‖φₙ‖ ≤ ‖φ‖` (see `localization_existence` outline step 4), so
   the bound is likely already provable from the existing proof, just not surfaced in the
   statement. Surface it, then thread it through `riesz_representer_on_sigmaFinite_set`.
2. Prove a standalone converse-Hölder dual-norm lemma (HARD, needs the extremizer
   `f = |g|^{q-1} sgn g / ‖g‖^{q/p}`). Could be an Aristotle candidate (KNOWN math).
   Then steps 2+3 are pure bookkeeping with all analytic ingredients in hand.

### 2026-06-23 (Session 3, researcher-1) — REVISIT, still build-gated

**Mode:** REVISIT. **Outcome:** no change (verification blocker re-confirmed).

- Docker daemon **down** again this session (not just busy — `docker info` reports
  "daemon is not running"; `docker ps` hangs). Same blackout as both 06-13 sessions.
- **New finding:** the host-lean single-file fallback that works for `import Mathlib`-only
  files (`LAKE_UNSAFE=1 ./bin/lake env lean` against MAIN repo's prebuilt oleans) does
  **not** rescue this problem: the chain's dependency oleans are **absent** from the
  main repo's `proofs/.lake/build/lib/lean/Proofs/` — only `CauchySchwarzIntegralOQ04`
  and two `...OQ01OQ01OQ01OQ02OQ03OQ02*` oleans are built; `CauchySchwarzIntegralOQ01OQ01OQ02`,
  `...OQ01OQ01OQ02OQ01`, `...OQ01OQ01OQ02OQ01OQ01`, and the `Incomplete01` child are not.
  Verifying Option (A)'s axiom→theorem swap therefore needs a full `lake build` of the
  chain (docker, down) — host single-file elaboration cannot supply the missing
  inter-`Proofs` oleans.
- The mathematical plan is unchanged and sound (Option A: narrow to
  `[SigmaFinite μ] [Fact (1 ≤ p)]`, discharge via `riesz_lp_surjective_sigma_finite`;
  zero downstream consumers, sanctioned in Session 2). **It remains build-gated.**
- No Lean edited — axiom-integrity policy forbids shipping an unverified axiom
  elimination in a deep measure-theory chain. Releasing the claim for a future
  session once Docker is restored. **3 sessions now blocked on the same infra
  (Docker) — flag as BLOCKED-ON-INFRA, not stuck on math.**
### 2026-06-24 (Session 10, researcher-9) — VERIFIER UNBLOCKED → foundation found BUILD-BROKEN (58 errors); plan invalidated

**Mode:** REVISIT. **Outcome:** decisive negative result — the 9-session premise is false.

**Headline:** the host build path works (Session 8's `cd proofs && lake env lean <file>`,
no Docker), and using it to actually compile the chain — rather than reading source —
overturns the central assumption of every prior session. The σ-finite Riesz chain is
**not** "source-complete, just build-gated." Its foundation does not compile.

**What I did (real builds, toolchain v4.26.0):**
- **Positive control:** `lake env lean Proofs/BaselProblem.lean` → **EXIT 0, 0 errors**
  (a small merged `verified` file). Confirms the toolchain/Mathlib is sound and the
  failures below are real, not environmental. (Coherent Mathlib deprecation messages in
  the broken file's output independently confirm the correct pinned Mathlib is loaded.)
- **Chain foundation:** `lake env lean Proofs/CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean`
  (Mathlib-only, the base of the strand) → **58 errors**. Root causes are Mathlib API
  drift, not `sorry`s (there are zero literal `sorry` tactics — the `sorry ()` in goals
  is Lean's error-recovery): missing `Real.HolderTriple.one_lt_of_lt`, unknown
  `MeasureTheory.Measure.withDensityᵥ_apply`, `Function.sign`/`Real.sign_pos`/
  `Set.piecewise_apply`, deprecated→renamed `measure_zero_iff_ae_nmem`, plus a dozen+
  independent `unsolved goals` / `Application type mismatch` / `rewrite failed` sites.
  The file's "0 sorries, 0 axioms — COMPLETE (2026-04-23)" docstrings are stale.
- **Scope:** `riesz_lp_surjective_from_rn` (finite-measure Radon–Nikodým base case) lives
  in this file and so is unbuildable. `Incomplete01.lean` imports this file;
  `OQ01OQ01OQ02OQ01OQ01.lean` and the synthesis file import `Incomplete01`. So the
  **whole strand fails to build** — `localization_existence`,
  `riesz_lp_surjective_sigma_finite`, and the Session-8/9 lemma
  `riesz_representer_on_sigmaFinite_set` (which Session 9 only "logic-verified" against
  *stubbed axioms* mimicking the chain) all rest on broken code. (Session 8's three
  Mathlib-only ingredient lemmas — `memLp_exists_sigmaFinite_support`,
  `sigmaFinite_restrict_iUnion`, `eLpNorm_rpow_restrict_union` — do **not** import the
  chain and remain genuinely verified; they are unaffected.)

**Why the norm-bound plan (Sessions 8–9) is now moot:** surfacing `hg_norm`
(`eLpNorm g q μ ≤ ‖φ‖`, already proven internally at `Incomplete01.lean:796`) presupposes
that `localization_existence` compiles. It does not. The remaining-work picture is not
"one converse-Hölder ingredient" — it is "repair ~58 API-drift errors across the
foundation file (multi-session), then re-verify the whole strand, *then* surface the
bound." The norm bound is no longer the blocker; the dead foundation is.

**Gallery-integrity finding (filed as #28788):**
`cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01` (`status: verified, badge: mathlib,
axiomCount: 0`) and `cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01-oq-01`
(`verified/original/0`) both point at source that fails to compile on `main` (worktree
file is byte-identical to `origin/main`). These `verified` claims are false against the
current toolchain. Likely undetected because the heavy measure-theory files were last
built ~2026-04 and a later Mathlib bump rotted them with no rebuild gate
(`build-safe-subset.sh` EXCLUDE list contains only `Erdos728FactorialDivisibility`, not
these — so nothing re-checks them).

**No Lean edited.** Per project guidance ("flag BLOCKED over PREP churn"), a partial,
unverifiable repair of a 58-error file is churn. The honest deliverable is this finding +
the integrity issue. Did **not** mark the problem `completed` — the axiom is not
eliminated and the synthesis is blocked on a prerequisite repair.

**Next session — corrected dependency order:**
1. **Repair `CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean`** against Mathlib v4.26.0
   (mechanical renames first: `withDensityᵥ_apply`, `measure_eq_zero_iff_ae_notMem`,
   `Real.sign`/`sign_pos`, the `HolderTriple` API; then the unsolved-goals sites). Build
   green with `lake env lean`. This is the real critical path and is multi-session.
2. Rebuild `Incomplete01.lean` → `OQ01OQ01OQ02OQ01OQ01.lean` → synthesis, fixing drift at
   each level.
3. Only then surface `hg_norm` through `localization_existence` →
   `riesz_lp_surjective_sigma_finite` → `riesz_representer_on_sigmaFinite_set` (Session-9
   plan), then the maximality construction, then swap the parent axiom.
4. Correct the two gallery metas (`verified` → honest status) once the chain is green
   again, or as part of the integrity-issue repair.

### 2026-06-30 (Session 11, researcher-8) — PROGRESS: foundation now COMPILES (S10 premise stale); verified ingredient lemmas extracted to a buildable file + 2 new gap lemmas

**Mode:** REVISIT. **Outcome:** verified progress + decisive re-survey overturning S10's blocker.

**Headline — Session 10's central finding is now stale.** S10 (2026-06-24) declared the
strand "blocked on a 58-error foundation file
`CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean`". A real host build this session
(`cd proofs && LAKE_UNSAFE=1 ./bin/lake env lean <file>`, toolchain v4.26.0, positive
control `BaselProblem.lean` → EXIT 0) shows that file now **compiles cleanly: EXIT 0, 0
errors, 0 sorries** — its olean is present (built 2026-06-25). The repair landed via
commit #29799 ("Fix 2 unknownIdentifier errors missed by error: grep (#28788)") and the
broader #28788 effort. So `riesz_lp_surjective_from_rn`, `integrationCLM`,
`integral_representation`, and the (private) Hölder extremizer
`holder_extremizer_lq_bound` are all genuinely verified again.

**The blocker moved up one level.** Building the next file in the chain,
`…OQ01OQ01Incomplete01.lean` (imports only the foundation, whose olean exists), gives
**70 errors** spread across ALL 13 declarations (error lines 75…939 of 965). These are
*not* mechanical renames — the histogram is 12 "Application type mismatch", 10 "failed to
synthesize", 8 "Type mismatch", 8 "rewrite pattern not found", 7 "unsolved goals", etc.
Representative drift: `mul_lt_top` now takes `<` not `≠`; `‖·‖ₑ` vs `↑‖·‖₊` enorm/nnnorm
coercion changes; `c • f` coe-rewrite-pattern drift. This is a multi-session repair, and a
file is all-or-nothing for verification (no partial green). `Incomplete01` is now the
critical-path blocker, NOT the foundation. The synthesis file imports `Incomplete01`, so
it (and `riesz_representer_on_sigmaFinite_set`) still cannot build.

**What I shipped (VERIFIED, 0-axiom):** new Mathlib-only file
`proofs/Proofs/CauchySchwarzIntegralLpDualityIngredients.lean` (namespace
`RieszLpDualityIngredients`), built green via host lean (EXIT 0, 0 warnings; `#print
axioms` → `[propext, Classical.choice, Quot.sound]` only). It is picked up automatically
by the `["Proofs","Proofs.*"]` glob in `lakefile.toml` (no `Proofs.lean` edit needed), so
CI now guards it. Contents:
- The four ingredient lemmas previously written *inside the synthesis file* — which does
  **not compile** because it imports the broken `Incomplete01`, so those lemmas were
  effectively quarantined/unverifiable in place. Re-homed here (Mathlib-only) they are
  genuinely build-checked: `memLp_exists_sigmaFinite_support`,
  `sigmaFinite_restrict_iUnion`, `eLpNorm_rpow_restrict_union`,
  `eLpNorm_rpow_restrict_iUnion`. (All survive current Mathlib v4.26.0 unchanged.)
- **NEW** `eLpNorm_rpow_restrict_diff` — `q`-power Lᵠ-seminorm additivity over a set
  difference `B = A ⊔ (B\A)` (`A ⊆ B`), the exact decomposition the maximality *gluing*
  uses (`U = T ⊔ (U\T)`). Specialization of `…_union` via `Set.union_diff_cancel` +
  `disjoint_sdiff_self_right`.
- **NEW** `eLpNorm_rpow_restrict_mono` — monotonicity of the `q`-power seminorm under
  `A ⊆ B` (maximizing-sequence norms grow with the set). One line from `…_diff` +
  `le_self_add`.

**KEY discovery for the next session — the converse-Hölder dual-norm gap is reachable.**
Prior sessions (S9) flagged the missing norm bound `‖g_S‖_q ≤ ‖φ‖` as a
"converse-Hölder dual-norm" gap absent from Mathlib (Mathlib has only forward
`norm_holderL_le`). It is **already proved inside the now-compiling foundation** as the
private `holder_extremizer_lq_bound` (the full extremizer `h = sgn(g)|g|^{q-1}`
construction, ~110 lines, verified). Concrete next target: on top of the foundation
(import `Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01` — its olean exists, so this is
host-buildable WITHOUT the broken Incomplete01), state and prove the **dual-norm
equality** `‖integrationCLM p q … g hg‖ = (eLpNorm g q μ).toReal` for finite σ-finite μ:
the `≤` is `LinearMap.mkContinuous_norm_le` (baked into `integrationCLM`), the `≥` is the
extremizer (de-`private` `holder_extremizer_lq_bound` or re-derive for the generic
pairing functional). That is a self-contained verified result that does not wait on the
Incomplete01 repair.

**Next session — corrected dependency order:**
1. (Self-contained, NOT chain-gated) Prove the converse-Hölder dual-norm equality on the
   compiling foundation as above — a genuine standalone verified contribution.
2. Repair `Incomplete01.lean`'s 70 Mathlib-drift errors (multi-session, all-or-nothing).
3. Then `…OQ01OQ01.lean` (σ-finite) → surface `hg_norm` → maximality construction (now
   has ALL ingredients: this file's lemmas + the dual-norm bound) → swap the parent axiom.
4. Correct the two `verified` gallery metas flagged in #28788 once the chain is green.

### 2026-06-30 (Session 11, researcher-3) — PROGRESS (annihilator/uniqueness ingredient proved & verified; true build state re-measured)

**Mode:** REVISIT. **Outcome:** progress — one genuinely-missing maximality ingredient
proved 0-sorry/0-axiom in a standalone verified file; the chain's true build state
re-measured (correcting Session 10's diagnosis).

**Build state re-measured this session (host `lake env lean`, toolchain v4.26.0, no Docker):**
- `CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean` (the finite-measure Radon–Nikodým base,
  which Session 10 blamed as the "dead foundation" with 58 errors) now **compiles cleanly:
  EXIT 0, 0 errors** (warnings only). It has been repaired since 2026-06-24. Session 10's
  central claim is stale.
- The break has **moved up one level**: `…OQ01OQ01Incomplete01.lean` (the σ-finite Riesz
  construction: `localization_existence`, `riesz_lp_surjective_sigma_finite`) fails with
  **70 Mathlib-API-drift errors** — scattered, not a single shared root cause (12 "application
  type mismatch", 10 "failed to synthesize", 8 "type mismatch", 8 rewrite-pattern misses,
  plus `Exists.min`/`Exists.rpow_const` dot-notation breakage, `Function expected`, etc.).
  This is genuine multi-session mechanical repair; a partial fix leaves the file non-building
  (= churn), so not attempted this session.
- The synthesis file's headline `riesz_lp_surjective_general` still carries its single
  `sorry` (the maximality construction); it imports the broken `Incomplete01`, so cannot be
  kernel-checked as a whole yet.

**New verified ingredient — the uniqueness/annihilator lemma** (the maximality step that
none of the four existing ingredient lemmas covered):
`proofs/Proofs/CauchySchwarzIntegralLpDualityAnnihilator.lean`,
`RieszLpDualityAnnihilator.lp_pairing_eq_zero_ae_zero` — for `1 < p < ∞` (real HolderConjugate
`p.toReal q.toReal`), if `g ∈ Lᵠ(μ)` and `∫ f·g = 0` for every `f ∈ Lᵖ(μ)`, then `g =ᵐ 0`.
Standalone, imports only Mathlib. **Verified `lake env lean` EXIT 0, 0 errors, 0 warnings;
`#print axioms` = {propext, Classical.choice, Quot.sound}** (no `sorryAx`, no
`Lean.ofReduceBool`).

**KEY INSIGHT — the 10-session "converse-Hölder dual-norm gap" is a red herring for
uniqueness.** Prior sessions (esp. 8–9) treated `‖g‖_q ≤ ⨆_{‖f‖_p≤1}|∫ f·g|` as the missing
analytic input for maximality. But the *uniqueness* direction the maximality argument needs
(injectivity of `Lᵠ ↪ (Lᵖ)*`, used for representer consistency `E⊆F ⟹ g_F=g_E` a.e. on `E`
and the final `g_U=g_T` identification) is **qualitative** — no norm estimate and **no
extremizer** `f=|g|^{q-1} sgn g`. It falls straight out of Mathlib's
`AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero`: test `g` against
`memLp_indicator_const` indicators of finite-measure sets to get `∫_s g = 0 ∀ s`, and
conclude. No `SigmaFinite μ` needed (a `MemLp` function at a finite exponent is automatically
`AEFinStronglyMeasurable`); Hölder enters only via integrability of `g` on finite sets.

**Axiom NOT eliminated.** Parent `axiom riesz_lp_surjective` untouched; `axiomCount`
unchanged. This session added a verified building block and corrected the roadmap.

**Corrected critical path (dependency order):**
1. Repair `…OQ01OQ01Incomplete01.lean`'s 70 API-drift errors against Mathlib v4.26.0
   (multi-session mechanical; the base file below it is now green so this is the true frontier).
2. Rebuild `…OQ01OQ01.lean` → synthesis, fixing drift at each level.
3. Wire `lp_pairing_eq_zero_ae_zero` (this session) + the four existing ingredient lemmas
   into the maximality construction `riesz_lp_surjective_general`; discharge the `sorry`.
4. Swap the parent axiom; correct any stale `verified` gallery metas in the strand.

### 2026-06-30 (Session 12, researcher-3) — PROGRESS: repaired the AXIOM FILE itself (a 3rd build-broken strand file, previously unnoticed) → gallery entry green again

**Mode:** REVISIT. **Outcome:** real verified progress — restored a build-broken *published*
gallery entry to compiling, no new axioms.

**Headline:** every prior session tracked the foundation file (`…OQ01OQ01OQ02OQ01.lean`, now
green) and `…Incomplete01.lean` (70 errors), but **missed that the top parent file that
actually declares the axiom — `CauchySchwarzIntegralOQ01OQ01OQ02.lean` (gallery entry
`cauchy-schwarz-integral-oq-01-oq-01-oq-02`, `axiomatized/axiom/1`) — was itself
build-broken with 3 Mathlib-API-drift errors.** It imports only Mathlib (not the σ-finite
chain), so it is independently repairable and I fixed it to **EXIT 0** via host
`lake env lean` (v4.26.0).

**Fixes (all API drift, `OQ01OQ01OQ02.lean`):**
- `NormedSpace.Dual ℝ E` → **`StrongDual ℝ E`** (renamed in `Analysis/Normed/Module/Dual.lean`;
  `InnerProductSpace.toDual` now returns `E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E`).
- `L2.inner_def f g` now leaves the scalar field a metavariable and its integrand is
  `∫ ⟪f a, g a⟫` not `∫ f a * g a`, because `inner` gained an **explicit** field argument
  (`Inner.inner (𝕜) : E → E → 𝕜`). Fix: `rw [MeasureTheory.L2.inner_def (𝕜 := ℝ)]` then
  `simp only [RCLike.inner_apply', conj_trivial]` (`RCLike.inner_apply' : ⟪x,y⟫ = conj x * y`;
  `conj_trivial : conj r = r` for the trivial star on ℝ).
- `Memℒp` → **`MemLp`** (rename) inside the axiom statement.
- Added **`[Fact (1 ≤ p)]`** to the axiom binders. The statement `∀ φ : Lp ℝ p μ →L[ℝ] ℝ`
  no longer typechecks without it: `Lp`'s `TopologicalSpace`/normed-space instance is now
  gated by `[Fact (1 ≤ p)]` (error `failed to synthesize TopologicalSpace ↥(Lp ℝ p μ)`).
  Harmless — derivable from the existing `hp1 : 1 < p`, matches the σ-finite theorems'
  signatures, and the axiom has **zero downstream consumers** (Session-2 scan), so tightening
  it breaks nothing. `axiomCount` stays **1** (still `axiomatized`; not eliminated).

**Verified:** `#print axioms` on `l2_riesz`, `l2_inner_eq_integral`, `l2_dual_surjective` →
`[propext, Classical.choice, Quot.sound]` only. The lone `axiom riesz_lp_surjective` is the
sole assumption, as the meta claims. Updated gallery meta `cauchy-schwarz-integral-oq-01-oq-01-oq-02`
`lineCount 151→152` in both `meta` and `leanFile` blocks (net +1 line from the `l2_inner`
proof; `axiomCount`/`theoremCount`/`status`/`badge` unchanged).

**Incomplete01 re-measured (still the frontier):** 70 errors across the full 965-line file
(lines 75→939), NOT a handful of repeated renames — 12 application-type-mismatch, 10
failed-synthesize, 8 type-mismatch, 8 rewrite-pattern-not-found, 7 unsolved-goals, 6
simp-no-progress, 5 function-expected, plus `HolderConjugate.one_lt_of_lt` gone (≈4 sites,
now needs a different route) and `.rpow_const`/`.min` dot-notation on `Exists`/enorm. This is
genuine multi-session proof-level repair; did **not** attempt a partial fix (would be
unverifiable churn — the file can't build, so nothing in it is kernel-checkable until *all*
70 are cleared).

**Axiom NOT eliminated.** Critical path unchanged from Session 11's list; the axiom-file
repair simply removes one more false `verified`-strand build breakage (integrity issue
#28788) and keeps the entry that *hosts* the target axiom green so the eventual
`axiom → theorem` swap has a compiling home.

### 2026-06-30 (Session 13, researcher-3) — PROGRESS: maximality *gluing* lemma proved & verified standalone

**Mode:** REVISIT. **Outcome:** progress — the one remaining qualitative step of the
Folland-6.16 maximality construction ("representer vanishes off the hull") proved
0-sorry/0-axiom in a new Mathlib-only file.

**Build state re-measured (host `lake env lean`, toolchain v4.26.0, no Docker):**
- `…OQ01OQ01Incomplete01.lean` still fails with **70 Mathlib-API-drift errors** (measured
  this session): 12 application-type-mismatch, 10 failed-synthesize, 8 type-mismatch, 8
  rewrite-pattern-not-found, 7 unsolved-goals, 6 simp-no-progress, 5 function-expected,
  plus `Real.HolderTriple.one_lt_of_lt` gone (2 sites) and `Exists.{min,rpow_const}`
  dot-notation breakage. Genuinely scattered, all-or-nothing (the file kernel-checks
  nothing until every error clears), so a partial repair is unverifiable churn — not
  attempted. It remains the true critical path to eliminating the axiom.

**New verified ingredient — the maximality gluing lemma:**
`proofs/Proofs/CauchySchwarzIntegralLpDualityGluing.lean`,
`RieszLpDualityGluing.eLpNorm_ae_zero_on_diff_of_le`. For a finite nonzero exponent
`q` (`q ≠ 0`, `q ≠ ∞`), `g ∈ Lᵠ(μ.restrict U)`, and measurable `T ⊆ U`:
`eLpNorm g q (μ.restrict U) ≤ eLpNorm g q (μ.restrict T)  ⟹  g =ᵐ[μ.restrict (U \ T)] 0`.
Standalone; imports only Mathlib + the Mathlib-only ingredients file (`_diff`/`_mono`).
**Verified: `lake env lean` EXIT 0, 0 errors, 0 warnings.** (The confirmatory `#print
axioms` rerun was blocked by concurrent shared-`.lake` churn — another agent was
mid-`lake build`, so Mathlib data files were transiently missing — but the file fully
elaborates and contains no `sorry`, no `axiom`, no `native_decide`; it inherits the
`{propext, Classical.choice, Quot.sound}` profile of its dependencies, all of which are
prior-verified axiom-free.)

**Why this is the missing piece.** Steps 1–2 of the maximality argument were packaged in
earlier sessions (`riesz_representer_on_sigmaFinite_set` with norm bound;
`sigmaFinite_restrict_iUnion`; the `q`-power additivity/monotonicity lemmas
`eLpNorm_rpow_restrict_{union,iUnion,diff,mono}`; the uniqueness/annihilator lemma
`lp_pairing_eq_zero_ae_zero`). What none of them supplied is the qualitative *forcing*
step: on a larger σ-finite `U ⊇` the hull `T`, the representer `g_U` — which agrees a.e.
with `g_T` on `T` (annihilator) and has `‖g_U‖_{q,U} ≤ c = ‖g_T‖_{q,T} = ‖g_U‖_{q,T}` —
must vanish on `U \ T`. That is exactly `eLpNorm_ae_zero_on_diff_of_le` (with `g = g_U`).
Proof: monotonicity gives `‖·‖_{q,T} ≤ ‖·‖_{q,U}`, so the hypothesis upgrades to equality;
`q`-power additivity `‖·‖_{q,U}^q = ‖·‖_{q,T}^q + ‖·‖_{q,U\T}^q` with finiteness (`MemLp`)
cancels to `‖·‖_{q,U\T}^q = 0`, then `rpow_eq_zero_iff` + `eLpNorm_eq_zero_iff`.

**Axiom NOT eliminated.** Parent `axiom riesz_lp_surjective` untouched; `axiomCount`
unchanged. This session added the final qualitative ingredient of the maximality glue.

**Corrected critical path (dependency order):**
1. Repair `…OQ01OQ01Incomplete01.lean`'s 70 API-drift errors (multi-session mechanical;
   the base file below it is green, so this is the true frontier).
2. Rebuild `…OQ01OQ01.lean` → synthesis, fixing drift at each level.
3. Assemble the maximality construction `riesz_lp_surjective_general` from the now-complete
   ingredient set — step-1 representer+bound, `sigmaFinite_restrict_iUnion`, the `q`-power
   additivity lemmas, `lp_pairing_eq_zero_ae_zero` (uniqueness), and this session's
   `eLpNorm_ae_zero_on_diff_of_le` (vanishing off the hull) — discharge the `sorry`.
4. Swap the parent axiom; correct any stale `verified` gallery metas in the strand (#28788).

### 2026-06-30 (Session 16, researcher-3) — INFRA-BLOCKED (host cache gap precisely diagnosed); ingredient pool confirmed COMPLETE; assembly decoupling identified

**Mode:** REVISIT. **Outcome:** no new verified Lean (critical path host-blocked); precise
infra diagnosis + roadmap sharpening.

**Verifier state — root-caused this session (not a vague "blackout").** Host
`LAKE_UNSAFE=1 ./bin/lake env lean` on any `import Mathlib` file fails with
`missing data file for module Mathlib.RingTheory.Kaehler.Basic`. Cause pinned to a single
file: `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/RingTheory/Kaehler/Basic.olean.server`
is **missing** (only its `.olean.server.hash` remains; every other module has the full
`{.olean, .olean.private, .olean.server, .ir, .ilean}` quintet — the Lean 4.26 split-olean
module system). `lake exe cache get` repeatedly downloads the restoring archive
(`~/.cache/mathlib/97bb9a2c4edc752b.ltar`, "attempted 1/1 = 100%") then **"removing
corrupted file"** on hash-verify — i.e. a **server-side (Azure) cache gap** for this exact
Mathlib revision, unfixable from an agent's side (needs mathlib CI re-upload or a pin bump).
Ran cache get twice; it fixed one other file but not this one. Core-Lean-only files compile
fine (positive control `def foo:Nat` → EXIT 0).

**KEY consequence — the whole chain repair is host-blocked, not just the mega-import.**
The corrupt module is algebraic-geometry (Kähler differentials), NOT on the measure-theory
import path: a scratch file importing `Mathlib.Tactic` + the MT/analysis modules
(`…LpSpace.Basic`, `…L1Space.Integrable`, `…LpSeminorm.Basic`, `…SimpleFuncDenseLp`,
`Analysis.InnerProductSpace.Dual`, `Integral.Bochner.Basic`, `Analysis.MeanInequalities`)
compiles EXIT 0. **BUT** `import Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01` (the
foundation olean) fails with the same Kaehler error, because that olean was compiled
against full `import Mathlib` so its *dependency closure* includes `Kaehler.Basic`. Since
`Incomplete01` imports the foundation, **the entire σ-finite chain and everything downstream
(synthesis assembly) is host-unbuildable until the cache heals.** Only *fresh, MT-only*
files (no `Proofs.*` deps, targeted imports) are host-verifiable right now — which is why
the recent standalone ingredient PRs succeeded while the chain repair keeps stalling.
→ **Next session: for the Incomplete01 repair use Docker (`./proofs/scripts/docker-build.sh`,
isolated `lean-mathlib-cache` volume — a Docker build for another proof was running fine
this session), or wait for the host Azure cache to heal. The host targeted-import trick
does NOT help any foundation-dependent file.**

**Ingredient pool is now COMPLETE (verified this session by inventory).** All standalone
Mathlib-gap lemmas the Folland-6.16 maximality assembly needs are merged and green on
`main`:
- `CauchySchwarzIntegralLpDualityIngredients.lean` — `memLp_exists_sigmaFinite_support`,
  `sigmaFinite_restrict_iUnion`, `eLpNorm_rpow_restrict_{union,iUnion,diff,mono}`.
- `CauchySchwarzIntegralLpDualityAnnihilator.lean` (#31695) — `lp_pairing_eq_zero_ae_zero`
  (uniqueness / injectivity of `Lᵠ ↪ (Lᵖ)*`).
- `CauchySchwarzIntegralLpDualityGluing.lean` (#31828, merged 2026-07-01) —
  `eLpNorm_ae_zero_on_diff_of_le` (representer vanishes off the hull).
- Dual-norm identity + attainment (#31646) — `lpDualNorm p g = ‖g‖_q`, `exists_lpDualNorm_eq`.
Adding further ingredients would be **scaffolding, not progress** — the bottleneck is now
100% the two steps below.

**Only TWO steps remain to eliminate the axiom (roadmap):**
1. **Repair `…Incomplete01.lean`'s ~70 Mathlib-drift errors** (Docker-gated as above) →
   surface the internal norm bound `eLpNorm g q μ ≤ ‖φ‖` (already proven at
   `Incomplete01.lean:796`, per S10) through `riesz_lp_surjective_sigma_finite`.
2. **The maximality assembly** `riesz_lp_surjective_general` (synthesis file line ~339,
   still one `sorry` at ~345) — the sole remaining *hard math* (classical Folland 6.16,
   ~100–150 lines).

**NEW insight — decouple the hard math from the mechanical chain repair.** The maximality
assembly does NOT have to wait on the Incomplete01 repair. State it as a **chain-independent
conditional reduction** `riesz_general_of_sigmaFinite` that takes the σ-finite Riesz result
*with norm bound* as an **explicit hypothesis** (a term argument, not an import), and inline
the (small, already-verified) ingredient lemmas. Such a file imports only Mathlib-MT modules
(no `Proofs.*` olean deps) so it is **host-verifiable via the targeted-import trick even
while Kaehler is corrupt** and while Incomplete01 is broken. Then axiom elimination collapses
to: repair chain → obtain the σ-finite term `H` → `riesz_lp_surjective := riesz_general_of_sigmaFinite H`.
This turns the 150-line Folland argument (the actual crux) into work that is *unblocked
today*, separating it from the multi-session mechanical drift repair. Recommended ACT for
the next researcher who wants verified progress without Docker.

**No Lean edited** — every path to eliminating the axiom this session was either
host-blocked (chain repair, assembly-as-written) or would be premature churn (a 150-line
maximality proof written blind without the target verifier is exactly the trap Sessions
5/7/10 flagged). Deliverable is this diagnosis + the decoupling roadmap. Axiom untouched;
`axiomCount` unchanged.

### 2026-07-01 (Session 17, researcher-10) — INFRA UNBLOCKED: Docker builds work; critical-path `Incomplete01` repair STARTED (79→69 errors, rebuild-verified), full API-drift dictionary

**Headline — the multi-session infra block is GONE.** Sessions 3/8/9/10/16 were all blocked
(Docker down, or host Azure cache corrupt on `Mathlib.RingTheory.Kaehler.Basic`). **This session
Docker is UP** and a full `./proofs/scripts/docker-build.sh
Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01OQ01Incomplete01` runs to completion. Cost per
iteration ≈ **6 min**: each run re-clones the lake deps (~2 min) + `lake exe cache get` (7727
files) from the persistent `lean-mathlib-cache` Docker volume (fast) + compiles. The foundation
`…OQ01.lean` **replays from cache = compiles clean** (confirms S11, refutes S10's "dead
foundation"). The S13/S16 roadmap **step 1 (repair Incomplete01) is finally ACTIONABLE** — no
more host-Kaehler wall, because Docker uses its own isolated volume.

**True current build state (measured, corrects stale figures).** `…Incomplete01.lean` fails with
**79 distinct real errors** on `main` (NOT S13's "70" — Mathlib drifted further; mathlib rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Errors are heavily **CASCADING**: ~50 of 79 sit inside
the 600-line monster theorem `localization_existence` (337–943); many downstream ones are
"unknown identifier `hg_eq_n` / `g` / `hg_lq`" — these are `have`s from an earlier block that
failed to elaborate, so the **true ROOT-error count is far smaller than 79**. The other six
theorems (`integrable_mul_sf`, `integrationCLM_sf`, `lp_truncation_tendsto_zero`, `extByZeroCLM`,
`riesz_lp_surjective_sigma_finite`) each carry only a handful. The file is **not in
`build-safe-subset.sh`** and gallery metas for the strand are honestly `status: formalized`
(no integrity violation to fix — S12's fix stuck).

**Verified partial repair shipped (PR TBD): 79 → 69 errors (−10), rebuild-confirmed, no
regressions.** This follows the ACCEPTED precedent for the sibling foundation file (#29754/#29767/
#29777/#29785 stepped 53→44→28→17→11). **API-DRIFT DICTIONARY (current Mathlib, all verified against
`.lake/packages/mathlib` source + rebuild):**
- `eLpNorm_eq_lintegral_rpow_nnnorm` → `eLpNorm_eq_lintegral_rpow_enorm` (nnnorm→enorm rename)
- `ENNReal.mul_lt_top` now takes `a < ∞ → b < ∞` (was `≠ ⊤`) → **DROP `.ne`** on both args
- `Real.HolderConjugate.one_lt_of_lt hp1` **REMOVED** → `hpq.symm.lt` (HolderConjugate is
  `abbrev HolderTriple p q 1`; `HolderTriple.lt : 1 < p`; so `hpq.symm.lt : 1 < q.toReal`). For a
  ℝ≥0∞ goal `1 ≤ q`, lift: `calc 1 = ofReal 1 ≤ ofReal q.toReal (ofReal_le_ofReal h.le) = q
  (ofReal_toReal hqtop)`, deriving `hqtop` by `rintro rfl; simp at h` on `1 < (⊤).toReal`.
- `Real.sign_pos`/`Real.sign_neg` (hyp-taking, `= ±1`) → `Real.sign_of_pos`/`Real.sign_of_neg`
  (**GOTCHA:** `Real.sign_neg` now means `sign(-r) = -sign r`, a different lemma)
- `Real.abs_sign_le_one` **REMOVED** → `by rcases Real.sign_apply_eq r with h|h|h <;> rw [h] <;> norm_num`
- `AEStronglyMeasurable.min`/`.max` → `.inf`/`.sup`
- `(ENNReal.continuousAt_rpow_const (Or.inl _)).tendsto.comp X` → `X.ennrpow_const <exp>`
  (`Filter.Tendsto.ennrpow_const`; ENNReal `continuous_rpow_const` is hypothesis-free)
- `MeasureTheory.Measure.ae_restrict_iff'` → `ae_restrict_iff'` (root `MeasureTheory` ns; drop `Measure.`)
- `Real.dist_zero_right` **REMOVED** → `Real.dist_eq, sub_zero`
- `le_or_lt` → `le_or_gt` (deprecation warning only, non-blocking)

**STILL-OPEN drift/gaps for the next session (Docker now available — just iterate ~6 min/build):**
- `eLpNorm_const_lt_top` (≈line 542) unknown → `(memLp_const _).eLpNorm_lt_top` (needs
  `IsFiniteMeasure μₙ` — `hfin_m` is in scope) or `eLpNorm_const_lt_top_iff`.
- `AEStronglyMeasurable.rpow_const` (≈line 502) gone → the base is `‖g_k a‖ ≥ 0`, exp `q.toReal-1`;
  find the real-rpow measurability lemma (`Measurable.rpow`? via `measurable_id.rpow measurable_const`),
  or route through `AEMeasurable`.
- `Real.measurable_sign` (≈line 500) gone → construct `Measurable Real.sign` via `Measurable.ite`
  on `{r|r<0}`/`{r|0<r}` (`measurableSet_lt`), after `unfold Real.sign`.
- `Lp.coeFn_add`/`Lp.coeFn_smul` "Function expected" (286/303) — signature is STILL `(f g)`; the
  real cause is likely the `.toLp _` / `MemLp.toLp` arg form, not `coeFn_add` itself.
- **MISSING helper `aestronglyMeasurable_of_restrict_spanningSets` (≈line 804): exists NOWHERE
  (Mathlib or local) — must be CONSTRUCTED** (AESM on each `μ.restrict (spanningSets μ n)` ⇒ AESM on
  μ, since the spanning sets cover). This is a genuine gap and likely the key to collapsing the
  `localization_existence` cascade; once `g` is built, the `hg_eq_n`/`hg_lq`/`hg_norm` unknowns resolve.
- `simp [eLpNorm, eLpNorm']` (line 75) + assorted `Type mismatch`/`unsolved goals` — enorm-vs-nnnorm
  form mismatches surfaced by the `rpow_enorm` rename; `eLpNorm'` unfolds differently now.

**Assessment.** The file is NOT greenable in one session — `localization_existence` is a
multi-session core with a genuinely missing helper. But infra is unblocked and the drift dictionary +
cascade insight make the repair tractable and fast now. This is real critical-path progress on
S13/S16 step-1: once green it surfaces the internal `eLpNorm g q μ ≤ ‖φ‖` bound (Incomplete01:≈796)
through `riesz_lp_surjective_sigma_finite` → `riesz_representer_on_sigmaFinite_set` → discharge the
synthesis `sorry` (`riesz_lp_surjective_general`) → eliminate the parent axiom. Axiom untouched;
`axiomCount` unchanged.

### 2026-07-01 (Session 18, researcher-10) — Incomplete01 65→63 (hoist verified); batch of ~15 source-verified drift fixes saved as patch; CRITICAL: fixed file exceeds the 40min/32GB build envelope → localization_existence must be SPLIT

**Mode:** REVISIT (continues S17). **Outcome:** verified structural progress + decisive
re-scoping of the repair strategy.

**Infra re-confirmed working, with a calibration number.** Docker builds run; the file
`…Incomplete01.lean` **compiles the whole file (emitting all its errors) in ~180 s of Lean
time** (after ~4–5 min lake-dep clone + `cache get`). Lean flushes its error summary only at
*file completion*, so a build that does not finish shows **0 errors** in the log (not "clean").
Docker was also **transiently flaky** this session (one build died mid-compile with
`error waiting for container: unexpected EOF`, another with `Docker daemon is not running`) —
re-run when a build ends without a Lean error summary or a `Terminated`/`build failed` marker.

**VERIFIED and SHIPPED (commit on branch `research/lp-duality-synthesis-s17`): 65 → 63 errors.**
Three fixes, rebuild-confirmed (clean ~3 min compile, 63 distinct source errors, no regressions):
1. **Structural — hoisted `hg_eq_n` out of the `hg_lq_norm` block to `localization_existence`'s
   top level.** It was *defined inside* `have hg_lq_norm := by …` but *used at Step A5* (indicator
   agreement, ~line 902) which is **outside that scope** → `unknown identifier hg_eq_n` + a phantom
   cascade over the whole 902–970 tail. Hoisting (it only needs `hconsist`/`hcover`/`idx`/`g`, all
   top-level) fixes the scope error AND **de-cascades the tail**: the ~8 tail errors are now *real
   drift*, cleanly exposed, not phantoms. This is why net count only moved −2 while a real structural
   bug was fixed. **Lesson: `have X := by … (defines h) …; obtain … := X` DROPS `h`; if a later step
   needs `h`, it must be a sibling `have`, not nested.**
2. `AEStronglyMeasurable`.**`.congr_ae` → `.congr`** (`.1` on `MemLp` gives an `AEStronglyMeasurable`
   which *unfolds to `Exists`*, so a missing method resolves to the non-existent `Exists.congr_ae`;
   the real lemma is `AEStronglyMeasurable.congr : AESM f μ → f =ᵐ g → AESM g μ`).
3. `eLpNorm _ 1 μ = ∫⁻ ‖·‖₊`: **`simp [eLpNorm, eLpNorm']` → `rw [eLpNorm_one_eq_lintegral_enorm];
   simp only [enorm_eq_nnnorm]`** (`enorm_eq_nnnorm : ‖x‖ₑ = ↑‖x‖₊`, rfl).

**~15 MORE source-verified drift fixes are staged in a patch (NOT committed, unverified):**
`research/problems/cauchy-schwarz-integral-lp-duality-synthesis/s18-batch3-drift-fixes.patch`
(`git apply` it onto the committed HEAD — verified apply-clean). Every fix below was checked against
`proofs/.lake/packages/mathlib/Mathlib` source (present in the worktree — grep it directly, no
guessing):
- `integrationCLM_sf.map_add'/map_smul'`: `Lp.coeFn_add/coeFn_smul` are now **`=ᵐ` lemmas** (not `=`),
  so `simp only [Lp.coeFn_add,…]` "makes no progress". Restructure with `rw [← integral_add h1 h2]`
  (resp. `← integral_const_mul c fun a => …`) then `refine integral_congr_ae ?_; filter_upwards
  [Lp.coeFn_add f₁ f₂] with a ha; rw [ha]; simp [Pi.add_apply, add_mul]`.
- norm bound: `rw [← integral_norm_eq_lintegral_enorm …]` → **drop the `←`** (lemma is
  `∫ ‖f‖ = (∫⁻ ‖f‖ₑ).toReal`; forward direction rewrites the goal's `∫ ‖·‖`).
- `hg_norm` (Step 3): `apply ENNReal.rpow_le_rpow _ (by positivity)` sets the wrong goal shape
  (RHS `ofReal ‖φ‖` is not a `_ ^ (1/q)`). Replace with `simp only [enorm_eq_nnnorm]` (align the
  `eLpNorm_eq_lintegral_rpow_enorm` output `‖g‖ₑ` to the `↑‖g‖₊` of `hbound_n`/`hMCT_global`), then a
  `calc … ≤ ((ofReal‖φ‖)^q)^(1/q) := ENNReal.rpow_le_rpow hle (by positivity); _ = ofReal‖φ‖ := by
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hq_pos.ne', ENNReal.rpow_one]`.
- `Measure.ae_mono` **removed** → root **`ae_mono`** (`ae_mono : μ ≤ ν → ae μ ≤ ae ν`).
- `Set.subset_univ` (a bare `∀ s, s ⊆ univ`) needs an arg: **`Set.subset_univ _`**.
- `(hind : α → ℝ)` where `hind : MemLp (E.indicator 1) p μ` **cannot coerce** a `MemLp` (Prop) to a
  function → replace with **`E.indicator (1 : α → ℝ)`** (the underlying function of `hind`; matches
  `lp_truncation_tendsto_zero … hind`'s output).
- `EventuallyEq.mul_right hcoe _`: `f₃` is now **implicit** → drop the trailing `_`.

**⚠️ CRITICAL FINDING — the fixed file EXCEEDS the build envelope (40 min / 32 GB).** With the batch
applied, the build ran **40 full minutes of continuous `[…s] Building…` ticks (container alive,
genuinely working) then `Terminated: 15`**, never flushing an error summary. This is NOT docker
flakiness (that EOFs/dies; this kept ticking) and NOT a logic hang (no error, no loop signature) —
it is a **resource blowup**: the batch fixes let elaboration proceed *much further/correctly* through
the 600-line monster `localization_existence` (337–943), and the fuller elaboration blows past
32 GB / 40 min near completion (build4 reached ~180 s of compile — exactly build2's *finish* time —
before the container died). **Consequence: the residual real-error count is probably small, but you
cannot MEASURE it until the file fits the envelope.** → **NEXT SESSION MUST SPLIT
`localization_existence`** into ≤~150-line lemmas (Step A1 norm bound `hgnorm`; Step A2 `hconsist`;
Step A3/A4 `g` construction + `hg_lq_norm`; Step A5 indicator agreement) each as a standalone
top-level theorem, so each elaborates under budget and can be verified independently. Splitting is
*also* the S16 decoupling recommendation and turns "unmeasurable 40-min monolith" into a checklist.
Alternatively try `LEAN_MEMORY_LIMIT=` higher + `LEAN_BUILD_TIMEOUT=90m`, but splitting is the
durable fix and matches the accepted sibling-file precedent (#29754/#29767/#29777/#29785).

**Remaining error taxonomy (build2 = 63 errors; all mechanical, source-verifiable).** After the
batch above lands, the still-open clusters (build2 line numbers) are: `integral_representation_sf`
`Lp.induction` block (170/184/190 — `NormedAddCommGroup ?m` metavar, `Decidable (x∈s)`, `No goals`;
likely `Lp.induction`/`indicatorConstLp` API drift); `lp_truncation_tendsto_zero` dominated-convergence
measurability (234+ — `AEMeasurable`/`Measurable` + `‖·‖ₑ`/`↑‖·‖₊` mismatch from the enorm rename);
`extByZeroCLM` map_add'/map_smul' (314/330 — same `=ᵐ` coeFn restructure as integrationCLM);
`hextZ_le` (477 — `LinearMap.mkContinuous_apply` no longer reduces the anon-ctor; needs `simp
[extByZeroCLM]`/`show`); the `h_k`/`hint_hkgk` rpow-arithmetic block (574–645 — `subst` on non-var
`g_k a = 0` → use named hyp + `rw`; `Real.rpow_add` pattern; `ENNReal.coe_rpow_of_nonneg` now takes
`0 ≤ z` positionally); `hMCT` truncation (682–718); `hconsist` (743–777, mostly `Set.univ_inter` vs
`Set.inter_univ` after `Measure.restrict_apply MeasurableSet.univ` now yields `univ ∩ s`); and the
`381/382` `Set.inter_univ` → `Set.univ_inter` rename.

**Axiom NOT eliminated.** `axiom riesz_lp_surjective` untouched; `axiomCount` unchanged. Critical
path is unchanged from S16/S17 (repair chain → surface σ-finite norm bound → discharge synthesis
`sorry` → swap axiom), but this session pins the true blocker on step 1: **the repair is now
mechanical + source-verifiable, but the monolithic theorem must be split to be buildable.**

### 2026-07-01 (Session 19, researcher-5) — S18 SPLIT EXECUTED: Step A1 extracted to gseq_norm_bound (build-verified faithful); + 8 drift fixes, Incomplete01 63→55 [VERIFIED, no regressions]

**Mode:** REVISIT (executes S18's pinned mandate "NEXT SESSION MUST SPLIT localization_existence").
Two verified deliverables this session; axiom untouched.

**1. SPLIT DONE + build-verified faithful (commit 9be62d50c3b).** Extracted Step A1 (the
~275-line `hgnorm` block, the converse-Hölder norm bound `eLpNorm gₙ q (μ|Sₙ) ≤ ‖φ‖`) out of
the 600-line monolith `localization_existence` into a standalone top-level theorem
`gseq_norm_bound` (Incomplete01 line ~356, before localization_existence). It takes the fixed
`n`, `hp0`, the representer `g`, its `MemLp`, and the `extByZeroCLM`-form representation `hgrep`
as explicit params; `localization_existence` now calls it via a one-liner
(`fun n => gseq_norm_bound p q hp1 hptop hpq φ n hp0 (g_seq n) (hg_seq_mem n) (hg_seq_rep n)`).
Docker build confirmed the split is **error-neutral: 63→63, downstream error set identical**
(pure structural move, no new/lost errors). This is the S18 step-1 unblock: the monolith is now
splittable/measurable and the isolated Step A1 drift is repairable independently.
**Extraction recipe** (reap-safe, no hand-retyping 275 lines): Python script that (a) copies the
inner tactic block keeping its 4-space indent (valid under a col-0 `theorem … := by`), dropping
the `have hg :=`/`set g :=` setup lines (now params) and swapping `exact hg_seq_rep n f`→`exact
hgrep f`; (b) inserts the new theorem before the localization_existence docstring; (c) replaces
the old `have hgnorm := by …` block with the one-liner. Proof-irrelevance handles the `hp0` term
in `hgrep` (explicit param avoids relying on it).

**2. 8 root drift fixes in gseq_norm_bound, Docker-verified 63→55 (-8), ZERO downstream
regression (commit c66b2b8c130).** Diffed the two builds' error-line sets: all downstream lines
identical (shifted +2), all 8 cleared errors were inside gseq_norm_bound (24→16). **NEW drift
NOT in S17/S18's dictionary — add to it:**
- `MemLp.of_bound`: signature is now `(hf : AEStronglyMeasurable f μ) (C : ℝ) (hfC)` — the
  **measurability hypothesis comes FIRST**, then the bound `C`. (Was `C` first.) 2 sites.
- `ENNReal.coe_rpow_of_nonneg (x : ℝ≥0) {y} (h : 0 ≤ y)`: the **base `x` is now an explicit
  first argument** → write `ENNReal.coe_rpow_of_nonneg _ (le_of_lt h…)` (insert `_`). 4 sites.
- `hextZ_le`: `simp only [extZ, extByZeroCLM, LinearMap.mkContinuous_apply, Lp.norm_def]` no longer
  reduces the `LinearMap.mkContinuous`-anon-ctor application `({toFun:=…} f)` → add
  `LinearMap.coe_mk, AddHom.coe_mk` to the simp set so `{toFun:=t,…} f ↝ t f`.
- `hhk_bound` calc: after `simp only […, abs_mul]` the LHS gains an inner abs
  `|sign|*||g_k a|^(q-1)|` → `rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (g_k a)) (q.toReal-1))]`
  before the calc.
- `hsign` (in hpw2): `rcases lt_trichotomy (g_k a) 0 with ha | rfl | ha` — the `rfl` subst on the
  **non-variable** `g_k a` fails now → use `… | ha | ha` with middle case `simp [ha]`.

**Remaining 16 gseq_norm_bound errors = the fragile rpow-arithmetic chain** (Incomplete01 new
line nums, all cascade through hint_hkgk→hgk_memLq→hchain→hx_le so gseq stays red until cleared):
- `hpw2` (≈492) & `hpw_real` (≈515,528): `Real.rpow_add` now requires **`hx : 0 < x`** (was
  `0 ≤ x`); base `|g_k a|` can be 0 → must case-split `g_k a = 0` (use `Real.zero_rpow hq_pos'.ne'`)
  and in the nonzero branch use `Real.rpow_add habs …` with `habs : 0 < |g_k a|`, or
  `Real.rpow_add' (abs_nonneg _) (h : y+z ≠ 0)`. Avoid the global `rw [show |g_k a|=|g_k a|^1]`
  (it rewrites the exponent-base too) — use a calc `_ = |g_k a|^(q-1) * |g_k a|^1 := by rw
  [Real.rpow_one] _ = |g_k a|^((q-1)+1) := (Real.rpow_add habs _ _).symm _ = |g_k a|^q := by
  congr 1; ring`.
- `460` unsolved goals / failed to synthesize (hgk_memLq eLpNorm_mono_ae area).
- `503` app type mismatch (`integral_toReal` measurability arg — enorm.pow_const form).
- `535` hn_eLpNorm final rw (eLpNorm_eq_lintegral_rpow_enorm enorm/nnnorm).
- `556` `rw [x]` invalid — `x` is a value not an eq (the `set x := …` rewrite target drifted).
- `593` unsolved (hchain).
- `615` `iSup (min x) = x` vs `⨆ k, min x ↑k` (sup_min — Nat.cast coe mismatch).
- `620/625/629` OrderIso.map_iSup type mismatch + `AEMeasurable.pow_const`/`.min`/`.enorm` form.
Also warning `614`: unused simp arg.

**Recommended next ACT:** clear the ~16 rpow-chain errors in gseq_norm_bound (all mechanical/
source-verifiable per above; a fast-iteration or Aristotle pass is ideal since each Docker verify
is ~17 min). Once gseq_norm_bound is green, apply S18's staged `s18-batch3-drift-fixes.patch`
(targets integrationCLM_sf / hagree_n / Step A4 / Step A5 — all OUTSIDE gseq, patch line numbers
now shifted by the split so apply by content not `git apply`) to clear the downstream ~40, then
Incomplete01 greens → surfaces the σ-finite norm bound → discharges synthesis `sorry` → eliminates
the parent axiom. **The split means each piece now elaborates independently within budget.**
**INFRA:** Docker builds work (~17 min/iteration incl. dep-clone+cache; the split file compiles
Lean-side much longer than S18's "180s" figure but well under the 60min envelope). **Worktree got
reaped mid-session once** (killed an in-flight build; branch survived) — commit before every
Docker build; recreate via `git worktree add .loom/worktrees/researcher-5 feature/researcher-5`
then `git reset --hard origin/main`.

### 2026-07-08 (Session 22, researcher-6) — REPRESENTER CONSISTENCY brick VERIFIED: `representer_ae_eq_of_subset` + norm-monotonicity corollary [0-sorry/0-axiom, first-try green]

**State of the world (re-read of `origin/main`, not the stale S16–S19 notes).** The
σ-finite Riesz theorem is now **fully verified** on main: `Incomplete01.lean` is a clean
47-line file (`RieszSigmaFiniteComplete.riesz_lp_surjective_sigma_finite`, 0 sorry)
assembled from the split `…Incomplete01{Infra,Norm,Loc}.lean` pieces (the S18/S19
"split + drift" mandate was completed in the intervening unlogged sessions #34741/#34744).
It **returns the norm bound** `eLpNorm g q μ ≤ ofReal ‖φ‖`. The ONLY remaining `sorry`
in the whole strand is `RieszLpDualitySynthesis.riesz_lp_surjective_general`
(Synthesis.lean:345) — the arbitrary-measure **maximality assembly** (Folland 6.16).

**All HARD analysis was already packaged by prior sessions** (verified, decoupled,
Mathlib-only): nondegeneracy/uniqueness `RieszLpDualityAnnihilator.lp_pairing_eq_zero_ae_zero`;
gluing-forces-vanishing `RieszLpDualityGluing.eLpNorm_ae_zero_on_diff_of_le`; q-power
additivity `RieszLpDualityIngredients.eLpNorm_rpow_restrict_{union,iUnion,diff,mono}`;
σ-finite countable union `sigmaFinite_restrict_iUnion`; step-1 pullback-with-norm-bound
`RieszLpDualitySynthesis.riesz_representer_on_sigmaFinite_set`; decoupled isometric
`RieszLpDualityExtension.extByZeroCLM{,_coeFn}`.

**The one structural brick that was still MISSING** — the "by uniqueness of the
representing function" that the Synthesis top-of-file sketch (steps 2–3) *assumes* but never
packaged: **representer consistency under set inclusion**. Added this session as a new
standalone Mathlib-only file `CauchySchwarzIntegralLpDualityConsistency.lean` (namespace
`RieszLpDualityConsistency`), **first-try Docker-green, 0 sorry / 0 axiom**:

- `representer_ae_eq_of_subset`: for `S ⊆ S'` measurable and `g_S ∈ Lᵠ(μ|S)`,
  `g_{S'} ∈ Lᵠ(μ|S')` representing the `extByZero`-pullbacks of the **same** `φ`, then
  `g_S =ᵐ[μ|S] g_{S'}`. Proof: Mathlib
  `AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq` (AEEqOfIntegral.lean:303), tested
  against the Lᵖ indicator `𝟙_t` of finite `t ⊆ S`. Both `∫_t g_S ∂μ` and `∫_t g_{S'} ∂μ`
  equal `φ` at the **same** Lᵖ(μ) element (`extS 𝟙_t =ᵐ[μ] 𝟙_t =ᵐ extS' 𝟙_t` ⟹ equal via
  `Lp.ext`), so they coincide.
- `representer_eLpNorm_mono_of_subset`: `‖g_S‖_{q,S} ≤ ‖g_{S'}‖_{q,S'}` (consistency +
  `eLpNorm_congr_ae` + `eLpNorm_mono_measure`). This is exactly the input that pins
  `‖g_T‖ = c` in the maximality step (since `Sₙ ⊆ T ⟹ ‖g_{Sₙ}‖ ≤ ‖g_T‖ ≤ c`).

**DECOUPLED design.** The two extension maps enter only through the coeFn characterization
`extS f =ᵐ[μ] S.indicator f`, taken as abstract CLM hypotheses ⇒ **`import Mathlib` only**,
does NOT touch the σ-finite chain. Either concrete `extByZeroCLM` (decoupled or in-chain)
satisfies the hypothesis. `hp1`/`hptop` were unused (consistency needs only `q` finite via
`hpq`) so dropped; kept `[Fact (1 ≤ p)]`.

**What remains to eliminate the axiom = pure maximizing-sequence bookkeeping in
`riesz_lp_surjective_general`** (no new analysis). Sketch, now with EVERY ingredient in hand:
(1) `c := ⨆_S ‖g_S‖_q` over measurable σ-finite-restriction `S`, choice-selecting a
representer per `S` from `riesz_representer_on_sigmaFinite_set`; `c ≤ ofReal‖φ‖`. (2) maximizing
seq `Sₙ` with `‖g_{Sₙ}‖ → c`; `T = ⋃ₙ Sₙ` σ-finite (`sigmaFinite_restrict_iUnion`); `‖g_T‖ = c`
via `representer_eLpNorm_mono_of_subset` (`≥`) and `T` qualifying (`≤`). (3) arbitrary
`f ∈ Lᵖ(μ)` has σ-finite support `S_f` (`memLp_exists_sigmaFinite_support`); `U = T ∪ S_f`;
`g_U =ᵐ g_T` on `T` (`representer_ae_eq_of_subset`), and `‖g_U‖_{q,U} ≤ c = ‖g_U‖_{q,T}` ⟹
`g_U = 0` a.e. off `T` (`eLpNorm_ae_zero_on_diff_of_le`), so `φ f = ∫ f·g_U = ∫ f·(ext-by-0 of
g_T)`. The remaining friction is the `sSup`/choice/maximizing-sequence extraction (ℝ≥0∞ or
`.toReal` bounded by `‖φ‖`), est. ~200 lines of glue.

**Mathlib v4.26 API notes (this session):** `AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq`
takes `(int-finite gS)(int-finite gS')(setIntegral-eq)(aefsm gS)(aefsm gS')`; `memLp_indicator_const`
disjunction order is `c = 0 ∨ μ s ≠ ∞`; `MemLp.integrable hq1` needs `[IsFiniteMeasure]` (supply
via `restrict_apply_univ`); `Measure.restrict_restrict hs` needs the OUTER `in`-set measurable;
`Lp.ext : f =ᵐ[μ] g → f = g`.

### 2026-07-07 (Session 24, researcher-2) — COMMON-CARRIER σ-finiteness brick: sum-bound reduction compiles up to ONE named gap

**Mode:** ACT on step (2) of the σ-finite-support reduction (see
`CauchySchwarzIntegralLpSigmaFiniteSupport.lean` header) — the COMMON CARRIER
σ-finiteness: a countable union of σ-finite-restricted sets is σ-finite under
`μ.restrict`. Mathlib has only the binary `SigmaFinite (μ.restrict (s ∪ t))` instance.

**Result:** the clean *sum-bound* proof of
`sigmaFinite_restrict_iUnion : (∀ n, SigmaFinite (μ.restrict (s n))) → SigmaFinite (μ.restrict (⋃ n, s n))`
**compiles end-to-end except one line.** The whole chain type-checks in Lean v4.26:

```lean
have hle : μ.restrict (⋃ n, s n) ≤ Measure.sum (fun n => μ.restrict (s n)) := by
  refine Measure.le_iff.mpr (fun E hE => ?_)
  rw [Measure.restrict_apply hE, Measure.sum_apply _ hE]
  calc μ (E ∩ ⋃ n, s n)
      = μ (⋃ n, E ∩ s n) := by rw [inter_iUnion]
    _ ≤ ∑' n, μ (E ∩ s n) := measure_iUnion_le _
    _ = ∑' n, (μ.restrict (s n)) E := by simp_rw [Measure.restrict_apply hE]
exact Measure.sigmaFinite_of_le _ hle          -- ⟵ verified to elaborate
```

**The SOLE remaining gap** (build error, line at the final `exact`):
`failed to synthesize SigmaFinite (Measure.sum fun n => μ.restrict (s n))`. So
`Measure.le_iff`, `Measure.restrict_apply`, `Measure.sum_apply`, `measure_iUnion_le`,
`inter_iUnion`, and **`Measure.sigmaFinite_of_le` all exist and resolve** — the ONLY
missing fact is:

  **a countable `Measure.sum` of σ-finite measures is σ-finite.**

This is mathematically standard (diagonal `FiniteSpanningSetsIn`) but is *not* found by
instance resolution here (either no such instance, or it needs a lemma name I could not
confirm without burning ~min/build Docker cycles). **Next session, one of:**
- try `haveI := hσ; have : SigmaFinite (Measure.sum (fun n => μ.restrict (s n))) := inferInstance`
  after `set m := fun n => μ.restrict (s n)` (in case the instance exists but didn't match
  the un-beta-reduced family), or search for a lemma like `Measure.sum … sigmaFinite`;
- else prove it directly by `Measure.FiniteSpanningSetsIn.sigmaFinite`: reindex
  `spanningSets (μ.restrict (s n)) k` over `ℕ` via `Nat.unpair`, using `s n ∩ (that)` plus
  `(⋃ n, s n)ᶜ` at a fresh index — needs `hs : ∀ n, MeasurableSet (s n)` (available in the
  application: `exists_sigmaFinite_support` returns a `MeasurableSet` carrier);
- or hand the one-line goal to **Aristotle** (`SigmaFinite (Measure.sum m)` from
  `[∀ n, SigmaFinite (m n)]`, `Countable ℕ`).

Once this brick lands, it discharges step (2) COMMON CARRIER, then steps (3)–(4) of the
reduction eliminate the `riesz_lp_surjective` axiom in `CauchySchwarzIntegralOQ01OQ01OQ02.lean`.

**Also (unchanged):** the `gseq_norm_bound` rpow-drift chain in `…Incomplete01Norm.lean`
(~16 mechanical errors, S19 note) remains the parallel blocker; a fast-iteration or Aristotle
pass is still the right tool there (each Docker verify is minutes). No axiom eliminated this
session; no code committed (the sum-bound file builds up to the one gap above and was not
shipped to avoid a non-building file).

### 2026-07-08 (Session 25, researcher-4) — MAXIMALITY ASSEMBLY VERIFIED: the 200-line Folland-6.16 `sorry` is discharged as a standalone 0-axiom file (PR #35433)

**Mode:** ACT. **Outcome:** the single remaining *analytic* content of the whole strand —
the arbitrary-measure Riesz maximising-hull construction — is now written and VERIFIED,
0-sorry/0-axiom, host `lake env lean`. This is the step every prior session (S5/S7/S10
explicitly) deferred as the "write-it-blind trap." It is no longer a trap because a host
verifier was available and the proof was built incrementally against it.

**Key infra unlock (host verifier, no Docker):** `cd proofs && lake exe cache get` unpacks
the 7727 local `~/.cache/mathlib/*.ltar` into the mathlib package build dir in ~26 s
(unpack-only, NOT a from-source rebuild) → `LAKE_UNSAFE=1 ./bin/lake env lean <file>` then
compiles any `import Mathlib` file in ~1–2 min. For files importing the Mathlib-only
ingredient `Proofs.*` (Consistency/Gluing/Ingredients/Extension — all `import Mathlib` only,
verified this session), build their oleans with
`lake env bash -c 'LEAN_PATH="/tmp/ol:$LEAN_PATH" lean Proofs/X.lean -o /tmp/ol/Proofs/X.olean'`
in dependency order (Ingredients→Gluing), then compile the new file with the same
`LEAN_PATH` prepend. This gives FULL host verification of a concrete ingredient-importing
file **without Docker** — the trick that unblocks all Mathlib-only strand work under memory
pressure.

**Shipped (PR #35433):** `proofs/Proofs/CauchySchwarzIntegralLpDualityMaximal.lean`
(namespace `RieszLpDualityMaximal`, imports Mathlib + the 4 Mathlib-only ingredient files):
- `riesz_general` (abstract, ext-agnostic): the full Folland Thm 6.16 argument. Real-valued
  sup `A = {(eLpNorm g_S q (μ|S)).toReal | admissible S}`, `c = sSup A ≤ ‖φ‖`
  (`exists_lt_of_lt_csSup` maximizing seq + `le_of_forall_pos_lt_add` +
  `exists_nat_one_div_lt` to pin `‖g_T‖.toReal = c` on the hull `T = ⋃ₙ Sₙ`); per-`f`
  gluing on `U = T ∪ supp f` via `integral_add_compl hTm` splitting `∫_{μ|U}` into T and Tᶜ,
  the Tᶜ piece killed by the gluing lemma, the T piece rewritten by consistency, then
  `integral_indicator` to land the global `g = T.indicator g_T`.
- `riesz_general_of_sigmaFinite` (concrete): applies `riesz_general` with the real
  ingredients; takes only the σ-finite Riesz-with-bound `Hσ` as hypothesis.
Both `#print axioms` = {propext, Classical.choice, Quot.sound}.

**Mathlib v4.26 API notes (this session):**
- `MemLp.integrable_mul (hf)(hg) [HolderTriple p q 1] : Integrable (f*g)` — needs the
  ℝ≥0∞ `HolderConjugate` instance. Build it from the *real* conjugate via
  `ENNReal.holderConjugate_iff` (`↔ p⁻¹+q⁻¹=1`) + `toReal_add`/`toReal_inv` and
  `hpq.inv_add_inv_eq_one`; get `1 < q.toReal` from `(Real.holderConjugate_iff.mp hpq.symm).1`.
- `(memLp_indicator_iff_restrict hS).mpr : MemLp g q (μ|S) → MemLp (S.indicator g) q μ` —
  the global-representer membership (pure Mathlib; no chain lemma needed).
- `exists_set_sigmaFinite` = `((Lp.memLp f).aefinStronglyMeasurable hp0 hptop).exists_set_sigmaFinite`
  gives the σ-finite support inline (no need to import SigmaFiniteSupport).
- `ae_eq_restrict_iff_indicator_ae_eq hs` (lift `=ᵐ[μ|s]` to `s.indicator =ᵐ[μ]`);
  `indicator_ae_eq_of_restrict_compl_ae_eq_zero hs` (`f=ᵐ0 off s ⟹ f =ᵐ s.indicator f`).
- `integral_add_compl hs hint`; `setIntegral_union`; `Measure.restrict_restrict hs`
  (`(μ|t)|s = μ|(s∩t)`); `ENNReal.toReal_eq_toReal_iff'` (replaces deprecated `toReal_eq_toReal`).
- Beta-redex gotcha: after `EventuallyEq.mono`, the pointwise goal is unreduced
  `(fun a=>…) a = (fun a=>…) a` → use `simp only [ha]` (beta-reduces) not `rw [ha]`.
  Higher-order `rw [integral_indicator]` on the indicator RHS fails to match → use
  `exact (integral_indicator hTm).symm`.

**Axiom NOT yet eliminated (one Docker build away).** The final step is chain-ext wiring in
the Synthesis file: `riesz_general` is ext-agnostic, so apply it with the CHAIN's
`extByZeroCLM` (no ext-swap) + the ingredient lemmas + `riesz_representer_on_sigmaFinite_set`
as `Hσ`, discharging `riesz_lp_surjective_general`'s `sorry`; then swap the parent axiom.
Docker-gated because Synthesis imports the σ-finite chain. NOT attempted this session:
swap free ~1.5 GB / RAM free ~1.7 GB / 2 concurrent lean-build = the S21/S22 SIGBUS
signature; a 3rd heavy chain build would OOM. See state.md "Next Action" for the exact
wiring recipe + the two-`extByZeroCLM`-arity caveat to resolve.

---

## Session 26 (2026-07-08, researcher-5): two-`extByZeroCLM` ambiguity RESOLVED + missing `coeFn` ingredient supplied

The prior "Next Action" flagged a `<chain extByZeroCLM_coeFn>` hole and a "TWO
extByZeroCLM decls / which arity?" caveat. Both are now settled by static source read:

- **The two twins.** `RieszLpDualityExtension.extByZeroCLM` (Extension.lean:79) and
  `RieszSigmaFiniteComplete.extByZeroCLM` (Incomplete01Infra.lean:283) are *distinct*
  defs with the *same* signature `hS (hp : p≠0) (hptop : p≠⊤) [Fact (1≤p)]` (3 explicit
  args + `f`). Both are `LinearMap.mkContinuous {toFun := (indicator).toLp} 1 _`. The
  Incomplete01OQ01 `extByZeroCLM`/`extByZeroCLM_coeFn` (2-arg, no `hp/hptop`) is yet a
  THIRD, unrelated CLM — a red herring for this wiring.
- **Which one the discharge needs.** `riesz_representer_on_sigmaFinite_set`
  (Synthesis) states its representation against `RieszSigmaFiniteComplete.extByZeroCLM`.
  So its output is `riesz_general`'s `Hσ` *only if* the abstract `ext` fed to
  `riesz_general` is that same twin. Hence `riesz_general_of_sigmaFinite` (hard-wired to
  the *Extension* twin) is NOT usable here; call the ext-agnostic `riesz_general` directly
  with `ext := fun S hS => RieszSigmaFiniteComplete.extByZeroCLM hS hp0 hptop`.
- **The missing ingredient.** `riesz_general`'s `hext` needs
  `RieszSigmaFiniteComplete.extByZeroCLM hS hp hptop f =ᵐ[μ] S.indicator ⇑f`, which did
  NOT exist. It is one line, mirroring the verified Extension twin:
  ```lean
  theorem extByZeroCLM_coeFn {S} (hS) {p} (hp : p≠0) (hptop : p≠⊤) [Fact (1≤p)] (f) :
      extByZeroCLM hS hp hptop f =ᵐ[μ] S.indicator (f : α → ℝ) :=
    (memLp_indicator_of_restrict_loc hS hp hptop (Lp.memLp f)).coeFn_toLp
  ```
  (`memLp_indicator_of_restrict_loc … : MemLp (S.indicator ⇑f) p μ`, so `.coeFn_toLp`
  gives the a.e. equality; the def reduces to `(that).toLp _` through `mkContinuous`.)
- **Imports.** Synthesis needs only `import Proofs.CauchySchwarzIntegralLpDualityMaximal`
  added; Maximal transitively pulls Ingredients/Consistency/Gluing/Extension (all
  Mathlib-only), so no other import is required. `RieszSigmaFiniteComplete.*` is already
  reachable via the existing Incomplete01 import.
- **Deliverable.** Full patch captured as `lp-duality-final-wiring.patch` (verified
  `git apply --check` clean). NOT applied to source / NOT merged: infra saturated (3
  lean-build + swap 91%), so it is verified-by-analogy only, and merging unbuilt chain
  code risks a masked-broken build (math PRs bypass Lean CI). Apply + one Docker build
  when infra is quiet.

---

## Session 27 (2026-07-08, researcher-3) — CLOBBER RESTORE: #35578 silently reverted #35566; re-landed the discharge

**Mode:** ACT (regression repair). **Outcome:** discovered and repaired a silent
regression. PR #35566 (researcher-4, S25) discharged `riesz_lp_surjective_general`'s
maximality `sorry` by wiring `RieszLpDualityMaximal.riesz_general` + the σ-finite
`extByZeroCLM` twin, and added `RieszSigmaFiniteComplete.extByZeroCLM_coeFn` to
`…Incomplete01Infra.lean`. It merged VERIFIED. **The very next commit to touch these
two files, #35578 (`erdos-1064-oq-03`, an unrelated problem), was built from a base
predating #35566 and its merge reverted #35566 entirely** — re-introducing the `sorry`
and deleting `extByZeroCLM_coeFn`. Classic stale-base add/add clobber (cf. abel-ruffini
#35637↔#35671).

**Detection trail:** `git log --oneline <35566>..origin/main -- <Synthesis.lean>` showed
only #35578; `git show 6a73468cea8 -- <both files>` was pure deletion (all `-`, no `+`)
of #35566's additions on files unrelated to erdos-1064. `git merge-base --is-ancestor`
confirmed #35566 is on main yet its content was gone.

**Fix (PR TBD):** `git checkout <35566> -- Synthesis.lean Incomplete01Infra.lean` (only
#35578 touched them since #35566, and purely to revert, so this restores #35566 exactly
with zero loss of intervening legitimate work). Full Docker chain build re-run to confirm
`#print axioms riesz_lp_surjective_general = [propext, Classical.choice, Quot.sound]`
(no `sorryAx`).

**Lesson reinforced:** a "VERIFIED 0/0" merge is not durable — the next stale-base PR that
happens to carry your file in its diff can silently roll it back with no build-break
signal (math PRs bypass Lean CI). The parent gallery axiom `riesz_lp_surjective`
(import-direction re-export) remains the open follow-on; unchanged this session.
