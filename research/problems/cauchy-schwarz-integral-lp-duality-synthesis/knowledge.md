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
