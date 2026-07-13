# Knowledge: fourier-series-oq-02-oq-01-oq-02

Vector-valued Riemann-Lebesgue via L²: extending parent slug
`fourier-series-oq-02-oq-01` (ℂ-target) to E-valued f : AddCircle T → E.

---

## 1. Open Question Summary

The parent slug proved, in ~83 LOC with 0 sorries / 0 axioms:

```
For f : AddCircle T → ℂ, HolderWith C α f, 0 < α
  ⊢ Tendsto (fun n => fourierCoeff f n) cofinite (𝓝 0)
```

via the 5-step chain

```
HolderWith.continuous  →  bounded-on-compact + finite-Haar ⇒ MemLp 2
                       →  MemLp.toLp                       (lift to L² element)
                       →  fourierCoeff (⇑f_Lp) n = fourierCoeff f n   (integral_congr_ae)
                       →  FourierSeries.fourierCoeff_tendsto_zero    (Parseval-RL)
```

**Open question (this slug):** Does the same chain go through when the target is E
(a Banach or Hilbert ℂ-vector space) instead of ℂ?

---

## 2. Branch Decision: Hilbert E vs Banach E

| Branch | Hypothesis on E | Method | Mathlib readiness | Recommendation |
|--------|-----------------|--------|-------------------|----------------|
| **Hilbert E** | `[InnerProductSpace ℂ E] [CompleteSpace E]` (+ separability) | Parseval-style: generalize `hasSum_sq_fourierCoeff` to E-valued L² | Partial (see §3) — needs vec-Parseval lemma | **PRIMARY** target for first ACT cycle |
| **Banach E** | `[NormedSpace ℂ E] [CompleteSpace E]` (no inner product) | L¹ density of trigonometric polynomials (classical RL) | Likely missing — Mathlib's `RiemannLebesgueLemma` is for ℝⁿ-target Fourier transforms, not AddCircle series | Secondary / future cycle |

**Why Hilbert first:** The parent proof's signature uses Parseval; the cleanest port preserves
that backbone. Banach-E requires a fundamentally different argument (density + the fact
that `fourierCoeff (fourier m * monomial) = δ_{m,n}`-style cancellation) and is therefore
a separate slug-worth of work, not a within-slug variant.

---

## 3. Mathlib Audit (pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, v4.26.0)

### Already in Mathlib for general E

| Item | File:line | Typeclass requirements | Notes |
|------|-----------|------------------------|-------|
| `fourierCoeff (f : AddCircle T → E)` | `Mathlib/Analysis/Fourier/AddCircle.lean:297` | `[NormedAddCommGroup E] [NormedSpace ℂ E]` | Bochner-integral definition; works for any Banach E over ℂ |
| `fourierCoeff_eq_intervalIntegral` | `:302` | same | LHS = `(1/T) • ∫ x in a..a+T, fourier(-n) x • f x` |
| `fourierCoeff.const_smul` | `:311` | same | |
| `fourierCoeff_congr_ae` | `:320` (approx) | same | a.e.-equal functions have equal coeffs |
| `fourierCoeffOn (f : ℝ → E)` | `:326` | same | Wrapper for closed-interval f |

### Mathlib's ℂ-only Parseval/RL pipeline

| Item | File:line | Type | Why ℂ-only |
|------|-----------|------|------------|
| `fourierLp` | `:250` | `Lp ℂ 2 haarAddCircle` (the basis vectors) | The basis is the orthonormal `e^{2πinx/T}` in ℂ |
| `hasSum_fourier_series_L2` | `:408` | `f : Lp ℂ 2 haarAddCircle` | Uses `HilbertBasis.hasSum_repr fourierBasis f` |
| `hasSum_sq_fourierCoeff` | `:415` | same | Σ ‖ĉ_n‖² = ‖f‖² (real-valued); uses `L2.inner_def` |
| `tsum_sq_fourierCoeff` | `:430` | same | tsum form |

**Key obstruction for Hilbert E:** Mathlib's `fourierBasis : HilbertBasis ℤ ℂ (Lp ℂ 2 ...)`
is intrinsically ℂ-valued. To lift to Hilbert E, one option is:

- **Option A:** Take the tensor product `(Lp ℂ 2 ...) ⊗ E` ≃ `Lp E 2 ...` and lift `fourierBasis`
  by tensoring. Heavy machinery; deep Mathlib internals.
- **Option B:** Bypass `HilbertBasis` and prove Parseval-for-E directly using `Hilbert.inner_def`-style
  Bochner-integrated inner products. Requires `L2.inner_def` generalized to E or hand-rolled.
- **Option C (RECOMMENDED for first ACT cycle):** Use componentwise reduction — for separable
  Hilbert E with orthonormal basis `{e_k}`, write `f = Σ_k ⟨f, e_k⟩ e_k` (in L²),
  then `‖fourierCoeff f n‖² = Σ_k ‖fourierCoeff ⟨f, e_k⟩ n‖²` and apply the ℂ-version to
  each component. Mathlib has `HilbertBasis.hasSum_inner_mul_inner` and Pythagorean-type
  lemmas that could support this.
- **Option D (FALLBACK):** Norm-comparison shortcut. For Hilbert E (or any Banach E),
  `‖fourierCoeff f n‖ ≤ ∫ ‖fourier(-n)‖ · ‖f‖ = ∫ ‖f‖ = ‖f‖₁` (Bochner triangle), so
  RL for E-valued reduces to RL for ‖f‖ : AddCircle T → ℝ — which is `MemLp 1` for compact T
  (since L² ⊂ L¹ on finite measure) and hence ĉ_n[‖f‖] → 0 by ℝ-valued RL.
  But: this gives `‖ĉ_n‖ → 0` of the *real* sequence `ĉ_n[‖f‖]`, not of the *E-valued*
  sequence `ĉ_n[f]`. The two are different — see §3.5.

### §3.5 — Why Option D doesn't directly work

Option D's reduction is *not* `‖fourierCoeff f n‖ ≤ fourierCoeff ‖f‖ n` (false in general:
the RHS is signed/complex-valued). The correct triangle inequality is

```
‖fourierCoeff f n‖ = ‖∫ fourier(-n) • f‖ ≤ ∫ ‖fourier(-n) • f‖ = ∫ ‖f‖
```

which gives `‖ĉ_n[f]‖ ≤ ‖f‖₁` (a uniform bound), NOT a decay statement. So Option D fails;
RL must come from *somewhere else* (Parseval for E, or L¹-density).

### §3.6 — Hilbert-basis component reduction (Option C, sketch)

Let `{e_k}` be an orthonormal basis of E (separable Hilbert). Define
`f_k : AddCircle T → ℂ` by `f_k(x) = ⟨f(x), e_k⟩_E`. Then:

1. `fourierCoeff f n = Σ_k fourierCoeff f_k n • e_k` (linearity of Bochner integral
   over orthonormal expansion).
2. `‖fourierCoeff f n‖² = Σ_k |fourierCoeff f_k n|²` (Pythagoras in E).
3. Each `f_k` is L² ℂ-valued (since `|⟨f(x), e_k⟩| ≤ ‖f(x)‖`), so by parent slug's
   theorem `fourierCoeff f_k n → 0` as `|n| → ∞`.
4. Dominated convergence on the sum: `Σ_k |fourierCoeff f_k n|² ≤ Σ_k C_k` (uniform-in-n
   bound from Parseval applied to f_k), and each summand → 0 ⇒ entire sum → 0
   (Fubini / monotone convergence on summing over k vs. taking limit in n).

**Risk on step 4:** swapping `Σ_k` and `lim_n` requires uniform integrability or
dominated convergence. The bound `Σ_k |fourierCoeff f_k n|² ≤ Σ_k ‖f_k‖²₂ = ‖f‖²₂`
is uniform in n (Parseval applied to each component summed by basis Pythagoras),
which IS enough for DCT. **VERIFY in S2 PREP.**

### Mathlib pieces likely needed for Option C

| Item | Expected location | Status |
|------|-------------------|--------|
| `HilbertBasis.hasSum_orthonormal_eq` (decompose f as ‖e_k‖-weighted) | `Mathlib/Analysis/InnerProductSpace/l2Space` | **pin-recheck S2** |
| `MeasureTheory.integral_inner` (Bochner-inner-product distribution) | `Mathlib/MeasureTheory/Integral/Bochner/Basic` | **pin-recheck S2** |
| `Summable.tendsto_cofinite_zero` (existing in Mathlib for ℝ-valued, generalize for ℝ≥0?) | `Mathlib/Topology/Algebra/InfiniteSum/...` | known |
| `Tendsto.norm` (norm of limit ↔ limit of norm) | `Mathlib/Analysis/Normed/Group/Basic` | known |
| Pythagoras for L² in Hilbert basis | `Mathlib/Analysis/InnerProductSpace/l2Space` (probably `HilbertBasis.sq_norm`) | **pin-recheck S2** |

---

## 4. Infrastructure Assessment

| Question | Answer |
|----------|--------|
| **Size estimate** (Option C, primary recommendation) | 200-400 LOC: ~50 LOC component-decomposition lemmas + ~50 LOC Pythagoras step + ~80 LOC DCT swap + ~50 LOC main theorem + ~50 LOC imports / setup |
| **Mathlib gap?** | Likely yes — vec-Parseval for AddCircle is probably absent. May reduce to local lemma if `HilbertBasis.sq_norm` of `f_k`s gives it. |
| **Build vs Block?** | **BUILD** — under 500 LOC, self-contained, leverages existing Hilbert-basis Mathlib API |
| **Alternative (Banach E)?** | L¹-density route — likely 500+ LOC (need approximation by trig polynomials in L¹; Mathlib has `fourierSubalgebra_closure_eq_top` for ℂ but extending to E needs work) — defer to separate slug |

---

## 5. Multi-Cycle Phase Plan

| Phase | Cycle | Scope | Deliverable | Est LOC |
|-------|-------|-------|-------------|---------|
| **S1 OBSERVE** (this PR) | bootstrap | Survey + Mathlib audit + plan | `problem.md`, `knowledge.md`, `state.md`, session memo | 0 Lean / ~600 doc |
| **S2 ORIENT** | S2 PREP / ACT | Mathlib re-audit at fresh pin; verify Option C bearer pins for `HilbertBasis.sq_norm`, `MeasureTheory.integral_inner`, DCT-swap lemma | Bearer-pin updates in `knowledge.md` §3.6; paste-ready skeleton of component decomposition | 0 Lean / ~150 doc |
| **S3 ACT-a** | first proof attempt | Implement `f_k` definition, prove `fourierCoeff f n = Σ_k (fourierCoeff f_k n) • e_k` | `proofs/Proofs/FourierSeriesOQ02OQ01OQ02.lean` v0 with 2-4 sorries | ~80 LOC |
| **S4 ACT-b** | continue | Pythagoras step; DCT swap | v1 with ≤2 sorries | ~120 LOC (cumulative) |
| **S5 ACT-c** | main theorem | Combine components; reduce to parent slug per-coordinate | v2 with ≤1 sorry | ~180 LOC |
| **S6 BUILD-VERIFY** | Docker | `./proofs/scripts/docker-build.sh Proofs.FourierSeriesOQ02OQ01OQ02` | green build | n/a |
| **S7 GALLERY** | gallery wiring | `src/data/proofs/<slug>/meta.json` + annotations | gallery entry | ~200 LOC json/md |
| **S8 COMPLETED** | wrap-up | Status / badge sync; phase → COMPLETED; release | merged PR | n/a |

**Optimistic estimate:** 6-10 cycles to COMPLETED.
**Pessimistic estimate:** 12-18 cycles if `HilbertBasis.sq_norm` for the parametric family
`{f_k}` requires hand-rolled lemmas about Pythagoras under Bochner integration.

---

## 6. Bearer Pins (4-spot recheck at `2df2f0150c…`)

All verified `2026-05-16T~10Z` via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<pin>`:

| # | Path | Size (bytes) | Used for |
|---|------|--------------|----------|
| B1 | `Mathlib/Analysis/Fourier/AddCircle.lean` | 26635 | `fourierCoeff (E-valued)`, `hasSum_sq_fourierCoeff (ℂ)` |
| B2 | `Mathlib/Analysis/Fourier/RiemannLebesgueLemma.lean` | 14732 | Classical RL for ℝⁿ (Banach-E fallback inspiration) |
| B3 | `Mathlib/Analysis/InnerProductSpace/l2Space.lean` | TBD S2 | `HilbertBasis`, `sq_norm`, basis expansion |
| B4 | `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean` | TBD S2 | `integral_inner`, Bochner triangle |

S2 will recheck B3, B4 (size + key signature).

---

## 7. Risk Inventory (Rn)

| ID | Risk | Severity | Mitigation |
|----|------|----------|------------|
| R1 | Mathlib's `HilbertBasis` doesn't directly support Bochner-valued L² | MEDIUM | Option C reduces to componentwise ℂ-Parseval; sidesteps E-valued HilbertBasis entirely |
| R2 | DCT-swap (sum over k vs. limit over n) requires uniform bound | MEDIUM | Bound: `Σ_k |fourierCoeff f_k n|² ≤ ‖f‖²₂` (uniform in n by basis-Pythagoras applied to f) — verify in S2 |
| R3 | `MemLp.toLp` for E-valued may differ from ℂ-version (additional measurable-codomain assumption) | LOW | Parent slug uses `aestronglyMeasurable`; E-valued variant uses same predicate (Bochner-integrability). Cross-check S2. |
| R4 | Hidden separability assumption on E (needed for HilbertBasis ℤ ⟶ countable index) | LOW | State assumption explicitly; document in problem.md |
| R5 | maxHeartbeats may need to be > 400000 (parent's setting) | LOW | Trivial fix; observe in S6 BUILD-VERIFY |
| R6 | Banach-E branch is desirable for completeness | LOW (deferred) | Open as separate slug `…-oq-02-oq-01-oq-02-oq-01` after this one closes |
| R7 | Docker daemon hung / disk pressure during S2-S6 | INFRA | Document in state.md; defer build verification to recovered-host cycle |
| R8 | Parent slug's `riemannLebesgue_of_holder_via_L2` already may be subsumable | LOW | Confirm parent stays the canonical ℂ-version; this slug specializes via E = ℂ |

---

## 8. Open Sub-Questions for Future Cycles

1. Does Mathlib have a `Pythagoras` lemma for Bochner-integrated E-valued L²? (S2 audit)
2. Is `MemLp.toLp` for E-valued the same name as for ℂ? (S2 confirm)
3. Is there a published proof of E-valued Parseval that we can mirror? (Diestel-Uhl "Vector Measures",
   Edwards "Fourier Series", Hewitt-Ross — S2 literature scan if needed)
4. Could the Banach-E branch use Mathlib's `fourierSubalgebra_closure_eq_top` plus a vec-density argument?

---

## 9. Pool / JSON / Iteration State

- **Pool entry:** `available` (will switch to `in-progress` post-bootstrap; release lock at end of cycle).
- **Research JSON:** `src/data/research/problems/fourier-series-oq-02-oq-01-oq-02.json` does **not** exist yet —
  will be created in a later cycle when knowledge accumulation justifies it (per the existing
  pattern, most slugs only get a research JSON entry once they have ≥1 ACT cycle).
- **Iteration:** 1 (this is S1; bumps to 2 in next session).
- **Status flag:** `seeker-selected` retained; no override.

---

## 10. Recent Sessions

### Session 2026-05-16 (S1) — OBSERVE Bootstrap
**Mode:** FRESH
**Outcome:** scouted; research dir seeded

- Verified slug had no `research/problems/` dir, no gallery, no PR history.
- Audited Mathlib pin `2df2f0150c…` (v4.26.0): `fourierCoeff` already E-valued; Parseval `hasSum_sq_fourierCoeff` is ℂ-only.
- Identified Option C (componentwise reduction to parent slug's ℂ-result via Hilbert basis of E) as primary path.
- Recorded 8-phase multi-cycle plan; R1-R8 risk inventory.

**Files Modified:** 4 NEW (problem.md, knowledge.md, state.md, sessions/2026-05-16-s1-observe-bootstrap.md).

**Next Steps:** S2 ORIENT — pin-recheck B3, B4; confirm `HilbertBasis.sq_norm` API; draft paste-ready component-decomposition skeleton.
