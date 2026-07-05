# Knowledge Base: rh-consequences-oq-01

Target: discharge the parent axiom `rh_implies_mertens_bound` in
`proofs/Proofs/RiemannHypothesisConsequences.lean` — i.e. prove that under the
Riemann Hypothesis the Mertens function `M(x) = Σ_{n ≤ x} μ(n)` satisfies
`M(x) = O(x^{1/2+ε})` for every `ε > 0`.

**Scope note (avoid duplication):** this problem is the *forward* implication
only (RH ⟹ bound). The sibling `rh-consequences-oq-03` owns the *full Littlewood
equivalence* RH ⟺ `M(x)=O(x^{1/2+ε})`. Keep the converse (bound ⟹ RH) out of
scope here; if the converse gets built, it belongs to oq-03.

---

## Problem Understanding

- The parent gallery file already **defines** `mertens n : ℤ := Σ_{k∈range(n+1)}
  moebius k` and states the conclusion as a bare top-level
  `axiom rh_implies_mertens_bound : RiemannHypothesis → ∃ C>0, ∀ n≥1,
  |mertens n| ≤ C * Real.sqrt n`. Note this is the sharper *√x* form (ε = 0 with
  an implied `log`-free constant); the seeker's title asks for the softer, and
  strictly weaker/more standard, `O(x^{1/2+ε})` form. **Recommendation: target
  the `x^{1/2+ε}` form**, which is the genuine RH-equivalent statement
  (`|M(x)| ≤ C√x` is *stronger* than RH — it is essentially the disproved
  Mertens-conjecture territory and is NOT known to follow from RH). This is a
  substantive correction: the parent axiom as literally stated (`≤ C√x`) is
  believed **false**; the correct RH consequence carries the `ε`.
- RH is encoded as a standalone `def RiemannHypothesis : Prop`, not as a field of
  an `RHAxioms`-style structure. So "discharging" the axiom means writing
  `theorem rh_implies_mertens_bound (h : RiemannHypothesis) : … := …` and
  deleting the `axiom`. No shared assumption-carrier to reuse — the RH hypothesis
  rides on the theorem signature.

---

## Insights

### I1 — The correct target is `x^{1/2+ε}`, not `√x`
`|M(x)| ≤ C√x` for all x would contradict known Ω-results
(Odlyzko–te Riele-style oscillation lower bounds show `limsup M(x)/√x > 1`, and
it is conjectured `= +∞`). RH is equivalent to `M(x) = O(x^{1/2+ε})` for every
`ε>0` (Littlewood), which is genuinely weaker. **Any formalization must use the
ε-form**; the parent's `≤ C√x` axiom overclaims and should be softened to
`∀ ε>0, ∃ C, |M(n)| ≤ C·n^{1/2+ε}` when the axiom is eventually discharged.

### I2 — The implication factors into one deep RH-free piece + one short RH piece
Classical route (Perron / Mellin inversion of the Dirichlet series
`Σ μ(n) n^{-s} = 1/ζ(s)`, valid for `Re s > 1`):

  M(x) = (1/2πi) ∫_{(c)} x^s / (s ζ(s)) ds ,   c > 1 (truncated at height T).

Shift the contour left to the line `Re s = 1/2 + ε`. The RH content enters at
exactly two points, both *localized*:
  - (a) **no-pole guarantee**: under RH, `ζ(s) ≠ 0` for `Re s > 1/2`, so `1/ζ` is
    holomorphic across the strip `1/2+ε ≤ Re s ≤ c` and the only residue crossed
    is the `s=0` pole of the `1/s` factor (residue `1/ζ(0) = -2`, an O(1) term);
  - (b) **growth bound**: under RH, `|1/ζ(1/2+ε+it)| ≪_ε |t|^{ε}` (Titchmarsh,
    *Theory of the Riemann Zeta-Function*, Thm 14.2), so on the shifted line
    `|x^s| = x^{1/2+ε}` and the truncated integral is `≪ x^{1/2+ε}` after the
    standard `T ≍ x` optimization of the truncation error.
Everything else — the truncated Perron formula with explicit error term, the
horizontal-segment estimates, the `T`-optimization — is **RH-free complex
analysis**. So the "hard mathematics" is not the RH step; it is the analytic
inversion machinery.

### I3 — Recommended axiom-boundary refactor (the actionable engineering insight)
Rather than carry one opaque `rh_implies_mertens_bound` axiom, a future
formalization should factor the parent axiom into two *individually recognizable*
analytic inputs and a **verified** assembly:

  (P)  [RH-free] Truncated Perron representation for the summatory Möbius
       function: for `x ∉ ℤ`, `c>1`, `T≥2`,
         `M(x) = (1/2πi)∫_{c-iT}^{c+iT} x^s/(s ζ(s)) ds + E`,  with
         `|E| ≪ x^c/(T · (c-1)) + (log x)·(…)`  (standard Perron error).
  (Z)  [RH-conditional] `RiemannHypothesis → ∀ ε>0, ∃ C_ε,
         ∀ t, |1/ζ(1/2+ε+it)| ≤ C_ε (1+|t|)^ε`  and  `ζ(s)≠0 for Re s>1/2`.
  (Assembly, VERIFIED) From (P)+(Z): shift the contour, bound `|x^s|=x^{1/2+ε}`,
       integrate the `≪ (1+|t|)^{ε-1}` integrand up to `T`, optimize `T≍x`
       ⟹ `M(x) = O(x^{1/2+ε})`.

The Assembly step is a *bounded-vertical-line integral estimate* — a plausible
~150–300-line Lean target using Mathlib's `MellinTransform` / `Complex` integral
API — provided (P) and (Z) are typed axioms/hypotheses. This strictly improves
axiom hygiene over the parent's monolith and isolates precisely what Mathlib must
eventually supply. **This is the recommended first ACT goal** once build infra
returns.

---

## Mathlib Coverage Audit (as of 2026-07, mainline mathlib4)

**Present / usable:**
- `ArithmeticFunction.moebius` (μ); `ArithmeticFunction.moebius_mul_coe_zeta`
  (μ ∗ 1 = δ, i.e. Σ_{d|n} μ(d) = [n=1]). Parent file already builds `mertens`.
- `LSeries`, `LSeries_moebius`-style identities: `LSeries μ (s) = 1/ζ(s)` on the
  half-plane `Re s > 1` (via `LSeries_mul` / the convolution `μ ∗ 1 = δ`). The
  reciprocal-of-zeta Dirichlet series is available where it converges.
- `riemannZeta`: analytic continuation, functional equation, trivial zeros,
  `riemannZeta_ne_zero_of_one_le_re` (ζ ≠ 0 on Re ≥ 1). Pole at s=1.
- `Mathlib.Analysis.MellinTransform`: Mellin transform + inversion API — the
  natural substrate for a Perron formula, though Perron itself is not derived.
- `Complex` contour / interval integrals, `intervalIntegral`, holomorphicity and
  residue-adjacent lemmas.

**Missing (the real gaps — each is the blocker):**
- **Perron's formula / truncated Perron** for summatory functions of a Dirichlet
  series. NOT in mainline. (The out-of-tree `PrimeNumberTheoremAnd` project has
  Perron-type and Newman-Tauberian machinery, but it is (i) not upstreamed and
  (ii) tuned to PNT via a *different* Tauberian route, not the explicit
  `x^{1/2+ε}` contour bound.) → this is input (P).
- **Conditional 1/ζ growth bounds** `|1/ζ(σ+it)| ≪_ε |t|^ε` in the critical
  strip under RH (Titchmarsh Ch. 14; requires Borel–Carathéodory + Hadamard
  three-circles applied to `log ζ`). NOT formalized. → this is input (Z).
- **Explicit formula for M(x)** in terms of the nontrivial zeros
  `M(x) = Σ_ρ x^ρ/(ρ ζ'(ρ)) + …`. NOT in mainline. (An alternative to the
  Perron+growth route; would let RH ⟹ each `|x^ρ| = x^{1/2}` directly.)
- The RH-zero-location fact `ζ(s)=0, 0<Re s<1 ⟹ Re s = 1/2` is *stateable* from
  the parent's `RiemannHypothesis` def, but its analytic consequences for `1/ζ`
  growth are exactly what is unformalized.

---

## Infrastructure Assessment

**Needed:** truncated Perron for L-series summatory functions (P) + conditional
critical-strip 1/ζ bound (Z).
**Size estimate:** (P) ≈ 400–800 lines (Mellin inversion + error term); (Z) ≈
500–1000+ lines (Borel–Carathéodory, three-circles, `log ζ` machinery). Total
well over 1000 lines of hard complex analysis.
**Decision:** **BLOCKED** for a full end-to-end verified/axiomatized proof at the
current Mathlib state. **BUILD-later:** the *Assembly* lemma (~150–300 lines) is
tractable once (P),(Z) are axiomatized — that is the recommended incremental path.
**Reasoning:** the two analytic inputs are individually large Mathlib
contributions; neither has an elementary shortcut. But the RH→bound *logic* is
short and formalizable in isolation, so partial verified progress is available via
the axiom-boundary refactor (I3) rather than an all-or-nothing axiom.

---

## Anti-Goals

- Do **not** target the parent's literal `|M(x)| ≤ C√x` form — it is believed
  **false** (overclaims RH). Use `∀ε>0, O(x^{1/2+ε})`.
- Do **not** formalize the converse (bound ⟹ RH) here — that is `oq-03`'s
  Littlewood-equivalence scope.
- Do **not** introduce a second RH assumption carrier; keep RH on the theorem
  signature as the parent does.
- Do **not** claim `verified`; any discharge is `axiomatized` (conditional on RH,
  and — under the I3 refactor — on the two analytic inputs P,Z).
- Do **not** attempt the full contour argument in one PR; land the Assembly
  lemma against typed (P),(Z) axioms first.

---

## Session Log

## Session 2026-07-04 (Session 1) — ORIENT survey (build-blocked)

**Mode**: FRESH · **Outcome**: surveyed (OBSERVE → ORIENT)

### What I Did
- Read parent `RiemannHypothesisConsequences.lean`: RH is a standalone `def`; the
  target is a bare `axiom rh_implies_mertens_bound` stated in the `≤ C√x` form.
- Confirmed sibling scope split: oq-03 = full Littlewood equivalence; oq-01 =
  forward direction only.
- Audited mainline Mathlib coverage (LSeries μ = 1/ζ, riemannZeta, MellinTransform
  present; Perron, conditional 1/ζ bounds, explicit formula absent).
- Web-checked current literature/Mathlib status (Perron + zero-free route
  confirmed standard; explicit-formula comparison to ζ-zeros is the alt route).

### Key Findings
- **Correction (I1):** parent axiom's `≤ C√x` form overclaims; the true RH
  consequence is the ε-form `O(x^{1/2+ε})`. Flag for the eventual discharge.
- **Factorization (I2):** RH enters only via (a) no-pole + (b) `|1/ζ| ≪ |t|^ε`;
  the bulk is RH-free Perron machinery.
- **Refactor (I3):** decompose the monolith axiom into (P) Perron + (Z)
  conditional 1/ζ bound + a *verifiable* Assembly estimate; land Assembly first.
- **Gap size:** (P)+(Z) > 1000 lines ⟹ full proof BLOCKED; Assembly ~150–300
  lines is the tractable incremental target.

### Tooling note
Session ran during a dual-tool blackout: Docker build (containerd blob I/O
corruption — needs a Docker restart, independent of disk) and Aristotle
(`Resource not found` / 404) both unavailable. No Lean written or built; this is a
prose/survey deliverable only.

### Next Steps
1. When build infra returns: write `RiemannHypothesisConsequencesOQ01.lean` with
   typed axioms `perron_mertens` (P) and `inv_zeta_bound_of_RH` (Z), then prove
   the Assembly lemma `mertens_bound_of_perron_and_zeta_bound` giving
   `∀ε>0, ∃C, |mertens n| ≤ C·n^{1/2+ε}`.
2. Separately, open a note against the parent to soften its `≤ C√x` axiom to the
   ε-form (correctness fix).
3. Long-horizon: contribute (P) truncated Perron for L-series to Mathlib (general
   interest, unblocks PNT-adjacent work too).
