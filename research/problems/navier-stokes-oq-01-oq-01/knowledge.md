# Knowledge Base: navier-stokes-oq-01-oq-01

**Can the Ladyzhenskaya inequality `‖u‖₄ ≤ C‖u‖₂^{1/2}‖∇u‖₂^{1/2}` (2D) be
formalized in Lean/Mathlib?**

---

## Problem Understanding

The Ladyzhenskaya inequality is the `d = 2` case of Gagliardo–Nirenberg:
for compactly-supported `u : ℝ² → ℝ`,

    ‖u‖_{L⁴(ℝ²)} ≤ C · ‖u‖_{L²}^{1/2} · ‖∇u‖_{L²}^{1/2},   sharp C = 2^{1/4}.

It is the estimate that closes the 2D Navier–Stokes energy/enstrophy loop, so it
sits directly under parent `navier-stokes-oq-01` (2D enstrophy decay).

### Ladyzhenskaya's classical proof (the structure to formalize)
For each fixed `y`, `u(x,y)² = ∫_{-∞}^x ∂₁(u²) ≤ 2∫ℝ |u||∂₁u| dx' =: g(y)`
(independent of `x`). Symmetrically `u(x,y)² ≤ 2∫ℝ |u||∂₂u| dy' =: h(x)`. Hence

    ∫∫ u⁴ = ∫∫ u²·u² ≤ ∫∫ g(y)h(x) = (∫g)(∫h)
          = (2∫∫|u||∂₁u|)(2∫∫|u||∂₂u|) = 4·a·b,   a := ∫∫|u||∂₁u|, b := ∫∫|u||∂₂u|.

Cauchy–Schwarz gives `a ≤ ‖u‖₂‖∂₁u‖₂`, `b ≤ ‖u‖₂‖∂₂u‖₂`, and AM–GM
`‖∂₁u‖₂‖∂₂u‖₂ ≤ ½‖∇u‖₂²`, so `‖u‖₄⁴ ≤ 2‖u‖₂²‖∇u‖₂²`, i.e. `C = 2^{1/4}`.

The proof factors into
* **(A) analytic inputs** — the integrated pointwise product bound `n4⁴ ≤ 4ab`
  and the two Cauchy–Schwarz slice estimates; and
* **(B) an algebraic assembly** of (A) into the final bound + sharp constant.

---

## Result (this session, VERIFIED)

`proofs/Proofs/NavierStokesOQ0101.lean` (122 L, 3 theorems, **0 axioms /
0 sorries**, `#print axioms` = `[propext, Classical.choice, Quot.sound]` only,
built on Mathlib v4.26 warm cache). It formalizes **Part (B) in full** and
exposes **Part (A) as explicit hypotheses**:

- `cross_le_grad_sq : d1*d2 ≤ (d1²+d2²)/2` — the sharp AM–GM step fixing the
  constant (equality at `d1 = d2`, i.e. `‖∂₁u‖ = ‖∂₂u‖`).
- `ladyzhenskaya_assembly` — from `(n4⁴ ≤ 4ab, a ≤ n2·d1, b ≤ n2·d2)` derive
  `n4⁴ ≤ 2·n2²·(d1²+d2²)`. This is the entire non-analytic content of the proof.
- `ladyzhenskaya_sq_form` — repackages `n4⁴ ≤ 2n2²ng²` as the clean
  `n4² ≤ √2·n2·ng` (`‖u‖₄² ≤ √2‖u‖₂‖∇u‖₂`), one square-root from the stated form.

So the answer to OQ-01-01 is a **qualified yes**: the algebraic skeleton and the
sharp constant are fully machine-checked; what remains is purely the analytic
inputs (A), which are exactly the Mathlib gap below.

---

## Insights / The Mathlib gap (Part A)

Grepping `Mathlib/Analysis/` (v4.26) for `Ladyzhenskaya`, `GagliardoNirenberg`,
`gagliardo`, and interpolation returns **nothing** relevant. Missing pieces:

1. **The pointwise/slice bound** `u(x,y)² ≤ 2∫|u||∂₁u|dx'`. Needs the 1D FTC for
   (weak) derivatives plus Fubini/Tonelli to integrate slices. Mathlib has
   `intervalIntegral.integral_deriv_eq_sub` and `MeasureTheory.lintegral_prod`,
   but wiring them to `∇u` in the Sobolev sense is not packaged.
2. **`L^p`-norm Cauchy–Schwarz** `∫|u||∂₁u| ≤ ‖u‖₂‖∂₁u‖₂` — this one *is* within
   reach (`MeasureTheory.inner_mul_le_norm_mul_norm` / `ENNReal.lintegral_mul_le`),
   the least-blocked input.
3. **Weak-derivative / Sobolev API.** No `W^{1,2}` space with `∂ᵢ` and a chain
   rule `∂ᵢ(u²) = 2u∂ᵢu` at the generality needed. This is the real blocker; a
   faithful formalization of (A) is a >1000-line foundational effort.

**Recommendation:** do **not** attempt the full analytic proof in one session.
The highest-value next step is input (2) — a standalone verified
`∫|u||v| ≤ ‖u‖₂‖v‖₂` in Mathlib's `MemLp` API — after which
`ladyzhenskaya_assembly` already consumes it. Inputs (1) and (3) should wait for
(or motivate) a Sobolev-space contribution to Mathlib itself.

---

## Dead Ends / Cautions

- Trying to `native_decide` or `nlinarith` the *analytic* facts is hopeless —
  they are integral inequalities, not real-arithmetic ones.
- Do **not** promote a "verified Ladyzhenskaya inequality" gallery claim from
  this file: only Part (B) is verified. The honest framing is "algebraic
  assembly + analytic-gap specification."

---

## Pointers
- New: `proofs/Proofs/NavierStokesOQ0101.lean`.
- Parent: `proofs/Proofs/NavierStokes.lean` (2D enstrophy, 845 thm / 1 axiom).
- Ladyzhenskaya, *Math. Theory of Viscous Incompressible Flow*, 1969.
