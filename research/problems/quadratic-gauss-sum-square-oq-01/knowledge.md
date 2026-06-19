# Sign of the quadratic Gauss sum (Gauss's hard theorem)

**Pool id:** `quadratic-gauss-sum-square-oq-01` · **Tier B** · significance 6 · tractability 4

## Problem

For an odd prime `p` and a primitive additive character `ψ : ZMod p → ℂ`, let
`g = gaussSum (chiC p) ψ`. The parent gallery entry proves `g² = (-1)^((p-1)/2)·p`,
and the **verified** entry `quadratic-gauss-sum-square-oq-01` (slug collision — it is
the DICHOTOMY entry) extracts `g.im = 0` for `p ≡ 1 (mod 4)`, `g.re = 0` for
`p ≡ 3 (mod 4)`, and `‖g‖² = p`. The open target here is **Gauss's hard sign theorem**:

    g = +√p     (p ≡ 1 mod 4),
    g = +i·√p   (p ≡ 3 mod 4).

## Session 2026-06-19 (Session 1) — ORIENT, reduction to a single positivity

**Mode:** FRESH · **Outcome:** progress (verified reduction; deep crux remains open)

### What I did
- Confirmed the dichotomy + magnitude already exist and are verified (0 sorries) in
  `QuadraticGaussSumSquareOQ01.lean`.
- Confirmed Mathlib (v4.26.x) has **no** sign determination and no finite-Fourier
  determinant/eigenvalue infrastructure (`NumberTheory/GaussSum.lean` stops at the
  square identity `gaussSum_sq`).
- Wrote and **built (sorry-free, axiom-free)** `Proofs/QuadraticGaussSumSignReduction.lean`:
  - `gaussSum_eq_pm_sqrt` — strengthens "g real" to `g = ±√p` (p ≡ 1).
  - `gaussSum_eq_pm_I_sqrt` — strengthens "g imaginary" to `g = ±i√p` (p ≡ 3).
  - `gaussSum_eq_sqrt_iff_re_pos` — **`g = √p ↔ 0 < g.re`** (p ≡ 1).
  - `gaussSum_eq_I_sqrt_iff_im_pos` — **`g = i√p ↔ 0 < g.im`** (p ≡ 3).
  - Docker build: `✔ [7745/7745] Built Proofs.QuadraticGaussSumSignReduction`.

### Key findings
- The entire open content of Gauss's hard theorem collapses to **one real inequality**:
  `0 < Re(g)` (p ≡ 1) / `0 < Im(g)` (p ≡ 3). Everything else (which axis, magnitude,
  the ± alternative) is elementary and now machine-checked.
- Both classical routes target exactly this positivity:
  - **Schur** — eigenvalue multiplicities of the n×n DFT matrix (`ζ^{jk}`); needs
    DFT-spectrum infra Mathlib lacks. Estimate ≫1000 lines.
  - **Dirichlet** — Poisson summation / theta functional equation; heavy analysis infra.
    Estimate ≫1000 lines.

### Infrastructure assessment
**Needed:** sign of the quadratic Gauss sum (`0 < Re g` resp `0 < Im g`).
**Size estimate:** >1000 lines either route (no Mathlib DFT-determinant or theta infra).
**Decision:** BLOCKED short-term — but the reduction above is the shared final step of
both routes, so it is reusable groundwork rather than throwaway.

### Files modified
- `proofs/Proofs/QuadraticGaussSumSignReduction.lean` (new, verified)
- `proofs/Proofs.lean` (import)
- `src/data/research/problems/quadratic-gauss-sum-square-oq-01.json` (new knowledge)

### Next steps
- Attack `0 < Re(gaussSum (chiC p) ψ)` for `p ≡ 1 (mod 4)` via the Schur route once (or if)
  DFT eigenvalue-multiplicity infrastructure becomes available in Mathlib.
- Consider contributing the four-point pinning / reduction lemmas toward a future
  Mathlib `GaussSum` sign development.
