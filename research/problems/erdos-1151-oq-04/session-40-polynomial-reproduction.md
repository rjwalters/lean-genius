# Session 40 (2026-07-24, researcher-3): polynomial reproduction — Lₙp = p for deg p < n

## Goal

Discharge S40 option (i) from the S39 roadmap: the polynomial-reproduction
lemma `chebyshevInterp n p x = p x` for `p.degree < n` — the missing
"lacunary-assembly" ingredient of Sorry 2's strong (full-limit) form.

## Outcome (Lean exit 0 first attempt; 1 pre-existing sorry unchanged)

`proofs/Proofs/Erdos1151OQ04.lean` +~70 LOC (new "Session 40" section at end,
plus `import Mathlib.LinearAlgebra.Lagrange`):

| New theorem | Content |
|---|---|
| `lagrangeBasis_eq_eval_basis` | bridge: the file's function-level `lagrangeBasis` = eval of Mathlib's polynomial-level `Lagrange.basis` (no injectivity needed) |
| `lagrangeInterp_polynomial` | injective nodes, `p.degree < n` ⟹ `lagrangeInterp n nodes p.eval x = p.eval x` |
| **`chebyshevInterp_polynomial`** | Chebyshev interpolation reproduces every polynomial of degree < n |
| `sum_lagrangeBasis_eq_one` | partition of unity Σₖ ℓₖ(x) = 1 (the p = 1 instance) |
| `sum_chebyshev_lagrangeBasis_eq_one` | ditto at Chebyshev nodes |

`#print axioms` on `chebyshevInterp_polynomial` and
`sum_chebyshev_lagrangeBasis_eq_one`: `[propext, Classical.choice, Quot.sound]`
— independent of the file's remaining sorry. Host-verified on the pinned
v4.31.0 toolchain (mathlib `9a9483a929`); the only diagnostics in the new
section: none (file-wide warnings are all pre-existing: deprecated Chebyshev
import, `push_neg` deprecations, unused-variable lints at lines ≤ 615).

## Method

Rather than a from-scratch degree induction, bridge to Mathlib's
`LinearAlgebra.Lagrange`:

* `Lagrange.basisDivisor a b = C (a - b)⁻¹ * (X - C b)` evaluates to
  `(a - b)⁻¹ * (x - b)`, which is `div_eq_inv_mul` away from this file's
  factor `(x - b)/(a - b)` — so `lagrangeBasis n nodes k x =
  (Lagrange.basis Finset.univ nodes k).eval x` by `Polynomial.eval_prod` +
  `Finset.prod_congr`.
* `Lagrange.eq_interpolate (hvs : Set.InjOn v s) (hdeg : p.degree < #s) :
  p = interpolate s v (fun i => p.eval (v i))`, evaluated at `x` through
  `Lagrange.interpolate_apply` + `Polynomial.eval_finsetSum`, gives the
  reproduction identity.

## Where this fits in the Sorry 2 roadmap

Sorry 2 (`divergence_from_lebesgue_growth`) in its strong full-limit form
needs (per the S39 correction): (a) the continuous saturation witness — DONE
S39; (b) a gliding-hump lacunary assembly, whose cross-term control needs
exactly `Lₙp = p` for the already-frozen polynomial part — DONE THIS SESSION —
plus the sign structure of ℓₖⁿ(x) across n for full-limit (not just limsup)
growth. Remaining for S41+: the gliding-hump assembly itself (inductive
choice of amplitudes aⱼ and degrees nⱼ, with the frozen part reproduced
exactly by `chebyshevInterp_polynomial` and the new tail controlled by the
saturation witness), or the PLAN decision to revive the S30 limsup weakening.

## Gotchas

* `Polynomial.eval_finsetSum` (camelCase) is the v4.31 name — not
  `eval_finset_sum`.
* Degree hypothesis states cleanly as `p.degree < (n : WithBot ℕ)`;
  `#univ`-form via `simpa using hdeg`.
* `Polynomial.degree_one` + `exact_mod_cast hn` handles the `0 < n` cast into
  `WithBot ℕ` for the partition-of-unity instance.
