import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Tactic

/-
# The Weierstrass Approximation Theorem

## What This Proves

Karl Weierstrass's 1885 approximation theorem is a cornerstone of analysis:

> Every real-valued function that is continuous on a closed bounded interval
> `[a, b]` is a uniform limit of polynomials.

This file assembles the theorem in four complementary forms — the
"epsilon" form, the genuine *sequence* form (a single sequence of polynomials
converging uniformly), the abstract *density* form, and an explicit
*constructive* sequence (Bernstein polynomials) — and finishes with
Weierstrass's own celebrated witness, the non-differentiable function `|x|`.

* **Epsilon form** (`weierstrass_epsilon`). For every `ε > 0` there is a
  polynomial `p` with `|p(x) - f(x)| < ε` for all `x ∈ [a, b]`.

* **Sequence form** (`exists_polynomial_seq_tendstoUniformlyOn`). There is a
  single sequence of polynomials `pₙ` converging *uniformly* to `f` on
  `[a, b]`. This is the literal "uniform limit of polynomials" statement and
  is the mathematical heart of the file: it is built from the epsilon form by
  choosing `pₙ` within `1/(n+1)` of `f` and proving the resulting sequence
  satisfies the `TendstoUniformlyOn` predicate.

* **Density form** (`weierstrass_density`). The subalgebra of polynomial
  functions is topologically dense in `C([a, b], ℝ)`: its closure is the whole
  space.

* **Constructive form** (`bernstein_tendstoUniformly`). On `[0, 1]` the
  explicit Bernstein polynomials `∑ₖ f(k/n)·C(n,k)·xᵏ·(1-x)^(n-k)` converge
  uniformly to `f` — an effective approximating sequence, not a mere existence
  statement.

* **Concrete instance** (`exists_polynomial_near_abs`,
  `exists_polynomial_seq_abs`). The absolute-value function `|x|`, Weierstrass's
  own example of a continuous but non-smooth function, is uniformly
  approximable by polynomials on `[-1, 1]`.

## Relation to Mathlib

Mathlib proves the theorem behind the bundled/unbundled epsilon forms
(`exists_polynomial_near_of_continuousOn`) and the density form
(`polynomialFunctions_closure_eq_top`), and the constructive Bernstein
convergence (`bernsteinApproximation_uniform`). What is **not** in Mathlib —
and what this file contributes — is the packaging of these into the single
*uniformly convergent sequence of polynomials* (`TendstoUniformlyOn`) that is
the textbook statement of the theorem, together with the worked `|x|`
instance. A `grep` of `proofs/Proofs` for `exists_polynomial_near`,
`polynomialFunctions`, or `bernsteinApproximation` returns no prior
formalization; the gallery had only incidental prose mentions.

This file is `0`-axiom (only `propext` / `Classical.choice` / `Quot.sound`;
no `native_decide`).
-/

namespace WeierstrassApproximation

open Filter Topology unitInterval
open scoped Polynomial

/-- **Weierstrass approximation, epsilon form.** Every function continuous on
`[a, b]` is within any `ε > 0` of some polynomial, uniformly on `[a, b]`. This
is `exists_polynomial_near_of_continuousOn`, restated as the headline. -/
theorem weierstrass_epsilon (a b : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε :=
  exists_polynomial_near_of_continuousOn a b f hf ε hε

/-- **Weierstrass approximation, density form.** The polynomial functions are
topologically dense in `C([a, b], ℝ)`: the closure of the subalgebra they
generate is the whole space. This is `polynomialFunctions_closure_eq_top`. -/
theorem weierstrass_density (a b : ℝ) :
    (polynomialFunctions (Set.Icc a b)).topologicalClosure = ⊤ :=
  polynomialFunctions_closure_eq_top a b

/-- **Weierstrass approximation, sequence form** (the textbook statement).
Every function continuous on `[a, b]` is the *uniform* limit of a single
sequence of polynomials.

Construction: choose, for each `n`, a polynomial `pₙ` within `1/(n+1)` of `f`
on `[a, b]` (epsilon form); since `1/(n+1) → 0`, the sequence `pₙ` converges to
`f` uniformly on `[a, b]`. -/
theorem exists_polynomial_seq_tendstoUniformlyOn (a b : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ p : ℕ → ℝ[X],
      TendstoUniformlyOn (fun n x => (p n).eval x) f atTop (Set.Icc a b) := by
  -- For each `n`, pick a polynomial within `1/(n+1)` of `f` on `[a, b]`.
  choose p hp using fun n : ℕ =>
    exists_polynomial_near_of_continuousOn a b f hf (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨p, ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- Beyond some index `N > 1/ε`, the gap `1/(n+1)` drops below `ε`.
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  filter_upwards [eventually_ge_atTop N] with n hn x hx
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- `1/(n+1) ≤ ε` for `n ≥ N`.
  have hbound : 1 / ((n : ℝ) + 1) ≤ ε := by
    rw [div_le_iff₀ hnpos]
    have h1 : (1 : ℝ) / ε < (n : ℝ) + 1 :=
      calc (1 : ℝ) / ε < N := hN
        _ ≤ (n : ℝ) := by exact_mod_cast hn
        _ ≤ (n : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hε] at h1
    nlinarith [h1]
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_lt_of_le (hp n x hx) hbound

/-- **Weierstrass approximation, constructive form (Bernstein).** For a
continuous `f` on `[0, 1]`, the explicit Bernstein approximants
`bernsteinApproximation n f = ∑ₖ bernstein n k · f(k/n)` converge uniformly to
`f` as `n → ∞`. This is `bernsteinApproximation_uniform`, an *effective*
approximating sequence — no choice or existential is needed to write it down. -/
theorem bernstein_tendstoUniformly (f : C(I, ℝ)) :
    Tendsto (fun n : ℕ => bernsteinApproximation n f) atTop (𝓝 f) :=
  bernsteinApproximation_uniform f

/-- **The absolute-value function is uniformly approximable.** Weierstrass's own
example: `|x|` is continuous but not differentiable at `0`, yet for every
`ε > 0` there is a polynomial `p` with `|p(x) - |x|| < ε` for all
`x ∈ [-1, 1]`. -/
theorem exists_polynomial_near_abs {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℝ[X], ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x - abs x| < ε :=
  weierstrass_epsilon (-1) 1 (fun x => |x|) (_root_.continuous_abs.continuousOn) hε

/-- **A polynomial sequence converging uniformly to `|x|` on `[-1, 1]`.** The
sequence form specialized to Weierstrass's non-smooth witness. -/
theorem exists_polynomial_seq_abs :
    ∃ p : ℕ → ℝ[X],
      TendstoUniformlyOn (fun n x => (p n).eval x) (fun x => |x|) atTop
        (Set.Icc (-1 : ℝ) 1) :=
  exists_polynomial_seq_tendstoUniformlyOn (-1) 1 (fun x => |x|)
    (_root_.continuous_abs.continuousOn)

end WeierstrassApproximation
