# Problem: Numerical Instabilities in Ferrari's Quartic Formula

## Statement

### Plain Language

Ferrari's method (1540) gives a closed-form solution of every quartic
`x⁴ + ax³ + bx² + cx + d = 0` over ℂ, but the explicit formula is *numerically
unstable*: in finite-precision arithmetic, it can lose almost all significant
digits in well-conditioned regions of parameter space. **How can these
instabilities be characterized rigorously, and what conditions on the
coefficients `(a, b, c, d)` make Ferrari's formula well-conditioned?**

### Formal Question

Let `ferrariRoots : ℂ → ℂ → ℂ → ℂ → ℂ⁴` denote the explicit Ferrari formula
(after depression) and `roots : ℂ → ℂ → ℂ → ℂ → Multiset ℂ` the exact
solution-set of the depressed quartic. Three nested sub-questions:

1. **(OQ-02.a) Exact-arithmetic stability witnesses.** Identify parameter
   families `(p(t), q(t), r(t))` along which an intermediate quantity of
   `ferrariRoots` cancels at a higher rate than the output roots themselves
   converge. Formal statement (placeholder):
   ```
   ∃ (p q r : ℝ → ℂ) (k : ℕ), k ≥ 2 ∧
     (∀ t, |ferrariIntermediate (p t) (q t) (r t)| = O(tᵏ)) ∧
     (∀ t, |rootSpread (p t) (q t) (r t)| = Θ(t))
   ```
   The ratio `(rootSpread / ferrariIntermediate)` then bounds the relative
   forward error in fixed-precision arithmetic by `Ω(t^{1−k})`.

2. **(OQ-02.b) Conditioning of the discriminant boundary.** Prove or refute:
   on the set `{ (p,q,r) ∈ ℝ³ : |Δ(p,q,r)| ≥ ε }` (where `Δ` is the quartic
   discriminant), Ferrari's formula is well-conditioned with explicit
   constant. Concretely, the *relative* condition number of `ferrariRoots`
   satisfies `κ ≤ C · poly(‖(p,q,r)‖) / ε` for absolute `C`.

3. **(OQ-02.c) Biquadratic-limit removable singularity.** When `q → 0`, the
   intermediate quantity `β = q / (2α)` is of indeterminate form `0/0` if
   the chosen resolvent root `m` makes `α = √(2m + p) = 0`. Show that the
   limit `lim_{q→0} ferrariRoots (p, q, r, m_{q})` agrees with the
   biquadratic roots `(±√((-p ± √(p²−4r))/2))`. This is a *symbolic*
   identity over ℂ, not a floating-point statement.

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - algebra
  - polynomial
  - numerical-analysis
  - wiedijk-100
  - seeker-selected
```

**Significance**: 6/10 — The instability of Ferrari's formula is folklore in
numerical analysis (Pan 1997; Bini–Pan 1996) but has no rigorous Lean
formalization. A clean OQ-02.c result would extend the parent gallery
entry's symbolic correctness story to its degenerate limits.

**Tractability**: 6/10 — OQ-02.c is concrete (a ℂ-symbolic identity,
provable by `ring` after L'Hôpital expansion). OQ-02.a admits a single
explicit witness family. OQ-02.b is genuinely hard (requires a `condNum`
infrastructure that doesn't currently exist in Mathlib).

## Why This Matters

1. **Algorithmic relevance.** Ferrari's formula is taught in algebra courses
   but is rarely the algorithm used in practice; root-finders default to
   companion-matrix QR (Pan 1997). A rigorous accounting of *why* lets us
   teach the algorithm more honestly in the gallery.

2. **Boundary completeness of parent.** `proofs/Proofs/GeneralQuartic.lean`
   states `ferrari_roots_are_roots` as an axiom on the generic stratum
   (`α ≠ 0` implicit in `β = q/(2α)`). OQ-02.c closes the `α = 0` edge case
   by symbolic limit, contributing to eventually replacing the
   `ferrari_roots_verify` axiom with a theorem.

3. **Mathlib gap surfaced.** Condition-number infrastructure for explicit
   algebraic formulas is absent from Mathlib. Even an OQ-02.c-shaped result
   would seed a possible `Mathlib.Analysis.Conditioning` namespace.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| [`general-quartic`](https://github.com/rjwalters/lean-genius/blob/main/proofs/Proofs/GeneralQuartic.lean) | Parent entry: axiomatized Ferrari root formula. OQ-02 attacks the limit/conditioning behavior of `ferrariRoots`. |
| `cardano-cubic` (Wiedijk #37) | Ferrari delegates to Cardano via `resolventCubic`. Numerical instability there propagates here. |
| `quadratic-formula` | The "stable" two-step reduction `quartic → quadratic in y² (biquadratic case)` is OQ-02.c's anchor. |

## References

- W. Kahan (2004). *To Solve a Real Cubic Equation* — analogous catastrophic
  cancellation discussion at the cubic level.
- V. Pan (1997). *Solving a Polynomial Equation: Some History and Recent
  Progress.* SIAM Review **39**(2), 187–220.
- D. Bini and V. Pan (1996). *Polynomial and Matrix Computations*, Vol. 1.
  Birkhäuser. Chapter on numerical conditioning of explicit root formulas.
- J. H. Wilkinson (1965). *The Algebraic Eigenvalue Problem*, Oxford.
  Foundational reference on QR-based root-finding stability.
- W. H. Press et al. *Numerical Recipes* §5.6 "Quartic Equations" — practical
  warning against Ferrari's formula in finite precision.
