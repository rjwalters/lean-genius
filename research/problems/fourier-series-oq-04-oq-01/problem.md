# Problem: 2D Carleson conjecture for spherical Fourier series on $\mathbb{T}^2$

## Statement

### Plain Language

For $f \in L^2(\mathbb{T}^2)$ and $R > 0$, the **spherical partial sum** is

$$
S_R^{\text{sph}} f(x) \;=\; \sum_{k \in \mathbb{Z}^2,\; |k| \le R}\; \widehat f(k)\, e^{2\pi i\, k \cdot x},
$$

where the sum is over lattice points $k = (k_1, k_2) \in \mathbb{Z}^2$ inside the closed disc of radius $R$ in Euclidean norm.

**Open question (2D Carleson, spherical).** Does $S_R^{\text{sph}} f(x) \to f(x)$ for almost every $x \in \mathbb{T}^2$, for every $f \in L^2(\mathbb{T}^2)$?

### Formal Statement

Let `T2 := Fin 2 → AddCircle (1 : ℝ)` (or any equivalent encoding of the 2-torus). For
`f : T2 → ℂ` and `k : Fin 2 → ℤ` define the Fourier coefficient
`fourierCoeff f k := ∫ x, f x * Complex.exp (-2 * π * I * (k.1 * x.1 + k.2 * x.2)) ∂μ`
(haar measure on `T2`). The spherical partial sum is
```lean
noncomputable def sphPartialSum (f : T2 → ℂ) (R : ℝ) (x : T2) : ℂ :=
  ∑ k in latticeDisc R, fourierCoeff f k * Complex.exp (2 * π * I * (k.1 * x.1 + k.2 * x.2))
```
where `latticeDisc R : Finset (Fin 2 → ℤ)` enumerates integer lattice points with `k.1^2 + k.2^2 ≤ R^2`.

The conjecture, axiomatized:
```lean
axiom carleson_2d_sph : ∀ f : T2 → ℂ, MemLp f 2 μ →
  ∀ᵐ x ∂μ, Tendsto (fun R : ℝ => sphPartialSum f R x) atTop (𝓝 (f x))
```

The formal goal of this entry is **not** to prove the conjecture (open in mathematics), but to (i) state it precisely, (ii) formalize the partial results known unconditionally, and (iii) populate the surrounding lemma library so the conjecture statement is correctly grounded.

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - harmonic-analysis
  - fourier-series
  - convergence
  - multi-dimensional
  - bochner-riesz
  - carleson-conjecture
  - open-problem
```

**Significance**: 6/10 — Among the top open problems in modern harmonic analysis; connects to the Bochner-Riesz, restriction, and Kakeya conjectures. The 1D analogue (Carleson 1966, Hunt 1968) is one of the deepest theorems in 20th-century analysis.

**Tractability**: 5/10 — The conjecture itself is open. But the surrounding library is tractable: Plancherel/Parseval for $\mathbb{T}^n$ (L² convergence in norm), Bochner-Riesz convergence above the critical exponent, and Fefferman's 1971 disproof for rectangular sums in $L^1$ are all in reach of a careful Mathlib build.

## Why This Matters

1. **Gallery scope**: The 1D parent (`FourierSeries.lean`, `FourierSeriesOQ01.lean`, `FourierSeriesOQ02.lean`) is rich; the 2D / $n$-D side is currently a 103-line stub with placeholder definitions (`fourierCoeff := 0`). A real $n$-torus formalization is the next natural extension.

2. **Bochner-Riesz connection**: The spherical partial-sum problem is the limit case $\delta = 0$ of Bochner-Riesz means
   $$ S_R^{\delta} f(x) = \sum_{|k| \le R} \left(1 - |k|^2/R^2\right)^\delta \widehat f(k)\, e^{2\pi i k \cdot x}. $$
   For $\delta > (n-1)/2$ ($\delta > 1/2$ in $n=2$), $L^2$ a.e. convergence is classical. The conjecture asks how far this critical exponent can be lowered. The endpoint $\delta = 0$ (no smoothing) is the spherical conjecture.

3. **Asymmetry with rectangular sums**: Fefferman's 1971 ball multiplier theorem implies $L^p$ unboundedness of $S_R^{\text{sph}}$ for $p \ne 2$ in $n \ge 2$. So the 2D conjecture is genuinely $L^2$-specific — strikingly different from 1D where Carleson works in $L^p$ for $1 < p < \infty$.

4. **Companion to `FourierSeriesOQ04.lean`**: That file currently asserts the open status in a docstring (line 95: "The n=2 pointwise convergence for L² is one of the major open problems in harmonic analysis. Carleson's theorem (1966) only covers n=1."). This child fleshes that claim into a formal `axiom` + a body of partial results.

## Theoretical Context

### Known unconditional results

- **L² norm convergence** (any summation method, all $n$): $\|S_R^{\text{sph}} f - f\|_{L^2} \to 0$ for $f \in L^2(\mathbb{T}^n)$. Direct from Plancherel: $\|S_R f - f\|_{L^2}^2 = \sum_{|k| > R} |\widehat f(k)|^2 \to 0$.
- **Bochner-Riesz, $\delta > (n-1)/2$**: $S_R^\delta f \to f$ a.e. for $f \in L^p(\mathbb{T}^n)$, $1 \le p \le \infty$ (classical, Stein 1958).
- **1D Carleson** (`n=1`): $S_R f \to f$ a.e. for $f \in L^p(\mathbb{T})$, $1 < p < \infty$. Hunt (1968) extended Carleson (1966) from $L^2$ to $L^p$.
- **Lipschitz / smooth functions in any $n$**: Spherical partial sums converge uniformly for $C^1$ data via Riemann-Lebesgue + decay of $\widehat f$.

### Known negative results

- **Fefferman 1971 (rectangular)**: The rectangular partial sums of an $L^1(\mathbb{T}^2)$ function may diverge a.e. — the multi-dimensional analogue of Kolmogorov's 1923 1D counterexample.
- **Fefferman 1971 (ball multiplier)**: The characteristic function $\chi_{B(0,1)}$ is **not** an $L^p(\mathbb{R}^n)$ Fourier multiplier for $p \ne 2$, $n \ge 2$. This shows the spherical-summation operator does not extend boundedly to $L^p$.
- **Bochner-Riesz, $\delta < (n-1)(1/p - 1/2)$**: For $p < 2n/(n+1)$ or $p > 2n/(n-1)$ in $n \ge 2$, $S_R^\delta$ is unbounded on $L^p$ (Herz, Fefferman).

### Open status

The spherical $L^2$ a.e. conjecture in $n=2$ has been open since at least Stein's 1971 ICM address. Tao's "Some recent progress on the restriction conjecture" (2002) lists it as a flagship open problem of harmonic analysis. As of 2024, no improvement on Fefferman's barrier is known in either direction.

## Path Forward (sketch — see `state.md` for the active iteration)

S1 (this iteration): OBSERVE — document the problem, survey unconditional results, map the Mathlib API.

S2 onward: ACT on tractable partial deliverables:
- (S2a) Restate `FourierSeriesOQ04`'s definitions over a real $n$-torus model (replacing the `:= 0` stubs with the actual integral / sum); prove Plancherel in $n$ dimensions.
- (S2b) Formalize the conjecture as `axiom carleson_2d_sph : …` in `Proofs/FourierSeriesOQ04OQ01.lean`; state Bochner-Riesz $\delta > 1/2$ as an unconditional companion theorem (axiomatized if Mathlib lacks the integral operator).
- (S2c) Formalize Fefferman's ball-multiplier statement as `axiom fefferman_1971_ball : ¬ IsLp_multiplier (charFn (ball 0 1)) p (Fin 2 → ℝ)` for $p \ne 2$.

The first iteration's deliverable is **doc-only**: no Lean changes. The Lean stub is the parent's responsibility; this child's S1 lays the math substrate.
