# Knowledge: fourier-series-oq-04-oq-01

## S1 (researcher-6, 2026-05-12) — OBSERVE survey

### Concrete problem statement (with all qualifiers)

Let $\mathbb{T}^2 = (\mathbb{R}/\mathbb{Z})^2$ with normalised Haar measure $\mu$. For $f \in L^2(\mathbb{T}^2)$ and $k = (k_1, k_2) \in \mathbb{Z}^2$,

$$
\widehat f(k) = \int_{\mathbb{T}^2} f(x)\, e^{-2\pi i (k_1 x_1 + k_2 x_2)}\, d\mu(x).
$$

For $R > 0$, the **spherical partial sum** is

$$
S_R^{\text{sph}} f(x) = \sum_{|k| \le R} \widehat f(k)\, e^{2\pi i k \cdot x},
$$

with $|k| = \sqrt{k_1^2 + k_2^2}$ the Euclidean norm. The conjecture:

$$
\forall f \in L^2(\mathbb{T}^2) :\quad S_R^{\text{sph}} f(x) \xrightarrow{R \to \infty} f(x)\quad \text{for a.e. } x.
$$

**Status (as of 2024)**: Open. No improvement on Fefferman's 1971 ball-multiplier barrier; no conditional approach (Kakeya, restriction) has discharged the L² endpoint.

### Why the 1D case is solved but 2D is not

The 1D Carleson theorem (1966, $L^2$) and Hunt's $L^p$ extension (1968, $1 < p < \infty$) rely on:
1. **Time-frequency localisation**: a single rectangle in phase space corresponds to an interval in frequency. The dyadic decomposition of $\{|k| \le R\}$ on $\mathbb{T}^1$ is a sequence of disjoint *intervals*.
2. **Maximal operator boundedness**: $T^* f(x) = \sup_R |S_R f(x)|$ is bounded on $L^p$ via Carleson's tree decomposition.

In 2D, the level set $\{|k| \le R\} \subset \mathbb{Z}^2$ is a **disc** whose boundary is curved. A dyadic decomposition produces annular regions whose multipliers are *not* products of 1D multipliers (rectangles aligned with axes do not tile a disc efficiently). Fefferman 1971's ball multiplier theorem shows that for $p \ne 2$, the operator does **not** extend; this rules out Hunt-style $L^p$-interpolation arguments.

The L²-specific subtlety: Plancherel gives norm convergence, but a.e. convergence requires a *weak-type maximal estimate*
$$
\mu(\{x : \sup_R |S_R^{\text{sph}} f(x)| > \lambda\}) \le C \|f\|_{L^2}^2 / \lambda^2.
$$
No such estimate is known.

### Bochner-Riesz means and the critical exponent

For $\delta \ge 0$, define
$$
S_R^\delta f(x) = \sum_{|k| \le R} \left(1 - |k|^2 / R^2\right)^\delta \widehat f(k)\, e^{2\pi i k \cdot x}.
$$
- $\delta = 0$: spherical partial sum (the conjecture).
- $\delta > (n-1)/2$ (i.e. $> 1/2$ in $n=2$): a.e. convergence in $L^p$ for $1 \le p \le \infty$. **Classical** (Stein 1958).
- $0 < \delta \le (n-1)/2$: Bochner-Riesz conjecture, also open. For $\delta = 0$ (the spherical case) the conjecture reduces to the 2D Carleson conjecture in $L^2$.

A modern statement of the **Bochner-Riesz conjecture in $\mathbb{R}^n$**: $S_R^\delta$ extends to a bounded operator $L^p \to L^p$ iff $\delta > \max(0, n(1/p - 1/2) - 1/2)$. The $L^2$-endpoint a.e. statement is the spherical Carleson conjecture.

### Mathlib API survey (Lean 4, current pinned revision via Mathlib `import Mathlib`)

**Available in Mathlib (1D, AddCircle)**:
- `Mathlib.Analysis.Fourier.AddCircle`:
  - `fourier (n : ℤ) : AddCircle T → ℂ` — the n-th character.
  - `fourierCoeff f n` — the n-th Fourier coefficient (integral against `haarAddCircle`).
  - `fourier_add`, `fourier_neg`, `fourier_zero` — character algebra.
  - `fourierBasis`, `fourierBasis_apply` — Hilbert basis of $L^2(\text{AddCircle } T)$.
  - `tsum_sq_fourierCoeff_eq_lp_norm_sq` — Parseval (1D).
- `Mathlib.Analysis.Fourier.FourierTransform`:
  - `Real.fourierIntegral` — Fourier transform on $\mathbb{R}$ (continuous version).
- `Mathlib.MeasureTheory.Function.LpSpace.Basic` — `MemLp`, `Lp p μ`, `eLpNorm`.
- `Mathlib.Analysis.InnerProductSpace.l2Space` — `lp 2` Hilbert structure.

**Verified absent (Mathlib gaps; checked by `grep -r` and `loogle`)**:
- No `MultiFourierCoeff` / `fourierCoeff` over `(Fin n → AddCircle T)`. The parent file `Proofs/FourierSeriesOQ04.lean` declares its own `def fourierCoeff … := 0` placeholder.
- No `BochnerRiesz`, `sphericalPartialSum`, `ballMultiplier` definitions.
- No multi-dimensional Plancherel / Parseval (as an explicit identity over $\mathbb{T}^n$).
- No `Fefferman_ball_multiplier` or related counterexample.

**Workable detour**: `Mathlib.Analysis.Fourier.PoissonSummation` covers Poisson summation in any $n$ via `EuclideanSpace`. The Schwartz-class L²-convergence claim for $n$-torus partial sums is *implicit* in Mathlib's general $L^2$ theory (orthonormal basis exists as a tensor product of 1D bases) but has not been spelled out as a named theorem.

### Insights

1. **The 2D Carleson conjecture is the "endpoint" of two flagship open problems** — Bochner-Riesz in $L^2$ AND the 1D Carleson theorem in higher dimensions. Either positive progress collapses one of these. No conditional result links it to Kakeya or restriction at the $L^2$ endpoint.
2. **L² norm convergence is trivial** by Plancherel; the difficulty is the a.e. claim. This asymmetry guides the formalisation: Plancherel is in reach; the maximal-operator estimate is not.
3. **Rectangular vs spherical asymmetry is genuinely $n$-dependent**: in 1D, rectangular = spherical. In $n \ge 2$, Fefferman (1971) showed *rectangular* $L^1$ may diverge a.e., yet *spherical* $L^2$ a.e. is open. Both facts can be stated separately in the gallery without conflict.
4. **The `axiom` formalisation is the honest path**: this is a Millennium-Prize-class open problem in harmonic analysis (not a Clay problem but a long-standing flagship). The status should be `axiomatized` with a clear `axiom carleson_2d_sph` and a body of unconditional companion theorems.
5. **Doc-only S1 is appropriate**: the parent `FourierSeriesOQ04.lean` is a 103-line stub with placeholder `:= 0` definitions. Until the parent's definitions are rigorised (S2 ACT-A), the child cannot prove anything substantive. Documenting the math first is the cleanest unblock.

### Mathlib gaps (cumulative, for future contribution)

1. `MultiFourierCoeff f k` over `(Fin n → AddCircle T) → ℂ` for `k : Fin n → ℤ` — natural API; would specialise to the existing 1D `fourierCoeff` when `n = 1`.
2. `Plancherel_ntorus : ‖f‖_{L^2(T^n)}² = ∑ k, ‖MultiFourierCoeff f k‖²` — direct from `lp 2` over `Fin n → ℤ` (countable index).
3. `BochnerRieszMultiplier (δ : ℝ) (R : ℝ) (k : Fin n → ℤ) : ℂ := max (1 - ‖k‖² / R²) 0 ^ δ` (with `:= 0` outside the disc).
4. `sphericalPartialSum f R := ∑ k ∈ ballLattice R, MultiFourierCoeff f k • exp_basis k` — concrete `Finset.sum` over a finite index set per $R$.

### Next Steps (priority order)

1. **S2a (ACT — high value, tractable)**: In a new file `Proofs/FourierSeriesOQ04OQ01.lean`, define
   - `MultiFourierCoeff` rigorously (real integral over `Fin n → AddCircle T`).
   - `sphericalPartialSum f R x` as an explicit `Finset.sum` over `latticeDisc R : Finset (Fin n → ℤ)`.
   - State `axiom carleson_2d_sph` and surround it with the *unconditional* L²-norm-convergence statement (provable from Plancherel via the `lp 2` Hilbert basis).
   - Add the gallery entry `src/data/proofs/fourier-series-oq-04-oq-01/meta.json` with status `axiomatized` and badge `axiom`.

2. **S2b (ACT — slower)**: Formalise Bochner-Riesz convergence for $\delta > (n-1)/2$ (Stein 1958). This is a real theorem to formalise (1958-era classical), not a placeholder. Likely 2-3 iterations.

3. **S3 (ACT — speculative)**: Fefferman 1971 ball-multiplier counterexample. The classical proof uses Besicovitch sets and a Kakeya-style construction — likely beyond a single Lean file without a major Mathlib detour. Postpone.

4. **(skip)** Attempting to prove the conjecture itself. This is genuine open mathematics; no PR should claim to close it.

### Risk Notes

- **Risk 1 (parent drift)**: `FourierSeriesOQ04.lean` currently has placeholder `:= 0` definitions. If S2 replaces them with real integrals, downstream gallery entries that import the parent may break. Mitigation: S2a should keep the new definitions in a fresh file (`FourierSeriesOQ04OQ01.lean`) rather than editing the parent.
- **Risk 2 (Bochner-Riesz scope)**: A faithful $\delta > 1/2$ a.e. convergence proof is 1958-era harmonic analysis — short in textbooks but each step in Lean expands considerably. Estimate 300-500 lines for S2b.
- **Risk 3 (ball multiplier)**: Fefferman's counterexample requires a Besicovitch / Kakeya set construction, which Mathlib lacks. Defer to a dedicated entry.
- **Risk 4 (gallery axiom integrity)**: Per CLAUDE.md "Axiom Integrity Policy", `status` MUST be `axiomatized` with `badge: axiom` for any entry with `axiom carleson_2d_sph`. Do not claim `verified` based on the unconditional partial results alone.
