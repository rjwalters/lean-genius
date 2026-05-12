# Research State: fourier-series-oq-04-oq-01

## Current State
**Phase**: OBSERVE
**Since**: 2026-05-12 (S1)
**Iteration**: 1

## Current Focus

S1 (researcher-6, 2026-05-12) — **OBSERVE** survey of the 2D Carleson
spherical-summation conjecture for $L^2(\mathbb{T}^2)$. Doc-only,
no Lean changes. Deliverables: this `state.md`, `problem.md` (formal
statement + classification), `knowledge.md` (Mathlib API map +
unconditional companion results + Bochner-Riesz context), and the
discovery JSON `src/data/research/problems/fourier-series-oq-04-oq-01.json`.

The parent file `Proofs/FourierSeriesOQ04.lean` (103 lines, 0 theorems,
3 placeholder `:= 0` definitions) declares the open-problem status in
its docstring (lines 95-96: "The n=2 pointwise convergence for L² is
one of the major open problems in harmonic analysis. Carleson's
theorem (1966) only covers n=1."). This child entry promotes that
docstring claim into a formal problem definition with a clearly
marked `axiom` and a body of unconditional partial results.

## Active Approach

**Axiomatize the open conjecture; formalize the partial results
that are provable unconditionally.**

The 2D spherical Carleson conjecture is open in mathematics (Stein
1971 ICM; Tao 2002 restriction-conjecture survey; no progress on
the L²-endpoint as of 2024). The honest formalisation is:

1. State the conjecture as a single `axiom carleson_2d_sph` with
   precise quantifiers over `f ∈ L^2(T^2)` and Lebesgue-a.e. `x`.
2. Surround it with unconditional results:
   - `L2_norm_convergence` — $\|S_R^{\text{sph}} f - f\|_{L^2} \to 0$
     from Plancherel (provable in Lean from the `lp 2` Hilbert
     basis of `(Fin 2 → AddCircle 1) → ℂ`).
   - `bochner_riesz_critical` — $S_R^\delta f \to f$ a.e. for
     $\delta > 1/2$ (classical, Stein 1958; multi-iteration target).
3. Gallery entry: `status = "axiomatized"`, `badge = "axiom"`.

This matches the gallery's standard treatment of open problems
(per CLAUDE.md Axiom Integrity Policy). Compare e.g. `riemann-hypothesis`,
`p-vs-np`: `axiomatized` with the conjecture as an `axiom`.

## Blockers

None mathematical for S1. S2 onward will need:
- A real-integral definition of `MultiFourierCoeff` on `Fin n → AddCircle T` (Mathlib gap; ~30 lines of careful setup).
- A real-`Finset`-based definition of `latticeDisc R : Finset (Fin n → ℤ)` (provable: integer lattice points in a closed disc are a finite set; need `Finset.filter` + bound on $|k_i|$ by $\lceil R \rceil$).

Practical: this worktree's `proofs/.lake` symlink points to itself,
so any Docker build would be a fresh ~25-minute clone. S1 is text-only
and unaffected. S2 will need to budget build time.

## Next Action

**S2a (any researcher) — ACT, doc-light scaffold**:

Create `proofs/Proofs/FourierSeriesOQ04OQ01.lean` (new file, ~150 lines) containing:

1. Header / imports:
   ```lean
   import Mathlib.Analysis.Fourier.AddCircle
   import Mathlib.MeasureTheory.Constructions.Pi
   import Mathlib.Tactic
   ```
2. Rigorous definitions (replace parent's `:= 0` placeholders):
   ```lean
   abbrev T2 : Type := Fin 2 → AddCircle (1 : ℝ)
   noncomputable def multiFourierCoeff (f : T2 → ℂ) (k : Fin 2 → ℤ) : ℂ := ...
   def latticeDisc (R : ℝ) : Finset (Fin 2 → ℤ) := ...   -- non-trivial; see knowledge.md
   noncomputable def sphPartialSum (f : T2 → ℂ) (R : ℝ) (x : T2) : ℂ :=
     ∑ k ∈ latticeDisc R, multiFourierCoeff f k * exp (2 * π * I * (k 0 * x 0 + k 1 * x 1))
   ```
3. The conjecture (axiomatized):
   ```lean
   /-- 2D Carleson conjecture for spherical Fourier series on the torus.
       Open in mathematics; stated as an axiom for gallery scope. -/
   axiom carleson_2d_sph (f : T2 → ℂ) (hf : MemLp f 2 μ) :
     ∀ᵐ x ∂μ, Tendsto (fun R : ℝ => sphPartialSum f R x) atTop (𝓝 (f x))
   ```
4. One unconditional companion theorem (proof skeleton, may have sorries):
   ```lean
   /-- L² norm convergence (Plancherel-direct, holds unconditionally). -/
   theorem sphPartialSum_L2_norm_converge (f : T2 → ℂ) (hf : MemLp f 2 μ) :
     Tendsto (fun R : ℝ => eLpNorm (sphPartialSum f R - f) 2 μ) atTop (𝓝 0) := by
     sorry  -- Plancherel + bigger-and-bigger lattice exhausts the index
   ```
5. Gallery entry: create `src/data/proofs/fourier-series-oq-04-oq-01/meta.json` with
   `status: "axiomatized"`, `badge: "axiom"`, `sorries: 1`, `axiomCount: 1`,
   `additionalFiles: ["Proofs/FourierSeriesOQ04.lean"]` (the parent).

S2a budget: ~150 Lean lines + meta.json. The `latticeDisc R` Finset
is the only non-routine definition (proof that integer pairs $(k_1, k_2)$
with $k_1^2 + k_2^2 \le R^2$ form a finite set — bound by `|k_i| ≤ ⌈R⌉`
and use `Finset.filter (· ∈ Icc (-⌈R⌉) ⌈R⌉ ×ˢ Icc (-⌈R⌉) ⌈R⌉)`).
A clean S2a may need a build cycle; tracking as "build pending" PR is
acceptable per gallery convention.

## Earlier Focus

(none — this is iteration 1)
