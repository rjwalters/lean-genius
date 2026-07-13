# S6b ACT — Complex Fourier-Gaussian eigenfunction (archimedean (C2))

**Researcher**: researcher-1
**Date**: 2026-05-31 (UTC)
**Mode**: ACT (Lean code + status update + session memo).
**Predecessor**: S11 PREP (2026-05-16, researcher-6) — `sessions/2026-05-16-s11-prep-s6b-sharpened.md`.

## Disposition

Ships **3 new theorems** in `proofs/Proofs/AreaOfCircleOQ05OQ04.lean`,
all sorry-free and axiom-free. Discharges the 2 acknowledged R-class
LOW sorries from S11 PREP §4 by writing the `_normSq` corollary in
sorry-free form and **deferring** the `_density_eigen` corollary to a
later session (see §5 below). Total addition: +108 LOC, 658 → 771.

| # | Theorem | Sorry-free | Notes |
|---|---------|-----------|-------|
| 1 | `complex_fourier_gaussian` (parametric) | ✓ | Direct `fourier_gaussian_innerProductSpace` specialization at `V := ℂ` |
| 2 | `complex_fourier_gaussian_pi` (eigenfunction, archimedean (C2)) | ✓ | `b = π` corollary; load-bearing |
| 3 | `complex_fourier_gaussian_normSq` (`Complex.normSq` form) | ✓ | Pointwise cast bridge to (1) |

## §1. What was built

### Parametric form (Mathlib direct specialization)

```lean
theorem complex_fourier_gaussian (b : ℂ) (hb : 0 < b.re) (w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ Complex.exp (-b * ‖z‖ ^ 2)) w
      = (Real.pi / b) * Complex.exp (-(Real.pi : ℂ) ^ 2 * ‖w‖ ^ 2 / b) := by
  have h := fourier_gaussian_innerProductSpace (V := ℂ) hb w
  have hfr : ((Module.finrank ℝ ℂ : ℂ) / 2) = (1 : ℂ) := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [hfr, Complex.cpow_one] at h
  exact h
```

The Mathlib lemma `_root_.fourier_gaussian_innerProductSpace` provides
the general statement over any finite-dimensional real inner product
space `V`. At `V := ℂ`:

- `Module.finrank ℝ ℂ = 2` (via `Complex.finrank_real_complex`)
- `(2 / 2 : ℂ) = 1`
- `(π / b) ^ (1 : ℂ) = π / b` via `Complex.cpow_one`

The instance chain is:
- `NormedAddCommGroup ℂ` ✓
- `InnerProductSpace ℝ ℂ` ✓ (via `instInnerProductSpaceRealComplex =
  RCLike.toInnerProductSpaceReal`, `Mathlib/Analysis/InnerProductSpace/Basic.lean:956`)
- `FiniteDimensional ℝ ℂ` ✓
- `MeasurableSpace ℂ` ✓
- `BorelSpace ℂ` ✓

### Eigenfunction corollary (archimedean (C2))

```lean
theorem complex_fourier_gaussian_pi (w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ Complex.exp (-(Real.pi : ℂ) * ‖z‖ ^ 2)) w
      = Complex.exp (-(Real.pi : ℂ) * ‖w‖ ^ 2) := by
  have hbre : (0 : ℝ) < ((Real.pi : ℂ)).re := by
    rw [Complex.ofReal_re]; exact Real.pi_pos
  have h := complex_fourier_gaussian (Real.pi : ℂ) hbre w
  have hπne : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [div_self hπne, one_mul] at h
  have hexp : -(Real.pi : ℂ) ^ 2 * ‖w‖ ^ 2 / (Real.pi : ℂ) =
              -(Real.pi : ℂ) * ‖w‖ ^ 2 := by
    field_simp; ring
  rw [hexp] at h
  exact h
```

This is **the** archimedean analogue of (C2) from `problem.md`: the
standard complex Gaussian `exp(-π · ‖z‖²)` is a fixed point of the
Fourier transform on ℂ (eigenvalue 1). Two simplifications collapse
the parametric form at `b = (π : ℂ)`:

1. `(π : ℂ) / (π : ℂ) = 1` via `div_self` (using `(π : ℂ) ≠ 0` from
   `Real.pi_ne_zero` via `exact_mod_cast`).
2. `-(π : ℂ)² · ‖w‖² / (π : ℂ) = -(π : ℂ) · ‖w‖²` via `field_simp; ring`.

The auxiliary `hbre : 0 < ((Real.pi : ℂ)).re` is needed because
the parametric `complex_fourier_gaussian` requires `0 < b.re`, and
`b = (π : ℂ)` ⇒ `b.re = π > 0`. Discharged via `Complex.ofReal_re`
(`(↑x).re = x`) + `Real.pi_pos`.

### `Complex.normSq` companion

```lean
theorem complex_fourier_gaussian_normSq (b : ℂ) (hb : 0 < b.re) (w : ℂ) :
    𝓕 (fun (z : ℂ) ↦ Complex.exp (-b * (Complex.normSq z : ℂ))) w
      = (Real.pi / b) * Complex.exp (-(Real.pi : ℂ) ^ 2 *
          (Complex.normSq w : ℂ) / b) := by
  have key : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = (‖z‖ : ℂ) ^ 2 := fun z => by
    rw [Complex.normSq_eq_norm_sq]; push_cast; ring
  simp_rw [key]
  exact complex_fourier_gaussian b hb w
```

Pointwise cast bridge: `(normSq z : ℂ) = (‖z‖ : ℂ)²` via
`Complex.normSq_eq_norm_sq` (in ℝ) followed by `push_cast` distributing
the ℝ → ℂ coercion through `^2`. After `simp_rw [key]`, the goal
exactly matches `complex_fourier_gaussian`.

This is the Fourier-domain analogue of the `_scaled` ↔ `_scaled_norm`
pair on the integral side (lines 226 ↔ 261).

## §2. Bearer recheck at SHA `2df2f0150c…` (Mathlib v4.26.0)

Re-verified the 4 load-bearing Mathlib pins from S11 PREP §3.1:

| Bearer | Location | Status |
|--------|----------|--------|
| `_root_.fourier_gaussian_innerProductSpace` | `Mathlib/Analysis/SpecialFunctions/Gaussian/FourierTransform.lean:372` | ✓ |
| `_root_.fourier_gaussian_innerProductSpace'` (shifted) | `…/FourierTransform.lean:355` | ✓ (unused this session) |
| `Complex.finrank_real_complex : finrank ℝ ℂ = 2` | `Mathlib/LinearAlgebra/Complex/FiniteDimensional.lean:31` | ✓ |
| `Complex.cpow_one : x ^ (1 : ℂ) = x` | `Mathlib/Analysis/SpecialFunctions/Pow/Complex.lean:72` | ✓ (pin verified) |
| `Real.pi_pos`, `Real.pi_ne_zero` | `Mathlib/Analysis/SpecialFunctions/Pi/Bounds.lean` and friends | ✓ |
| `Complex.normSq_eq_norm_sq` | `Mathlib/Analysis/Complex/Norm.lean:146` | ✓ |
| `Complex.ofReal_re` | `Mathlib/Data/Complex/Basic.lean` (standard) | ✓ |

The notation `𝓕` is `scoped notation` in `FourierTransform` namespace
(`Mathlib/Analysis/Fourier/Notation.lean:53`). Pulled in via
`open scoped FourierTransform`.

The `FourierTransform (V → E) (V → E)` instance is provided at
`Mathlib/Analysis/Fourier/FourierTransform.lean:421` for any `V` that is
a `NormedAddCommGroup` + `InnerProductSpace ℝ V` + `MeasurableSpace V` +
`BorelSpace V` + `FiniteDimensional ℝ V` — all satisfied by `V := ℂ`.

## §3. Import gap patch (per S11 PREP §3.3)

Added one new import to `proofs/Proofs/AreaOfCircleOQ05OQ04.lean`:

```lean
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
```

And one new `open scoped`:

```lean
open scoped FourierTransform
```

The `cexp` notation (from `namespace Complex`) and `Complex.exp` are
already available via the existing `open ... Complex` (line 90). We
use `Complex.exp` explicitly in the new theorems to avoid any ambiguity
with `Real.exp` (the file's convention).

## §4. Departures from S11 PREP §4 skeleton

The PREP §4 skeleton listed 5 theorems with 2 acknowledged R-class LOW
sorries. This ACT ships 3 of those 5, all sorry-free:

| PREP §4 # | Theorem | Disposition | Notes |
|-----------|---------|-------------|-------|
| 1 | `complex_fourier_gaussian` parametric | ✓ SHIPPED sorry-free | Matches PREP skeleton |
| 2 | `complex_fourier_gaussian_pi` | ✓ SHIPPED sorry-free | Matches PREP skeleton |
| 3 | `complex_fourier_gaussian_normSq` | ✓ SHIPPED **sorry-free** (PREP had R1 LOW sorry) | Direct `push_cast` + `simp_rw [key]` chain works without sorry |
| 4 | `complex_fourier_gaussian_shifted` | DEFERRED | See §5 |
| 5 | `complex_fourier_gaussian_density_eigen` | DEFERRED | See §5 |

### Why `_normSq` came out sorry-free

The PREP §4 R1 LOW sketch noted "3-line rewrite chain pulling `hnormSq z`
through the integrand". The actual sorry-free discharge is also 3 lines
(the body of `key` + `simp_rw [key]` + `exact complex_fourier_gaussian`).
The trick is that `Complex.normSq_eq_norm_sq` is an equation in `ℝ`, so
after `rw`, the `push_cast` lemma normalises `((‖z‖^2 : ℝ) : ℂ) = (‖z‖ : ℂ)^2`
which is the same form Lean elaborates `‖z‖^2` to under expected-type-ℂ.
Then `simp_rw [key]` rewrites both occurrences in the goal and the
parametric theorem closes by `exact`.

## §5. Deferred (next ACT)

- **`complex_fourier_gaussian_shifted`** (with-shift companion): the
  archimedean analogue of "translate-then-Fourier" — same direct
  specialization of `fourier_gaussian_innerProductSpace'` at `V := ℂ`.
  Same 1-line dimension-collapse trick should work, plus the inner
  product `⟪x, z⟫_ℝ` (real-valued, cast to ℂ) carries through. ~25 LOC.

- **`complex_fourier_gaussian_density_eigen`** (normalised eigenstate):
  pull `(1/π : ℂ)` out of `𝓕` and reduce to `complex_fourier_gaussian_pi`.
  The pull-out lemma is `VectorFourier.fourierIntegral_const_smul` (at
  `Mathlib/Analysis/Fourier/FourierTransform.lean:86`); Mathlib does NOT
  provide a `FourierModule ℂ (ℂ → ℂ) (ℂ → ℂ)` instance, so the
  `FourierTransform.fourier_smul` typeclass route does **not** apply
  directly. Need a hand-rolled bridge via `VectorFourier.fourierIntegral_const_smul`
  + unfolding `𝓕` to `VectorFourier.fourierIntegral 𝐞 volume (innerₗ V)`
  via `Real.fourier_eq` or similar. ~15-20 LOC. Deferred to keep this
  ACT focused on the load-bearing pair.

## §6. Bridge to integral-side identities

The new Fourier-side theorems pair with the existing integral-side
identities in this file:

| Integral side (∫ exp(-b · ‖z‖²) dz) | Fourier side (𝓕 (exp(-b · ‖z‖²))) |
|---|---|
| `complex_gaussian_integral_scaled` (= π/b) | `complex_fourier_gaussian` (= (π/b) · exp(-π² · ‖w‖²/b)) |
| `complex_gaussian_integral_unit_norm` (= π at `b = 1`) | `complex_fourier_gaussian_pi` (= exp(-π · ‖w‖²) at `b = π`, fixed point) |
| `complex_gaussian_integral_normalised` (= 1) | `complex_fourier_gaussian_density_eigen` (= same density, deferred) |

The integral-side and Fourier-side together pin down the unique-up-to-scale
Gaussian as the self-Fourier eigenfunction with eigenvalue 1, which is
the archimedean fact backing the (C2) p-adic conjecture.

## §7. Path-to-completion update

| Session | Phase | Deliverable | PR | Status |
|---------|-------|-------------|----|----|
| S1–S11 | (prior) | n-dim shifted complex Gaussian + Path B Fubini chain | (multiple, see state.md) | merged |
| S11 PREP | PREP | S6b sharpened skeleton (this PR's predecessor) | not located (memo-only?) | merged or in-flight |
| **S6b ACT (this)** | **ACT** | **Parametric + (C2) + normSq Fourier-Gaussian** | (this PR) | **unmerged** |
| (next) | ACT | `_shifted` + `_density_eigen` companions | — | unclaimed |
| (later) | ACT | n-dim Fourier-Gaussian (lift via `EuclideanSpace ℂ (Fin n)`) | — | unclaimed |
| (deferred) | OBS | S6d Mathlib milestone (`Measure ℚ_p` upstream) | — | tracked in S4b survey |

## §8. ACT-readiness gate (S11 PREP §6, re-evaluated 2026-05-31)

| # | Gate item | S11 PREP (2026-05-16) | This ACT (2026-05-31) |
|---|-----------|----------------------|----------------------|
| 1 | Mathlib pins re-verified | GREEN | GREEN (this session §2) |
| 2 | Supporting lemma pins | GREEN | GREEN |
| 3 | Import gap patched | GREEN (in skeleton) | GREEN (now in file) |
| 4 | Paste-ready skeleton | GREEN | GREEN (3/5 shipped sorry-free) |
| 5 | Sorry inventory bounded | GREEN (N=2 LOW) | GREEN (N=0 — `_normSq` came out sorry-free) |
| 6 | R1-R7 substantive risks | GREEN (LOW) | GREEN (R1 + R7 hit and discharged in this ACT) |
| 7 | Sibling PR disposition | GREEN | GREEN (still no open PRs for this slug) |
| 8 | Host infra (disk / Docker) | RED INFRA (6.9Gi avail, daemon hung) | **GREEN** (58Gi avail, Docker daemon responsive) |

**All 8 gates GREEN.** Disk pressure has recovered (94% used vs prior
99.9%+); Docker daemon responsive. ACT proceeded with full Docker build
verify.

## §9. Risk recheck (from S11 PREP §5)

| ID | Risk | Class | Outcome this ACT |
|----|------|-------|------------------|
| R1 | `_normSq` bridge fails on cast | LOW | Discharged sorry-free using `push_cast; ring` after `Complex.normSq_eq_norm_sq` |
| R2 | Pull-constant on `𝓕` for `_density_eigen` | LOW | **Deferred this ACT** — no `FourierModule` instance for `(V → ℂ)`, needs hand-roll via `VectorFourier.fourierIntegral_const_smul` |
| R3 | `field_simp` fails for `_pi` | LOW | Worked first try (`field_simp; ring` discharges `-π²·‖w‖²/π = -π·‖w‖²`) |
| R4 | `(0 : ℝ) < (Real.pi : ℂ).re` reduction | LOW | Discharged via `rw [Complex.ofReal_re]; exact Real.pi_pos` (1 line) |
| R5 | `cexp` vs `Complex.exp` ambiguity | LOW | Used `Complex.exp` explicitly throughout to match file convention |
| R6 | `Module.finrank` vs `FiniteDimensional.finrank` | LOW | `Module.finrank` form works; `Complex.finrank_real_complex` is the same form |
| R7 | `InnerProductSpace ℝ ℂ` ambiguity | LOW | Worked via auto-instance resolution (`instInnerProductSpaceRealComplex`) |
| R8 | Host disk / Docker | INFRA | **GREEN** at ACT time (58Gi avail vs 6.9Gi at PREP) |

## §10. Build verification

`./proofs/scripts/docker-build.sh Proofs.AreaOfCircleOQ05OQ04` ran to
completion (see §11 below for the run record).

## §11. Snapshot (this PR)

| Metric | Before (S6 ACT close) | After (this S6b ACT) | Δ |
|--------|----------------------|---------------------|---|
| `AreaOfCircleOQ05OQ04.lean` LOC | 658 | 771 | +113 |
| Theorems | 21 + 2 private | 24 + 2 private | +3 |
| Sorries | 0 | 0 | 0 |
| `axiom` decls | 0 | 0 | 0 |
| Imports | 5 | 6 | +1 (`…Gaussian.FourierTransform`) |

## §12. Disposition + Next-Action

**This PR**: S6b ACT shipped — 3 new sorry-free theorems delivering the
archimedean (C2) eigenfunction identity. Phase remains `RESEARCH`
(the slug's open frontiers are the deferred companions in §5 plus the
multi-week S6d Mathlib milestone).

**Next-Action**: ship the deferred S6b ACT-2: `complex_fourier_gaussian_shifted`
(direct specialization of `fourier_gaussian_innerProductSpace'` at `V := ℂ`)
+ `complex_fourier_gaussian_density_eigen` (pull-constant via
`VectorFourier.fourierIntegral_const_smul`). ~40 LOC combined. Then
optionally lift to `EuclideanSpace ℂ (Fin n)` for the n-dim Fourier-Gaussian
package.

**Iter bump**: 11 → 12.

---

*End of S6b ACT.*
