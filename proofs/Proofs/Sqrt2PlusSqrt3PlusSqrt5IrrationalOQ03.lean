import Mathlib

open Polynomial Real IntermediateField

set_option maxHeartbeats 1600000

/-
# Minimal Polynomial of √2 + √3 + √5 over ℚ (degree-8 annihilator)

## Main Results

Let θ = √2 + √3 + √5. This file establishes the explicit monic integer polynomial

  m(X) = X⁸ - 40 X⁶ + 352 X⁴ - 960 X² + 576

as a degree-8 annihilator of θ:

- `key`           : the abstract algebraic identity — for any reals s,t,u with
                    s²=2, t²=3, u²=5, m(s+t+u) = 0.
- `theta_root`    : m(θ) = 0 as a plain real-number equation.
- `aeval_theta`   : `aeval θ m = 0` (Polynomial framing).
- `m_monic`       : m is monic of degree 8.
- `theta_isIntegral` : θ is integral over ℚ (witnessed by m).

m(X) is the product over the eight sign choices ε ∈ {±1}³ of
(X - ε₁√2 - ε₂√3 - ε₃√5); expanding cancels every radical and leaves integer
coefficients (-40, 352, -960, 576).

## Proof of the algebraic identity (key)

Write a = s+t+u, P = st+tu+us. The radicals are eliminated by a four-step tower
(each step is a pure polynomial consequence of s²=2, t²=3, u²=5, machine-checked
by `linear_combination` + `ring`):

  h1 : a²            = 10 + 2P                    (from s²+t²+u² = 10)
  h2 : P²            = 31 + 2·(stu)·a             (st·tu+tu·us+us·st = stu·a; s²t²+t²u²+u²s² = 31)
  h3 : (stu)²        = 30                         (2·3·5)
  hA : (a²-10)²      = 4P²                         (square h1)
  hB : (a²-10)²      = 124 + 8·(stu)·a            (hA, h2)
  hC : ((a²-10)²-124)² = 1920·a²                   (square hB, h3:  64·30 = 1920)

and finally m(a) = ((a²-10)²-124)² - 1920·a² = 0 is a `ring` identity in a.
The coefficient identity ((b-10)²-124)² = b⁴-40b³+352b²+960b+576 (b = a²)
together with the -1920b shift produces exactly (-40, 352, -960, 576).

## Status

- Goals (i) annihilation and (ii) integer/rational coefficients: COMPLETE here.
- Goal (iii) irreducibility (hence m = minpoly and [ℚ(θ):ℚ] = 8): OPEN — see the
  note at the end of the file. The annihilator already gives [ℚ(θ):ℚ] ≤ 8.

BUILD STATUS: written under a fleet-wide build outage (Docker containerd content
store corrupt; Aristotle 404). Every `ring`/`linear_combination` identity below
was verified symbolically with sympy (exact cofactors), but the file has NOT yet
been compiled by Lean. Do not register in Proofs.lean until `docker-build` is green.
-/

namespace Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ03

/-! ## Part I: The abstract algebraic identity -/

/-- The core radical-elimination identity. For any reals `s, t, u` with
    `s² = 2`, `t² = 3`, `u² = 5`, the degree-8 polynomial
    `m(X) = X⁸ - 40X⁶ + 352X⁴ - 960X² + 576` vanishes at `s + t + u`.

    Every step is a polynomial consequence of the three square relations,
    discharged by `linear_combination` (the cofactors were computed and verified
    with a Gröbner reduction). -/
theorem key (s t u : ℝ) (hs : s ^ 2 = 2) (ht : t ^ 2 = 3) (hu : u ^ 2 = 5) :
    (s + t + u) ^ 8 - 40 * (s + t + u) ^ 6 + 352 * (s + t + u) ^ 4
      - 960 * (s + t + u) ^ 2 + 576 = 0 := by
  -- a := s + t + u,  P := s*t + t*u + u*s  (written out explicitly below)
  -- Step 1:  a² = 10 + 2P
  have h1 : (s + t + u) ^ 2 = 10 + 2 * (s * t + t * u + u * s) := by
    linear_combination hs + ht + hu
  -- Step 2:  P² = 31 + 2·(s t u)·a
  have h2 : (s * t + t * u + u * s) ^ 2
      = 31 + 2 * (s * t * u) * (s + t + u) := by
    linear_combination (t ^ 2 + u ^ 2) * hs + (u ^ 2 + 2) * ht + 5 * hu
  -- Step 3:  (s t u)² = 30
  have h3 : (s * t * u) ^ 2 = 30 := by
    linear_combination (t ^ 2 * u ^ 2) * hs + (2 * u ^ 2) * ht + 6 * hu
  -- Step A:  (a² - 10)² = 4 P²   (squaring Step 1)
  have hA : ((s + t + u) ^ 2 - 10) ^ 2 = 4 * (s * t + t * u + u * s) ^ 2 := by
    linear_combination ((s + t + u) ^ 2 - 10 + 2 * (s * t + t * u + u * s)) * h1
  -- Step B:  (a² - 10)² = 124 + 8·(s t u)·a   (using Step A and Step 2)
  have hB : ((s + t + u) ^ 2 - 10) ^ 2
      = 124 + 8 * (s * t * u) * (s + t + u) := by
    linear_combination hA + 4 * h2
  -- Step C:  ((a² - 10)² - 124)² = 1920 a²   (squaring Step B and using Step 3)
  have hC : (((s + t + u) ^ 2 - 10) ^ 2 - 124) ^ 2 = 1920 * (s + t + u) ^ 2 := by
    linear_combination
      (((s + t + u) ^ 2 - 10) ^ 2 - 124 + 8 * (s * t * u) * (s + t + u)) * hB
        + 64 * (s + t + u) ^ 2 * h3
  -- Finish: m(a) = ((a²-10)²-124)² - 1920 a²  is a ring identity equal to 0.
  linear_combination hC

/-! ## Part II: Consequences for θ = √2 + √3 + √5 -/

/-- `m(θ) = 0` as a plain real-number equation, where θ = √2 + √3 + √5. -/
theorem theta_root :
    (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) ^ 8
      - 40 * (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) ^ 6
      + 352 * (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) ^ 4
      - 960 * (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) ^ 2 + 576 = 0 :=
  key (Real.sqrt 2) (Real.sqrt 3) (Real.sqrt 5)
    (Real.sq_sqrt (by norm_num)) (Real.sq_sqrt (by norm_num))
    (Real.sq_sqrt (by norm_num))

/-- The candidate minimal polynomial `m(X) = X⁸ - 40X⁶ + 352X⁴ - 960X² + 576 ∈ ℚ[X]`. -/
noncomputable def m : ℚ[X] := X ^ 8 - 40 * X ^ 6 + 352 * X ^ 4 - 960 * X ^ 2 + 576

/-- `aeval θ m = 0`: the Polynomial framing of `theta_root`. -/
theorem aeval_theta :
    Polynomial.aeval (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) m = 0 := by
  unfold m
  simp only [map_sub, map_add, map_pow, map_mul, map_one, aeval_X, map_ofNat,
             Polynomial.aeval_one]
  push_cast
  linear_combination theta_root

/-- `m` has degree 8: the leading `X^8` dominates the lower-degree tail. -/
theorem m_natDegree : m.natDegree = 8 := by
  unfold m; compute_degree!

/-- `m` is monic. -/
theorem m_monic : m.Monic := by
  unfold m; monicity!

/-- θ = √2 + √3 + √5 is integral over ℚ, witnessed by the monic polynomial `m`. -/
theorem theta_isIntegral : IsIntegral ℚ (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) :=
  ⟨m, m_monic, aeval_theta⟩

/-- The degree of `θ` over `ℚ` is at most 8: `m` is a degree-8 annihilator, so the
    minimal polynomial cannot have larger degree. -/
theorem theta_finrank_le :
    Module.finrank ℚ ℚ⟮Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5⟯ ≤ 8 := by
  rw [IntermediateField.adjoin.finrank theta_isIntegral]
  -- `minpoly.min` gives `degree (minpoly ℚ θ) ≤ degree m`; transfer to `natDegree`.
  calc (minpoly ℚ (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5)).natDegree
      ≤ m.natDegree :=
        natDegree_le_natDegree
          (minpoly.min ℚ (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5) m_monic aeval_theta)
    _ = 8 := m_natDegree

/-! ## Part III: Remaining open goal — irreducibility / degree 8

The remaining task is to show `m` is irreducible over ℚ, which upgrades the
bounds above to equalities: `minpoly ℚ θ = m` and `[ℚ(θ):ℚ] = 8`.

Two routes, both substantial:

1. **Brute ℤ[X] factor analysis** (the route used for the degree-4 sister
   `Sqrt2PlusSqrt3IrrationalOQ03`). For degree 8 this requires ruling out
   factorizations of type 1+7, 2+6, 3+5, 4+4 by coefficient matching — several
   hundred lines, and the 4+4 case in particular is involved.

2. **Field-tower route** (cleaner mathematically): show `ℚ(θ) = ℚ(√2,√3,√5)` and
   `[ℚ(√2,√3,√5):ℚ] = 8` via the multiquadratic tower
   `ℚ ⊂ ℚ(√2) ⊂ ℚ(√2,√3) ⊂ ℚ(√2,√3,√5)`, each step degree 2 (each new radical
   is not a square in the previous field). Then `[ℚ(θ):ℚ] = 8`, and since `m`
   is a monic degree-8 annihilator, `m = minpoly ℚ θ`, hence irreducible.

The annihilation identity (`key`/`theta_root`) — the explicitly stated goal (i)
of the problem, and the only part requiring genuine radical algebra — is complete.
-/

end Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ03
