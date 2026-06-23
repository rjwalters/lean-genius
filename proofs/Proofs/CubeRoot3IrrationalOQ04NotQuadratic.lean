/-
Proof: ∛3 is NOT a quadratic irrational (the structural obstacle behind the
non-periodicity of its continued fraction).

Research: cube-root-3-irrational-oq-04, S20 (researcher-2, 2026-06-15).

CONTEXT (OQ #3 / Half (a)).
The simple continued fraction of `cbrt3` is non-periodic by Lagrange's theorem
(1770): a real irrational has an eventually-periodic simple CF iff it is a
*quadratic* irrational. `cbrt3` is a *cubic* irrational, so its CF is not
periodic and the prefix-by-prefix grind (`cbrt3_a0 … cbrt3_a11` in
`CubeRoot3IrrationalOQ04.lean`) is the only currently-formalizable route.

S19 (researcher-3) pinned the "not a quadratic irrational" half to the
`minpoly` / `X_pow_sub_C_irreducible_iff_of_prime` irreducibility route, which
requires bridging the `rpow` definition of `cbrt3` to `IsIntegral`/`minpoly`
machinery. THIS file takes the *elementary* route instead:

  `cbrt3` is not a quadratic irrational  ⟺  `1, cbrt3, cbrt3²` are linearly
  independent over `ℚ`,

and proves the latter from `cbrt3 ^ 3 = 3` and `Irrational cbrt3` ALONE — no
`minpoly`, no `NumberField`, no irreducibility API. The proof is a finite
elimination:

  • from `a·t² + b·t + c = 0` (t = cbrt3, t³ = 3), multiply by `t` and reduce:
        `b·t² + c·t + 3a = 0`;
  • eliminate `t²`:   `(b²−ac)·t + (bc−3a²) = 0`;
  • if `b²−ac ≠ 0`, then `t = −(bc−3a²)/(b²−ac) ∈ ℚ`, contradicting irrationality;
  • if `b²−ac = 0`, then also `bc−3a² = 0`, whence `b³ = 3a³`; if `a ≠ 0` then
    `(b/a)³ = 3` gives a *rational* cube root of 3, again contradicting
    irrationality (via the positive quadratic-factor identity, no cube
    injectivity lemma needed); otherwise `a = b = c = 0`.

Every algebraic identity above is verified exactly (sympy over ℚ) in
`research/problems/cube-root-3-irrational-oq-04/verify_cubic_lin_indep.py`
(CERTIFICATE PASSED).

BUILD STATUS: VERIFIED (researcher-9, 2026-06-18). Docker-built by name
(`docker-build.sh Proofs.CubeRoot3IrrationalOQ04NotQuadratic`, 7744 jobs,
"Build succeeded") and now registered in `Proofs.lean`, so it is part of the
gallery build closure. The name-level risks flagged at authoring time
(`pow_eq_zero_iff`, the `Irrational` membership unfolding) all resolved with no
edits — the file compiled exactly as written. The proof uses only robust,
cert-anchored tactics (`linear_combination` for the three elimination
identities, `nlinarith`/`push_cast`/`field_simp` for the bridges).

No axioms, no sorries.
-/

import Proofs.CubeRoot3Irrational
import Mathlib

namespace CubeRoot3IrrationalOQ04NotQuadratic

open CubeRoot3Irrational

/-- **Core lemma (abstract).** For any real `t` with `t ^ 3 = 3` that is
irrational, the family `1, t, t²` is linearly independent over `ℚ`:
`a·t² + b·t + c = 0` with `a, b, c ∈ ℚ` forces `a = b = c = 0`.

This is exactly the statement "`t` is not a root of any nonzero rational
polynomial of degree `≤ 2`", i.e. "`t` is not a quadratic irrational". -/
theorem cubic_lin_indep_of_irrational
    (t : ℝ) (ht : t ^ 3 = 3) (hirr : Irrational t)
    (a b c : ℚ)
    (h : (a : ℝ) * t ^ 2 + (b : ℝ) * t + (c : ℝ) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  -- `t > 0`, since `t³ = 3 > 0`.
  have htpos : 0 < t := by
    by_contra hle
    push_neg at hle
    nlinarith [ht, mul_nonneg (mul_nonneg (neg_nonneg.2 hle) (neg_nonneg.2 hle))
      (neg_nonneg.2 hle)]
  -- Step 1: multiply `h` by `t` and reduce `t³ = 3`.
  have h2 : (b : ℝ) * t ^ 2 + (c : ℝ) * t + 3 * (a : ℝ) = 0 := by
    linear_combination t * h - (a : ℝ) * ht
  -- Step 2: eliminate `t²`.
  have h3 : ((b : ℝ) ^ 2 - (a : ℝ) * (c : ℝ)) * t
      + ((b : ℝ) * (c : ℝ) - 3 * (a : ℝ) ^ 2) = 0 := by
    linear_combination (b : ℝ) * h - (a : ℝ) * h2
  by_cases hDz : b ^ 2 - a * c = 0
  · -- Case B: `b² − ac = 0` ⟹ `bc − 3a² = 0` ⟹ `b³ = 3a³`.
    have hDr : (b : ℝ) ^ 2 - (a : ℝ) * (c : ℝ) = 0 := by exact_mod_cast hDz
    have hEr : (b : ℝ) * (c : ℝ) - 3 * (a : ℝ) ^ 2 = 0 := by
      linear_combination h3 - t * hDr
    have hEz : b * c - 3 * a ^ 2 = 0 := by exact_mod_cast hEr
    have hcube : b ^ 3 = 3 * a ^ 3 := by linear_combination b * hDz + a * hEz
    by_cases haz : a = 0
    · -- `a = 0` ⟹ `b = 0` ⟹ `c = 0`.
      subst haz
      have h0 : b ^ 3 = 0 := by linear_combination hcube
      have hb : b = 0 := by
        exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h0
      subst hb
      have hc : (c : ℝ) = 0 := by simpa using h
      have hcz : c = 0 := by exact_mod_cast hc
      exact ⟨rfl, rfl, hcz⟩
    · -- `a ≠ 0` ⟹ `(b/a)³ = 3`: a rational cube root of 3, impossible.
      exfalso
      have ha : a ≠ 0 := haz
      have hr3 : (b / a) ^ 3 = 3 := by
        field_simp
        linear_combination hcube
      have hrr : ((b / a : ℚ) : ℝ) ^ 3 = 3 := by exact_mod_cast hr3
      -- `(↑(b/a))³ = t³`, so `(↑(b/a) − t)·((↑(b/a))² + ↑(b/a)·t + t²) = 0`.
      have hfac : (((b / a : ℚ) : ℝ) - t)
          * (((b / a : ℚ) : ℝ) ^ 2 + ((b / a : ℚ) : ℝ) * t + t ^ 2) = 0 := by
        linear_combination hrr - ht
      have hpos : 0 < ((b / a : ℚ) : ℝ) ^ 2 + ((b / a : ℚ) : ℝ) * t + t ^ 2 := by
        nlinarith [sq_nonneg (((b / a : ℚ) : ℝ) + t / 2), mul_pos htpos htpos]
      have hteq : t = ((b / a : ℚ) : ℝ) := by
        rcases mul_eq_zero.mp hfac with h' | h'
        · linarith [h']
        · exact absurd h' (ne_of_gt hpos)
      exact hirr ⟨b / a, hteq.symm⟩
  · -- Case A: `b² − ac ≠ 0` ⟹ `t` is rational, contradiction.
    exfalso
    have hDr : (b : ℝ) ^ 2 - (a : ℝ) * (c : ℝ) ≠ 0 := by
      intro hcon; exact hDz (by exact_mod_cast hcon)
    have key : ((b : ℝ) ^ 2 - (a : ℝ) * (c : ℝ)) * t
        = -((b : ℝ) * (c : ℝ) - 3 * (a : ℝ) ^ 2) := by linear_combination h3
    have hteq : t = (-((b : ℝ) * (c : ℝ) - 3 * (a : ℝ) ^ 2))
        / ((b : ℝ) ^ 2 - (a : ℝ) * (c : ℝ)) := by
      rw [eq_div_iff hDr]; linear_combination key
    have hrat : (-((b : ℝ) * (c : ℝ) - 3 * (a : ℝ) ^ 2))
        / ((b : ℝ) ^ 2 - (a : ℝ) * (c : ℝ))
        = ((-(b * c - 3 * a ^ 2) / (b ^ 2 - a * c) : ℚ) : ℝ) := by
      push_cast; ring
    rw [hrat] at hteq
    exact hirr ⟨-(b * c - 3 * a ^ 2) / (b ^ 2 - a * c), hteq.symm⟩

/-- **`cbrt3` is not a quadratic irrational.** Instantiation of the abstract
core at `t = cbrt3`, using `cbrt3_cubed` and `irrational_cbrt3` from the
parent file. -/
theorem cbrt3_not_quadratic (a b c : ℚ)
    (h : (a : ℝ) * cbrt3 ^ 2 + (b : ℝ) * cbrt3 + (c : ℝ) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 :=
  cubic_lin_indep_of_irrational cbrt3 cbrt3_cubed irrational_cbrt3 a b c h

/-- Contrapositive packaging: there is **no** nonzero rational quadratic
relation among `1, cbrt3, cbrt3²`. Equivalent to `cbrt3_not_quadratic`;
this is the form that most directly reads as "`cbrt3` satisfies no degree-`≤2`
rational polynomial", i.e. it is not a quadratic irrational. -/
theorem cbrt3_no_nontrivial_quadratic_relation
    (a b c : ℚ) (hnz : ¬ (a = 0 ∧ b = 0 ∧ c = 0)) :
    (a : ℝ) * cbrt3 ^ 2 + (b : ℝ) * cbrt3 + (c : ℝ) ≠ 0 :=
  fun h => hnz (cbrt3_not_quadratic a b c h)

end CubeRoot3IrrationalOQ04NotQuadratic
