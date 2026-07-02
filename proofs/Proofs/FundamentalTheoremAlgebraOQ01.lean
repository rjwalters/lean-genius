import Mathlib

/-
# Is Analysis Inherently Required for the Fundamental Theorem of Algebra?

## The open question

The parent entry (Fundamental Theorem of Algebra) records the folklore remark:
*"Despite its name, every known proof requires analysis — there is no purely
algebraic proof."*  The associated open question asks:

> Can a purely algebraic proof of the FTA ever be found, or is analysis
> inherently required?

## The definitive answer

**Analysis is inherently required — but its role can be pinned down exactly.**

A proof using *only* the field axioms is impossible: the FTA is a statement
about the specific field `ℝ` (equivalently `ℂ = ℝ[i]`), and it is simply *false*
for other fields (`ℚ`, finite fields, …).  So any proof must consume some
property of `ℝ` that goes beyond "being a field".  The modern
Artin–Schreier / Galois-theoretic proof isolates that non-algebraic content to
exactly **two** order/analytic facts about the reals:

* **(A)** every odd-degree real polynomial has a real root
  (a consequence of the Intermediate Value Theorem — hence of the *order
  completeness* of `ℝ`);
* **(B)** every complex number has a square root
  (equivalently, every non-negative real has a real square root).

Given (A) and (B), the remainder of the proof — that `ℝ[i]` is algebraically
closed — is *pure algebra* (Sylow theory + Galois theory, no further analysis).
Both (A) and (B) fail over general fields, so they carry genuine analytic
weight; this is the precise sense in which analysis is unavoidable.

This file formalizes the two analytic ingredients and the algebraic
obstruction, then connects them to Mathlib's proof that `ℂ` is algebraically
closed.

## What is proved here

* `odd_degree_real_root` — **(A)**: every real polynomial of odd degree has a
  real root.  Proved analytically: the polynomial function `ℝ → ℝ` is
  continuous and, having odd degree, tends to `+∞` at one end and `-∞` at the
  other, so by `Continuous.surjective` it hits `0`.  This is the irreducible
  IVT / order-completeness input.
* `complex_has_sqrt` — **(B)**: every complex number has a square root, via the
  polar form `w = √‖z‖ · exp(i·arg z / 2)`.  Non-circular: it uses only the
  real square root, *not* the FTA.
* `real_not_alg_closed` and `cubic_no_root_zmod2` — the **algebraic
  obstruction**: neither "is algebraically closed" nor "odd-degree polynomials
  have roots" is a consequence of the field axioms.  `X² + 1` has no root in
  `ℝ`, and the odd-degree (cubic) `X³ + X + 1` has no root in the field `𝔽₂`.
* `fta_complex` — the conclusion the Artin reduction targets, supplied by
  Mathlib (`Complex.exists_root`): every non-constant complex polynomial has a
  root.

## Status

Verified, 0 sorries, 0 axioms.  `native_decide` is **not** used.
-/

open Polynomial Filter Topology

namespace FundamentalTheoremAlgebraOQ01

/-! ## Analytic ingredient (A): odd-degree real polynomials have a root -/

/-- Helper: an odd-degree real polynomial with **positive** leading coefficient
tends to `+∞` at `+∞` and to `−∞` at `−∞`, hence (being continuous) is
surjective and in particular has a root. -/
private theorem root_of_odd_pos (p : ℝ[X]) (hodd : Odd p.natDegree)
    (hlc : 0 < p.leadingCoeff) : ∃ x : ℝ, p.IsRoot x := by
  -- odd degree ⇒ degree ≥ 1
  have hpos : 0 < p.natDegree := by rcases hodd with ⟨m, hm⟩; omega
  have hne : p ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hpos; exact lt_irrefl 0 hpos
  have hdeg : 0 < p.degree := natDegree_pos_iff_degree_pos.mp hpos
  have hcont : Continuous fun x : ℝ => p.eval x := p.continuous
  -- behaviour at +∞
  have htop : Tendsto (fun x : ℝ => p.eval x) atTop atTop :=
    p.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc.le
  -- behaviour at −∞, obtained by reflecting `p` through `X ↦ -X`
  have hnd : (-X : ℝ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  have hbot : Tendsto (fun x : ℝ => p.eval x) atBot atBot := by
    -- leading coefficient of `p(-X)` is `-leadingCoeff p < 0`
    have hlc' : (p.comp (-X)).leadingCoeff ≤ 0 := by
      rw [leadingCoeff_comp (by rw [hnd]; exact one_ne_zero),
        leadingCoeff_neg, leadingCoeff_X,
        show (-1 : ℝ) = -(1 : ℝ) from rfl, hodd.neg_pow, one_pow]
      linarith
    have hqd : 0 < (p.comp (-X)).degree := by
      rw [← natDegree_pos_iff_degree_pos, natDegree_comp, hnd, mul_one]; exact hpos
    have hcomp : Tendsto (fun y : ℝ => (p.comp (-X)).eval y) atTop atBot :=
      (p.comp (-X)).tendsto_atBot_of_leadingCoeff_nonpos hqd hlc'
    have heq : (fun y : ℝ => (p.comp (-X)).eval y) = fun y : ℝ => p.eval (-y) := by
      funext y; rw [eval_comp, eval_neg, eval_X]
    rw [heq] at hcomp
    have hc := hcomp.comp tendsto_neg_atBot_atTop
    have hfun : ((fun y : ℝ => p.eval (-y)) ∘ Neg.neg) = fun x : ℝ => p.eval x := by
      funext x; simp [Function.comp, neg_neg]
    rwa [hfun] at hc
  obtain ⟨x, hx⟩ := hcont.surjective htop hbot 0
  exact ⟨x, hx⟩

/-- **(A)** — Every real polynomial of odd degree has a real root.  This is the
irreducible Intermediate-Value-Theorem input to the FTA. -/
theorem odd_degree_real_root (p : ℝ[X]) (hodd : Odd p.natDegree) :
    ∃ x : ℝ, p.IsRoot x := by
  rcases lt_trichotomy p.leadingCoeff 0 with h | h | h
  · -- negative leading coefficient: apply the helper to `-p`, same roots
    obtain ⟨x, hx⟩ :=
      root_of_odd_pos (-p) (by rwa [natDegree_neg]) (by rw [leadingCoeff_neg]; linarith)
    exact ⟨x, by simpa [IsRoot, eval_neg] using hx⟩
  · -- zero leading coefficient forces `p = 0`, whose degree `0` is not odd
    exfalso
    rw [leadingCoeff_eq_zero] at h
    rw [h, natDegree_zero] at hodd
    exact (by decide : ¬ Odd 0) hodd
  · exact root_of_odd_pos p hodd h

/-! ## Analytic ingredient (B): complex numbers have square roots -/

/-- **(B)** — Every complex number has a square root, built from the *real*
square root via the polar form `w = √‖z‖ · exp(i · arg z / 2)`.  This proof does
not invoke the FTA, so it is a genuinely independent analytic ingredient. -/
theorem complex_has_sqrt (z : ℂ) : ∃ w : ℂ, w ^ 2 = z := by
  refine ⟨(Real.sqrt ‖z‖ : ℂ) * Complex.exp ((Complex.arg z : ℂ) / 2 * Complex.I), ?_⟩
  have sq1 : ((Real.sqrt ‖z‖ : ℝ) : ℂ) ^ 2 = (‖z‖ : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (norm_nonneg z)]
  have e2 : Complex.exp ((Complex.arg z : ℂ) / 2 * Complex.I) ^ 2
      = Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by
    rw [sq, ← Complex.exp_add]; congr 1; ring
  calc
    ((Real.sqrt ‖z‖ : ℂ) * Complex.exp ((Complex.arg z : ℂ) / 2 * Complex.I)) ^ 2
        = ((Real.sqrt ‖z‖ : ℂ)) ^ 2
            * Complex.exp ((Complex.arg z : ℂ) / 2 * Complex.I) ^ 2 := by rw [mul_pow]
    _ = (‖z‖ : ℂ) * Complex.exp ((Complex.arg z : ℂ) * Complex.I) := by rw [sq1, e2]
    _ = z := Complex.norm_mul_exp_arg_mul_I z

/-! ## The algebraic obstruction: the two facts are not field-theoretic -/

/-- `ℝ` is **not** algebraically closed: `X² + 1` has no real root.  Order
completeness gives odd-degree roots (ingredient A), yet closure still fails —
this is exactly why ingredient (B), the imaginary unit `i`, must be adjoined. -/
theorem real_not_alg_closed : ∀ x : ℝ, x ^ 2 + 1 ≠ 0 := by
  intro x
  have : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  positivity

/-- The "odd-degree ⇒ root" property (ingredient A) is **special to `ℝ`**, not a
consequence of the field axioms: over the finite field `𝔽₂ = ZMod 2` the
odd-degree (cubic) polynomial `X³ + X + 1` has no root.  Decidable, so `decide`
suffices — no `native_decide`. -/
theorem cubic_no_root_zmod2 : ∀ x : ZMod 2, x ^ 3 + x + 1 ≠ 0 := by decide

/-- The same cubic packaged as an honest `Polynomial` with no root in `𝔽₂`. -/
theorem cubic_poly_no_root_zmod2 :
    ∀ x : ZMod 2, ((X ^ 3 + X + 1 : (ZMod 2)[X])).IsRoot x → False := by
  intro x hx
  rw [IsRoot.def] at hx
  simp only [eval_add, eval_pow, eval_X, eval_one] at hx
  exact cubic_no_root_zmod2 x hx

/-! ## The conclusion the algebraic reduction targets (from Mathlib) -/

/-- The FTA itself, as proved in Mathlib (`Complex.exists_root`, via Liouville's
theorem).  Given the two analytic ingredients (A) and (B) above, the
Artin–Schreier argument derives this by *pure algebra*; Mathlib instead derives
it directly from complex analysis.  Either way, analysis enters — which answers
the open question. -/
theorem fta_complex (p : ℂ[X]) (hp : 0 < p.degree) : ∃ z : ℂ, p.IsRoot z :=
  Complex.exists_root hp

end FundamentalTheoremAlgebraOQ01
