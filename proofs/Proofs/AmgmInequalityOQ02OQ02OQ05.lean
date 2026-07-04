/-
  Newton's inequality via real-rootedness and the quadratic discriminant.

  Problem: amgm-inequality-oq-02-oq-02-oq-05
  Title:   Newton's Inequality via Real-Rooted Polynomials and Rolle's Theorem

  The parent entry `amgm-inequality-oq-02-oq-02` proves Newton's log-concavity
  step `p_k^2 ≥ p_{k-1} p_{k+1}` by a direct inductive/algebraic argument, and
  crucially assumes the inputs are NONNEGATIVE (`0 ≤ x i`).  The sibling
  `amgm-inequality-oq-02-oq-03-oq-03-oq-01` gives the first Newton inequality
  (`k = 1`) via a Cauchy–Schwarz / sum-of-squares "discriminant" engine.

  This file develops the *classical calculus route* the entry asks for, which is
  genuinely different from both and NOT previously present in the amgm family:
  Newton's inequality is the statement that a certain quadratic in three
  consecutive coefficients, obtained by repeatedly differentiating the
  real-rooted splitting polynomial `∏ (X - x_i)`, is itself real-rooted, hence
  has a NONNEGATIVE DISCRIMINANT.

  What is proved here (0 sorries, 0 axioms — foundational axioms only):

  * `discrim_nonneg_of_root`
        the reusable atom: a real quadratic `a x² + b x + c` that has a real
        root has `0 ≤ discrim a b c`.  This is "real-rooted quadratic ⇒
        log-concave coefficients", the exact per-derivative building block of
        the whole Rolle program.
  * `monic_quadratic_discrim_nonneg` / `discrim_nonneg_of_roots_nonempty`
        the same statement phrased through Mathlib's `Polynomial` API — a monic
        quadratic `X² + b X + c` with a real root (equivalently, whose `roots`
        multiset is nonempty) has nonnegative discriminant.
  * `realRooted_quadratic_coeff_ineq`  :  `4 c ≤ b²`.
  * `newton_two_vars`  :  `x y ≤ ((x + y)/2)²` for ALL real `x, y` — Newton's
        inequality `p_1² ≥ p_0 p_2` at `n = 2`, derived by taking the
        discriminant of the real-rooted polynomial `(X - x)(X - y)`.  Note there
        is NO sign hypothesis: the roots need only be real, which is exactly the
        advantage of the real-rootedness route the entry highlights (the parent's
        inductive proof needs `0 ≤ x i`).

  The general case (`n ≥ 3`) needs the crux lemma "differentiation preserves
  full real-rootedness (counting multiplicity)" — Rolle's theorem iterated on
  `∏ (X - x_i)` — which is the multi-week formalization risk flagged in
  `problem.md`.  It is honestly retained as open (documented in knowledge.md) and is
  deliberately NOT stubbed out in this file, which is instead a complete,
  self-contained, fully machine-checked quadratic/base atom of that program.
-/
import Mathlib

namespace NewtonRealRooted

open Polynomial

/-!  ## The discriminant atom: a real root forces a nonnegative discriminant  -/

/-- **Real-rooted quadratic ⇒ nonnegative discriminant.**
If the quadratic `a x² + b x + c` has a real root `x`, then its discriminant
`b² - 4ac` is nonnegative.  This is the single per-derivative step of the
classical Newton/Rolle argument: after differentiating a real-rooted polynomial
down to degree two, real-rootedness of the reduced quadratic *is* Newton's
inequality for the three surviving coefficients. -/
theorem discrim_nonneg_of_root (a b c x : ℝ) (h : a * (x * x) + b * x + c = 0) :
    0 ≤ discrim a b c := by
  rw [discrim_eq_sq_of_quadratic_eq_zero h]
  exact sq_nonneg _

/-!  ## Phrased through the `Polynomial` API (genuine real-rootedness)  -/

/-- A monic real quadratic `X² + b X + c` with a real root has nonnegative
discriminant `discrim 1 b c`.  Same content as `discrim_nonneg_of_root`, stated
via `Polynomial.IsRoot` so it plugs directly into the splitting-polynomial
picture. -/
theorem monic_quadratic_discrim_nonneg (b c r : ℝ)
    (hr : (X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r) :
    0 ≤ discrim 1 b c := by
  have hroot : r ^ 2 + b * r + c = 0 := by
    simpa [IsRoot, eval_add, eval_mul, eval_pow, eval_X, eval_C] using hr
  exact discrim_nonneg_of_root 1 b c r (by linear_combination hroot)

/-- If the monic real quadratic `X² + b X + c` splits over `ℝ` far enough to have
a nonempty `roots` multiset (i.e. it is real-rooted), its discriminant is
nonnegative.  This is the `Polynomial.roots`-level phrasing of real-rootedness. -/
theorem discrim_nonneg_of_roots_nonempty (b c : ℝ)
    (h : (X ^ 2 + C b * X + C c : ℝ[X]).roots ≠ 0) :
    0 ≤ discrim 1 b c := by
  obtain ⟨r, hr⟩ := Multiset.exists_mem_of_ne_zero h
  exact monic_quadratic_discrim_nonneg b c r (mem_roots'.1 hr).2

/-- The discriminant inequality rewritten as the coefficient inequality
`4c ≤ b²` (log-concavity of the coefficient triple `(1, b, c)`). -/
theorem realRooted_quadratic_coeff_ineq (b c r : ℝ)
    (hr : (X ^ 2 + C b * X + C c : ℝ[X]).IsRoot r) :
    4 * c ≤ b ^ 2 := by
  have h := monic_quadratic_discrim_nonneg b c r hr
  rw [discrim] at h
  linarith

/-!  ## The splitting polynomial for two roots, and Newton at `n = 2`  -/

/-- Vieta for two roots: `(X - x)(X - y) = X² - (x+y) X + x y`. -/
theorem prod_two_linear_eq (x y : ℝ) :
    ((X - C x) * (X - C y) : ℝ[X]) = X ^ 2 + C (-(x + y)) * X + C (x * y) := by
  rw [C_neg, C_add, C_mul]
  ring

/-- Each root of `(X - x)(X - y)` is, well, a root: `x` is a real root. -/
theorem root_of_prod_two_linear (x y : ℝ) :
    ((X - C x) * (X - C y) : ℝ[X]).IsRoot x := by
  simp [IsRoot, eval_mul, eval_sub, eval_X, eval_C]

/-- **Newton's inequality at `n = 2`, via real-rootedness.**
For every pair of real numbers `x, y` (no sign restriction),
`x y ≤ ((x + y)/2)²`, i.e. `p_1² ≥ p_0 p_2` for the normalized elementary
symmetric means of `x, y`.  Proof: the polynomial `(X - x)(X - y)` is
real-rooted, so the discriminant of `X² - (x+y) X + x y` is `≥ 0`, which is
exactly `(x + y)² ≥ 4 x y`. -/
theorem newton_two_vars (x y : ℝ) : x * y ≤ ((x + y) / 2) ^ 2 := by
  have hroot : (X ^ 2 + C (-(x + y)) * X + C (x * y) : ℝ[X]).IsRoot x := by
    rw [← prod_two_linear_eq]; exact root_of_prod_two_linear x y
  have h := realRooted_quadratic_coeff_ineq (-(x + y)) (x * y) x hroot
  nlinarith [h]

/-- The `n = 2` Newton inequality in normalized (`p`) form, emphasizing the
`p_1² ≥ p_0 · p_2` shape with `p_0 = 1`, `p_1 = e_1/2 = (x+y)/2`, `p_2 = e_2 = xy`.
Holds for signed inputs. -/
theorem newton_two_vars_normalized (x y : ℝ) :
    (1 : ℝ) * (x * y) ≤ ((x + y) / 2) ^ 2 := by
  simpa using newton_two_vars x y

/-!  ## Newton at `n = 3`, via the real-rooted derivative quadratics

For three real roots `x, y, z` the splitting cubic is
`(X - x)(X - y)(X - z) = X³ - e₁ X² + e₂ X - e₃`, with
`e₁ = x+y+z`, `e₂ = xy+yz+zx`, `e₃ = xyz`.  The two Newton inequalities are the
nonnegative discriminants of the two degree-two polynomials Rolle produces:

* differentiate once:  `P' = 3X² - 2e₁X + e₂`  (real-rooted ⇒ `4e₁² - 12e₂ ≥ 0`),
  giving the first step `e₁² ≥ 3e₂`;
* pass to the reciprocal cubic and differentiate:
  `-3e₃X² + 2e₂X - e₁`  (real-rooted ⇒ `4e₂² - 12e₁e₃ ≥ 0`), giving the second
  step `e₂² ≥ 3e₁e₃`.

Each derivative quadratic's discriminant is established here *directly* as a sum
of squares — which **is** the real-rootedness of that quadratic — so the `n = 3`
case needs neither the general Rolle-iteration lemma (the multi-week crux flagged
in `problem.md`) nor any sign hypothesis.  The Rolle picture is the motivation;
the SOS certificate is the proof. -/

/-- **Newton's first inequality at `n = 3`** (`p₁² ≥ p₀ p₂`), for arbitrary real
`x, y, z`: in elementary-symmetric form `e₁² ≥ 3 e₂`, i.e.
`3(xy+yz+zx) ≤ (x+y+z)²`.  This is the nonnegativity of the discriminant of the
once-differentiated splitting cubic `P' = 3X² - 2e₁X + e₂`; the SOS certificate
is `½[(x−y)² + (y−z)² + (z−x)²] ≥ 0`.  No sign hypothesis. -/
theorem newton_three_first (x y z : ℝ) :
    3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

/-- The once-differentiated splitting cubic `P' = 3X² - 2e₁X + e₂` has
nonnegative discriminant — the discriminant phrasing of `newton_three_first`, and
the `n = 3` instance of "a derivative of a real-rooted polynomial is real-rooted
(discriminant `≥ 0`)". -/
theorem discrim_deriv_cubic_first (x y z : ℝ) :
    0 ≤ discrim 3 (-2 * (x + y + z)) (x * y + y * z + z * x) := by
  rw [discrim]; nlinarith [newton_three_first x y z]

/-- **Newton's second inequality at `n = 3`** (`p₂² ≥ p₁ p₃`), for arbitrary real
`x, y, z`: in elementary-symmetric form `e₂² ≥ 3 e₁ e₃`, i.e.
`3(x+y+z)·xyz ≤ (xy+yz+zx)²`.  This is the nonnegativity of the discriminant of
the differentiated *reciprocal* cubic `-3e₃X² + 2e₂X - e₁`; the SOS certificate is
`½[(xy−yz)² + (yz−zx)² + (zx−xy)²] ≥ 0`.  Holds for all signed reals. -/
theorem newton_three_second (x y z : ℝ) :
    3 * (x + y + z) * (x * y * z) ≤ (x * y + y * z + z * x) ^ 2 := by
  nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x),
    sq_nonneg (z * x - x * y)]

/-- The differentiated reciprocal cubic `-3e₃X² + 2e₂X - e₁` has nonnegative
discriminant — the discriminant phrasing of `newton_three_second`. -/
theorem discrim_recip_deriv_cubic_second (x y z : ℝ) :
    0 ≤ discrim (-3 * (x * y * z)) (2 * (x * y + y * z + z * x)) (-(x + y + z)) := by
  rw [discrim]; nlinarith [newton_three_second x y z]

/-- **Newton at `n = 3` in normalized (`p`) form.**  With `p₀ = 1`,
`p₁ = e₁/3 = (x+y+z)/3`, `p₂ = e₂/3 = (xy+yz+zx)/3`, `p₃ = e₃ = xyz`, both
log-concavity steps `p₁² ≥ p₀·p₂` and `p₂² ≥ p₁·p₃` hold for all signed reals. -/
theorem newton_three_normalized (x y z : ℝ) :
    (1 : ℝ) * ((x * y + y * z + z * x) / 3) ≤ ((x + y + z) / 3) ^ 2 ∧
      ((x + y + z) / 3) * (x * y * z) ≤ ((x * y + y * z + z * x) / 3) ^ 2 := by
  refine ⟨?_, ?_⟩
  · nlinarith [newton_three_first x y z]
  · nlinarith [newton_three_second x y z]

end NewtonRealRooted
