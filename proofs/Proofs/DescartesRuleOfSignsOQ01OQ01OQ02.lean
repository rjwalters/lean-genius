import Mathlib

/-
# Toward Budan–Fourier: the derivative sequence and its endpoint sign variations

*Open Question from `DescartesRuleOfSignsOQ01OQ01` (the complex-root-theory file):*
"The Budan–Fourier theorem (1807/1820) generalizes Descartes' rule to arbitrary
intervals [a,b]. Can a Lean formalization be built on top of the complex root
framework developed here?"

## What the Budan–Fourier theorem says

For a real polynomial `p` of degree `n`, the **Fourier sequence** is the list of
its iterated derivatives `(p, p', p'', …, p⁽ⁿ⁾)`. For a real number `x`, let `V(x)`
be the number of sign variations in `(p(x), p'(x), …, p⁽ⁿ⁾(x))`. The Budan–Fourier
theorem states: for `a < b`, the number of real roots of `p` in `(a, b]` (counted
with multiplicity) is at most `V(a) − V(b)`, and the defect `V(a) − V(b) − #roots`
is even.

Descartes' rule (and the parent file's parity result) is the special case obtained
by taking the interval over the whole real line: as `x → +∞` every derivative has
the sign of the leading coefficient, so `V(+∞) = 0`; as `x → −∞` the signs strictly
alternate, so `V(−∞) = n`. Hence `V(−∞) − V(+∞) = n`, which both bounds the real
root count by `n` and forces `#real roots ≡ n (mod 2)` — exactly the parity result
proved by conjugate pairing in the parent file.

## What this file proves (0 sorries, 0 axioms)

This file formalizes the **endpoint backbone** of Budan–Fourier:

1. `leadingCoeff_iterate_derivative` — for `k ≤ n`, the `k`-th derivative of `p`
   has degree `n − k` and leading coefficient `(n.descFactorial k) · leadingCoeff p`.
   In particular every derivative in the Fourier sequence has the **same sign**
   leading coefficient as `p`.
2. `topSign` / `botSign` — the formal sign of the `k`-th derivative at `+∞` and `−∞`
   (leading coefficient, resp. leading coefficient times `(−1)^{deg}`).
3. `signVarTop_eq_zero` — `V(+∞) = 0` (all leading coefficients share a sign).
4. `signVarBot_eq_natDegree` — `V(−∞) = n` (the `−∞` signs strictly alternate).
5. `budan_fourier_whole_line` — `V(−∞) − V(+∞) = n`: the whole-line Budan–Fourier
   identity, recovering the parent file's parity result.
6. `eval_mul_leadingCoeff_eventually_pos` — analytic anchoring: as `x → +∞` the value
   `p(x)` genuinely has the sign of `leadingCoeff p`, so `topSign` really is the sign
   of the Fourier sequence at `+∞`.

The remaining content of the full theorem — the root-counting inequality on a finite
interval `(a,b]`, which needs Rolle's theorem and a sign-change analysis at interior
roots — is documented at the end as the natural next step but is not proved here.

## Dependencies
- Mathlib: `Polynomial.coeff_iterate_derivative`, polynomial asymptotics at `atTop`.
-/

namespace DescartesRuleOfSignsOQ01OQ01OQ02

open Polynomial Filter

/-! ## Part 1: Leading coefficients of the iterated derivatives

The `k`-th derivative of a degree-`n` polynomial has degree `n − k` and leading
coefficient `(n.descFactorial k) · leadingCoeff p`. Since the descending factorial
is a positive integer for `k ≤ n`, every derivative in the Fourier sequence shares
the sign of `leadingCoeff p`. -/

/-- The coefficient of `derivative^[k] p` at index `n − k` (where `n = natDegree p`)
is the descending-factorial multiple of the leading coefficient of `p`. -/
theorem coeff_iterate_derivative_natDegree_sub (p : ℝ[X]) {k : ℕ}
    (hk : k ≤ p.natDegree) :
    (derivative^[k] p).coeff (p.natDegree - k) =
      (p.natDegree.descFactorial k : ℝ) * p.leadingCoeff := by
  rw [coeff_iterate_derivative, Nat.sub_add_cancel hk, nsmul_eq_mul]
  rfl

/-- The `k`-th derivative of a nonzero polynomial of degree `n` has degree exactly
`n − k`, for `k ≤ n`. -/
theorem natDegree_iterate_derivative_eq (p : ℝ[X]) (hp : p ≠ 0) {k : ℕ}
    (hk : k ≤ p.natDegree) :
    (derivative^[k] p).natDegree = p.natDegree - k := by
  refine le_antisymm (natDegree_iterate_derivative p k) ?_
  apply le_natDegree_of_ne_zero
  rw [coeff_iterate_derivative_natDegree_sub p hk]
  have h1 : (0 : ℝ) < (p.natDegree.descFactorial k : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hk
  exact mul_ne_zero (ne_of_gt h1) (leadingCoeff_ne_zero.mpr hp)

/-- The leading coefficient of `derivative^[k] p` is `(n.descFactorial k) · leadingCoeff p`. -/
theorem leadingCoeff_iterate_derivative (p : ℝ[X]) (hp : p ≠ 0) {k : ℕ}
    (hk : k ≤ p.natDegree) :
    (derivative^[k] p).leadingCoeff =
      (p.natDegree.descFactorial k : ℝ) * p.leadingCoeff := by
  unfold Polynomial.leadingCoeff
  rw [natDegree_iterate_derivative_eq p hp hk, coeff_iterate_derivative_natDegree_sub p hk]
  rfl

/-- Consecutive leading coefficients in the Fourier sequence have positive product:
they all share the sign of `leadingCoeff p`. -/
theorem leadingCoeff_mul_succ_pos (p : ℝ[X]) (hp : p ≠ 0) {k : ℕ}
    (hk : k < p.natDegree) :
    0 < (derivative^[k] p).leadingCoeff * (derivative^[(k + 1)] p).leadingCoeff := by
  rw [leadingCoeff_iterate_derivative p hp (le_of_lt hk),
      leadingCoeff_iterate_derivative p hp hk]
  have hd0 : (0 : ℝ) < (p.natDegree.descFactorial k : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr (le_of_lt hk)
  have hd1 : (0 : ℝ) < (p.natDegree.descFactorial (k + 1) : ℝ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr hk
  have hlc : (0 : ℝ) < p.leadingCoeff * p.leadingCoeff :=
    mul_self_pos.mpr (leadingCoeff_ne_zero.mpr hp)
  calc (0 : ℝ) < (p.natDegree.descFactorial k : ℝ) * (p.natDegree.descFactorial (k + 1) : ℝ)
                  * (p.leadingCoeff * p.leadingCoeff) :=
        mul_pos (mul_pos hd0 hd1) hlc
    _ = ((p.natDegree.descFactorial k : ℝ) * p.leadingCoeff)
          * ((p.natDegree.descFactorial (k + 1) : ℝ) * p.leadingCoeff) := by ring

/-! ## Part 2: The endpoint sign sequences and a sign-variation counter -/

/-- The sign of the value of `derivative^[k] p` at `+∞`: the leading coefficient. -/
noncomputable def topSign (p : ℝ[X]) (k : ℕ) : ℝ := (derivative^[k] p).leadingCoeff

/-- The sign of the value of `derivative^[k] p` at `−∞`: `leadingCoeff · (−1)^{deg}`,
since a polynomial of degree `d` and leading coefficient `c` behaves like `c·x^d`,
whose sign at `−∞` is `c·(−1)^d`. -/
noncomputable def botSign (p : ℝ[X]) (k : ℕ) : ℝ :=
  (derivative^[k] p).leadingCoeff * (-1) ^ (derivative^[k] p).natDegree

/-- Number of sign variations (strict sign changes) in `f 0, f 1, …, f m`. -/
noncomputable def sv (f : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | (m + 1) => sv f m + (if f m * f (m + 1) < 0 then 1 else 0)

/-- If no consecutive pair changes sign, the variation count is `0`. -/
theorem sv_eq_zero (f : ℕ → ℝ) (m : ℕ) (h : ∀ k < m, ¬ (f k * f (k + 1) < 0)) :
    sv f m = 0 := by
  induction m with
  | zero => rfl
  | succ d ih =>
    rw [sv, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
        if_neg (h d (Nat.lt_succ_self d))]

/-- If every consecutive pair changes sign, the variation count is `m`. -/
theorem sv_eq_self (f : ℕ → ℝ) (m : ℕ) (h : ∀ k < m, f k * f (k + 1) < 0) :
    sv f m = m := by
  induction m with
  | zero => rfl
  | succ d ih =>
    rw [sv, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
        if_pos (h d (Nat.lt_succ_self d))]

/-! ## Part 3: `V(+∞) = 0` and `V(−∞) = n` -/

/-- **`V(+∞) = 0`.** At `+∞` all derivatives in the Fourier sequence have the sign of
`leadingCoeff p`, so there are no sign variations. -/
theorem signVarTop_eq_zero (p : ℝ[X]) (hp : p ≠ 0) :
    sv (topSign p) p.natDegree = 0 := by
  apply sv_eq_zero
  intro k hk
  exact not_lt.mpr (le_of_lt (leadingCoeff_mul_succ_pos p hp hk))

/-- Consecutive `−∞` signs in the Fourier sequence have negative product: they
strictly alternate (degree drops by one at each derivative). -/
theorem botSign_mul_succ_neg (p : ℝ[X]) (hp : p ≠ 0) {k : ℕ} (hk : k < p.natDegree) :
    botSign p k * botSign p (k + 1) < 0 := by
  have hpos := leadingCoeff_mul_succ_pos p hp hk
  unfold botSign
  rw [natDegree_iterate_derivative_eq p hp (le_of_lt hk),
      natDegree_iterate_derivative_eq p hp hk]
  have hsum : ((p.natDegree - k) + (p.natDegree - (k + 1))) % 2 = 1 := by omega
  have hodd : Odd ((p.natDegree - k) + (p.natDegree - (k + 1))) := Nat.odd_iff.mpr hsum
  have hrw :
      ((derivative^[k] p).leadingCoeff * (-1 : ℝ) ^ (p.natDegree - k))
        * ((derivative^[(k + 1)] p).leadingCoeff * (-1 : ℝ) ^ (p.natDegree - (k + 1)))
      = ((derivative^[k] p).leadingCoeff * (derivative^[(k + 1)] p).leadingCoeff)
          * (-1 : ℝ) ^ ((p.natDegree - k) + (p.natDegree - (k + 1))) := by
    rw [pow_add]; ring
  rw [hrw, hodd.neg_one_pow]
  nlinarith [hpos]

/-- **`V(−∞) = n`.** At `−∞` the Fourier sequence has strictly alternating signs, so
the number of sign variations equals the degree. -/
theorem signVarBot_eq_natDegree (p : ℝ[X]) (hp : p ≠ 0) :
    sv (botSign p) p.natDegree = p.natDegree := by
  apply sv_eq_self
  intro k hk
  exact botSign_mul_succ_neg p hp hk

/-! ## Part 4: The whole-line Budan–Fourier identity -/

/-- **Whole-line Budan–Fourier.** `V(−∞) − V(+∞) = deg p`. Taking the Budan–Fourier
interval to be all of `ℝ`, the sign-variation drop equals the degree. This both bounds
the number of real roots by `deg p` and (since the defect is even) recovers the parent
file's parity statement that the real-root count has the same parity as the degree. -/
theorem budan_fourier_whole_line (p : ℝ[X]) (hp : p ≠ 0) :
    sv (botSign p) p.natDegree - sv (topSign p) p.natDegree = p.natDegree := by
  rw [signVarBot_eq_natDegree p hp, signVarTop_eq_zero p hp, Nat.sub_zero]

/-! ## Part 5: Analytic anchoring of the `+∞` sign

`topSign p k` is defined as a leading coefficient; the next lemma confirms it really
is the sign of the polynomial value at `+∞`: for any nonzero `q`, the product
`q(x) · leadingCoeff q` is eventually positive as `x → +∞`, i.e. `q(x)` eventually has
the sign of its leading coefficient. -/

theorem eval_mul_leadingCoeff_eventually_pos (q : ℝ[X]) (hq : q ≠ 0) :
    ∀ᶠ x in atTop, 0 < q.eval x * q.leadingCoeff := by
  rcases eq_or_lt_of_le (Nat.zero_le q.natDegree) with h0 | hpos
  · -- constant polynomial: q = C (coeff 0), value is the leading coefficient
    have hC : q = C (q.coeff 0) := eq_C_of_natDegree_le_zero (le_of_eq h0.symm)
    have hlc : q.leadingCoeff = q.coeff 0 := by
      rw [hC, leadingCoeff_C, coeff_C]; simp
    filter_upwards with x
    rw [hC, eval_C, ← hC, hlc]
    have hc0 : q.coeff 0 ≠ 0 := by
      rw [← hlc]; exact leadingCoeff_ne_zero.mpr hq
    exact mul_self_pos.mpr hc0
  · have hdeg : 0 < q.degree := natDegree_pos_iff_degree_pos.mp hpos
    rcases lt_or_ge 0 q.leadingCoeff with hlc | hlc
    · have htt := q.tendsto_atTop_of_leadingCoeff_nonneg hdeg (le_of_lt hlc)
      filter_upwards [htt.eventually_gt_atTop 0] with x hx
      exact mul_pos hx hlc
    · have hlc' : q.leadingCoeff < 0 := lt_of_le_of_ne hlc (leadingCoeff_ne_zero.mpr hq)
      have htb := q.tendsto_atBot_of_leadingCoeff_nonpos hdeg (le_of_lt hlc')
      filter_upwards [htb.eventually_lt_atBot 0] with x hx
      exact mul_pos_of_neg_of_neg hx hlc'

/-! ## Part 6: What remains for the full interval theorem

The whole-line case proved above is the Budan–Fourier theorem for the interval
`(−∞, +∞)`. The general finite-interval statement

  `#{ real roots of p in (a, b] (with multiplicity) } ≤ V(a) − V(b)`,  defect even,

requires two further ingredients beyond the endpoint sign analysis formalized here:

* **Interior sign changes.** As `x` increases past a simple root of one of the
  derivatives `p⁽ʲ⁾`, the sign-variation count `V(x)` can only stay the same or drop,
  and it drops by an odd amount precisely when `x` passes a root of `p` itself. This is
  a local sign-bookkeeping argument that needs continuity of `eval` (available in
  Mathlib) plus a Rolle-type interleaving of the roots of `p⁽ʲ⁾` and `p⁽ʲ⁺¹⁾`.

* **Counting with multiplicity.** Connecting the variation drop to `Polynomial.roots`
  (the multiset of roots) requires `Polynomial.rootMultiplicity` bookkeeping — exactly
  the open direction flagged in the parent file's third open question.

The leading-coefficient theory (`leadingCoeff_iterate_derivative`), the sign-variation
counter (`sv`), and the endpoint identifications (`topSign`/`botSign`) developed here
are the reusable backbone for that argument.
-/

end DescartesRuleOfSignsOQ01OQ01OQ02
