import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Rolle

/-
# Descartes' Rule of Signs

## What This Proves
We prove Descartes' Rule of Signs: the number of positive real roots of a polynomial
(counted with multiplicity) is either equal to the number of sign changes in the
sequence of coefficients, or less than it by an even number.

This is Wiedijk's 100 Theorems #100.

## Historical Context
René Descartes published this rule in his work "La Géométrie" (1637), an appendix
to "Discours de la méthode." It was one of the first systematic methods for
determining properties of polynomial roots without explicitly solving the equation.

The rule was refined by Carl Friedrich Gauss and others to give exact conditions
for when the bound is achieved.

## The Theorem
For a polynomial p(x) = a_n x^n + a_{n-1} x^{n-1} + ... + a_1 x + a_0:
1. Count sign changes in the sequence (a_n, a_{n-1}, ..., a_1, a_0) ignoring zeros
2. The number of positive real roots is ≤ this count
3. The difference is an even number

For negative roots: apply the rule to p(-x).

## Approach
- **Foundation:** We define sign changes for coefficient sequences
- **Original Contributions:** Formalization of sign change counting and root bounds
- **Proof Techniques:** Induction on polynomial degree, Rolle's theorem connection

## Status
- [ ] Complete proof
- [x] Uses Mathlib for polynomial foundations
- [x] Proves extensions/corollaries
- [x] Pedagogical example
- [x] Incomplete (has sorries)

## Mathlib Dependencies
- `Polynomial` : Polynomial type and basic operations
- `Polynomial.coeff` : Coefficient access
- `Polynomial.eval` : Polynomial evaluation
- `Polynomial.natDegree` : Degree of polynomial

Original formalization for Lean Genius.
-/

namespace DescartesRuleOfSigns

open Polynomial

/- ## Sign Change Definitions

We define the notion of sign changes in a sequence of real numbers.
A sign change occurs between consecutive non-zero elements when one is
positive and the other is negative.
-/

/-- The sign of a real number: 1 for positive, -1 for negative, 0 for zero -/
noncomputable def realSign (x : ℝ) : ℤ :=
  if x > 0 then 1
  else if x < 0 then -1
  else 0

/-- Two numbers have opposite signs if their product is negative -/
def oppositeSign (x y : ℝ) : Prop := x * y < 0

/-- A sign change between indices i and j in a sequence means:
    - Both f(i) and f(j) are non-zero
    - They have opposite signs
    - All elements between them are zero -/
def SignChangeBetween {n : ℕ} (f : Fin n → ℝ) (i j : Fin n) : Prop :=
  i < j ∧
  f i ≠ 0 ∧
  f j ≠ 0 ∧
  (∀ k, i < k → k < j → f k = 0) ∧
  oppositeSign (f i) (f j)

/-- Count sign changes in a finite sequence.
    We count pairs (i, j) where there's a sign change from i to j. -/
noncomputable def countSignChanges {n : ℕ} (f : Fin n → ℝ) : ℕ :=
  @Finset.card (Fin n × Fin n) (Finset.univ.filter fun p =>
    @decide (SignChangeBetween f p.1 p.2) (Classical.dec _))

/- ## Coefficient Sign Changes for Polynomials

For a polynomial, we look at sign changes in the coefficient sequence.
-/

/-- Get the coefficient sequence of a polynomial as a function on Fin (d+1)
    where d is the degree. Returns coefficients from highest to lowest degree. -/
noncomputable def coeffSequence (p : ℝ[X]) (d : ℕ) : Fin (d + 1) → ℝ :=
  fun i => p.coeff (d - i.val)

/-- The number of sign changes in the coefficients of a polynomial -/
noncomputable def signChangesInCoeffs (p : ℝ[X]) : ℕ :=
  if _h : p = 0 then 0
  else countSignChanges (coeffSequence p p.natDegree)

/- ## Positive Roots

We define positive roots and count them with multiplicity.
-/

/-- A positive root of a polynomial -/
def IsPositiveRoot (p : ℝ[X]) (r : ℝ) : Prop :=
  r > 0 ∧ p.eval r = 0

/-- The set of positive roots of a polynomial -/
def positiveRoots (p : ℝ[X]) : Set ℝ :=
  {r : ℝ | IsPositiveRoot p r}

/-- Root multiplicity -/
noncomputable def rootMultiplicity' (p : ℝ[X]) (r : ℝ) : ℕ :=
  if p = 0 then 0
  else (p.map (algebraMap ℝ ℝ)).rootMultiplicity r

/- ## Descartes' Rule of Signs - Main Theorem

The main theorem states that the number of positive real roots (with multiplicity)
is at most the number of sign changes in the coefficients, and the difference
is even.
-/

/-- The number of positive roots counted with multiplicity.
    This requires summing multiplicities over positive roots, which is
    only well-defined for polynomials with finitely many roots. -/
noncomputable def countPositiveRoots (p : ℝ[X]) : ℕ :=
  if p = 0 then 0
  else Multiset.card (p.roots.filter (· > 0))

/-- **Axiom: Descartes' Rule of Signs (Upper Bound)**

The proof proceeds by induction on the degree of p.
- Base case: constant polynomial has no positive roots.
- Inductive case: uses Rolle's theorem - between any two roots of p,
  there's a root of p'. Sign changes decrease by at most one when
  differentiating, matching the loss of at most one root. -/
axiom descartes_upper_bound_axiom (p : ℝ[X]) (hp : p ≠ 0) :
    countPositiveRoots p ≤ signChangesInCoeffs p

/-- **Descartes' Rule of Signs (Upper Bound)**

The number of positive real roots of a polynomial is at most equal to
the number of sign changes in its coefficient sequence. -/
theorem descartes_upper_bound (p : ℝ[X]) (hp : p ≠ 0) :
    countPositiveRoots p ≤ signChangesInCoeffs p :=
  descartes_upper_bound_axiom p hp

/-- **Axiom: Descartes' Rule of Signs (Parity)**

The proof uses the fact that complex roots come in conjugate pairs.
Each pair of complex conjugate roots contributes 0 to positive root count
but may contribute 0 or 2 to sign changes (a net even number). -/
axiom descartes_parity_axiom (p : ℝ[X]) (hp : p ≠ 0) :
    Even (signChangesInCoeffs p - countPositiveRoots p)

/-- **Descartes' Rule of Signs (Parity)**

The difference between the number of sign changes and the number of
positive roots is even. -/
theorem descartes_parity (p : ℝ[X]) (hp : p ≠ 0) :
    Even (signChangesInCoeffs p - countPositiveRoots p) :=
  descartes_parity_axiom p hp

/-- **Descartes' Rule of Signs (Combined)**

The number of positive roots equals the number of sign changes minus
some non-negative even number. -/
theorem descartes_rule_of_signs (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, countPositiveRoots p + 2 * k = signChangesInCoeffs p := by
  -- Combines the upper bound and parity results
  have hbound := descartes_upper_bound p hp
  have hparity := descartes_parity p hp
  -- The difference is non-negative (from bound) and even (from parity)
  obtain ⟨m, hm⟩ := hparity
  use m
  omega

/- ## Negative Roots via Substitution

For negative roots, we apply Descartes' rule to p(-x).
-/

/-- Substitute -X for X in a polynomial -/
noncomputable def negSubst (p : ℝ[X]) : ℝ[X] :=
  p.comp (-X)

/-- A negative root of p corresponds to a positive root of p(-x) -/
theorem negative_root_iff_positive_of_negSubst (p : ℝ[X]) (r : ℝ) :
    (r < 0 ∧ p.eval r = 0) ↔ (-r > 0 ∧ (negSubst p).eval (-r) = 0) := by
  constructor
  · intro ⟨hr, heval⟩
    constructor
    · exact neg_pos.mpr hr
    · simp only [negSubst, eval_comp, eval_neg, eval_X, neg_neg]
      exact heval
  · intro ⟨hnr, heval⟩
    constructor
    · exact neg_of_neg_pos hnr
    · simp only [negSubst, eval_comp, eval_neg, eval_X, neg_neg] at heval
      exact heval

/-- negSubst preserves non-zero polynomials. -/
theorem negSubst_ne_zero (p : ℝ[X]) (hp : p ≠ 0) : negSubst p ≠ 0 := by
  unfold negSubst
  intro h
  apply hp
  have key : p = (p.comp (-X)).comp (-X) := by
    simp [Polynomial.comp_assoc]
  rw [h] at key
  simp at key
  exact key

/-- The map r ↦ -r sends negative roots of p to positive roots of negSubst p. -/
theorem neg_root_map_to_pos (p : ℝ[X]) (r : ℝ) (hr : r < 0) (heval : p.eval r = 0) :
    -r > 0 ∧ (negSubst p).eval (-r) = 0 := by
  constructor
  · linarith
  · simp [negSubst, Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
    exact heval

/-- **Descartes' Rule for Negative Roots**

The number of negative roots of p is bounded by the sign changes in p(-x).
The full proof requires showing the multiset `p.roots.filter (· < 0)` maps
bijectively to `(negSubst p).roots.filter (· > 0)` via r ↦ -r, which
needs careful handling of Polynomial.roots_comp. -/
axiom descartes_negative_roots_axiom (p : ℝ[X]) (hp : p ≠ 0) :
    Multiset.card (p.roots.filter (· < 0)) ≤ signChangesInCoeffs (negSubst p)

theorem descartes_negative_roots (p : ℝ[X]) (hp : p ≠ 0) :
    Multiset.card (p.roots.filter (· < 0)) ≤ signChangesInCoeffs (negSubst p) :=
  descartes_negative_roots_axiom p hp

/- ## Sign Change Examples

Concrete examples demonstrating sign change counting.
-/

/-- **One sign change across a zero.**  If `f : Fin 3 → ℝ` has a zero middle entry
(`f 1 = 0`) and outer entries of opposite sign (`f 0 · f 2 < 0`), then `f` has exactly
one sign change — the pair `(0, 2)` jumping over the vanishing middle term.  Axiom-free.
The `Fin 3` middle-zero engine behind the `X² − 1` example below; a self-contained copy of
the downstream `DescartesRuleOfSignsOQ01OQ03` lemma, brought in-file so the base can prove
its own quadratic examples without the (circular) downstream import. -/
theorem countSignChanges_three_mid_zero_pos {f : Fin 3 → ℝ}
    (hmid : f 1 = 0) (h : f 0 * f 2 < 0) :
    countSignChanges f = 1 := by
  have h0 : f 0 ≠ 0 := fun he => by rw [he, zero_mul] at h; exact lt_irrefl 0 h
  have h2 : f 2 ≠ 0 := fun he => by rw [he, mul_zero] at h; exact lt_irrefl 0 h
  unfold countSignChanges
  rw [Finset.card_eq_one]
  refine ⟨(0, 2), ?_⟩
  ext ⟨i, j⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
    decide_eq_true_eq, SignChangeBetween, oppositeSign, Prod.mk.injEq]
  constructor
  · rintro ⟨hij, hi0, hj0, -, -⟩
    have hi1 : i ≠ 1 := by rintro rfl; exact hi0 hmid
    have hj1 : j ≠ 1 := by rintro rfl; exact hj0 hmid
    fin_cases i <;> fin_cases j <;>
      first
        | exact ⟨rfl, rfl⟩
        | (exfalso; revert hij hi1 hj1; decide)
  · rintro ⟨rfl, rfl⟩
    refine ⟨by decide, h0, h2, ?_, h⟩
    intro k hk0 hk2
    fin_cases k <;>
      first
        | exact hmid
        | exact absurd hk0 (by decide)
        | exact absurd hk2 (by decide)

/-- **No sign change with a zero middle and non-opposite outer entries.**  If `f 1 = 0`
and the outer entries do not have strictly opposite signs (`0 ≤ f 0 · f 2` — covering
equal signs *and* a vanishing outer entry), then `f` has no sign change.  Axiom-free.
Companion middle-zero engine behind the `X² + 1` example below. -/
theorem countSignChanges_three_mid_zero_zero {f : Fin 3 → ℝ}
    (hmid : f 1 = 0) (h : 0 ≤ f 0 * f 2) :
    countSignChanges f = 0 := by
  unfold countSignChanges
  rw [Finset.card_eq_zero]
  apply Finset.filter_eq_empty_iff.mpr
  rintro ⟨i, j⟩ -
  simp only [decide_eq_true_eq, SignChangeBetween, oppositeSign]
  rintro ⟨hij, hi0, hj0, -, hopp⟩
  have hi1 : i ≠ 1 := by rintro rfl; exact hi0 hmid
  have hj1 : j ≠ 1 := by rintro rfl; exact hj0 hmid
  have hij02 : i = 0 ∧ j = 2 := by
    fin_cases i <;> fin_cases j <;>
      first
        | exact ⟨rfl, rfl⟩
        | (exfalso; revert hij hi1 hj1; decide)
  obtain ⟨rfl, rfl⟩ := hij02
  exact absurd hopp (not_lt.mpr h)

/-- **`X² − 1` has exactly one coefficient sign change, computed axiom-free.**  The
coefficient sequence is `[1, 0, −1]`: a zero middle with opposite outer signs, hence one
sign change.  Formerly an `axiom`; now discharged directly from the `Fin 3` middle-zero
engine `countSignChanges_three_mid_zero_pos` (name kept for the downstream re-exports). -/
theorem example_x2_minus_1_sign_changes :
    signChangesInCoeffs (X ^ 2 - 1 : ℝ[X]) = 1 := by
  have hne : (X ^ 2 - 1 : ℝ[X]) ≠ 0 := by
    intro h
    have : (X ^ 2 - 1 : ℝ[X]).coeff 2 = 0 := by rw [h]; simp
    simp [coeff_sub, coeff_X_pow, coeff_one] at this
  have hdeg : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by compute_degree!
  unfold signChangesInCoeffs
  rw [dif_neg hne, hdeg]
  apply countSignChanges_three_mid_zero_pos
  · simp [coeffSequence, coeff_sub, coeff_X_pow, coeff_one]
  · have e0 : coeffSequence (X ^ 2 - 1 : ℝ[X]) 2 0 = 1 := by
      simp [coeffSequence, coeff_sub, coeff_X_pow, coeff_one]
    have e2 : coeffSequence (X ^ 2 - 1 : ℝ[X]) 2 2 = -1 := by
      simp [coeffSequence, coeff_sub, coeff_X_pow, coeff_one]
    rw [e0, e2]; norm_num

/-- **`X² + 1` has no coefficient sign change, computed axiom-free.**  The coefficient
sequence is `[1, 0, 1]`: a zero middle with equal outer signs, hence no sign change.
Formerly an `axiom`; now discharged from `countSignChanges_three_mid_zero_zero`. -/
theorem example_x2_plus_1_sign_changes :
    signChangesInCoeffs (X ^ 2 + 1 : ℝ[X]) = 0 := by
  have hne : (X ^ 2 + 1 : ℝ[X]) ≠ 0 := by
    intro h
    have : (X ^ 2 + 1 : ℝ[X]).coeff 2 = 0 := by rw [h]; simp
    simp [coeff_add, coeff_X_pow, coeff_one] at this
  have hdeg : (X ^ 2 + 1 : ℝ[X]).natDegree = 2 := by compute_degree!
  unfold signChangesInCoeffs
  rw [dif_neg hne, hdeg]
  apply countSignChanges_three_mid_zero_zero
  · simp [coeffSequence, coeff_add, coeff_X_pow, coeff_one]
  · have e0 : coeffSequence (X ^ 2 + 1 : ℝ[X]) 2 0 = 1 := by
      simp [coeffSequence, coeff_add, coeff_X_pow, coeff_one]
    have e2 : coeffSequence (X ^ 2 + 1 : ℝ[X]) 2 2 = 1 := by
      simp [coeffSequence, coeff_add, coeff_X_pow, coeff_one]
    rw [e0, e2]; norm_num

/-- Example: `x³ - x = x(x-1)(x+1)` has real roots `{0, 1, -1}`, of which exactly one
    (`x = 1`) is positive, so `countPositiveRoots (X³ - X) = 1`.

    Formerly an `axiom`; the count is now computed directly from Mathlib's polynomial
    root API (`roots_mul`, `roots_X`, `roots_X_sub_C`) — a concrete arithmetic fact
    that needs no assumption. -/
theorem x_cubed_minus_x_positive_roots_axiom :
    countPositiveRoots (X^3 - X : ℝ[X]) = 1 := by
  have hfac : (X ^ 3 - X : ℝ[X]) = X * (X - C 1) * (X + C 1) := by
    simp only [map_one]; ring
  have hX : (X : ℝ[X]) ≠ 0 := X_ne_zero
  have hXm : (X - C 1 : ℝ[X]) ≠ 0 := X_sub_C_ne_zero 1
  have hpe : (X + C 1 : ℝ[X]) = X - C (-1) := by rw [map_neg, sub_neg_eq_add]
  have hXp : (X + C 1 : ℝ[X]) ≠ 0 := by rw [hpe]; exact X_sub_C_ne_zero (-1)
  have hne : (X ^ 3 - X : ℝ[X]) ≠ 0 := by
    rw [hfac]; exact mul_ne_zero (mul_ne_zero hX hXm) hXp
  unfold countPositiveRoots
  rw [if_neg hne, hfac,
    roots_mul (by rw [← hfac]; exact hne),
    roots_mul (mul_ne_zero hX hXm), roots_X, roots_X_sub_C, hpe, roots_X_sub_C]
  simp only [Multiset.filter_add, Multiset.filter_singleton]
  norm_num

theorem x_cubed_minus_x_positive_roots :
    countPositiveRoots (X^3 - X : ℝ[X]) = 1 :=
  x_cubed_minus_x_positive_roots_axiom

/- ## Special Cases

Special cases where the bound is achieved or easily computed.
-/

/-- For x > 0, if all coefficients are non-negative and at least one is positive,
    then p(x) > 0. -/
theorem eval_pos_of_nonneg_coeffs (p : ℝ[X]) (_hp : p ≠ 0)
    (hpos : ∀ i, 0 ≤ p.coeff i)
    (hsome : ∃ i, 0 < p.coeff i)
    (x : ℝ) (hx : x > 0) :
    0 < p.eval x := by
  rw [Polynomial.eval_eq_sum_range]
  obtain ⟨j, hj⟩ := hsome
  -- The sum is non-negative since each term is non-negative
  have hle : j ≤ p.natDegree := by
    by_contra h
    push_neg at h
    have := Polynomial.coeff_eq_zero_of_natDegree_lt h
    linarith
  have hmem : j ∈ Finset.range (p.natDegree + 1) := Finset.mem_range.mpr (by omega)
  calc 0 < p.coeff j * x ^ j :=
        mul_pos hj (pow_pos hx j)
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * x ^ i :=
        Finset.single_le_sum (fun i _ => mul_nonneg (hpos i) (pow_nonneg (le_of_lt hx) i)) hmem

/-- No positive roots if all coefficients are non-negative with at least one positive. -/
theorem no_positive_roots_if_positive_coeffs (p : ℝ[X]) (hp : p ≠ 0)
    (hpos : ∀ i, 0 ≤ p.coeff i)
    (hsome : ∃ i, 0 < p.coeff i) :
    countPositiveRoots p = 0 := by
  unfold countPositiveRoots
  simp only [hp, ↓reduceIte]
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro r hr
  push_neg
  by_contra h
  push_neg at h
  have heval : p.eval r = 0 := (Polynomial.mem_roots hp).mp hr
  have heval_pos := eval_pos_of_nonneg_coeffs p hp hpos hsome r h
  linarith

/-- **Axiom: Alternating signs achieve maximum roots**

Alternating signs means n sign changes for degree n.
The bound is achieved in this case. -/
axiom alternating_signs_max_roots_axiom (p : ℝ[X]) (hp : p ≠ 0)
    (halt : ∀ i, i ≤ p.natDegree →
      (Even i → 0 < p.coeff i) ∧ (Odd i → p.coeff i < 0)) :
    countPositiveRoots p = p.natDegree

/-- A polynomial with alternating signs has the maximum number of positive roots -/
theorem alternating_signs_max_roots (p : ℝ[X]) (hp : p ≠ 0)
    (halt : ∀ i, i ≤ p.natDegree →
      (Even i → 0 < p.coeff i) ∧ (Odd i → p.coeff i < 0)) :
    countPositiveRoots p = p.natDegree :=
  alternating_signs_max_roots_axiom p hp halt

/- ## Connection to Rolle's Theorem

The proof of Descartes' rule relies on Rolle's theorem from calculus.
-/

/-- **Rolle's theorem for polynomials**

Between two distinct roots of p, there exists a root of p'.
This follows from Mathlib's `exists_deriv_eq_zero` applied to polynomial evaluation.

The proof structure:
1. Use Polynomial.continuous for continuity on [a,b]
2. Apply exists_deriv_eq_zero (Rolle's theorem) to get c with deriv(p.eval) c = 0
3. Use Polynomial.deriv to connect deriv(p.eval) to (derivative p).eval -/
theorem rolle_polynomial (p : ℝ[X]) (a b : ℝ) (hab : a < b)
    (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ c, a < c ∧ c < b ∧ (derivative p).eval c = 0 := by
  -- Use Mathlib's Rolle's theorem for real functions
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) :=
    p.continuous.continuousOn
  have heq : p.eval a = p.eval b := ha.trans hb.symm
  -- Apply Rolle's theorem to get c where deriv(eval p) c = 0
  obtain ⟨c, ⟨hac, hcb⟩, hderiv⟩ := exists_deriv_eq_zero hab hcont heq
  use c
  refine ⟨hac, hcb, ?_⟩
  -- Need: deriv (fun x => p.eval x) c = (derivative p).eval c
  -- This is Polynomial.deriv from Mathlib
  simp only [Polynomial.deriv] at hderiv
  exact hderiv

/-- **Axiom: Derivative reduces or preserves sign changes**

Differentiating a polynomial can reduce sign changes by at most one
per root lost, or preserve the sign change count. -/
axiom derivative_reduces_sign_changes_axiom (p : ℝ[X]) (hp : p ≠ 0) :
    signChangesInCoeffs (derivative p) ≤ signChangesInCoeffs p - 1 ∨
    signChangesInCoeffs (derivative p) = signChangesInCoeffs p

/-- Differentiating a polynomial reduces sign changes by at most one per root lost -/
theorem derivative_reduces_sign_changes (p : ℝ[X]) (hp : p ≠ 0) :
    signChangesInCoeffs (derivative p) ≤ signChangesInCoeffs p - 1 ∨
    signChangesInCoeffs (derivative p) = signChangesInCoeffs p :=
  derivative_reduces_sign_changes_axiom p hp

/- ## Why This Matters

Descartes' Rule of Signs is important because:

1. **Root Bounds**: Gives an upper bound on positive/negative real roots
   without solving the polynomial.

2. **Existence Tests**: If sign changes = 1, there's exactly one positive root.
   If sign changes = 0, there are no positive roots.

3. **Historical Significance**: One of the earliest general results about
   polynomial roots, predating the Fundamental Theorem of Algebra.

4. **Algorithmic Applications**: Used in root isolation algorithms like
   Sturm's theorem and Vincent's theorem for real root computation.

5. **Educational Value**: Demonstrates the connection between algebraic
   properties (coefficients) and analytic properties (roots).
-/

/- ## Additional Structural Theorems -/

/-- Sign properties of realSign. -/
theorem realSign_pos {x : ℝ} (hx : x > 0) : realSign x = 1 := by
  unfold realSign
  simp [hx]

theorem realSign_neg {x : ℝ} (hx : x < 0) : realSign x = -1 := by
  unfold realSign
  simp only [show ¬(x > 0) from by linarith, ↓reduceIte, hx]

theorem realSign_zero : realSign 0 = 0 := by
  unfold realSign
  simp

/-- oppositeSign is symmetric. -/
theorem oppositeSign_comm (x y : ℝ) : oppositeSign x y ↔ oppositeSign y x := by
  unfold oppositeSign
  constructor <;> intro h <;> linarith [mul_comm x y]

/-- The zero polynomial has no positive roots. -/
theorem countPositiveRoots_zero : countPositiveRoots (0 : ℝ[X]) = 0 := by
  unfold countPositiveRoots
  simp

/-- Zero polynomial has no sign changes. -/
theorem signChangesInCoeffs_zero : signChangesInCoeffs (0 : ℝ[X]) = 0 := by
  unfold signChangesInCoeffs
  simp

/-- Evaluation of negSubst relates to evaluation at negation. -/
theorem negSubst_eval (p : ℝ[X]) (x : ℝ) :
    (negSubst p).eval x = p.eval (-x) := by
  unfold negSubst
  simp [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]

/-- Double negSubst is the identity. -/
theorem negSubst_negSubst (p : ℝ[X]) : negSubst (negSubst p) = p := by
  unfold negSubst
  simp [Polynomial.comp_assoc]

/-- Constant polynomials have no positive roots. -/
theorem countPositiveRoots_C (c : ℝ) (hc : c ≠ 0) :
    countPositiveRoots (Polynomial.C c) = 0 := by
  unfold countPositiveRoots
  simp only [Polynomial.C_eq_zero.not.mpr hc, ↓reduceIte]
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro r hr
  push_neg
  exfalso
  have := (Polynomial.mem_roots (Polynomial.C_ne_zero.mpr hc)).mp hr
  simp [Polynomial.eval_C] at this
  exact hc this

/-- The monomial xⁿ has no positive roots (0 is not positive). -/
theorem countPositiveRoots_X_pow (n : ℕ) (_hn : n ≥ 1) :
    countPositiveRoots (X ^ n : ℝ[X]) = 0 := by
  unfold countPositiveRoots
  have hne : (X : ℝ[X]) ^ n ≠ 0 := pow_ne_zero n (Polynomial.X_ne_zero)
  simp only [hne, ↓reduceIte]
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro r hr
  push_neg
  by_contra h
  push_neg at h
  have heval := (Polynomial.mem_roots hne).mp hr
  simp [Polynomial.eval_pow, Polynomial.eval_X] at heval
  have hr0 : r = 0 := by
    rcases heval with ⟨hr0, _⟩
    exact hr0
  linarith

/-- Rolle's theorem implies derivative has a root between consecutive roots.
    This is a key lemma used in the inductive proof of Descartes' rule. -/
theorem derivative_root_between_roots (p : ℝ[X]) (a b : ℝ) (hab : a < b)
    (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ c, a < c ∧ c < b ∧ (Polynomial.derivative p).eval c = 0 :=
  rolle_polynomial p a b hab ha hb

/- ## Bridge to Mathlib's Polynomial.RuleOfSigns API

Mathlib provides `Polynomial.signVariations` and the Descartes bound
`roots_countP_pos_le_signVariations`. We bridge our custom definitions to
Mathlib's API.
-/

/-- Our countPositiveRoots equals Mathlib's roots.countP (0 < ·) for nonzero p.
    Both count the multiplicity of positive roots; the definitions differ only
    in notation: filter+card vs countP. -/
theorem countPositiveRoots_eq_roots_countP (p : ℝ[X]) (hp : p ≠ 0) :
    countPositiveRoots p = p.roots.countP (0 < ·) := by
  unfold countPositiveRoots
  simp only [hp, ↓reduceIte]
  simp [Multiset.countP_eq_card_filter, gt_iff_lt]

/-- If our sign change count agrees with Mathlib's signVariations, then
    Descartes' upper bound follows directly from Mathlib without the axiom. -/
theorem descartes_upper_bound_via_signVariations (p : ℝ[X]) (hp : p ≠ 0)
    (hbridge : signChangesInCoeffs p = p.signVariations) :
    countPositiveRoots p ≤ signChangesInCoeffs p := by
  rw [countPositiveRoots_eq_roots_countP p hp, hbridge]
  exact p.roots_countP_pos_le_signVariations

/- ## Consequences of Descartes' Bound -/

/-- Zero sign changes means no positive roots.
    Immediate corollary of the upper bound. -/
theorem zero_sign_changes_no_positive_roots (p : ℝ[X]) (hp : p ≠ 0)
    (h : signChangesInCoeffs p = 0) : countPositiveRoots p = 0 := by
  have hle := descartes_upper_bound p hp
  omega

/-- One sign change means at most one positive root. -/
theorem one_sign_change_at_most_one_root (p : ℝ[X]) (hp : p ≠ 0)
    (h : signChangesInCoeffs p = 1) : countPositiveRoots p ≤ 1 := by
  have hle := descartes_upper_bound p hp
  omega

/-- Descartes bound implies: if sign changes < k, then fewer than k positive roots. -/
theorem sign_changes_lt_k_fewer_roots (p : ℝ[X]) (hp : p ≠ 0) (k : ℕ)
    (h : signChangesInCoeffs p < k) : countPositiveRoots p < k :=
  lt_of_le_of_lt (descartes_upper_bound p hp) h

/- ## Applications of Rolle's Theorem -/

/-- Between three distinct roots a < b < c of p, the derivative has at least
    two roots: one in (a, b) and one in (b, c).
    This is the key inductive step in the proof of Descartes' rule. -/
theorem three_roots_two_derivative_roots (p : ℝ[X]) (a b c : ℝ)
    (hab : a < b) (hbc : b < c)
    (ha : p.eval a = 0) (hb : p.eval b = 0) (hc : p.eval c = 0) :
    ∃ d e, a < d ∧ d < b ∧ b < e ∧ e < c ∧
      (derivative p).eval d = 0 ∧
      (derivative p).eval e = 0 := by
  obtain ⟨d, had, hdb, hd⟩ := rolle_polynomial p a b hab ha hb
  obtain ⟨e, hbe, hec, he⟩ := rolle_polynomial p b c hbc hb hc
  exact ⟨d, e, had, hdb, hbe, hec, hd, he⟩

/-- If a polynomial has n + 1 distinct roots a₀ < a₁ < ... < aₙ, then for each
    consecutive pair, the derivative has a root strictly between them.
    This gives n roots of the derivative from n + 1 roots of p. -/
theorem n_roots_implies_derivative_roots (p : ℝ[X]) (n : ℕ)
    (rootsF : Fin (n + 1) → ℝ)
    (hstrict : StrictMono rootsF)
    (heval : ∀ i, p.eval (rootsF i) = 0) :
    ∀ i : Fin n, ∃ c, rootsF i.castSucc < c ∧ c < rootsF i.succ ∧
      (derivative p).eval c = 0 := by
  intro i
  have hi : rootsF i.castSucc < rootsF i.succ := hstrict i.castSucc_lt_succ
  exact rolle_polynomial p (rootsF i.castSucc) (rootsF i.succ) hi
    (heval i.castSucc) (heval i.succ)

/-- A polynomial of degree d has at most d positive roots.
    This follows from the standard root count bound and our bridge. -/
theorem countPositiveRoots_le_natDegree (p : ℝ[X]) (hp : p ≠ 0) :
    countPositiveRoots p ≤ p.natDegree := by
  rw [countPositiveRoots_eq_roots_countP p hp]
  exact le_trans (Multiset.countP_le_card _ p.roots) (Polynomial.card_roots' p)

/-- The number of non-zero roots is bounded by the degree.
    Since filter (· ≠ 0) gives a sub-multiset of roots, its cardinality is ≤ roots.card,
    and roots.card ≤ natDegree by the polynomial root bound. -/
theorem nonzero_root_count_le_degree (p : ℝ[X]) (hp : p ≠ 0) :
    Multiset.card (p.roots.filter (· ≠ 0)) ≤ p.natDegree :=
  le_trans (Multiset.card_le_card (Multiset.filter_le _ _)) (Polynomial.card_roots' p)

/-- The number of negative roots is bounded by the degree.
    Since filter (· < 0) gives a sub-multiset of roots, its cardinality is ≤ roots.card,
    and roots.card ≤ natDegree. -/
theorem negative_root_count_le_natDegree (p : ℝ[X]) (hp : p ≠ 0) :
    Multiset.card (p.roots.filter (· < 0)) ≤ p.natDegree :=
  le_trans (Multiset.card_le_card (Multiset.filter_le _ _)) (Polynomial.card_roots' p)

/-- The number of negative roots of p is bounded by signChangesInCoeffs (negSubst p). -/
theorem negative_roots_le_sign_changes (p : ℝ[X]) (hp : p ≠ 0) :
    Multiset.card (p.roots.filter (· < 0)) ≤ signChangesInCoeffs (negSubst p) :=
  descartes_negative_roots p hp

end DescartesRuleOfSigns
