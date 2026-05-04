/-
# Sturm's Theorem: Exact Root Count via Sign-Change Sequences (OQ-02-OQ-01-OQ-02)

## Research Question

While Budan's theorem (OQ-02) gives an *upper bound* on roots in (a, b], can we
find a construction that gives the *exact* count of distinct real roots?

## What This Proves

Sturm's theorem (Jacques Charles François Sturm, 1829) gives the EXACT number of
distinct real roots of a squarefree polynomial in any interval (a, b]:

  #{distinct real roots of p in (a,b]} = σ_p(a) - σ_p(b)

where σ_p(x) = number of sign changes in the Sturm sequence of p evaluated at x.

Unlike Budan's theorem which uses the derivative sequence [p, p', p'', ..., p^(n)],
Sturm's theorem uses a GCD-based sequence [p₀, p₁, p₂, ..., pₘ] where:
  p₀ = p
  p₁ = p'
  pₖ₊₁ = -rem(pₖ₋₁, pₖ)   (negative polynomial remainder)

## The Key Structural Properties

1. **Interior sign property**: At any root r of pₖ (k ≥ 1, an interior term),
   pₖ₋₁(r) and pₖ₊₁(r) have OPPOSITE signs.
   Proof: pₖ₋₁ = quotient · pₖ + pₖ₊₁ is wrong — actually:
   pₖ₋₁(r) = (pₖ₋₁/pₖ)(r) · 0 + (pₖ₋₁%pₖ)(r) = (pₖ₋₁%pₖ)(r) = -pₖ₊₁(r)
   Hence pₖ₋₁(r) = -pₖ₊₁(r), so they have opposite signs (if both nonzero).

2. **Sign count at roots of p**: As x passes through a real root r of p (from left):
   - p changes sign
   - p₁ = p' evaluates to p'(r) ≠ 0 (since p is squarefree, so gcd(p,p') = 1)
   - The sign change count decreases by exactly 1.

3. **No sign count change at interior roots**: As x passes through a root of pₖ (k ≥ 1):
   The triple (pₖ₋₁, pₖ, pₖ₊₁) contributes the same sign-change count just before
   and just after r (the two sign changes from +,-,+ or -,+,- both appear or both disappear),
   so the total sign count is unchanged.

## Relation to Budan's Theorem

Sturm's theorem implies Budan's upper bound for squarefree polynomials:
  sturmVariations(a) - sturmVariations(b) = #{roots in (a,b]} ≤ budanCount(a) - budanCount(b)

The Budan count can exceed the Sturm count by an even number (matching the parity result).

## Historical Significance

Sturm's theorem was among the first constructive/algorithmic results in real algebraic
geometry. It enables:
- Exact real root isolation (bisect until interval contains exactly one root)
- Deciding whether a polynomial has any real roots (check if σ(-M) - σ(M) = 0 for large M)
- Computing the number of real roots of any polynomial in any interval in O(n²) time

The theorem directly answers a question Lagrange posed in 1767, and was extended to
Sylvester's sequence (1853), which computes σ(x) for more general sign sequences.

## Axiom Budget: 1 axiom (sturm_exact_count_axiom)

Original formalization for Lean Genius.
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Squarefree.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

namespace SturmTheorem

open Polynomial

-- ============================================================================
-- § 1. Auxiliary Definitions
-- ============================================================================

/-- Count adjacent sign alternations in a list of ±1 integers. -/
def countSignAlts : List ℤ → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (if a ≠ b then 1 else 0) + countSignAlts (b :: rest)

@[simp] theorem countSignAlts_nil : countSignAlts [] = 0 := rfl
@[simp] theorem countSignAlts_singleton (a : ℤ) : countSignAlts [a] = 0 := rfl

/-- Number of sign changes in a list of reals, ignoring zeros. -/
noncomputable def signVariations (l : List ℝ) : ℕ :=
  let nonzero := l.filter (· ≠ 0)
  let signs := nonzero.map (fun x => if x > 0 then (1 : ℤ) else -1)
  countSignAlts signs

@[simp]
theorem signVariations_nil : signVariations [] = 0 := by
  simp [signVariations]

theorem signVariations_singleton (r : ℝ) : signVariations [r] = 0 := by
  simp [signVariations, countSignAlts]
  split <;> simp

/-- Count of roots of p in the half-open interval (a, b], with multiplicity. -/
noncomputable def rootsInInterval (p : ℝ[X]) (a b : ℝ) : ℕ :=
  if p = 0 then 0
  else Multiset.card (p.roots.filter (fun r => a < r ∧ r ≤ b))

@[simp]
theorem rootsInInterval_zero (a b : ℝ) : rootsInInterval (0 : ℝ[X]) a b = 0 := by
  simp [rootsInInterval]

theorem rootsInInterval_C (c : ℝ) (hc : c ≠ 0) (a b : ℝ) :
    rootsInInterval (C c) a b = 0 := by
  simp only [rootsInInterval, C_eq_zero.not.mpr hc, ↓reduceIte]
  rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
  intro r hr
  have := (mem_roots (C_ne_zero.mpr hc)).mp hr
  rw [Polynomial.IsRoot, eval_C] at this
  exact hc this

-- ============================================================================
-- § 2. The Sturm Sequence
-- ============================================================================

/-- Build the Sturm sequence starting from (p, q) with fuel n.
    The fuel bounds iterations; n = p.natDegree + 1 suffices since each step
    strictly reduces the degree of the leading term. -/
noncomputable def sturmSeqAux : ℝ[X] → ℝ[X] → ℕ → List ℝ[X]
  | p, _, 0 => [p]
  | p, q, n + 1 =>
    if q = 0 then [p]
    else p :: sturmSeqAux q (-(p % q)) n

/-- The Sturm sequence of p: [p, p', -rem(p,p'), -rem(p', -rem(p,p')), ...] -/
noncomputable def sturmSeq (p : ℝ[X]) : List ℝ[X] :=
  sturmSeqAux p (derivative p) (p.natDegree + 1)

-- ============================================================================
-- § 3. Basic Properties of the Sturm Sequence
-- ============================================================================

theorem sturmSeqAux_ne_empty (p q : ℝ[X]) (n : ℕ) :
    (sturmSeqAux p q n).length > 0 := by
  cases n with
  | zero => simp [sturmSeqAux]
  | succ n =>
    simp only [sturmSeqAux]
    split <;> simp

theorem sturmSeq_ne_empty (p : ℝ[X]) : (sturmSeq p).length > 0 :=
  sturmSeqAux_ne_empty p (derivative p) (p.natDegree + 1)

theorem sturmSeqAux_head (p q : ℝ[X]) (n : ℕ) :
    (sturmSeqAux p q n).head? = some p := by
  cases n with
  | zero => simp [sturmSeqAux]
  | succ n =>
    simp only [sturmSeqAux]
    split
    · simp
    · simp

theorem sturmSeq_head (p : ℝ[X]) : (sturmSeq p).head? = some p :=
  sturmSeqAux_head p (derivative p) (p.natDegree + 1)

/-- The Sturm sequence has at least 2 elements for nonzero polynomials of degree ≥ 1. -/
theorem sturmSeq_length_ge_two (p : ℝ[X]) (hp : p ≠ 0) (hd : 0 < p.natDegree) :
    (sturmSeq p).length ≥ 2 := by
  unfold sturmSeq sturmSeqAux
  -- In char 0, derivative p ≠ 0 when natDegree p ≥ 1
  -- The key: natDegree (derivative p) = natDegree p - 1 (char 0), so deriv p ≠ 0 for natDeg ≥ 1
  have hdp : derivative p ≠ 0 := by
    -- In char 0, leading coeff of derivative is natDegree * leadingCoeff ≠ 0
    intro h
    have hcoeff : (p.natDegree : ℝ) * p.leadingCoeff = 0 := by
      have := congr_arg (Polynomial.coeff · (p.natDegree - 1)) h
      simp only [Polynomial.coeff_zero, Polynomial.coeff_derivative] at this
      have hk : p.natDegree - 1 + 1 = p.natDegree := by omega
      rw [hk] at this
      exact_mod_cast this
    have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hnd : (p.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact hnd (or_iff_not_imp_right.mp (mul_eq_zero.mp hcoeff) hlc)
  obtain ⟨m, hm⟩ : ∃ m, p.natDegree + 1 = m + 1 := ⟨p.natDegree, rfl⟩
  rw [hm]
  simp only [sturmSeqAux, hdp, ↓reduceIte, List.length_cons]
  exact Nat.succ_le_succ (sturmSeqAux_ne_empty _ _ _)

-- ============================================================================
-- § 4. The Sturm Sign-Variation Count
-- ============================================================================

/-- The Sturm sign-variation count at x: number of sign changes in the
    Sturm sequence evaluated at x (ignoring zeros). -/
noncomputable def sturmVariations (p : ℝ[X]) (x : ℝ) : ℕ :=
  signVariations ((sturmSeq p).map (fun q => q.eval x))

theorem sturmVariations_zero (x : ℝ) : sturmVariations (0 : ℝ[X]) x = 0 := by
  simp [sturmVariations, sturmSeq, sturmSeqAux, signVariations]

theorem sturmVariations_C (c : ℝ) (hc : c ≠ 0) (x : ℝ) :
    sturmVariations (C c) x = 0 := by
  simp [sturmVariations, sturmSeq, sturmSeqAux]
  simp [signVariations, countSignAlts, derivative_C]

-- ============================================================================
-- § 5. Key Structural Lemma: Mod at a Root
-- ============================================================================

/-- At a root r of q, the remainder p % q equals p(r) when evaluated.
    Proof: p = (p/q) * q + (p%q), evaluating at r where q(r) = 0 gives p(r) = (p%q)(r). -/
theorem mod_eval_at_root (p q : ℝ[X]) (r : ℝ) (hr : q.eval r = 0) :
    (p % q).eval r = p.eval r := by
  have hdiv : q * (p / q) + p % q = p := EuclideanDomain.div_add_mod p q
  have := congr_arg (Polynomial.eval r) hdiv
  simp only [eval_add, eval_mul, hr, zero_mul, zero_add] at this
  exact this.symm

/-- The key structural property of the Sturm sequence:
    At a root r of q, -(p % q)(r) = -p(r), so the next Sturm term has value -p(r).
    This means consecutive Sturm terms bracket any interior root with opposite signs. -/
theorem sturm_interior_sign_property (p q : ℝ[X]) (r : ℝ) (hr : q.eval r = 0) :
    (-(p % q)).eval r = -p.eval r := by
  simp [mod_eval_at_root p q r hr]

/-- If consecutive Sturm terms at r satisfy: p₀(r) ≠ 0 and q(r) = 0, then
    -(p₀ % q)(r) = -p₀(r), so the two neighbors of q have OPPOSITE signs
    (they differ by a sign flip). -/
theorem sturm_neighbors_opposite_at_root (p₀ q : ℝ[X]) (r : ℝ)
    (hr : q.eval r = 0) (hp₀ : p₀.eval r ≠ 0) :
    p₀.eval r * (-(p₀ % q)).eval r < 0 := by
  rw [sturm_interior_sign_property]
  have : p₀.eval r ≠ 0 := hp₀
  nlinarith [sq_nonneg (p₀.eval r)]

-- ============================================================================
-- § 6. Main Theorem: Exact Root Count
-- ============================================================================

/-- **Axiom: Sturm's Theorem (Exact Count)**

For a squarefree polynomial p ∈ ℝ[X] and real interval (a, b] with p(a) ≠ 0
and p(b) ≠ 0, the number of distinct real roots of p in (a, b] equals
the difference in Sturm sign-variation counts:

  #{roots in (a,b]} = σ_p(a) - σ_p(b)

The proof proceeds by showing:
1. σ_p is piecewise constant (non-decreasing in the σ(b) direction)
2. σ_p decreases by exactly 1 as x passes through each real root of p
3. σ_p is unchanged as x passes through roots of interior Sturm terms

This is Sturm's original theorem (1829). -/
axiom sturm_exact_count_axiom
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    rootsInInterval p a b = sturmVariations p a - sturmVariations p b

theorem sturm_exact_count
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    rootsInInterval p a b = sturmVariations p a - sturmVariations p b :=
  sturm_exact_count_axiom p hp hpsc a b hab ha hb

-- ============================================================================
-- § 7. Corollaries
-- ============================================================================

/-- **Root isolation**: If the Sturm counts at a and b agree, there are no roots in (a,b]. -/
theorem sturm_no_roots
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0)
    (heq : sturmVariations p a = sturmVariations p b) :
    rootsInInterval p a b = 0 := by
  rw [sturm_exact_count p hp hpsc a b hab ha hb, heq, Nat.sub_self]

/-- **Unique root**: If the Sturm count drops by exactly 1, there is exactly one root. -/
theorem sturm_unique_root
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0)
    (hdiff : sturmVariations p a = sturmVariations p b + 1) :
    rootsInInterval p a b = 1 := by
  rw [sturm_exact_count p hp hpsc a b hab ha hb, hdiff, Nat.add_sub_cancel]

/-- **Two roots**: Sturm count drop of 2 implies exactly 2 distinct roots. -/
theorem sturm_two_roots
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0)
    (hdiff : sturmVariations p a = sturmVariations p b + 2) :
    rootsInInterval p a b = 2 := by
  rw [sturm_exact_count p hp hpsc a b hab ha hb, hdiff, Nat.add_sub_cancel]

/-- **Non-decreasing Sturm count**: rootsInInterval is always ≤ sturmVariations difference.
    This is a weakening of the exact count, following directly from Nat.le_refl. -/
theorem sturm_count_le_variations
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    rootsInInterval p a b ≤ sturmVariations p a - sturmVariations p b := by
  rw [sturm_exact_count p hp hpsc a b hab ha hb]

/-- Sturm's theorem implies the Sturm count is monotone:
    sturmVariations p a ≥ sturmVariations p b whenever a < b and p doesn't vanish at endpoints. -/
theorem sturmVariations_antitone
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    sturmVariations p b ≤ sturmVariations p a := by
  have h := sturm_exact_count p hp hpsc a b hab ha hb
  omega

-- ============================================================================
-- § 8. Example: Sturm Sequence for a Linear Polynomial
-- ============================================================================

section LinearExample

/-- For a linear polynomial p(x) = x - c, the Sturm sequence is [x - c, 1].
    The sign variation at x is 1 if x < c (x - c < 0, 1 > 0: one sign change)
    and 0 if x > c (x - c > 0, 1 > 0: no sign change). -/

variable (c : ℝ)

/-- The derivative of x - c is 1. -/
theorem linear_deriv : derivative (X - C c) = (1 : ℝ[X]) := by
  simp [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C]

/-- The Sturm sequence of x - c is [x - c, 1]:
    p₁ = derivative(x - c) = 1, and (x - c) % 1 = 0 terminating the sequence. -/
theorem sturmSeq_linear : sturmSeq (X - C c) = [X - C c, 1] := by
  simp only [sturmSeq, sturmSeqAux, linear_deriv, Polynomial.natDegree_X_sub_C]
  norm_num [sturmSeqAux]
  -- (X - C c) % 1 = 0: any polynomial mod 1 is 0
  have hmod : (X - C c) % (1 : ℝ[X]) = 0 :=
    (EuclideanDomain.dvd_iff_mod_eq_zero.mp (one_dvd _))
  simp [sturmSeqAux, hmod]

/-- For the linear polynomial x - c, the Sturm sign count at x < c equals 1.
    At x < c: evaluate [X-c, 1] to get [x-c, 1]; x-c < 0 and 1 > 0, so 1 sign change. -/
theorem sturm_linear_left (x : ℝ) (hx : x < c) :
    sturmVariations (X - C c) x = 1 := by
  simp only [sturmVariations, sturmSeq_linear, List.map, Polynomial.eval_sub, Polynomial.eval_X,
             Polynomial.eval_C, Polynomial.eval_one]
  have hxc : x - c < 0 := by linarith
  have hne : x - c ≠ 0 := ne_of_lt hxc
  -- The list [x-c, 1] filtered is [x-c, 1] (both nonzero), mapped to [-1, 1], 1 sign change
  simp only [signVariations, List.filter, hne, ne_eq, not_false_eq_true, ↓reduceIte,
             one_ne_zero, List.map]
  simp only [show ¬(x - c > 0) from not_lt.mpr (le_of_lt hxc)]
  simp [countSignAlts]

/-- For the linear polynomial x - c, the Sturm sign count at x > c equals 0.
    At x > c: evaluate [X-c, 1] to get [x-c, 1]; x-c > 0 and 1 > 0, so 0 sign changes. -/
theorem sturm_linear_right (x : ℝ) (hx : x > c) :
    sturmVariations (X - C c) x = 0 := by
  simp only [sturmVariations, sturmSeq_linear, List.map, Polynomial.eval_sub, Polynomial.eval_X,
             Polynomial.eval_C, Polynomial.eval_one]
  have hxc : x - c > 0 := by linarith
  have hne : x - c ≠ 0 := ne_of_gt hxc
  -- The list [x-c, 1] filtered is [x-c, 1] (both nonzero), mapped to [1, 1], 0 sign changes
  simp only [signVariations, List.filter, hne, ne_eq, not_false_eq_true, ↓reduceIte,
             one_ne_zero, List.map, hxc]
  simp [countSignAlts]

end LinearExample

-- ============================================================================
-- § 9. Squarefree Polynomials and the GCD Connection
-- ============================================================================

/-- A squarefree polynomial p satisfies gcd(p, p') = constant.
    This ensures the Sturm sequence terminates with a nonzero constant,
    which is the key ingredient making the exact count theorem work. -/

/-- For squarefree p, p and p' have no common real roots. -/
theorem squarefree_no_common_roots (p : ℝ[X]) (hpsc : Squarefree p) (r : ℝ) :
    ¬(p.eval r = 0 ∧ (derivative p).eval r = 0) := by
  intro ⟨hp, hdp⟩
  -- If p(r) = 0 and p'(r) = 0, then (X - r)² | p
  -- Write p = (X - r) * q (from the root). Differentiate: p' = q + (X - r) * q'.
  -- At r: p'(r) = q(r), so q(r) = 0. Hence (X - r) | q, giving (X - r)² | p.
  have hdvd : (X - C r) ∣ p := Polynomial.dvd_iff_isRoot.mpr hp
  obtain ⟨q, hq⟩ := hdvd
  have hqr : q.eval r = 0 := by
    have hpd : (derivative p).eval r = 0 := hdp
    rw [hq, Polynomial.derivative_mul] at hpd
    simp [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C,
          Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one] at hpd
    linarith
  have hsq : (X - C r) ^ 2 ∣ p := by
    rw [hq, pow_two]
    exact Dvd.dvd.mul_left (Polynomial.dvd_iff_isRoot.mpr hqr) _
  have hunit : IsUnit (X - C r) := hpsc (X - C r) hsq
  rw [Polynomial.isUnit_iff] at hunit
  obtain ⟨u, _, hu⟩ := hunit
  have hdeg : (X - C r).natDegree = 1 := Polynomial.natDegree_X_sub_C r
  have hcu : (C (u : ℝ)).natDegree = 0 := Polynomial.natDegree_C _
  rw [← hu] at hcu
  omega

/-- A squarefree polynomial p of degree ≥ 1 cannot satisfy p' = 0.
    (Since p' = 0 would mean p is a constant, contradicting degree ≥ 1.) -/
theorem squarefree_deriv_ne_zero_of_pos_degree (p : ℝ[X]) (hpsc : Squarefree p)
    (hd : 0 < p.natDegree) : derivative p ≠ 0 := by
  -- In char 0, leading coeff of derivative p is natDegree * leadingCoeff ≠ 0 for deg ≥ 1
  intro h
  have hne : p ≠ 0 := by
    intro hp0; rw [hp0] at hd; simp at hd
  have hcoeff : (p.natDegree : ℝ) * p.leadingCoeff = 0 := by
    have := congr_arg (Polynomial.coeff · (p.natDegree - 1)) h
    simp only [Polynomial.coeff_zero, Polynomial.coeff_derivative] at this
    have hk : p.natDegree - 1 + 1 = p.natDegree := by omega
    rw [hk] at this
    exact_mod_cast this
  have hlc : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  have hnd : (p.natDegree : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  exact hnd (or_iff_not_imp_right.mp (mul_eq_zero.mp hcoeff) hlc)

-- ============================================================================
-- § 10. Comparison with Budan's Theorem
-- ============================================================================

/-
## Sturm vs Budan: Two Approaches to Root Counting

Both Budan's theorem (1807) and Sturm's theorem (1829) solve the problem of
counting real roots of polynomials in an interval.

| Property | Budan | Sturm |
|----------|-------|-------|
| Count type | Upper bound | Exact count |
| Sequence | Derivatives [p, p', ..., p^(n)] | GCD-based [p, p', -rem(p,p'), ...] |
| Squarefree required? | No | Yes (for exact count) |
| Length | Always n+1 terms | At most n+1 terms, often fewer |
| Parity | budanCount - roots is even | Count is exact |
| Computational cost | O(n) evaluations | O(n²) GCD steps |

For squarefree polynomials:
- sturmVariations p a - sturmVariations p b = rootsInInterval p a b (Sturm)
- budanCount p a - budanCount p b ≥ rootsInInterval p a b (Budan upper bound)
- budanCount p a - budanCount p b - (sturmVariations p a - sturmVariations p b) is even

The key algebraic insight: Budan uses the FULL derivative tower, while Sturm
uses a TRUNCATED GCD sequence. The GCD structure ensures the sequence is "tight"
(no excess sign changes), giving exactness rather than just an upper bound.
-/

end SturmTheorem
