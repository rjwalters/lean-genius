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
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Polynomial

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
  by_cases hr : r = 0
  · simp [signVariations, hr]
  · simp [signVariations, hr]

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
  intro r hr _
  have h : (C c).eval r = 0 := (mem_roots (C_ne_zero.mpr hc)).mp hr
  rw [eval_C] at h
  exact hc h

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
theorem sturmSeq_length_ge_two (p : ℝ[X]) (_hp : p ≠ 0) (hd : 0 < p.natDegree) :
    (sturmSeq p).length ≥ 2 := by
  have hdp : derivative p ≠ 0 := by
    intro h
    have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
    omega
  show (sturmSeqAux p (derivative p) (p.natDegree + 1)).length ≥ 2
  have hunfold : sturmSeqAux p (derivative p) (p.natDegree + 1) =
      p :: sturmSeqAux (derivative p) (-(p % derivative p)) p.natDegree := by
    show (if derivative p = 0 then [p]
          else p :: sturmSeqAux (derivative p) (-(p % derivative p)) p.natDegree) = _
    exact if_neg hdp
  rw [hunfold, List.length_cons]
  have h := sturmSeqAux_ne_empty (derivative p) (-(p % derivative p)) p.natDegree
  omega

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
  simp [sturmVariations, sturmSeq, sturmSeqAux, signVariations,
        derivative_C, hc]

-- ============================================================================
-- § 3a. Squarefree Root Lemma (B.1 of Sturm exact-count proof)
-- ============================================================================

/-- **B.1 (S10 PREP recipe)** — For a squarefree real polynomial `p`,
    at any root of `p` the derivative is non-zero.

    Path: `Squarefree p → p.Separable` (via `PerfectField.separable_iff_squarefree.mpr`,
    using the automatic `[PerfectField ℝ]` from `[CharZero ℝ]`)
    → `∃ a b, a * p + b * p' = 1` (via `Polynomial.separable_def'.mp`)
    → contradiction at the proposed double root. -/
lemma squarefree_root_has_nonzero_derivative
    {p : ℝ[X]} (hp : Squarefree p) {r : ℝ} (hroot : p.eval r = 0) :
    (Polynomial.derivative p).eval r ≠ 0 := by
  have hsep : p.Separable :=
    (PerfectField.separable_iff_squarefree (g := p)).mpr hp
  -- `Separable p` is by definition `IsCoprime p (derivative p)`, i.e.
  -- `∃ a b, a * p + b * (derivative p) = 1`; destructure it directly.
  obtain ⟨a, b, hab⟩ := hsep
  intro hroot'
  have h1 : (a * p + b * Polynomial.derivative p).eval r = (1 : ℝ[X]).eval r :=
    congrArg (Polynomial.eval r) hab
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
        hroot, hroot'] at h1

-- ============================================================================
-- § 4a. Locally-Constant Lemma (Step A of Sturm exact-count proof)
-- ============================================================================

/-- **Step A** of Sturm's theorem. On any closed interval `[x, y]` on which
    every member of the Sturm sequence avoids zero, the Sturm sign-variation
    count is the same at the endpoints.

    Argument: for each `q ∈ sturmSeq p`, `q.eval` is continuous (real
    polynomial evaluation) and nonvanishing on `[x, y]`. By the intermediate
    value theorem, a continuous nonvanishing real function cannot change
    sign, so `q.eval x` and `q.eval y` have the same sign. The
    sign-variation count of a list of fixed-sign reals is determined by the
    signs alone, so `sturmVariations p x = sturmVariations p y`. -/
private lemma sturmVariations_locally_constant
    (p : ℝ[X]) {x y : ℝ} (hxy : x ≤ y)
    (h_no_zero : ∀ q ∈ sturmSeq p, ∀ z ∈ Set.Icc x y, q.eval z ≠ 0) :
    sturmVariations p x = sturmVariations p y := by
  show countSignAlts ((((sturmSeq p).map (fun q => q.eval x)).filter (· ≠ 0)).map
        (fun r => if r > 0 then (1 : ℤ) else -1)) =
       countSignAlts ((((sturmSeq p).map (fun q => q.eval y)).filter (· ≠ 0)).map
        (fun r => if r > 0 then (1 : ℤ) else -1))
  have h_same_sign :
      ∀ q ∈ sturmSeq p, (q.eval x > 0 ↔ q.eval y > 0) := by
    intro q hq
    have hcx : q.eval x ≠ 0 := h_no_zero q hq x ⟨le_refl x, hxy⟩
    have hcy : q.eval y ≠ 0 := h_no_zero q hq y ⟨hxy, le_refl y⟩
    have hcont : ContinuousOn (fun z => q.eval z) (Set.Icc x y) :=
      q.continuous.continuousOn
    by_contra hne
    push_neg at hne
    rcases hne with ⟨hpx, hny⟩ | ⟨hnx, hpy⟩
    · have hyneg : q.eval y < 0 := lt_of_le_of_ne hny hcy
      have h0 : (0 : ℝ) ∈ Set.Icc (q.eval y) (q.eval x) :=
        ⟨le_of_lt hyneg, le_of_lt hpx⟩
      obtain ⟨z, hz, hez⟩ := intermediate_value_Icc' hxy hcont h0
      exact h_no_zero q hq z hz hez
    · have hxneg : q.eval x < 0 := lt_of_le_of_ne hnx hcx
      have h0 : (0 : ℝ) ∈ Set.Icc (q.eval x) (q.eval y) :=
        ⟨le_of_lt hxneg, le_of_lt hpy⟩
      obtain ⟨z, hz, hez⟩ := intermediate_value_Icc hxy hcont h0
      exact h_no_zero q hq z hz hez
  have h_lists_match :
      (((sturmSeq p).map (fun q => q.eval x)).filter (· ≠ 0)).map
          (fun r => if r > 0 then (1 : ℤ) else -1) =
      (((sturmSeq p).map (fun q => q.eval y)).filter (· ≠ 0)).map
          (fun r => if r > 0 then (1 : ℤ) else -1) := by
    have hx_nz : ∀ q ∈ sturmSeq p, q.eval x ≠ 0 :=
      fun q hq => h_no_zero q hq x ⟨le_refl x, hxy⟩
    have hy_nz : ∀ q ∈ sturmSeq p, q.eval y ≠ 0 :=
      fun q hq => h_no_zero q hq y ⟨hxy, le_refl y⟩
    have hfx : ((sturmSeq p).map (fun q => q.eval x)).filter (· ≠ 0)
                = (sturmSeq p).map (fun q => q.eval x) := by
      apply List.filter_eq_self.mpr
      intro r hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact decide_eq_true (hx_nz q hq)
    have hfy : ((sturmSeq p).map (fun q => q.eval y)).filter (· ≠ 0)
                = (sturmSeq p).map (fun q => q.eval y) := by
      apply List.filter_eq_self.mpr
      intro r hr
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
      exact decide_eq_true (hy_nz q hq)
    rw [hfx, hfy, List.map_map, List.map_map]
    apply List.map_congr_left
    intro q hq
    by_cases hxp : q.eval x > 0
    · have hyp : q.eval y > 0 := (h_same_sign q hq).mp hxp
      simp [hxp, hyp]
    · have hyp : ¬ q.eval y > 0 := fun h => hxp ((h_same_sign q hq).mpr h)
      simp [hxp, hyp]
  rw [h_lists_match]

-- ============================================================================
-- § 5. Key Structural Lemma: Mod at a Root
-- ============================================================================

/-- At a root r of q, the remainder p % q equals p(r) when evaluated.
    Proof: p = (p/q) * q + (p%q), evaluating at r where q(r) = 0 gives p(r) = (p%q)(r). -/
theorem mod_eval_at_root (p q : ℝ[X]) (r : ℝ) (hr : q.eval r = 0) :
    (p % q).eval r = p.eval r := by
  have hdiv : q * (p / q) + p % q = p := EuclideanDomain.div_add_mod p q
  have h : (q * (p / q) + p % q).eval r = p.eval r := by rw [hdiv]
  rw [Polynomial.eval_add, Polynomial.eval_mul, hr, zero_mul, zero_add] at h
  exact h

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
  rw [sturm_interior_sign_property _ _ _ hr]
  have hsq : 0 < p₀.eval r * p₀.eval r := mul_self_pos.mpr hp₀
  nlinarith [hsq]

-- ============================================================================
-- § 6. Main Theorem: Exact Root Count
-- ============================================================================

/-- **Axiom: Sturm's Theorem (Exact Count, additive form)**

For a squarefree polynomial p ∈ ℝ[X] and real interval (a, b] with p(a) ≠ 0
and p(b) ≠ 0, the Sturm sign-variation count at a equals the count at b plus
the number of distinct real roots of p in (a, b]:

  σ_p(a) = σ_p(b) + #{roots in (a,b]}

This is logically equivalent to the classical statement
#{roots in (a,b]} = σ_p(a) - σ_p(b) (in ℕ) but also captures the
monotonicity σ_p(b) ≤ σ_p(a). The classical and antitone forms appear as
corollaries below.

The proof proceeds by showing:
1. σ_p is piecewise constant on subintervals avoiding zeros of any Sturm term
2. σ_p decreases by exactly 1 as x passes through each real root of p
3. σ_p is unchanged as x passes through roots of interior Sturm terms

This is Sturm's original theorem (1829). -/
axiom sturm_exact_count_axiom
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    sturmVariations p a = sturmVariations p b + rootsInInterval p a b

theorem sturm_exact_count
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    rootsInInterval p a b = sturmVariations p a - sturmVariations p b := by
  have := sturm_exact_count_axiom p hp hpsc a b hab ha hb
  omega

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
  have := sturm_exact_count_axiom p hp hpsc a b hab ha hb
  omega

/-- **Unique root**: If the Sturm count drops by exactly 1, there is exactly one root. -/
theorem sturm_unique_root
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0)
    (hdiff : sturmVariations p a = sturmVariations p b + 1) :
    rootsInInterval p a b = 1 := by
  have := sturm_exact_count_axiom p hp hpsc a b hab ha hb
  omega

/-- **Two roots**: Sturm count drop of 2 implies exactly 2 distinct roots. -/
theorem sturm_two_roots
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0)
    (hdiff : sturmVariations p a = sturmVariations p b + 2) :
    rootsInInterval p a b = 2 := by
  have := sturm_exact_count_axiom p hp hpsc a b hab ha hb
  omega

/-- **Non-decreasing Sturm count**: rootsInInterval is always ≤ sturmVariations difference.
    This is a weakening of the exact count, following directly from Nat.le_refl. -/
theorem sturm_count_le_variations
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    rootsInInterval p a b ≤ sturmVariations p a - sturmVariations p b := by
  have := sturm_exact_count_axiom p hp hpsc a b hab ha hb
  omega

/-- Sturm's theorem implies the Sturm count is monotone:
    sturmVariations p a ≥ sturmVariations p b whenever a < b and p doesn't vanish at endpoints. -/
theorem sturmVariations_antitone
    (p : ℝ[X]) (hp : p ≠ 0) (hpsc : Squarefree p)
    (a b : ℝ) (hab : a < b)
    (ha : p.eval a ≠ 0) (hb : p.eval b ≠ 0) :
    sturmVariations p b ≤ sturmVariations p a := by
  have := sturm_exact_count_axiom p hp hpsc a b hab ha hb
  omega

-- ============================================================================
-- § 8. Example: Sturm Sequence for a Linear Polynomial
-- ============================================================================

section LinearExample

/- For a linear polynomial p(x) = x - c, the Sturm sequence is [x - c, 1].
   The sign variation at x is 1 if x < c (x - c < 0, 1 > 0: one sign change)
   and 0 if x > c (x - c > 0, 1 > 0: no sign change). -/

variable (c : ℝ)

/-- The derivative of x - c is 1. -/
theorem linear_deriv : derivative (X - C c) = (1 : ℝ[X]) := by
  simp [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C]

/-- The Sturm sequence of x - c is [x - c, 1]:
    p₁ = derivative(x - c) = 1, and (x - c) % 1 = 0 terminating the sequence. -/
theorem sturmSeq_linear : sturmSeq (X - C c) = [X - C c, 1] := by
  have hmod : (X - C c) % (1 : ℝ[X]) = 0 := EuclideanDomain.mod_one _
  simp [sturmSeq, sturmSeqAux, hmod]

/-- For the linear polynomial x - c, the Sturm sign count at x < c equals 1.
    At x < c: evaluate [X-c, 1] to get [x-c, 1]; x-c < 0 and 1 > 0, so 1 sign change. -/
theorem sturm_linear_left (x : ℝ) (hx : x < c) :
    sturmVariations (X - C c) x = 1 := by
  have hxc : x - c < 0 := by linarith
  have hne : x - c ≠ 0 := ne_of_lt hxc
  have hno : ¬ (x - c > 0) := not_lt.mpr hxc.le
  simp [sturmVariations, sturmSeq_linear, signVariations, countSignAlts, hne, hno]

/-- For the linear polynomial x - c, the Sturm sign count at x > c equals 0.
    At x > c: evaluate [X-c, 1] to get [x-c, 1]; x-c > 0 and 1 > 0, so 0 sign changes. -/
theorem sturm_linear_right (x : ℝ) (hx : x > c) :
    sturmVariations (X - C c) x = 0 := by
  have hxc : x - c > 0 := by linarith
  have hne : x - c ≠ 0 := ne_of_gt hxc
  simp [sturmVariations, sturmSeq_linear, signVariations, countSignAlts, hne, hxc]

end LinearExample

-- ============================================================================
-- § 8a. Sturm's Exact Count, Verified for Linear Polynomials (axiom-free)
-- ============================================================================

/-- The roots of `X - C c` in the half-open interval `(a, b]`: exactly one
    (namely `c`) when `a < c ≤ b`, and none otherwise. -/
theorem rootsInInterval_X_sub_C (c a b : ℝ) :
    rootsInInterval (X - C c) a b = if a < c ∧ c ≤ b then 1 else 0 := by
  have hne : (X - C c : ℝ[X]) ≠ 0 := X_sub_C_ne_zero c
  rw [rootsInInterval, if_neg hne, Polynomial.roots_X_sub_C, Multiset.filter_singleton]
  by_cases h : a < c ∧ c ≤ b
  · simp [h]
  · simp [h]

/-- **Sturm's exact count, verified for linear polynomials** (no axiom).

    For `p = X - c`, the additive Sturm identity
    `σ_p(a) = σ_p(b) + #{roots in (a,b]}` holds whenever `a < b`, `a ≠ c` and
    `b ≠ c`. This is a fully machine-checked instance of `sturm_exact_count_axiom`,
    confirming the axiom in the degree-1 base case via the explicit Sturm
    sequence `[X - c, 1]`. -/
theorem sturm_exact_count_linear (c a b : ℝ) (hab : a < b)
    (ha : a ≠ c) (hb : b ≠ c) :
    sturmVariations (X - C c) a =
      sturmVariations (X - C c) b + rootsInInterval (X - C c) a b := by
  rw [rootsInInterval_X_sub_C]
  rcases lt_trichotomy c a with hca | hca | hca
  · -- c < a < b: both endpoints exceed c, both counts 0, no root in (a,b]
    have hva : sturmVariations (X - C c) a = 0 := sturm_linear_right c a hca
    have hvb : sturmVariations (X - C c) b = 0 := sturm_linear_right c b (hca.trans hab)
    have hnr : ¬ (a < c ∧ c ≤ b) := by rintro ⟨h, _⟩; linarith
    rw [hva, hvb, if_neg hnr]
  · exact absurd hca.symm ha
  · -- a < c
    have hva : sturmVariations (X - C c) a = 1 := sturm_linear_left c a hca
    rcases lt_trichotomy c b with hcb | hcb | hcb
    · -- a < c < b: count drops 1 → 0, exactly one root c ∈ (a,b]
      have hvb : sturmVariations (X - C c) b = 0 := sturm_linear_right c b hcb
      have hr : a < c ∧ c ≤ b := ⟨hca, hcb.le⟩
      rw [hva, hvb, if_pos hr]
    · exact absurd hcb.symm hb
    · -- a < b < c: both endpoints below c, both counts 1, no root in (a,b]
      have hvb : sturmVariations (X - C c) b = 1 := sturm_linear_left c b hcb
      have hnr : ¬ (a < c ∧ c ≤ b) := by rintro ⟨_, h⟩; linarith
      rw [hva, hvb, if_neg hnr]

-- ============================================================================
-- § 9. Squarefree Polynomials and the GCD Connection
-- ============================================================================

/- A squarefree polynomial p satisfies gcd(p, p') = constant.
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
          Polynomial.eval_X, Polynomial.eval_C] at hpd
    linarith
  have hsq : (X - C r) * (X - C r) ∣ p := by
    rw [hq]
    exact mul_dvd_mul_left (X - C r) (Polynomial.dvd_iff_isRoot.mpr hqr)
  have hunit : IsUnit (X - C r) := hpsc (X - C r) hsq
  rw [Polynomial.isUnit_iff] at hunit
  obtain ⟨u, _, hu⟩ := hunit
  have hdeg : (X - C r).natDegree = 1 := Polynomial.natDegree_X_sub_C r
  have hcu : (C u).natDegree = 0 := Polynomial.natDegree_C _
  rw [hu] at hcu
  omega

/-- A squarefree polynomial p of degree ≥ 1 cannot satisfy p' = 0.
    (Since p' = 0 would mean p is a constant, contradicting degree ≥ 1.) -/
theorem squarefree_deriv_ne_zero_of_pos_degree (p : ℝ[X]) (_hpsc : Squarefree p)
    (hd : 0 < p.natDegree) : derivative p ≠ 0 := by
  intro h
  have := Polynomial.natDegree_eq_zero_of_derivative_eq_zero h
  omega

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
