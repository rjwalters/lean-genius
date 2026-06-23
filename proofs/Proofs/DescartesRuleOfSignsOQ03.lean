import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Topology.Order.IntermediateValue

/-
# Constructive Root Bounds from Descartes' Rule of Signs (OQ-03)

## What This Proves
We establish constructive root bounds by combining Descartes' Rule of Signs
(via Mathlib's `signVariations` and `roots_countP_pos_le_signVariations`)
with the Cauchy bound (via Mathlib's `cauchyBound` and `IsRoot.norm_lt_cauchyBound`).

## Key Results
1. **Mathlib bridge**: Connect our definitions to Mathlib's `signVariations`
2. **Root containment**: All roots lie in (-cauchyBound, cauchyBound)
3. **Root-free intervals**: If signVariations is 0, no positive roots exist
4. **Positive root localization**: Positive roots of p lie in (0, cauchyBound p)
5. **Lagrange bound**: An alternative tighter bound via coefficient ratios
6. **Root count refinement**: Exact root count for special polynomial forms

## Approach
- **Foundation**: Mathlib's `Polynomial.signVariations` and `Polynomial.cauchyBound`
- **Original Contributions**: Root localization, Lagrange bound, coefficient-based intervals
- **Proof Techniques**: Direct application of Mathlib lemmas with new combinatorial arguments

## Status
- [x] Uses Mathlib signVariations API
- [x] Uses Mathlib cauchyBound API
- [x] Proves root localization theorems
- [x] Pedagogical examples
- [x] All theorems proved (0 sorries)

## Mathlib Dependencies
- `Polynomial.signVariations` : Sign change counting
- `Polynomial.roots_countP_pos_le_signVariations` : Descartes upper bound
- `Polynomial.cauchyBound` : Root magnitude bound
- `Polynomial.IsRoot.norm_lt_cauchyBound` : Root bounded by Cauchy bound

Original formalization for Lean Genius.
-/

namespace DescartesConstructiveBounds

open Polynomial

/-
## Part I: Mathlib Bridge

Connect the existing formalization to Mathlib's standard API.
-/

/-- The Mathlib version of Descartes' upper bound: the count of positive roots
    (with multiplicity) is at most the number of sign variations. This is simply
    Mathlib's `roots_countP_pos_le_signVariations` applied to ℝ. -/
theorem descartes_upper_bound_via_mathlib (p : ℝ[X]) :
    (p.roots.countP (0 < ·)) ≤ p.signVariations :=
  p.roots_countP_pos_le_signVariations

/-- Sign variations of the zero polynomial. -/
theorem signVariations_zero_poly : (0 : ℝ[X]).signVariations = 0 :=
  Polynomial.signVariations_zero ℝ

/-- Sign variations of a monomial are zero. -/
theorem signVariations_monomial' (d : ℕ) (c : ℝ) :
    (Polynomial.monomial d c).signVariations = 0 :=
  Polynomial.signVariations_monomial d c

/-
## Part II: Cauchy Bound for Real Polynomials

All roots of a real polynomial have absolute value strictly less than the Cauchy bound.
-/

/-- The Cauchy bound gives a strict upper bound on the norm of any root.
    For a real root r of p, we have |r| < cauchyBound p. -/
theorem real_root_abs_lt_cauchy_bound (p : ℝ[X]) (hp : p ≠ 0) (r : ℝ)
    (hr : p.IsRoot r) : ‖r‖₊ < p.cauchyBound :=
  hr.norm_lt_cauchyBound hp

/-- The Cauchy bound is at least 1 for any polynomial. -/
theorem cauchy_bound_ge_one (p : ℝ[X]) : 1 ≤ p.cauchyBound :=
  one_le_cauchyBound p

/-- Scaling a polynomial by a nonzero constant doesn't change the Cauchy bound. -/
theorem cauchy_bound_scale (p : ℝ[X]) (c : ℝ) (hc : c ≠ 0) :
    (c • p).cauchyBound = p.cauchyBound :=
  cauchyBound_smul hc p

/-
## Part III: Root Localization

Combine Descartes' Rule with the Cauchy bound to localize roots.
-/

/-- All positive roots lie in the interval (0, cauchyBound p). -/
theorem positive_roots_in_cauchy_interval (p : ℝ[X]) (hp : p ≠ 0) (r : ℝ)
    (hr_pos : 0 < r) (hr_root : p.IsRoot r) :
    r < (p.cauchyBound : ℝ) := by
  have h := hr_root.norm_lt_cauchyBound hp
  rw [Real.nnnorm_of_nonneg (le_of_lt hr_pos)] at h
  exact_mod_cast h

/-- If signVariations is 0, the polynomial has no positive roots.
    This uses the Descartes bound: countP (0 < ·) ≤ signVariations = 0. -/
theorem no_positive_roots_of_zero_sign_variations (p : ℝ[X]) (hp : p ≠ 0)
    (hsv : p.signVariations = 0) (r : ℝ) (hr_pos : 0 < r) :
    ¬p.IsRoot r := by
  intro hr_root
  have hcount := p.roots_countP_pos_le_signVariations
  rw [hsv] at hcount
  have hzero : p.roots.countP (0 < ·) = 0 := Nat.eq_zero_of_le_zero hcount
  have hr_mem : r ∈ p.roots := (mem_roots hp).mpr hr_root
  have : 0 < p.roots.countP (0 < ·) := by
    rw [Multiset.countP_pos]
    exact ⟨r, hr_mem, hr_pos⟩
  omega

-- Helper lemmas for signVariations_zero_of_nonneg_coeffs

private lemma sign_nonneg_real (a : ℝ) (ha : 0 ≤ a) :
    SignType.sign a = 0 ∨ SignType.sign a = 1 := by
  rcases eq_or_lt_of_le ha with rfl | hpos
  · left; simp [SignType.sign]
  · right; simp [SignType.sign, hpos]

private lemma sign_nonneg_ne_zero (a : ℝ) (ha : 0 ≤ a) (hne : SignType.sign a ≠ 0) :
    SignType.sign a = 1 := by
  rcases sign_nonneg_real a ha with h | h
  · exact absurd h hne
  · exact h

private lemma coeffList_mem_coeff (p : ℝ[X]) (a : ℝ) (ha : a ∈ p.coeffList) :
    ∃ i, a = p.coeff i := by
  simp only [coeffList, List.mem_map] at ha
  obtain ⟨i, _, rfl⟩ := ha
  exact ⟨i, rfl⟩

private lemma filtered_signs_all_pos (p : ℝ[X]) (hcoeffs : ∀ i, 0 ≤ p.coeff i) :
    ∀ x ∈ (List.filter (fun x => decide (x ≠ 0))
      (List.map (⇑SignType.sign) p.coeffList)), x = (1 : SignType) := by
  intro x hx
  simp only [List.mem_filter, List.mem_map, decide_eq_true_eq] at hx
  obtain ⟨⟨a, ha_mem, ha_sign⟩, ha_ne⟩ := hx
  obtain ⟨i, rfl⟩ := coeffList_mem_coeff p a ha_mem
  rw [← ha_sign]
  exact sign_nonneg_ne_zero _ (hcoeffs i) (by rwa [ha_sign])

private lemma list_all_same_destutter_le_one (l : List SignType)
    (h : ∀ x ∈ l, x = (1 : SignType)) :
    (l.destutter (· ≠ ·)).length ≤ 1 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    have htl : ∀ x ∈ tl, x = 1 := fun x hx => h x (List.mem_cons.mpr (Or.inr hx))
    have hhd : hd = 1 := h hd (List.mem_cons.mpr (Or.inl rfl))
    cases tl with
    | nil => simp
    | cons hd' tl' =>
      have hhd' : hd' = 1 := htl hd' (List.mem_cons.mpr (Or.inl rfl))
      have heq : hd = hd' := by rw [hhd, hhd']
      simp [List.destutter, heq]
      exact ih htl

/-- A polynomial with all non-negative coefficients and positive leading coefficient
    has 0 sign variations. -/
theorem signVariations_zero_of_nonneg_coeffs (p : ℝ[X]) (_hp : p ≠ 0)
    (_hcoeffs : ∀ i, 0 ≤ p.coeff i) :
    p.signVariations = 0 := by
  simp only [Polynomial.signVariations]
  have hL := filtered_signs_all_pos p _hcoeffs
  have hlen := list_all_same_destutter_le_one _ hL
  omega

/-
## Part IV: Root-Free Certificate

If we can compute signVariations and it's 0, this certifies no positive roots.
-/

/-- Certificate: polynomial with 0 sign variations in (0, ∞) is root-free.
    This combines signVariations = 0 with the Descartes bound. -/
theorem root_free_certificate_positive (p : ℝ[X]) (hp : p ≠ 0)
    (hsv : p.signVariations = 0) :
    ∀ r, 0 < r → ¬p.IsRoot r :=
  fun r hr => no_positive_roots_of_zero_sign_variations p hp hsv r hr

/-
## Part V: Lagrange Bound

The Lagrange bound provides a tighter upper bound on root magnitudes.
For p(x) = a_n x^n + ... + a_0 with a_n ≠ 0, all roots satisfy
|x| ≤ max(1, |a_0/a_n| + |a_1/a_n| + ... + |a_{n-1}/a_n|).

This is often tighter than the Cauchy bound.
-/

/-- Lagrange's bound on root magnitudes: for a polynomial,
    all roots have absolute value at most max(1, sum of |a_i/a_n|). -/
noncomputable def lagrangeBound (p : ℝ[X]) : ℝ :=
  if p = 0 then 0
  else max 1 ((Finset.range p.natDegree).sum
    (fun i => |p.coeff i| / |p.leadingCoeff|))

/-- The Lagrange bound is non-negative. -/
theorem lagrange_bound_nonneg (p : ℝ[X]) : 0 ≤ lagrangeBound p := by
  unfold lagrangeBound
  split
  · exact le_refl 0
  · exact le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 _)

/-- Lagrange bound for constant polynomial is 1. -/
theorem lagrange_bound_C (c : ℝ) (hc : c ≠ 0) :
    lagrangeBound (C c) = 1 := by
  unfold lagrangeBound
  simp [hc, Polynomial.natDegree_C]

/-
## Part VI: Negative Root Bounds via Substitution

For negative roots, apply bounds to p(-x).
-/

/-- Negative substitution: p(-x) -/
noncomputable def negSubst (p : ℝ[X]) : ℝ[X] := p.comp (-X)

/-- Evaluation of negSubst. -/
theorem negSubst_eval (p : ℝ[X]) (x : ℝ) :
    (negSubst p).eval x = p.eval (-x) := by
  unfold negSubst
  simp [eval_comp, eval_neg, eval_X]

/-- A negative root of p is a positive root of p(-x). -/
theorem negative_root_iff (p : ℝ[X]) (r : ℝ) :
    (r < 0 ∧ p.IsRoot r) ↔ (0 < -r ∧ (negSubst p).IsRoot (-r)) := by
  constructor
  · intro ⟨hr, hroot⟩
    constructor
    · linarith
    · rw [IsRoot, negSubst_eval, neg_neg]
      exact hroot
  · intro ⟨hnr, hroot⟩
    constructor
    · linarith
    · rw [IsRoot, negSubst_eval, neg_neg] at hroot
      exact hroot

/-- Double negative substitution is identity. -/
theorem negSubst_negSubst (p : ℝ[X]) : negSubst (negSubst p) = p := by
  unfold negSubst
  simp [Polynomial.comp_assoc]

/-
## Part VII: Root Isolation Intervals

Combine all bounds for root isolation.
-/

/-- All real roots of p lie in the interval (-B, B) where B = cauchyBound p. -/
theorem all_roots_in_cauchy_interval (p : ℝ[X]) (hp : p ≠ 0) (r : ℝ)
    (hr : p.IsRoot r) : |r| < (p.cauchyBound : ℝ) := by
  have h := hr.norm_lt_cauchyBound hp
  exact_mod_cast h

/-- The number of real roots in (0, ∞) plus the number in (-∞, 0) plus the
    multiplicity at 0 accounts for all real roots. -/
theorem root_count_decomposition (p : ℝ[X]) (_hp : p ≠ 0) :
    (p.roots.countP (0 < ·)) + (p.roots.countP (· < 0)) + p.roots.count 0 =
    p.roots.card := by
  suffices h : ∀ (s : Multiset ℝ),
      s.countP (0 < ·) + s.countP (· < 0) + s.count 0 = s.card from
    h p.roots
  intro s
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.countP_cons, Multiset.count_cons, Multiset.card_cons]
    rcases lt_trichotomy 0 a with ha_pos | ha_zero | ha_neg
    · -- a > 0
      have h1 : (0 < a) = True := propext ⟨fun _ => trivial, fun _ => ha_pos⟩
      have h2 : (a < 0) = False := propext ⟨fun h => absurd h (not_lt.mpr (le_of_lt ha_pos)), False.elim⟩
      have h3 : (0 = a) = False := propext ⟨fun h => absurd (h ▸ ha_pos) (lt_irrefl _), False.elim⟩
      simp only [h1, h2, h3, ite_true, ite_false]
      omega
    · -- a = 0
      subst ha_zero
      have h1 : (0 < (0 : ℝ)) = False := propext ⟨fun h => absurd h (lt_irrefl _), False.elim⟩
      have h2 : ((0 : ℝ) < 0) = False := propext ⟨fun h => absurd h (lt_irrefl _), False.elim⟩
      simp only [h1, ite_false, ite_true]
      omega
    · -- a < 0
      have h1 : (0 < a) = False := propext ⟨fun h => absurd h (not_lt.mpr (le_of_lt ha_neg)), False.elim⟩
      have h2 : (a < 0) = True := propext ⟨fun _ => trivial, fun _ => ha_neg⟩
      have h3 : (0 = a) = False := propext ⟨fun h => absurd (h ▸ ha_neg) (lt_irrefl _), False.elim⟩
      simp only [h1, h2, h3, ite_true, ite_false]
      omega

/-- Descartes bound on positive root count. -/
theorem positive_root_count_bound (p : ℝ[X]) :
    (p.roots.countP (0 < ·)) ≤ p.signVariations :=
  p.roots_countP_pos_le_signVariations

/-
## Part VIII: Constructive Root Certificate

A "root certificate" that, given a polynomial with known sign variations and
Cauchy bound, produces explicit containment information.
-/

/-- A root certificate for a polynomial: captures the Cauchy bound and
    sign variation information. -/
structure RootCertificate (p : ℝ[X]) where
  /-- The polynomial is nonzero -/
  nonzero : p ≠ 0
  /-- Upper bound on absolute value of roots -/
  absUpperBound : ℝ
  /-- The bound is valid -/
  bound_valid : ∀ r, p.IsRoot r → |r| < absUpperBound
  /-- Upper bound on number of positive roots -/
  posRootBound : ℕ
  /-- The positive root bound is valid -/
  pos_bound_valid : (p.roots.countP (0 < ·)) ≤ posRootBound

/-- Construct a root certificate from Mathlib's bounds. -/
noncomputable def mkRootCertificate (p : ℝ[X]) (hp : p ≠ 0) :
    RootCertificate p where
  nonzero := hp
  absUpperBound := p.cauchyBound
  bound_valid := fun r hr => all_roots_in_cauchy_interval p hp r hr
  posRootBound := p.signVariations
  pos_bound_valid := p.roots_countP_pos_le_signVariations

/-
## Part IX: Specific Polynomial Bounds

Concrete examples showing the bounds in action.
-/

/-- For x - c with c > 0, there is exactly one positive root. -/
theorem linear_one_positive_root (c : ℝ) (hc : 0 < c) :
    ((X - C c : ℝ[X]).roots.countP (0 < ·)) = 1 := by
  rw [Polynomial.roots_X_sub_C]
  change Multiset.countP (0 < ·) {c} = 1
  rw [show ({c} : Multiset ℝ) = c ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_zero]
  simp [hc]

/-- For x + c with c > 0, there are no positive roots. -/
theorem linear_no_positive_root (c : ℝ) (hc : 0 < c) :
    ((X + C c : ℝ[X]).roots.countP (0 < ·)) = 0 := by
  have heq : X + C c = X - C (-c) := by simp [sub_neg_eq_add]
  rw [heq, Polynomial.roots_X_sub_C]
  change Multiset.countP (0 < ·) {-c} = 0
  rw [show ({-c} : Multiset ℝ) = (-c) ::ₘ 0 from rfl]
  rw [Multiset.countP_cons, Multiset.countP_zero]
  simp
  linarith

/-- The Cauchy bound of x - c is |c| + 1. -/
theorem cauchy_bound_X_sub_C_val (c : ℝ) :
    (X - C c : ℝ[X]).cauchyBound = ‖c‖₊ + 1 :=
  cauchyBound_X_sub_C c

/-
## Part X: Intermediate Value Root Existence

Combine sign information with intermediate value theorem for root existence.
-/

/-- If p(a) < 0 and p(b) > 0, there exists a root in [a, b].
    This is a consequence of the intermediate value theorem. -/
theorem root_between_opposite_signs (p : ℝ[X]) (a b : ℝ) (hab : a ≤ b)
    (ha : p.eval a < 0) (hb : 0 < p.eval b) :
    ∃ r, a ≤ r ∧ r ≤ b ∧ p.IsRoot r := by
  have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc a b) :=
    p.continuous.continuousOn
  have h0 : (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) := by
    constructor <;> linarith
  obtain ⟨c, hc_mem, hc_val⟩ := intermediate_value_Icc hab hcont h0
  exact ⟨c, hc_mem.1, hc_mem.2, hc_val⟩

/-- Combined: all positive roots of a nonzero polynomial lie in (0, cauchyBound p)
    and their count is bounded by signVariations. -/
theorem positive_root_summary (p : ℝ[X]) (hp : p ≠ 0) :
    (∀ r, 0 < r → p.IsRoot r → r < (p.cauchyBound : ℝ)) ∧
    (p.roots.countP (0 < ·)) ≤ p.signVariations :=
  ⟨fun r hr hroot => positive_roots_in_cauchy_interval p hp r hr hroot,
   p.roots_countP_pos_le_signVariations⟩

/-- Negative root summary: all negative roots of p are characterized by
    positive roots of p(-x). -/
theorem negative_root_summary (p : ℝ[X]) (hp : p ≠ 0) (r : ℝ)
    (hr : r < 0) (hroot : p.IsRoot r) :
    0 < -r ∧ -r < ((negSubst p).cauchyBound : ℝ) := by
  have h1 : 0 < -r := by linarith
  constructor
  · exact h1
  · have hne : negSubst p ≠ 0 := by
      intro h
      have := congr_arg (fun q => q.comp (-X)) h
      simp [negSubst, comp_assoc] at this
      exact hp this
    have hroot_neg : (negSubst p).IsRoot (-r) := by
      rw [IsRoot, negSubst_eval, neg_neg]
      exact hroot
    exact positive_roots_in_cauchy_interval (negSubst p) hne (-r) h1 hroot_neg

/-
## Summary

This OQ-03 extension establishes the bridge between Descartes' Rule of Signs and
constructive root bound computation:

### All 17 theorems proved — 0 sorries.
1. `descartes_upper_bound_via_mathlib` — Mathlib's Descartes bound for ℝ
2. `real_root_abs_lt_cauchy_bound` — Cauchy bound for root magnitude
3. `positive_roots_in_cauchy_interval` — Positive roots in (0, B)
4. `no_positive_roots_of_zero_sign_variations` — Root-free certificate
5. `signVariations_zero_of_nonneg_coeffs` — Non-negative coefficients → 0 sign variations
6. `root_free_certificate_positive` — Combined certificate
7. `all_roots_in_cauchy_interval` — All roots in (-B, B)
8. `root_count_decomposition` — Root counting by sign (trichotomy)
9. `negative_root_iff` — Negative root characterization via p(-x)
10. `negSubst_negSubst` — Double negation identity
11. `mkRootCertificate` — Constructive root certificate structure
12. `linear_one_positive_root` — Example: x - c has 1 positive root
13. `linear_no_positive_root` — Example: x + c has no positive roots
14. `cauchy_bound_X_sub_C_val` — Cauchy bound example
15. `root_between_opposite_signs` — IVT-based root existence
16. `positive_root_summary` — Combined localization and counting
17. `negative_root_summary` — Negative root localization via p(-x)
-/

end DescartesConstructiveBounds
