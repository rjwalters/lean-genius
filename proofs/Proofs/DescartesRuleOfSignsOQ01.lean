import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue

set_option maxHeartbeats 400000

/-
# Descartes' Rule of Signs — Full Mathlib Formalization (OQ-01)

## What This Proves

This file provides the authoritative formalization of Descartes' Rule of Signs
using Mathlib's native `Polynomial.signVariations` API.

The main result — that the number of positive real roots (counted with multiplicity)
is at most the number of sign variations in the coefficient sequence — is proved
directly from Mathlib with **0 axioms** for the upper bound.

## Mathlib's Formulation

Mathlib uses:
- `Polynomial.signVariations p` — counts sign changes via `List.destutter` on
  the nonzero elements of the coefficient list mapped through `SignType.sign`
- `p.roots_countP_pos_le_signVariations : p.roots.countP (0 < ·) ≤ p.signVariations`

This is Wiedijk's 100 Theorems #100.

## New Contributions

1. **Direct Mathlib bridge**: Upper bound proved with 0 axioms
2. **Sign variation arithmetic**: Behavior under positive-root insertion, negation, scaling
3. **Special polynomial families**: nonneg coefficients, zero sign variations
4. **Negative root formulation**: Framework via p(-x) substitution
5. **Linear polynomial case**: Exact signVariations for X - C c (c > 0)
6. **Parity framework**: Documentation of the open formalization challenge

## Open Problem (Parity Result)

Mathlib contains the UPPER BOUND but NOT the PARITY RESULT:
  signVariations p ≡ p.roots.countP (0 < ·) [MOD 2]

This requires the Fundamental Theorem of Algebra plus analysis of how complex
conjugate pairs and negative roots affect sign variations.

Original formalization for Lean Genius.
-/

namespace DescartesRuleOQ01

open Polynomial

/-
## Part I: The Main Theorem — Zero Axioms Version
-/

/-- **Descartes' Rule of Signs** (from Mathlib — 0 axioms, 0 sorries)

The number of positive real roots of p, counted with multiplicity,
is at most the number of sign variations in the coefficient sequence. -/
theorem descartes_upper_bound (p : ℝ[X]) :
    p.roots.countP (0 < ·) ≤ p.signVariations :=
  p.roots_countP_pos_le_signVariations

/-- The zero polynomial has 0 sign variations. -/
theorem signVariations_zero_poly : (0 : ℝ[X]).signVariations = 0 :=
  Polynomial.signVariations_zero ℝ

/-- Any monomial c·Xⁿ has 0 sign variations (single nonzero coefficient). -/
theorem signVariations_monomial' (d : ℕ) (c : ℝ) :
    (Polynomial.monomial d c).signVariations = 0 :=
  Polynomial.signVariations_monomial d c

/-
## Part II: Sign Variations Under Root Insertion

NOTE: `succ_signVariations_le_X_sub_C_mul` requires r > 0 — only multiplying by
a POSITIVE-root linear factor (X - r with r > 0) necessarily adds a sign variation.
Multiplying by (X + r) for r > 0 (negative root factor) does NOT in general.
-/

/-- Multiplying by (X - r) with r > 0 adds at least one sign variation (requires p ≠ 0). -/
theorem signVariations_increase_by_pos_root (p : ℝ[X]) (r : ℝ) (hr : 0 < r) (hp : p ≠ 0) :
    p.signVariations + 1 ≤ ((X - C r) * p).signVariations :=
  Polynomial.succ_signVariations_le_X_sub_C_mul hr hp

/-- Negating a polynomial preserves sign variations. -/
theorem signVariations_neg_poly (p : ℝ[X]) :
    (-p).signVariations = p.signVariations :=
  Polynomial.signVariations_neg p

/-- Scaling by a nonzero constant preserves sign variations. -/
theorem signVariations_const_mul (p : ℝ[X]) (c : ℝ) (hc : c ≠ 0) :
    (C c * p).signVariations = p.signVariations :=
  Polynomial.signVariations_C_mul p hc

/-
## Part III: Zero Sign Variations — Root-Free Certificate
-/

/-- If p ≠ 0 and signVariations p = 0, then p has no positive roots. -/
theorem no_positive_roots_of_zero_variations (p : ℝ[X]) (hp : p ≠ 0)
    (hsv : p.signVariations = 0) (r : ℝ) (hr : 0 < r) : ¬ p.IsRoot r := by
  intro hroot
  have hmem : r ∈ p.roots := (mem_roots hp).mpr hroot
  have hpos : 0 < p.roots.countP (0 < ·) :=
    Multiset.countP_pos.mpr ⟨r, hmem, hr⟩
  have hbound := descartes_upper_bound p
  omega

/-- A polynomial with all non-negative coefficients has 0 sign variations. -/
theorem nonneg_coeffs_have_zero_variations (p : ℝ[X]) (_hp : p ≠ 0)
    (hcoeffs : ∀ i, 0 ≤ p.coeff i) : p.signVariations = 0 := by
  simp only [Polynomial.signVariations]
  have hL := filtered_signs_all_pos p hcoeffs
  have hlen := list_all_same_destutter_le_one _ hL
  omega
  where
    sign_nonneg_real (a : ℝ) (ha : 0 ≤ a) :
        SignType.sign a = 0 ∨ SignType.sign a = 1 := by
      rcases eq_or_lt_of_le ha with rfl | hpos
      · left; simp [SignType.sign]
      · right; simp [SignType.sign, hpos]
    sign_nonneg_ne_zero (a : ℝ) (ha : 0 ≤ a) (hne : SignType.sign a ≠ 0) :
        SignType.sign a = 1 := by
      rcases sign_nonneg_real a ha with h | h
      · exact absurd h hne
      · exact h
    coeffList_mem_coeff (p : ℝ[X]) (a : ℝ) (ha : a ∈ p.coeffList) :
        ∃ i, a = p.coeff i := by
      simp only [coeffList, List.mem_map] at ha
      obtain ⟨i, _, rfl⟩ := ha
      exact ⟨i, rfl⟩
    filtered_signs_all_pos (p : ℝ[X]) (hcoeffs : ∀ i, 0 ≤ p.coeff i) :
        ∀ x ∈ (List.filter (fun x => decide (x ≠ 0))
          (List.map (⇑SignType.sign) p.coeffList)), x = (1 : SignType) := by
      intro x hx
      simp only [List.mem_filter, List.mem_map, decide_eq_true_eq] at hx
      obtain ⟨⟨a, ha_mem, ha_sign⟩, ha_ne⟩ := hx
      obtain ⟨i, rfl⟩ := coeffList_mem_coeff p a ha_mem
      rw [← ha_sign]
      exact sign_nonneg_ne_zero _ (hcoeffs i) (by rwa [ha_sign])
    list_all_same_destutter_le_one (l : List SignType)
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

/-
## Part IV: Negative Roots — Framework via p(-x)
-/

/-- The polynomial p(-X) via composition with (-X). -/
noncomputable def negSubst (p : ℝ[X]) : ℝ[X] := p.comp (-X)

/-- Evaluation: (negSubst p)(x) = p(-x). -/
theorem negSubst_eval (p : ℝ[X]) (x : ℝ) :
    (negSubst p).eval x = p.eval (-x) := by
  unfold negSubst; simp [eval_comp, eval_neg, eval_X]

/-- Double negSubst is the identity. -/
theorem negSubst_negSubst (p : ℝ[X]) : negSubst (negSubst p) = p := by
  unfold negSubst; simp [comp_assoc]

/-- negSubst preserves nonzero polynomials. -/
theorem negSubst_ne_zero {p : ℝ[X]} (hp : p ≠ 0) : negSubst p ≠ 0 := by
  intro h
  apply hp
  have h2 : p = negSubst (negSubst p) := (negSubst_negSubst p).symm
  rw [h] at h2
  have h3 : negSubst (0 : ℝ[X]) = 0 := by simp [negSubst]
  rw [h3] at h2
  exact h2

/-- A negative root r < 0 of p becomes a positive root -r > 0 of negSubst p. -/
theorem negative_root_iff_positive_of_negSubst (p : ℝ[X]) (r : ℝ) :
    (r < 0 ∧ p.IsRoot r) ↔ (0 < -r ∧ (negSubst p).IsRoot (-r)) := by
  constructor
  · intro ⟨hr, hroot⟩
    exact ⟨neg_pos.mpr hr, by rw [IsRoot, negSubst_eval, neg_neg]; exact hroot⟩
  · intro ⟨hnr, hroot⟩
    exact ⟨neg_of_neg_pos hnr,
           by rw [IsRoot, negSubst_eval, neg_neg] at hroot; exact hroot⟩

/-
## Helper Lemmas for Negative Root Bound
-/

/-- Key divisibility helper: if (X - C r)^m divides p, then (X - C (-r))^m divides negSubst p.
    Proof: negSubst transforms (X - C r) to -(X - C(-r)), so (X - C r)^m becomes
    (-1)^m * (X - C(-r))^m, which is an associate of (X - C(-r))^m. -/
private lemma pow_X_sub_C_dvd_negSubst {r : ℝ} {m : ℕ} {p : ℝ[X]}
    (h : (X - C r : ℝ[X]) ^ m ∣ p) : (X - C (-r) : ℝ[X]) ^ m ∣ negSubst p := by
  obtain ⟨q, rfl⟩ := h
  refine ⟨(-1 : ℝ[X]) ^ m * negSubst q, ?_⟩
  simp only [negSubst, Polynomial.mul_comp, Polynomial.pow_comp]
  -- Show: (X - C r).comp (-X) = -(X - C (-r))
  have hcomp : (X - C r : ℝ[X]).comp (-X) = -(X - C (-r)) := by
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, Polynomial.C_neg]
    abel
  rw [hcomp, neg_pow]
  ring

/-- Root multiplicity is non-decreasing under negSubst: mult of r in p ≤ mult of -r in negSubst p. -/
private lemma rootMult_le_negSubst (p : ℝ[X]) (r : ℝ) :
    p.rootMultiplicity r ≤ (negSubst p).rootMultiplicity (-r) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp only [Polynomial.rootMultiplicity_zero, negSubst, Polynomial.zero_comp,
               Polynomial.rootMultiplicity_zero]
    omega
  · rw [Polynomial.le_rootMultiplicity_iff (negSubst_ne_zero hp)]
    exact pow_X_sub_C_dvd_negSubst (Polynomial.pow_rootMultiplicity_dvd p r)

/-- **Descartes' Rule for Negative Roots** (0 sorries):

The number of negative real roots of p is at most the sign variations of p(-x). -/
theorem descartes_negative_roots (p : ℝ[X]) :
    p.roots.countP (· < 0) ≤ (negSubst p).signVariations := by
  cases eq_or_ne p 0 with
  | inl hp => subst hp; simp [negSubst]
  | inr hp =>
    have hne : negSubst p ≠ 0 := negSubst_ne_zero hp
    -- The map r ↦ -r sends negative roots of p to positive roots of negSubst p
    -- Key: countP (· < 0) on p.roots = countP (0 < ·) on (p.roots.map neg)
    have hstep1 : p.roots.countP (· < 0) = (p.roots.map Neg.neg).countP (0 < ·) := by
      rw [Multiset.countP_eq_card_filter, Multiset.countP_map]
      congr 1
      ext x
      simp [neg_pos]
    -- The mapped multiset is ≤ (negSubst p).roots (count-wise)
    have hstep2 : p.roots.map Neg.neg ≤ (negSubst p).roots := by
      rw [Multiset.le_iff_count]
      intro s
      -- (p.roots.map neg).count s = p.roots.count (-s) [by induction]
      have hcount : (p.roots.map Neg.neg).count s = p.roots.count (-s) := by
        induction p.roots using Multiset.induction_on with
        | empty => simp
        | cons a t ih =>
          rw [Multiset.map_cons, Multiset.count_cons, Multiset.count_cons, ih]
          congr 1
          -- (s = -a) ↔ (-s = a) by negation
          have heq : (s = -a) ↔ (-s = a) := ⟨fun h => by linarith, fun h => by linarith⟩
          simp [heq]
      -- Both counts equal their rootMultiplicities
      rw [hcount]
      simp only [Polynomial.count_roots]
      -- p.rootMultiplicity (-s) ≤ (negSubst p).rootMultiplicity s
      have hle := rootMult_le_negSubst p (-s)
      simpa [neg_neg] using hle
    -- Count inequality from multiset ≤
    have hmap : p.roots.countP (· < 0) ≤ (negSubst p).roots.countP (0 < ·) := by
      rw [hstep1]
      -- countP is monotone in the multiset
      simp only [Multiset.countP_eq_card_filter]
      exact Multiset.card_le_card (Multiset.filter_le_filter _ hstep2)
    exact le_trans hmap (descartes_upper_bound _)

/-
## Part V: Sign Variations for the Linear Polynomial X - C c
-/

/-- The constant polynomial C a has 0 sign variations. -/
theorem signVariations_C_const (a : ℝ) : (C a : ℝ[X]).signVariations = 0 := by
  have : (C a : ℝ[X]) = Polynomial.monomial 0 a := by simp
  rw [this]; exact Polynomial.signVariations_monomial 0 a

/-- The eraseLead of X - C c equals C (-c) (degree-0 polynomial = constant -c).

Proof: eraseLead removes the degree-1 term from X - C c,
leaving only the degree-0 term which is the constant -c. -/
private theorem eraseLead_X_sub_C_eq (c : ℝ) :
    (X - C c : ℝ[X]).eraseLead = C (-c) := by
  ext n
  have hd : (X - C c : ℝ[X]).natDegree = 1 := natDegree_X_sub_C c
  rcases eq_or_ne n 1 with rfl | hn1
  · -- n = 1 = natDegree: eraseLead gives 0, C(-c) gives 0
    rw [← hd, Polynomial.eraseLead_coeff_natDegree]
    simp [Polynomial.coeff_C, one_ne_zero]
  · -- n ≠ 1 = natDegree: eraseLead preserves the coefficient
    have hne_nd : n ≠ (X - C c : ℝ[X]).natDegree := by rw [hd]; exact hn1
    rw [Polynomial.eraseLead_coeff_of_ne n hne_nd]
    rcases Nat.eq_zero_or_pos n with rfl | hn_pos
    · -- n = 0: (X - C c).coeff 0 = -c = (C (-c)).coeff 0
      simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    · -- n ≥ 2: both coefficients are 0
      have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn_pos
      have hlt : (X - C c : ℝ[X]).natDegree < n := by rw [hd]; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, Polynomial.coeff_C, if_neg hn0]

/-- For X - C c with c > 0, signVariations = 1.

Proof:
- Upper bound: from `signVariations_le_eraseLead_succ` and eraseLead = C(-c) has sv = 0
- Lower bound: from `succ_signVariations_le_X_sub_C_mul hc (C 1)` and mul_one -/
theorem signVariations_X_sub_C (c : ℝ) (hc : 0 < c) :
    (X - C c : ℝ[X]).signVariations = 1 := by
  apply le_antisymm
  · -- Upper bound: sv(X - C c) ≤ sv(eraseLead(X - C c)) + 1 = 0 + 1 = 1
    have h := Polynomial.signVariations_le_eraseLead_succ (X - C c)
    rw [eraseLead_X_sub_C_eq, signVariations_C_const] at h
    linarith
  · -- Lower bound: 1 ≤ sv(X - C c) from the positive-root multiplication lemma
    have h := signVariations_increase_by_pos_root (C 1 : ℝ[X]) c hc (by simp)
    rw [show (C 1 : ℝ[X]).signVariations = 0 from signVariations_C_const 1,
        show (X - C c) * C 1 = X - C c from mul_one _, zero_add] at h
    exact h

/-- **Tight Descartes bound for X - C c** (c > 0):
    The bound countP(0 < ·) ≤ signVariations is achieved with equality = 1. -/
theorem descartes_tight_X_sub_C (c : ℝ) (hc : 0 < c) :
    (X - C c : ℝ[X]).roots.countP (0 < ·) = (X - C c : ℝ[X]).signVariations := by
  rw [signVariations_X_sub_C c hc]
  have hne : (X - C c : ℝ[X]) ≠ 0 := X_sub_C_ne_zero c
  -- Upper bound: from Descartes
  have hle : (X - C c : ℝ[X]).roots.countP (0 < ·) ≤ 1 := by
    have := descartes_upper_bound (X - C c)
    rwa [signVariations_X_sub_C c hc] at this
  -- Lower bound: c is a positive root
  have hge : 1 ≤ (X - C c : ℝ[X]).roots.countP (0 < ·) := by
    apply Multiset.countP_pos.mpr
    exact ⟨c, (mem_roots hne).mpr (by simp [IsRoot]), hc⟩
  omega

/-
## Part VI: The Parity Result — Proved in This File (no axiom)

Mathlib has the UPPER BOUND but NOT the PARITY RESULT. This file supplies the
parity result itself: `descartes_parity_proved` (Part IX) establishes it with
0 sorries and 0 axioms, and the public theorem `descartes_parity` (Part X) is
discharged by it. The sketch below records the strategy actually carried out.

**Statement** (theorem `descartes_parity`):
  ∃ k : ℕ, p.roots.countP (0 < ·) + 2 * k = p.signVariations

**Classical proof sketch**:
1. Factor p over ℂ (Fundamental Theorem of Algebra)
2. For each conjugate pair (a ± bi), the quadratic (X² - 2aX + (a²+b²))
   contributes 0 to positive root count and 0 or 2 to sign variations (both even)
3. For each negative real root -r (r > 0), the factor (X + r) contributes
   0 to both (nonneg coefficients, so signVariations = 0)
4. For each positive real root r, (X - r) contributes +1 to both counts
5. Sum: signVariations = (# positive real roots) + 2k

**What the complete proof requires**:
- The key lemma: for r > 0, `signVariations ((X + C r) * p) = signVariations p`
  (negative-root linear factor adds 0 sign variations)
- The quadratic lemma: for complex pairs, signVariations((X²-2aX+b) * p) ≡
  signVariations(p) [MOD 2] when b > a² (complex discriminant)
- The Fundamental Theorem of Algebra to factor into such pieces
These are doable but require ~200 lines of new Mathlib infrastructure.
-/

/-
**Descartes parity** is fully proved in this file — there is no parity axiom.
The proof, `descartes_parity_proved` (Part IX), and the corollaries that depend on
it (`descartes_parity`, `descartes_rule_combined`, `one_sign_variation_one_positive_root`,
`positive_root_count_from_sv`) appear at the end of the file, after the algebraic
infrastructure they require.
-/

/-
## Part VII: Consequences
-/

/-- The Descartes bound for products: countP(p*q) ≤ sv(p) + sv(q). -/
theorem descartes_mul_bound (p q : ℝ[X]) (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).roots.countP (0 < ·) ≤ p.signVariations + q.signVariations := by
  rw [Polynomial.roots_mul (mul_ne_zero hp hq), Multiset.countP_add]
  exact Nat.add_le_add (descartes_upper_bound p) (descartes_upper_bound q)

/-- Zero sign variations implies no positive roots (in the roots multiset). -/
theorem zero_sv_no_positive_roots (p : ℝ[X]) (h : p.signVariations = 0) :
    p.roots.countP (0 < ·) = 0 := by
  have hle := descartes_upper_bound p
  omega

/-
## Summary

This file provides the authoritative Lean 4 formalization of Descartes' Rule of Signs
using Mathlib's native API. The key advantage over the older `DescartesRuleOfSigns.lean`
is that the main upper bound is proved directly from Mathlib with 0 axioms.

**Proved (0 sorries, 0 axioms)** — 27 theorems total (19 original + 8 new in Part VIII):
1. `descartes_upper_bound` — Main Mathlib theorem (the core result)
2. `signVariations_zero_poly`, `signVariations_monomial'` — Base cases
3. `signVariations_increase_by_pos_root` — Positive-root insertion increases sv
4. `signVariations_neg_poly`, `signVariations_const_mul` — Symmetries
5. `no_positive_roots_of_zero_variations` — Zero-sv certificate (requires p ≠ 0)
6. `nonneg_coeffs_have_zero_variations` — Nonneg coefficients → sv = 0
7. `negSubst_eval`, `negSubst_negSubst`, `negSubst_ne_zero` — Substitution tools
8. `negative_root_iff_positive_of_negSubst` — Negative root characterization
9. `signVariations_C_const` — Constants have sv = 0
10. `eraseLead_X_sub_C_eq` — Key computational lemma
11. `signVariations_X_sub_C` — Exact sv for X - C c (c > 0) = 1
12. `descartes_tight_X_sub_C` — Tight Descartes bound for X - C c
13. `descartes_mul_bound` — Product polynomial bound
14. `zero_sv_no_positive_roots` — Zero-sv consequence
15. `descartes_negative_roots` — Negative root bound (0 sorries, via rootMultiplicity algebra)

**Parity corollaries** (0 axioms — `descartes_parity` is now a theorem, see Part X):
16. `descartes_parity` — Parity result (theorem, discharged by `descartes_parity_proved`)
17. `descartes_rule_combined` — Combined form
18. `one_sign_variation_one_positive_root` — 1 sv → 1 positive root
19. `positive_root_count_from_sv` — Root count from sv via parity

**NOTE**: The former `axiom descartes_parity` has been removed. The parity result is
now the theorem `descartes_parity`, discharged by `descartes_parity_proved` (Part IX);
its corollaries are collected in Part X (after the proof they depend on). This file is
now fully axiom-free (0 axioms, 0 sorries).

**Key technique for negative roots (replacing old sorry)**:
The proof uses three private helper lemmas:
- `negSubst_X_sub_C_eq`: negSubst(X - C r) = -(X - C(-r))
- `pow_X_sub_C_dvd_negSubst`: (X-Cr)^m | p → (X-C(-r))^m | negSubst p
- `rootMult_le_negSubst`: rootMultiplicity r p ≤ rootMultiplicity (-r) (negSubst p)
Combined with Multiset.countP_map and Multiset.filter_le_filter for the count argument.

**New in Part VIII** (8 additional theorems):
20. `signVariations_X_add_C_nonneg` — sv(X + Cr) = 0 for r ≥ 0 (negative-root factor)
21. `signVariations_X_sub_C_nonpos` — sv(X - Cr) = 0 for r ≤ 0 (other negative-root form)
22. `descartes_parity_X_sub_C_pos` — Parity confirmed for positive-root linear factor
23. `descartes_parity_X_add_C_pos` — Parity confirmed for negative-root linear factor
24. `descartes_parity_constant` — Parity confirmed for constant polynomials
25. `descartes_parity_monomial` — Parity confirmed for monomials
26. `descartes_parity_when_tight` — Parity when sv = countP (trivially)
27. `descartes_parity_mod2` — Parity reformulated as modular equality

**New in Part IX** (parity proof — 0 sorries):
28. `sv_parity_sign_eq` — Combinatorial parity of sign variations (Stage A)
29. `no_pos_roots_sign_eq` — IVT-based root sign agreement (Stage B)
30. `signVariations_X_mul_eq` — Multiplying by X preserves sign variations
31. `parity_equiv_nonzero_const` — Parity equivalence for nonzero constant term
32. `descartes_parity_nonzero_const` — Parity for nonzero constant term
33. `descartes_parity_proved` — **Full parity proof** (factoring out X^m)
-/

/-
## Part VIII: Special Cases and Parity Infrastructure

These lemmas provide verified special cases of the Descartes parity result
and build toward the eventual proof of `descartes_parity`.

### Proof Strategy for the Full Parity Result

The full parity proof proceeds in two stages:

**Stage 1 — Combinatorial Parity of Sign Sequences**:
For any non-empty list of non-zero SignType elements l:
  `(l.destutter (·≠·)).length % 2 = if l.head = l.last then 0 else 1`
(The number of sign changes is even iff first and last signs agree.)

This is a pure induction on alternating sequences.

**Stage 2 — IVT-based Root Parity**:
For p ≠ 0 with p.coeff 0 ≠ 0:
  countP(0 < ·, p.roots) % 2 = if sign(p.coeff 0) = sign(p.leadingCoeff) then 0 else 1
(The parity of positive roots is determined by the sign of p(0) vs. p(+∞).)

Combining Stage 1 and Stage 2:
  sv(p) % 2 = (sign(p.coeff 0) ≠ sign(p.leadingCoeff)) = countP(0 < ·, p.roots) % 2

The zero-constant-term case (X | p) factors out the X part and reduces to non-zero case.

This approach is ~200 lines and requires infrastructure for:
- The combinatorial alternating sequence lemma
- IVT for polynomial root parity (counting with multiplicity)
- Handling of zero leading/trailing coefficients
-/

/-- For r ≥ 0, X + C r has only non-negative coefficients, hence 0 sign variations.
    This is the key lemma: negative-root linear factors have sv = 0. -/
theorem signVariations_X_add_C_nonneg (r : ℝ) (hr : 0 ≤ r) :
    (X + C r : ℝ[X]).signVariations = 0 := by
  have hne : (X + C r : ℝ[X]) ≠ 0 := by
    intro h
    have : (X + C r : ℝ[X]).coeff 1 = 0 := by simp [h]
    simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C] at this
  apply nonneg_coeffs_have_zero_variations _ hne
  intro i
  match i with
  | 0 => simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C, hr]
  | 1 => norm_num [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
  | i + 2 => simp [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]

/-- For r ≤ 0, X - C r has only non-negative coefficients, hence 0 sign variations. -/
theorem signVariations_X_sub_C_nonpos (r : ℝ) (hr : r ≤ 0) :
    (X - C r : ℝ[X]).signVariations = 0 := by
  apply nonneg_coeffs_have_zero_variations _ (X_sub_C_ne_zero r)
  intro i
  match i with
  | 0 =>
    simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
    linarith
  | 1 => norm_num [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  | i + 2 => simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]

/-- **Parity confirmed**: For the positive-root linear factor (X - C c) with c > 0,
    exactly 1 positive root and exactly 1 sign variation (difference = 0, even). -/
theorem descartes_parity_X_sub_C_pos (c : ℝ) (hc : 0 < c) :
    ∃ k : ℕ, (X - C c : ℝ[X]).roots.countP (0 < ·) + 2 * k =
             (X - C c : ℝ[X]).signVariations :=
  ⟨0, by simp only [Nat.mul_zero, Nat.add_zero]; exact descartes_tight_X_sub_C c hc⟩

/-- **Parity confirmed**: For the negative-root linear factor (X + C r) with r > 0,
    0 positive roots and 0 sign variations (difference = 0, even). -/
theorem descartes_parity_X_add_C_pos (r : ℝ) (hr : 0 < r) :
    ∃ k : ℕ, (X + C r : ℝ[X]).roots.countP (0 < ·) + 2 * k =
             (X + C r : ℝ[X]).signVariations := by
  refine ⟨0, ?_⟩
  simp only [Nat.mul_zero, Nat.add_zero]
  have hsv : (X + C r : ℝ[X]).signVariations = 0 := signVariations_X_add_C_nonneg r hr.le
  rw [hsv, zero_sv_no_positive_roots _ hsv]

/-- **Parity confirmed**: Constant polynomials have 0 positive roots and sv = 0. -/
theorem descartes_parity_constant (a : ℝ) :
    ∃ k : ℕ, (C a : ℝ[X]).roots.countP (0 < ·) + 2 * k =
             (C a : ℝ[X]).signVariations := by
  refine ⟨0, ?_⟩
  simp only [Nat.mul_zero, Nat.add_zero]
  have hsv : (C a : ℝ[X]).signVariations = 0 := signVariations_C_const a
  rw [hsv, zero_sv_no_positive_roots _ hsv]

/-- **Parity confirmed**: Monomials have 0 positive roots (roots only at 0) and sv = 0. -/
theorem descartes_parity_monomial (d : ℕ) (c : ℝ) :
    ∃ k : ℕ, (monomial d c : ℝ[X]).roots.countP (0 < ·) + 2 * k =
             (monomial d c : ℝ[X]).signVariations := by
  refine ⟨0, ?_⟩
  simp only [Nat.mul_zero, Nat.add_zero]
  have hsv : (monomial d c : ℝ[X]).signVariations = 0 := signVariations_monomial' d c
  rw [hsv, zero_sv_no_positive_roots _ hsv]

/-- **Parity confirmed**: When the Descartes bound is tight (sv = countP),
    parity holds trivially with k = 0. -/
theorem descartes_parity_when_tight (p : ℝ[X])
    (h : p.roots.countP (0 < ·) = p.signVariations) :
    ∃ k : ℕ, p.roots.countP (0 < ·) + 2 * k = p.signVariations :=
  ⟨0, by simp [h]⟩

/-- **Parity reformulation**: The parity result is equivalent to saying sv and countP
    have the same remainder mod 2. -/
theorem descartes_parity_mod2 (p : ℝ[X])
    (h : ∃ k : ℕ, p.roots.countP (0 < ·) + 2 * k = p.signVariations) :
    p.roots.countP (0 < ·) % 2 = p.signVariations % 2 := by
  obtain ⟨k, hk⟩ := h
  omega

/-
## Part IX: Toward the Full Parity Proof

This section contains the algebraic infrastructure needed to prove `descartes_parity`
without appealing to the axiom. The proof proceeds in two stages:

**Stage A — Combinatorial**: sv(p) % 2 = (sign(p.coeff 0) ≠ sign(p.leadingCoeff))
  The signVariations definition is:
    sv(p) = (coeffList.map sign |>.filter (·≠0) |>.destutter (·≠·)).length - 1
  For an alternating list over {neg, pos}, (length-1) is even iff first = last element.
  First element = sign(p.coeff 0) (when p.coeff 0 ≠ 0), last = sign(p.leadingCoeff).

**Stage B — IVT**: countP(0<·) % 2 = (sign(p.coeff 0) ≠ sign(p.leadingCoeff))
  If sign(p.coeff 0) ≠ sign(p.leadingCoeff), IVT gives a root in (0,∞).
  Inductive argument on positive roots shows parity matches sign mismatch.

**Main proof**: sv % 2 = countP % 2, so sv - countP is even, giving ∃ k, countP + 2k = sv.
-/

/-- The degree-0 coefficient of a product equals the product of degree-0 coefficients. -/
private lemma coeff_zero_mul_eq (p q : ℝ[X]) : (p * q).coeff 0 = p.coeff 0 * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]

/-- When multiplying by (X - C r), the constant coefficient becomes -r times the original. -/
private lemma coeff_zero_X_sub_C_mul (r : ℝ) (q : ℝ[X]) :
    ((X - C r) * q).coeff 0 = -r * q.coeff 0 := by
  rw [coeff_zero_mul_eq]
  simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]

/-- The leading coefficient of (X - C r) * q equals the leading coefficient of q. -/
private lemma leadingCoeff_X_sub_C_factor (r : ℝ) (q : ℝ[X]) :
    ((X - C r) * q).leadingCoeff = q.leadingCoeff := by
  rw [Polynomial.leadingCoeff_mul, (Polynomial.monic_X_sub_C r).leadingCoeff, one_mul]

/-- Factoring out a positive root increases the positive root count by exactly 1. -/
private lemma roots_countP_X_sub_C (r : ℝ) (q : ℝ[X]) (hq : q ≠ 0) (hr : 0 < r) :
    ((X - C r) * q).roots.countP (0 < ·) = q.roots.countP (0 < ·) + 1 := by
  have hmul : (X - C r) * q ≠ 0 := mul_ne_zero (Polynomial.X_sub_C_ne_zero r) hq
  rw [Polynomial.roots_mul hmul, Polynomial.roots_X_sub_C, Multiset.countP_add]
  have hone : ({r} : Multiset ℝ).countP (fun x => 0 < x) = 1 := by
    rw [show ({r} : Multiset ℝ) = r ::ₘ 0 from rfl, Multiset.countP_cons]
    simp [hr]
  rw [hone]; omega

/-- For r > 0 and a ≠ 0: sign(-r * a) ≠ sign(a).
    Multiplying by a negative scalar flips the sign. -/
private lemma signType_neg_pos_mul_ne (r : ℝ) (a : ℝ) (hr : 0 < r) (ha : a ≠ 0) :
    SignType.sign (-r * a) ≠ SignType.sign a := by
  have hrn : -r < 0 := neg_lt_zero.mpr hr
  rcases lt_or_gt_of_ne ha with ha | ha
  · -- a < 0: sign(a) = neg, sign(-r * a) = pos (neg × neg = pos)
    have hprod : 0 < -r * a := mul_pos_of_neg_of_neg hrn ha
    rw [sign_neg ha, sign_pos hprod]
    decide
  · -- a > 0: sign(a) = pos, sign(-r * a) = neg (neg × pos = neg)
    have hprod : -r * a < 0 := mul_neg_of_neg_of_pos hrn ha
    rw [sign_pos ha, sign_neg hprod]
    decide

/-- eraseLead preserves the degree-0 coefficient for polynomials of degree ≥ 1. -/
private lemma eraseLead_coeff_zero' (p : ℝ[X]) (hd : 0 < p.natDegree) :
    p.eraseLead.coeff 0 = p.coeff 0 := by
  rw [Polynomial.eraseLead_coeff, if_neg (by omega)]

/-- eraseLead of a polynomial with nonzero constant term and degree ≥ 1 is nonzero. -/
private lemma eraseLead_ne_zero_of_coeff_zero_ne' (p : ℝ[X]) (hc0 : p.coeff 0 ≠ 0)
    (hd : 0 < p.natDegree) : p.eraseLead ≠ 0 := by
  intro h
  have : p.eraseLead.coeff 0 = 0 := by simp [h]
  rw [eraseLead_coeff_zero' p hd] at this
  exact hc0 this

/-- The sign of a nonzero real number is nonzero. -/
private lemma sign_ne_zero_of_ne_zero' {a : ℝ} (ha : a ≠ 0) : SignType.sign a ≠ 0 := by
  rcases lt_or_gt_of_ne ha with h | h
  · simp [sign_neg h]
  · simp [sign_pos h]

/-- **Stage A** (Combinatorial — key for parity proof):
    The parity of signVariations is determined by whether the signs of the constant
    term and leading coefficient agree.

    Proved by strong induction on support.card using the eraseLead recursive formula. -/
private lemma sv_parity_sign_eq (p : ℝ[X]) (hp : p ≠ 0) (hc0 : p.coeff 0 ≠ 0) :
    p.signVariations % 2 =
      if SignType.sign (p.coeff 0) = SignType.sign p.leadingCoeff then 0 else 1 := by
  -- Strong induction on support.card
  suffices ∀ (n : ℕ) (q : ℝ[X]), q.support.card ≤ n → q ≠ 0 → q.coeff 0 ≠ 0 →
      q.signVariations % 2 =
        if SignType.sign (q.coeff 0) = SignType.sign q.leadingCoeff then 0 else 1 by
    exact this p.support.card p le_rfl hp hc0
  intro n
  induction n with
  | zero =>
    intro q hqn hq _
    exfalso; apply hq
    rw [Nat.le_zero] at hqn
    rwa [Finset.card_eq_zero, Polynomial.support_eq_empty] at hqn
  | succ n ih =>
    intro q hqn hq hqc0
    rcases Nat.eq_zero_or_pos q.natDegree with hd0 | hd_pos
    · -- Degree 0: constant polynomial
      have : q.coeff 0 = q.leadingCoeff := by rw [Polynomial.leadingCoeff, hd0]
      have hsv : q.signVariations = 0 := by
        rw [eq_C_of_natDegree_eq_zero hd0]; exact signVariations_monomial 0 _
      simp [hsv, this]
    · -- Degree ≥ 1: recursive formula via eraseLead
      have hel_ne : q.eraseLead ≠ 0 := eraseLead_ne_zero_of_coeff_zero_ne' q hqc0 hd_pos
      have hel_c0 : q.eraseLead.coeff 0 ≠ 0 := by
        rwa [eraseLead_coeff_zero' q hd_pos]
      have hel_card_lt : q.eraseLead.support.card < q.support.card :=
        eraseLead_support_card_lt hq
      -- IH for eraseLead
      have hih := ih q.eraseLead (by omega) hel_ne hel_c0
      -- IH gives: sv(eraseLead q) % 2 = if a = b then 0 else 1
      rw [eraseLead_coeff_zero' q hd_pos] at hih
      -- Recursive formula (ite condition: sign(leadingCoeff) = -sign(eraseLead.leadingCoeff))
      rw [signVariations_eq_eraseLead_add_ite (P := q) hq, Nat.add_mod, hih]
      -- Case analysis: all three signs ∈ {neg, pos} (nonzero)
      have ha : SignType.sign (q.coeff 0) ≠ 0 := sign_ne_zero_of_ne_zero' hqc0
      have hb : SignType.sign q.eraseLead.leadingCoeff ≠ 0 :=
        sign_ne_zero_of_ne_zero' (leadingCoeff_ne_zero.mpr hel_ne)
      have hc : SignType.sign q.leadingCoeff ≠ 0 :=
        sign_ne_zero_of_ne_zero' (leadingCoeff_ne_zero.mpr hq)
      set a := SignType.sign (q.coeff 0)
      set b := SignType.sign q.eraseLead.leadingCoeff
      set c := SignType.sign q.leadingCoeff
      clear_value a b c
      cases a <;> cases b <;> cases c <;> revert ha hb hc <;> decide

/-- Helper: sum of lower-order terms is bounded by R^(d-1) times the sum of |coefficients|. -/
private lemma lower_bound' (p : ℝ[X]) (R : ℝ) (hR : 1 ≤ R)
    (hd : 0 < p.natDegree) :
    |∑ i ∈ Finset.range p.natDegree, p.coeff i * R ^ i| ≤
      R ^ (p.natDegree - 1) *
        (Finset.range p.natDegree).sum (fun i => |p.coeff i|) := by
  calc |∑ i ∈ Finset.range p.natDegree, p.coeff i * R ^ i|
    ≤ ∑ i ∈ Finset.range p.natDegree, |p.coeff i * R ^ i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range p.natDegree, (|p.coeff i| * R ^ i) := by
        congr 1; ext i
        rw [abs_mul, abs_of_nonneg (pow_nonneg (le_trans zero_le_one hR) i)]
    _ ≤ ∑ i ∈ Finset.range p.natDegree, (|p.coeff i| * R ^ (p.natDegree - 1)) := by
        apply Finset.sum_le_sum; intro i hi
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        apply pow_le_pow_right₀ hR
        exact Nat.lt_iff_le_pred hd |>.mp (Finset.mem_range.mp hi)
    _ = R ^ (p.natDegree - 1) *
          (Finset.range p.natDegree).sum (fun i => |p.coeff i|) := by
        rw [← Finset.sum_mul]; ring

/-- For nonzero p, there exists R > 0 where p(R) has the same sign as leadingCoeff. -/
private theorem exists_eval_same_sign' (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ 0 < p.eval R * p.leadingCoeff := by
  rcases Nat.eq_zero_or_pos p.natDegree with hd0 | hd_pos
  · -- Degree 0: constant
    use 1, one_pos
    have hC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hd0
    have hne : p.coeff 0 ≠ 0 := fun h => hp (by rw [hC, h, map_zero])
    rw [hC, eval_C, leadingCoeff_C]
    exact mul_self_pos.mpr hne
  · -- Degree ≥ 1
    set d := p.natDegree
    set c := p.leadingCoeff
    have hc_ne : c ≠ 0 := leadingCoeff_ne_zero.mpr hp
    have hc_pos : 0 < |c| := abs_pos.mpr hc_ne
    set S := (Finset.range d).sum (fun i => |p.coeff i|)
    have hS_nn : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    -- Choose R so that |c| * R > S
    set R := max 2 (S / |c| + 2) with hR_def
    have hR_pos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
    have hR_ge_1 : (1 : ℝ) ≤ R := le_trans one_le_two (le_max_left _ _)
    -- Key dominance: |c| * R > S
    have hdom : S < |c| * R := by
      calc S = |c| * (S / |c|) := by field_simp
        _ < |c| * (S / |c| + 2) := by nlinarith
        _ ≤ |c| * R := mul_le_mul_of_nonneg_left (le_max_right _ _) hc_pos.le
    -- Bound lower-order terms
    have hbound := lower_bound' p R hR_ge_1 hd_pos
    -- Leading term dominates
    have hR_d_split : R ^ d = R * R ^ (d - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hlead : R ^ (d - 1) * S < |c| * R ^ d := by
      rw [hR_d_split]
      nlinarith [pow_pos hR_pos (d - 1)]
    -- Decompose p.eval R
    have heval : p.eval R = p.coeff d * R ^ d +
        ∑ i ∈ Finset.range d, p.coeff i * R ^ i := by
      rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ]
      ring
    have hc_eq : p.coeff d = c := Polynomial.coeff_natDegree
    rw [hc_eq] at heval
    set L := ∑ i ∈ Finset.range d, p.coeff i * R ^ i
    -- |L| < |c| * R^d
    have hL_bound : |L| < |c| * R ^ d := by
      calc |L| ≤ R ^ (d - 1) * S := hbound
        _ < |c| * R ^ d := hlead
    -- (c * R^d + L) * c > 0
    have hLc_bound : |L * c| < c ^ 2 * R ^ d := by
      rw [abs_mul]
      have : |L| * |c| < |c| * R ^ d * |c| := by nlinarith
      calc |L| * |c| < |c| * R ^ d * |c| := this
        _ = c ^ 2 * R ^ d := by rw [← sq_abs]; ring
    have h_csq : 0 < c ^ 2 * R ^ d := by positivity
    have h_lc_lower : -(c ^ 2 * R ^ d) < L * c := neg_lt_of_abs_lt hLc_bound
    use R, hR_pos
    rw [heval]
    have : (c * R ^ d + L) * c = c ^ 2 * R ^ d + L * c := by ring
    linarith

/-- **Stage B** (IVT — key for parity proof):
    If p has no positive real roots, then sign(p.coeff 0) = sign(p.leadingCoeff).

    Proved using IVT: if signs differ, p is continuous with p(0) and p(+∞) having
    opposite signs, forcing a root in (0, ∞). -/
private lemma no_pos_roots_sign_eq (p : ℝ[X]) (hp : p ≠ 0) (hc0 : p.coeff 0 ≠ 0)
    (hnr : p.roots.countP (0 < ·) = 0) :
    SignType.sign (p.coeff 0) = SignType.sign p.leadingCoeff := by
  by_contra h_ne
  -- Get R > 0 where p.eval R has the same sign as leadingCoeff
  obtain ⟨R, hR_pos, hR_sign⟩ := exists_eval_same_sign' p hp
  -- p.eval 0 = p.coeff 0
  have heval0 : p.eval 0 = p.coeff 0 := (Polynomial.coeff_zero_eq_eval_zero p).symm
  -- p.eval 0 * p.leadingCoeff < 0 (signs differ)
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have h_neg : p.eval 0 * p.leadingCoeff < 0 := by
    rw [heval0]
    rcases lt_or_gt_of_ne hc0 with hc0_neg | hc0_pos <;>
    rcases lt_or_gt_of_ne hlc with hlc_neg | hlc_pos
    · exfalso; apply h_ne; simp [sign_neg hc0_neg, sign_neg hlc_neg]
    · exact mul_neg_of_neg_of_pos hc0_neg hlc_pos
    · exact mul_neg_of_pos_of_neg hc0_pos hlc_neg
    · exfalso; apply h_ne; simp [sign_pos hc0_pos, sign_pos hlc_pos]
  -- p.eval 0 and p.eval R have opposite signs → IVT gives a root
  rcases lt_or_gt_of_ne (show p.eval 0 ≠ 0 by rwa [heval0]) with heval0_neg | heval0_pos
  · -- p.eval 0 < 0, so p.eval R > 0
    have hR_pos' : 0 < p.eval R := by nlinarith
    have hcont : ContinuousOn (fun x => p.eval x) (Set.Icc 0 R) :=
      p.continuous.continuousOn
    have h0_mem : (0 : ℝ) ∈ Set.Icc (p.eval 0) (p.eval R) := by
      constructor <;> linarith
    obtain ⟨r, ⟨hr_lo, hr_hi⟩, hr_root⟩ :=
      intermediate_value_Icc hR_pos.le hcont h0_mem
    have hr_pos : 0 < r := by
      rcases eq_or_lt_of_le hr_lo with rfl | h
      · linarith [hr_root ▸ heval0_neg]
      · exact h
    have hr_mem : r ∈ p.roots := (mem_roots hp).mpr hr_root
    have : 0 < p.roots.countP (0 < ·) :=
      Multiset.countP_pos.mpr ⟨r, hr_mem, hr_pos⟩
    omega
  · -- p.eval 0 > 0, so p.eval R < 0
    have hR_neg : p.eval R < 0 := by nlinarith
    -- Use -p: continuous, opposite signs, same roots
    have hcont : ContinuousOn (fun x => -(p.eval x)) (Set.Icc 0 R) :=
      p.continuous.continuousOn.neg
    have h0_mem : (0 : ℝ) ∈ Set.Icc (-(p.eval 0)) (-(p.eval R)) := by
      constructor <;> linarith
    obtain ⟨r, ⟨hr_lo, hr_hi⟩, hr_root⟩ :=
      intermediate_value_Icc hR_pos.le hcont h0_mem
    have hr_pos : 0 < r := by
      rcases eq_or_lt_of_le hr_lo with rfl | h
      · simp at hr_root; linarith
      · exact h
    have hr_is_root : p.IsRoot r := by rw [IsRoot]; linarith
    have hr_mem : r ∈ p.roots := (mem_roots hp).mpr hr_is_root
    have : 0 < p.roots.countP (0 < ·) :=
      Multiset.countP_pos.mpr ⟨r, hr_mem, hr_pos⟩
    omega

/-- The signVariations of (X * p) equals the signVariations of p.
    Multiplying by X shifts all coefficients up by 1, prepending a 0 constant term.
    Since zeros are filtered from the sign sequence, sv is unchanged.

    Proof: by induction on p.support.card using the eraseLead recursive formula.
    Key insight: eraseLead(X * p) = X * eraseLead(p) and leadingCoeff(X * p) = leadingCoeff(p). -/
private lemma signVariations_X_mul_eq (p : ℝ[X]) :
    (Polynomial.X * p).signVariations = p.signVariations := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · -- Induction on support.card
    suffices ∀ (n : ℕ) (q : ℝ[X]), q.support.card ≤ n → q ≠ 0 →
        (X * q).signVariations = q.signVariations by
      exact this p.support.card p le_rfl hp
    intro n
    induction n with
    | zero =>
      intro q hq_card hq
      exfalso; apply hq
      rw [Nat.le_zero] at hq_card
      rwa [Finset.card_eq_zero, Polynomial.support_eq_empty] at hq_card
    | succ n ih =>
      intro q hq_card hq
      -- Base: q is a monomial (support.card = 1)
      rcases Nat.eq_zero_or_pos q.natDegree with hd0 | hd_pos
      · -- Degree 0: q = C a, X * q = C a * X = monomial 1 a
        have hq_const : q = C (q.coeff 0) := eq_C_of_natDegree_eq_zero hd0
        rw [hq_const,
          show (X : ℝ[X]) * C (q.coeff 0) = monomial 1 (q.coeff 0) by
            rw [mul_comm, ← pow_one (X : ℝ[X]), Polynomial.C_mul_X_pow_eq_monomial],
          signVariations_monomial, signVariations_C_const]
      · -- Degree ≥ 1: use recursive formula via eraseLead
        have hXq : X * q ≠ 0 := mul_ne_zero X_ne_zero hq
        -- leadingCoeff(X * q) = leadingCoeff(q)
        have hlc : (X * q).leadingCoeff = q.leadingCoeff := by
          rw [leadingCoeff_mul, leadingCoeff_X, one_mul]
        -- eraseLead(X * q) = X * eraseLead(q)
        have hel_eq : (X * q).eraseLead = X * q.eraseLead := by
          ext n
          rcases eq_or_ne n (X * q).natDegree with rfl | hn
          · -- n = natDegree(X * q): both sides are 0
            rw [eraseLead_coeff_natDegree]
            have hnd : (X * q).natDegree = q.natDegree + 1 := by
              rw [natDegree_mul X_ne_zero hq, natDegree_X]; omega
            rw [hnd, coeff_X_mul, eraseLead_coeff_natDegree]
          · -- n ≠ natDegree(X * q): eraseLead preserves
            rw [Polynomial.eraseLead_coeff, if_neg hn]
            rcases n with _ | n
            · -- n = 0: (X * q).coeff 0 = 0, (X * eraseLead q).coeff 0 = 0
              simp [coeff_X_mul_zero]
            · -- n = m + 1: both shift by 1
              simp only [coeff_X_mul]
              rw [Polynomial.eraseLead_coeff, if_neg]
              intro hn'
              apply hn
              rw [natDegree_mul X_ne_zero hq, natDegree_X]
              omega
        -- eraseLead(q) is nonzero when degree ≥ 1 (has lower-degree terms)
        -- This isn't necessarily true... eraseLead q could be 0 if q is a monomial
        -- But we handled degree 0 above, so q has degree ≥ 1
        -- For q with exactly 1 support element (monomial), support.card = 1 but natDegree could be > 0
        -- In that case, eraseLead q = 0
        -- Recursive formula: sv(X * q) = sv(eraseLead(X * q)) + ite(...)
        rw [signVariations_eq_eraseLead_add_ite (P := X * q) hXq]
        rw [signVariations_eq_eraseLead_add_ite (P := q) hq]
        rw [hel_eq, hlc]
        -- Need: eraseLead(X * q) ≠ 0 ↔ eraseLead(q) ≠ 0
        rcases eq_or_ne q.eraseLead 0 with hel0 | hel_ne
        · -- eraseLead q = 0: q is a monomial of degree ≥ 1
          simp [hel0]
        · -- eraseLead q ≠ 0: align the ite conditions, then reduce to the IH
          have hlc_el : (X * q.eraseLead).leadingCoeff = q.eraseLead.leadingCoeff := by
            rw [leadingCoeff_mul, leadingCoeff_X, one_mul]
          rw [hlc_el]
          -- Apply IH: sv(X * eraseLead q) = sv(eraseLead q)
          have hel_card : q.eraseLead.support.card < q.support.card :=
            eraseLead_support_card_lt hq
          congr 1
          exact ih q.eraseLead (by omega) hel_ne

/-- **Parity equivalence** (core): For p ≠ 0 with p.coeff 0 ≠ 0,
    countP(0<·) ≡ signVariations [mod 2].
    Proved by strong induction on natDegree. -/
private theorem parity_equiv_nonzero_const (p : ℝ[X]) (hp : p ≠ 0) (hc0 : p.coeff 0 ≠ 0) :
    p.roots.countP (0 < ·) % 2 = p.signVariations % 2 := by
  -- Wrap in a universally quantified statement for strong induction
  suffices ∀ (n : ℕ) (q : ℝ[X]), q.natDegree ≤ n → q ≠ 0 → q.coeff 0 ≠ 0 →
      q.roots.countP (0 < ·) % 2 = q.signVariations % 2 by
    exact this p.natDegree p (le_refl _) hp hc0
  intro n
  induction n with
  | zero =>
    intro q hqn hq hqc0
    -- natDegree q = 0: q is a nonzero constant
    have hqd0 : q.natDegree = 0 := Nat.eq_zero_of_le_zero hqn
    -- Nonzero constant has no positive roots and sv = 0
    have hpos_zero : q.roots.countP (0 < ·) = 0 := by
      apply Nat.eq_zero_of_le_zero
      calc q.roots.countP (0 < ·) ≤ q.signVariations := descartes_upper_bound q
        _ = 0 := by
          have hqC : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hqd0
          rw [hqC]; exact signVariations_C_const (q.coeff 0)
    have hsv_zero : q.signVariations = 0 := by
      have hqC : q = C (q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hqd0
      rw [hqC]; exact signVariations_C_const (q.coeff 0)
    simp [hpos_zero, hsv_zero]
  | succ n ih =>
    intro q hqn hq hqc0
    -- Check whether q has any positive roots
    by_cases hpos : q.roots.countP (0 < ·) = 0
    · -- No positive roots: use IVT helper
      rw [hpos, Nat.zero_mod]
      have hsign : SignType.sign (q.coeff 0) = SignType.sign q.leadingCoeff :=
        no_pos_roots_sign_eq q hq hqc0 hpos
      rw [sv_parity_sign_eq q hq hqc0, if_pos hsign]
    · -- Has positive roots
      have hpos' : 0 < q.roots.countP (0 < ·) := Nat.pos_of_ne_zero hpos
      obtain ⟨r, hr_mem, hr_pos⟩ := Multiset.countP_pos.mp hpos'
      have hr_root : q.IsRoot r := (Polynomial.mem_roots hq).mp hr_mem
      have hr_dvd : (X - C r) ∣ q := Polynomial.dvd_iff_isRoot.mpr hr_root
      -- Factor: q = (X - C r) * s
      obtain ⟨s, hqs⟩ := hr_dvd
      -- s ≠ 0
      have hs : s ≠ 0 := by
        intro h
        simp [h] at hqs
        exact hq hqs
      -- s has degree ≤ n (since natDegree q ≤ n+1 and q = (X-Cr)*s)
      have hdeg_q : q.natDegree = s.natDegree + 1 := by
        rw [hqs, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hs,
          Polynomial.natDegree_X_sub_C]
        omega
      have hdeg : s.natDegree ≤ n := by omega
      -- s.coeff 0 ≠ 0
      have hsc0 : s.coeff 0 ≠ 0 := by
        have : q.coeff 0 = -r * s.coeff 0 := by
          rw [hqs]; exact coeff_zero_X_sub_C_mul r s
        intro h
        simp [h] at this
        exact hqc0 this
      -- Apply IH to s
      have hs_par : s.roots.countP (0 < ·) % 2 = s.signVariations % 2 :=
        ih s hdeg hs hsc0
      -- Root count: q.countP = s.countP + 1
      have hcount : q.roots.countP (0 < ·) = s.roots.countP (0 < ·) + 1 := by
        rw [hqs]; exact roots_countP_X_sub_C r s hs hr_pos
      -- leadingCoeff: q = s (after factoring)
      have hlc : q.leadingCoeff = s.leadingCoeff := by
        rw [hqs]; exact leadingCoeff_X_sub_C_factor r s
      -- sign(q.coeff 0) ≠ sign(s.coeff 0) (since q.coeff 0 = -r * s.coeff 0, r > 0)
      have hcoeff_sign : SignType.sign (q.coeff 0) ≠ SignType.sign (s.coeff 0) := by
        rw [hqs, coeff_zero_X_sub_C_mul]
        exact signType_neg_pos_mul_ne r (s.coeff 0) hr_pos hsc0
      -- sv parities: q and s have different sv parities
      have hsv_q : q.signVariations % 2 =
          if SignType.sign (q.coeff 0) = SignType.sign q.leadingCoeff then 0 else 1 :=
        sv_parity_sign_eq q hq hqc0
      have hsv_s : s.signVariations % 2 =
          if SignType.sign (s.coeff 0) = SignType.sign s.leadingCoeff then 0 else 1 :=
        sv_parity_sign_eq s hs hsc0
      -- Rewrite using common leadingCoeff
      rw [hlc] at hsv_q
      -- Since sign(q.coeff 0) ≠ sign(s.coeff 0), the if-conditions are opposite
      have hsv_par_flip : q.signVariations % 2 = (s.signVariations % 2 + 1) % 2 := by
        have ha : SignType.sign (q.coeff 0) ≠ 0 := sign_ne_zero_of_ne_zero' hqc0
        have hb : SignType.sign (s.coeff 0) ≠ 0 := sign_ne_zero_of_ne_zero' hsc0
        have hc : SignType.sign s.leadingCoeff ≠ 0 :=
          sign_ne_zero_of_ne_zero' (leadingCoeff_ne_zero.mpr hs)
        rw [hsv_q, hsv_s]
        set a := SignType.sign (q.coeff 0)
        set b := SignType.sign (s.coeff 0)
        set c := SignType.sign s.leadingCoeff
        clear_value a b c
        cases a <;> cases b <;> cases c <;> revert ha hb hc hcoeff_sign <;> decide
      -- Combine all
      rw [hcount, Nat.add_mod, hs_par, hsv_par_flip]

/-- **Descartes Parity (proved)**: For p ≠ 0 with p.coeff 0 ≠ 0,
    the positive root count and signVariations have the same parity. -/
private theorem descartes_parity_nonzero_const (p : ℝ[X]) (hp : p ≠ 0) (hc0 : p.coeff 0 ≠ 0) :
    ∃ k : ℕ, p.roots.countP (0 < ·) + 2 * k = p.signVariations := by
  have hmod : p.roots.countP (0 < ·) % 2 = p.signVariations % 2 :=
    parity_equiv_nonzero_const p hp hc0
  have hub : p.roots.countP (0 < ·) ≤ p.signVariations := descartes_upper_bound p
  obtain ⟨d, hd⟩ : ∃ d, p.signVariations = p.roots.countP (0 < ·) + d :=
    ⟨p.signVariations - p.roots.countP (0 < ·), by omega⟩
  have hd_even : d % 2 = 0 := by
    have : p.roots.countP (0 < ·) % 2 = (p.roots.countP (0 < ·) + d) % 2 := by
      rw [← hd]; exact hmod
    omega
  obtain ⟨k, hk⟩ := (Nat.even_iff.mpr hd_even)
  exact ⟨k, by omega⟩

/-- **Descartes Parity** (full proof):
    For any p ≠ 0, ∃ k, p.roots.countP (0 < ·) + 2 * k = p.signVariations.
    The zero-constant-term case reduces to the nonzero case by factoring out X^m
    using the rootMultiplicity at 0. -/
theorem descartes_parity_proved (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, p.roots.countP (0 < ·) + 2 * k = p.signVariations := by
  -- Factor p = (X - C 0)^m * q where ¬(X ∣ q), i.e., X^m * q with q.coeff 0 ≠ 0
  obtain ⟨q, hpq, hndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp (0 : ℝ)
  simp only [map_zero, sub_zero] at hpq
  -- q ≠ 0 (since p = X^m * q and p ≠ 0)
  have hq : q ≠ 0 := right_ne_zero_of_mul (hpq ▸ hp)
  -- q.coeff 0 ≠ 0 (since ¬(X ∣ q) and X ∣ q ↔ q.coeff 0 = 0)
  have hqc0 : q.coeff 0 ≠ 0 := by
    simp only [map_zero, sub_zero] at hndvd
    rwa [Polynomial.X_dvd_iff] at hndvd
  obtain ⟨k, hk⟩ := descartes_parity_nonzero_const q hq hqc0
  -- sv(p) = sv(X^m * q) = sv(q)
  have hsv : p.signVariations = q.signVariations := by
    rw [hpq]; generalize p.rootMultiplicity 0 = m
    induction m with
    | zero => simp
    | succ m ihm => rw [pow_succ', mul_assoc]; exact (signVariations_X_mul_eq _).trans ihm
  -- countP(p) = countP(X^m * q) = countP(q) (X has no positive roots)
  have hcountP : p.roots.countP (0 < ·) = q.roots.countP (0 < ·) := by
    rw [hpq]; generalize p.rootMultiplicity 0 = m
    induction m with
    | zero => simp
    | succ m ihm =>
      rw [pow_succ', mul_assoc]
      have hqm : Polynomial.X ^ m * q ≠ 0 := by
        apply mul_ne_zero _ hq
        exact pow_ne_zero m Polynomial.X_ne_zero
      rw [Polynomial.roots_mul (mul_ne_zero Polynomial.X_ne_zero hqm)]
      simp [Polynomial.roots_X, Multiset.countP_add, ihm]
  rw [hsv, hcountP]
  exact ⟨k, hk⟩

/-
## Part X: Parity Result and Corollaries (formerly axiomatized)

These were previously stated in Parts VI–VII backed by `axiom descartes_parity`.
That axiom has been removed: `descartes_parity` is now a theorem discharged by
`descartes_parity_proved`, and the corollaries follow. They live here because
`descartes_parity_proved` (Part IX) must be defined before they can cite it.
-/

/-- **Descartes' Rule of Signs (Parity)** — now a theorem (no axiom):
    the difference between sign variations and the positive root count is even,
    i.e. positive root count + 2k = sign variation count for some k. -/
theorem descartes_parity (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, p.roots.countP (0 < ·) + 2 * k = p.signVariations :=
  descartes_parity_proved p hp

/-- **Combined Descartes' Rule**:
    positive root count + even number = sign variation count. -/
theorem descartes_rule_combined (p : ℝ[X]) (hp : p ≠ 0) :
    ∃ k : ℕ, p.roots.countP (0 < ·) + 2 * k = p.signVariations :=
  descartes_parity p hp

/-- If p has exactly 1 sign variation, it has exactly 1 positive root. -/
theorem one_sign_variation_one_positive_root (p : ℝ[X]) (hp : p ≠ 0)
    (h1 : p.signVariations = 1) : p.roots.countP (0 < ·) = 1 := by
  obtain ⟨k, hk⟩ := descartes_parity p hp
  rw [h1] at hk
  have hle := descartes_upper_bound p
  rw [h1] at hle
  omega

/-- If we know the sign variation count exactly, we know the positive root count
    (via parity): sv = countP + 2k for some k ≥ 0. -/
theorem positive_root_count_from_sv (p : ℝ[X]) (hp : p ≠ 0) (n : ℕ)
    (h : p.signVariations = n) :
    ∃ k : ℕ, p.roots.countP (0 < ·) + 2 * k = n := by
  obtain ⟨k, hk⟩ := descartes_parity p hp
  exact ⟨k, by rw [← h]; exact hk⟩

end DescartesRuleOQ01
