/-
  Discriminant of the General Cubic, Depression Invariance, and the
  Separability Criterion

  Open question stemming from `SolutionOfCubicOQ03OQ01` (Discriminant of the
  Depressed Cubic), which proves Δ = -4p³ - 27q² = (x₁-x₂)²(x₁-x₃)²(x₂-x₃)²
  for the *depressed* cubic x³ + px + q = 0 (the x² coefficient is zero,
  i.e. e₁ = x₁+x₂+x₃ = 0).

  This file removes the e₁ = 0 restriction and answers the natural follow-ups:

  1. The discriminant of the GENERAL monic cubic x³ + ax² + bx + c,
        Δ(a,b,c) = 18abc - 4a³c + a²b² - 4b³ - 27c²,
     equals the same root-separation product (x₁-x₂)²(x₁-x₃)²(x₂-x₃)².
     The parent is recovered as the a = 0 (depressed) specialization
     Δ(0,p,q) = -4p³ - 27q².

  2. The discriminant is invariant under translation of the roots
     x ↦ x + t — equivalently, under the *depression* substitution that
     sends a general cubic to its depressed form. Depressing a cubic does
     not change its discriminant; this is why the coefficient formula
     -4p³ - 27q² of the parent computes the discriminant of the original
     cubic as well.

  3. Over an integral domain, Δ(a,b,c) ≠ 0 ⟺ the three roots are pairwise
     distinct (the separability / squarefree criterion). This is a
     characteristic-free strengthening of the parent's real-sign analysis:
     it needs no ordering, only that there are no zero divisors.

  Parts 1 and 2 are polynomial identities over an arbitrary commutative
  ring; part 3 holds over any integral domain. The depressed
  discriminant and the root-separation product are recalled locally so the
  file is self-contained.
-/
import Mathlib

namespace GeneralCubicDiscriminant

variable {R : Type*} [CommRing R]

-- ============================================================
-- SECTION I: Discriminants and the Root-Separation Product
-- ============================================================

/-- The discriminant of the general monic cubic x³ + ax² + bx + c. -/
def genDiscriminant (a b c : R) : R :=
  18 * a * b * c - 4 * a ^ 3 * c + a ^ 2 * b ^ 2 - 4 * b ^ 3 - 27 * c ^ 2

/-- The discriminant of the depressed cubic x³ + px + q (the parent's
    coefficient formula, recalled locally). -/
def depressedDiscriminant (p q : R) : R := -4 * p ^ 3 - 27 * q ^ 2

/-- The root-separation form of the discriminant
    (x₁-x₂)²(x₁-x₃)²(x₂-x₃)². -/
def rootDiscriminant (x₁ x₂ x₃ : R) : R :=
  (x₁ - x₂) ^ 2 * (x₁ - x₃) ^ 2 * (x₂ - x₃) ^ 2

/-- Vieta's formulas for the general monic cubic x³ + ax² + bx + c = 0:
    x₁ + x₂ + x₃ = -a, x₁x₂ + x₁x₃ + x₂x₃ = b, x₁x₂x₃ = -c. -/
structure IsGenRootTriple (a b c : R) (x₁ x₂ x₃ : R) : Prop where
  sum_roots : x₁ + x₂ + x₃ = -a
  sum_products : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = b
  product : x₁ * x₂ * x₃ = -c

-- ============================================================
-- SECTION II: Discriminant of the General Cubic = Root Form
-- ============================================================

/-- The general-cubic discriminant equals the root-separation product:
    18abc - 4a³c + a²b² - 4b³ - 27c² = (x₁-x₂)²(x₁-x₃)²(x₂-x₃)²
    whenever x₁, x₂, x₃ are roots satisfying Vieta's formulas. -/
theorem genDiscriminant_eq_root_form (a b c x₁ x₂ x₃ : R)
    (h : IsGenRootTriple a b c x₁ x₂ x₃) :
    genDiscriminant a b c = rootDiscriminant x₁ x₂ x₃ := by
  obtain ⟨hs, hp, hpr⟩ := h
  -- Express a, b, c via Vieta and reduce to a ring identity in the roots.
  have ha : a = -(x₁ + x₂ + x₃) := by linear_combination hs
  have hb : b = x₁ * x₂ + x₁ * x₃ + x₂ * x₃ := hp.symm
  have hc : c = -(x₁ * x₂ * x₃) := by linear_combination hpr
  subst ha hb hc
  unfold genDiscriminant rootDiscriminant
  ring

-- ============================================================
-- SECTION III: Recovering the Depressed Cubic (a = 0)
-- ============================================================

/-- Setting a = 0 in the general discriminant recovers the parent's
    depressed-cubic discriminant -4p³ - 27q². -/
theorem genDiscriminant_zero_lead (p q : R) :
    genDiscriminant 0 p q = depressedDiscriminant p q := by
  unfold genDiscriminant depressedDiscriminant
  ring

/-- The depressed-cubic discriminant equals the root form when the roots
    sum to zero (e₁ = 0) — the parent's statement, recovered as the a = 0
    case of `genDiscriminant_eq_root_form`. -/
theorem depressedDiscriminant_eq_root_form (p q x₁ x₂ x₃ : R)
    (hsum : x₁ + x₂ + x₃ = 0)
    (hp : x₁ * x₂ + x₁ * x₃ + x₂ * x₃ = p)
    (hq : x₁ * x₂ * x₃ = -q) :
    depressedDiscriminant p q = rootDiscriminant x₁ x₂ x₃ := by
  have h : IsGenRootTriple 0 p q x₁ x₂ x₃ :=
    { sum_roots := by simpa using hsum, sum_products := hp, product := hq }
  rw [← genDiscriminant_zero_lead p q, genDiscriminant_eq_root_form 0 p q _ _ _ h]

-- ============================================================
-- SECTION IV: Depression / Translation Invariance
-- ============================================================

/-- The root-separation product is invariant under a common translation
    of all three roots: shifting x ↦ x + t leaves every difference
    xᵢ - xⱼ unchanged. -/
theorem rootDiscriminant_translation_invariant (x₁ x₂ x₃ t : R) :
    rootDiscriminant (x₁ + t) (x₂ + t) (x₃ + t) = rootDiscriminant x₁ x₂ x₃ := by
  unfold rootDiscriminant
  ring

/-- Vieta's data is carried along a common translation of the roots:
    if (a, b, c) are the coefficients of the cubic with roots x₁, x₂, x₃,
    then the cubic with roots xᵢ + t has the explicit shifted coefficients
    (a - 3t,  b - 2at + 3t²,  c - bt + at² - t³). -/
theorem isGenRootTriple_translate (a b c x₁ x₂ x₃ t : R)
    (h : IsGenRootTriple a b c x₁ x₂ x₃) :
    IsGenRootTriple (a - 3 * t) (b - 2 * a * t + 3 * t ^ 2)
      (c - b * t + a * t ^ 2 - t ^ 3) (x₁ + t) (x₂ + t) (x₃ + t) where
  sum_roots := by
    have h1 := h.sum_roots; linear_combination h1
  sum_products := by
    have h1 := h.sum_roots; have h2 := h.sum_products
    linear_combination h2 + 2 * t * h1
  product := by
    have h1 := h.sum_roots; have h2 := h.sum_products; have h3 := h.product
    linear_combination h3 + t * h2 + t ^ 2 * h1

/-- **Depression invariance of the discriminant.** Translating all three
    roots by a common t (in particular, the depression substitution that
    zeroes out the x² coefficient) does not change the discriminant. The
    discriminant of a general cubic therefore equals the discriminant of
    its depressed form. -/
theorem genDiscriminant_translation_invariant
    (a b c a' b' c' x₁ x₂ x₃ t : R)
    (h : IsGenRootTriple a b c x₁ x₂ x₃)
    (h' : IsGenRootTriple a' b' c' (x₁ + t) (x₂ + t) (x₃ + t)) :
    genDiscriminant a' b' c' = genDiscriminant a b c := by
  rw [genDiscriminant_eq_root_form a' b' c' _ _ _ h',
      genDiscriminant_eq_root_form a b c _ _ _ h,
      rootDiscriminant_translation_invariant]

-- ============================================================
-- SECTION V: Separability Criterion over an Integral Domain
-- ============================================================

/-- Over an integral domain, the general-cubic discriminant vanishes iff
    two of the roots coincide. This is the characteristic-free separability
    criterion: no ordering or sign analysis is needed, only the absence of
    zero divisors. -/
theorem genDiscriminant_eq_zero_iff
    {R : Type*} [CommRing R] [IsDomain R]
    (a b c x₁ x₂ x₃ : R) (h : IsGenRootTriple a b c x₁ x₂ x₃) :
    genDiscriminant a b c = 0 ↔ x₁ = x₂ ∨ x₁ = x₃ ∨ x₂ = x₃ := by
  rw [genDiscriminant_eq_root_form a b c x₁ x₂ x₃ h]
  unfold rootDiscriminant
  constructor
  · intro hzero
    -- a product of squares is zero, so one factor is zero
    rcases mul_eq_zero.mp hzero with h12 | h23
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · refine Or.inl (sub_eq_zero.mp ?_)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      · refine Or.inr (Or.inl (sub_eq_zero.mp ?_))
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    · refine Or.inr (Or.inr (sub_eq_zero.mp ?_))
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h23
  · rintro (h12 | h13 | h23)
    · simp [sub_eq_zero.mpr h12]
    · simp [sub_eq_zero.mpr h13]
    · simp [sub_eq_zero.mpr h23]

/-- Reformulation: over an integral domain the discriminant is nonzero iff
    all three roots are pairwise distinct (the cubic is separable). -/
theorem genDiscriminant_ne_zero_iff
    {R : Type*} [CommRing R] [IsDomain R]
    (a b c x₁ x₂ x₃ : R) (h : IsGenRootTriple a b c x₁ x₂ x₃) :
    genDiscriminant a b c ≠ 0 ↔ x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃ := by
  rw [ne_eq, genDiscriminant_eq_zero_iff a b c x₁ x₂ x₃ h]
  push_neg
  tauto

end GeneralCubicDiscriminant
