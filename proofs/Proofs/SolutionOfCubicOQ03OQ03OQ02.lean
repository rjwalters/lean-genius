import Mathlib

/-
# OQ-03-OQ-03-OQ-02: Ferrari's Four Quartic Roots, Verified by Substitution

The parent (`SolutionOfCubicOQ03OQ03.lean`) showed that the resolvent cubic of
Ferrari's quartic method depresses to Cardano's form, completing the *reduction*
chain quartic → resolvent cubic → depressed cubic.  What it did **not** do is
exhibit the four roots of the quartic and verify them.

This file closes that gap over `ℂ` (the prototypical algebraically closed field,
matching the parent's convention).  For the general depressed quartic
  x⁴ + p x² + q x + r = 0
we take **any** root `m` of the resolvent cubic
  8m³ + 20p m² + (16p² − 8r) m + (4p³ − 4pr − q²) = 0,
put `s = m + p/2`, pick a square root `w` of `2s`, and set `e = q/(2w)`.  The two
Ferrari quadratics are
  Q₁(x) = x² − w x + (s + p/2 + e),   Q₂(x) = x² + w x + (s + p/2 − e).

Everything is verified by `ring`/`linear_combination` from the three polynomial
relations
  `w² = 2s`,   `2 w e = q`,   `e² = (s + p/2)² − r`
(the last two being exactly what the resolvent root provides):

* `ferrari_factorization` — the quartic equals `Q₁ · Q₂`.
* `ferrari_splits` — choosing square roots `d₁, d₂` of the two discriminants, the
  quartic splits completely into four explicit linear factors.
* `ferrari_root_Q1`, `ferrari_root_Q2`, `ferrari_four_roots` — each of the four
  closed forms `(w ± d₁)/2`, `(−w ± d₂)/2` is a genuine root: substituting and
  simplifying gives `0`.
* `resolvent_shift_eq` / `exists_ferrari_data` — the bridge: a resolvent root `m`
  (parent convention) supplies the `e` with `2 w e = q` and `e² = (s+p/2)² − r`.
* `ferrari_solvable` — every depressed quartic with a usable resolvent root has an
  explicit root over `ℂ`, produced by Ferrari's construction.

No `sorry`; `#print axioms` shows only the standard kernel axioms.

Parent: SolutionOfCubicOQ03OQ03.lean (resolvent depression)
Grandparent: SolutionOfCubicOQ03.lean (Cardano)
-/

set_option linter.unusedVariables false

namespace FerrariQuarticRoots

open Complex

-- ============================================================
-- SECTION I: The Ferrari factorization
-- ============================================================

/-- **Ferrari factorization.**  Given the three polynomial relations
      `w² = 2s`,  `2 w e = q`,  `e² = (s + p/2)² − r`,
    the depressed quartic factors into the two Ferrari quadratics.  This is the
    algebraic heart of Ferrari's method; everything else specialises it. -/
theorem ferrari_factorization (p q r s w e x : ℂ)
    (hw : w ^ 2 = 2 * s) (hwe : 2 * w * e = q)
    (he2 : e ^ 2 = (s + p / 2) ^ 2 - r) :
    x ^ 4 + p * x ^ 2 + q * x + r
      = (x ^ 2 - w * x + (s + p / 2 + e))
        * (x ^ 2 + w * x + (s + p / 2 - e)) := by
  linear_combination x ^ 2 * hw - x * hwe + he2

-- ============================================================
-- SECTION II: Roots of a monic quadratic by its discriminant
-- ============================================================

/-- A monic quadratic `x² + b x + c` vanishes at `(-b ± d)/2` whenever `d² = b² − 4c`. -/
theorem monic_quadratic_root (b c d x : ℂ)
    (hd : d ^ 2 = b ^ 2 - 4 * c)
    (hx : x = (-b + d) / 2 ∨ x = (-b - d) / 2) :
    x ^ 2 + b * x + c = 0 := by
  rcases hx with h | h <;> subst h <;> linear_combination hd / 4

-- ============================================================
-- SECTION III: The four Ferrari roots are genuine roots
-- ============================================================

/-- The two roots of the first Ferrari quadratic, `(w ± d₁)/2`, solve the quartic. -/
theorem ferrari_root_Q1 (p q r s w e d x : ℂ)
    (hw : w ^ 2 = 2 * s) (hwe : 2 * w * e = q)
    (he2 : e ^ 2 = (s + p / 2) ^ 2 - r)
    (hd : d ^ 2 = w ^ 2 - 4 * (s + p / 2 + e))
    (hx : x = (w + d) / 2 ∨ x = (w - d) / 2) :
    x ^ 4 + p * x ^ 2 + q * x + r = 0 := by
  rw [ferrari_factorization p q r s w e x hw hwe he2]
  have hQ1 : x ^ 2 - w * x + (s + p / 2 + e) = 0 := by
    rcases hx with h | h <;> subst h <;> linear_combination hd / 4
  rw [hQ1]; ring

/-- The two roots of the second Ferrari quadratic, `(−w ± d₂)/2`, solve the quartic. -/
theorem ferrari_root_Q2 (p q r s w e d x : ℂ)
    (hw : w ^ 2 = 2 * s) (hwe : 2 * w * e = q)
    (he2 : e ^ 2 = (s + p / 2) ^ 2 - r)
    (hd : d ^ 2 = w ^ 2 - 4 * (s + p / 2 - e))
    (hx : x = (-w + d) / 2 ∨ x = (-w - d) / 2) :
    x ^ 4 + p * x ^ 2 + q * x + r = 0 := by
  rw [ferrari_factorization p q r s w e x hw hwe he2]
  have hQ2 : x ^ 2 + w * x + (s + p / 2 - e) = 0 := by
    rcases hx with h | h <;> subst h <;> linear_combination hd / 4
  rw [hQ2]; ring

/-- **All four Ferrari closed forms are genuine roots** of the depressed quartic. -/
theorem ferrari_four_roots (p q r s w e d₁ d₂ : ℂ)
    (hw : w ^ 2 = 2 * s) (hwe : 2 * w * e = q)
    (he2 : e ^ 2 = (s + p / 2) ^ 2 - r)
    (hd₁ : d₁ ^ 2 = w ^ 2 - 4 * (s + p / 2 + e))
    (hd₂ : d₂ ^ 2 = w ^ 2 - 4 * (s + p / 2 - e)) :
    ∀ x ∈ ({(w + d₁) / 2, (w - d₁) / 2,
            (-w + d₂) / 2, (-w - d₂) / 2} : Set ℂ),
        x ^ 4 + p * x ^ 2 + q * x + r = 0 := by
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with h | h | h | h
  · exact ferrari_root_Q1 p q r s w e d₁ x hw hwe he2 hd₁ (Or.inl h)
  · exact ferrari_root_Q1 p q r s w e d₁ x hw hwe he2 hd₁ (Or.inr h)
  · exact ferrari_root_Q2 p q r s w e d₂ x hw hwe he2 hd₂ (Or.inl h)
  · exact ferrari_root_Q2 p q r s w e d₂ x hw hwe he2 hd₂ (Or.inr h)

/-- **Ferrari split.**  With square roots `d₁, d₂` of the two quadratic
    discriminants, the depressed quartic splits into four explicit linear
    factors over `ℂ`. -/
theorem ferrari_splits (p q r s w e d₁ d₂ x : ℂ)
    (hw : w ^ 2 = 2 * s) (hwe : 2 * w * e = q)
    (he2 : e ^ 2 = (s + p / 2) ^ 2 - r)
    (hd₁ : d₁ ^ 2 = w ^ 2 - 4 * (s + p / 2 + e))
    (hd₂ : d₂ ^ 2 = w ^ 2 - 4 * (s + p / 2 - e)) :
    x ^ 4 + p * x ^ 2 + q * x + r
      = (x - (w + d₁) / 2) * (x - (w - d₁) / 2)
        * (x - (-w + d₂) / 2) * (x - (-w - d₂) / 2) := by
  rw [ferrari_factorization p q r s w e x hw hwe he2]
  have e1 : x ^ 2 - w * x + (s + p / 2 + e)
      = (x - (w + d₁) / 2) * (x - (w - d₁) / 2) := by
    linear_combination hd₁ / 4
  have e2 : x ^ 2 + w * x + (s + p / 2 - e)
      = (x - (-w + d₂) / 2) * (x - (-w - d₂) / 2) := by
    linear_combination hd₂ / 4
  rw [e1, e2]; ring

-- ============================================================
-- SECTION IV: Bridge to the resolvent cubic (parent convention)
-- ============================================================

/-- The resolvent cubic from Ferrari's method, in the parent's convention
    (`SolutionOfCubicOQ03OQ03.lean`):
    `8m³ + 20p m² + (16p² − 8r) m + (4p³ − 4pr − q²) = 0`. -/
def IsResolventRoot (p q r m : ℂ) : Prop :=
  8 * m ^ 3 + 20 * p * m ^ 2 + (16 * p ^ 2 - 8 * r) * m
    + (4 * p ^ 3 - 4 * p * r - q ^ 2) = 0

/-- The Ferrari shift `s = m + p/2` turns the resolvent cubic into the
    perfect-square parameter equation `8s³ + 8p s² + (2p² − 8r) s = q²`. -/
theorem resolvent_shift_eq (p q r m : ℂ) (h : IsResolventRoot p q r m) :
    8 * (m + p / 2) ^ 3 + 8 * p * (m + p / 2) ^ 2
      + (2 * p ^ 2 - 8 * r) * (m + p / 2) = q ^ 2 := by
  unfold IsResolventRoot at h
  linear_combination h

/-- **Bridge.**  A resolvent root `m` with nonzero shift `s = m + p/2` and a
    nonzero square root `w` of `2s` supplies the Ferrari data: `e = q/(2w)`
    satisfies `2 w e = q` and `e² = (s + p/2)² − r`. -/
theorem exists_ferrari_data (p q r m w : ℂ)
    (hs : m + p / 2 ≠ 0) (hw0 : w ≠ 0) (hw : w ^ 2 = 2 * (m + p / 2))
    (h : IsResolventRoot p q r m) :
    ∃ e : ℂ, 2 * w * e = q ∧ e ^ 2 = ((m + p / 2) + p / 2) ^ 2 - r := by
  have hres : 8 * (m + p / 2) ^ 3 + 8 * p * (m + p / 2) ^ 2
      + (2 * p ^ 2 - 8 * r) * (m + p / 2) = q ^ 2 := resolvent_shift_eq p q r m h
  have h2w : (2 * w) ≠ 0 := mul_ne_zero (by norm_num) hw0
  refine ⟨q / (2 * w), by field_simp, ?_⟩
  have hden : (2 * w) ^ 2 = 8 * (m + p / 2) := by
    have h4 : (2 * w) ^ 2 = 4 * w ^ 2 := by ring
    rw [h4, hw]; ring
  have h8s : (8 : ℂ) * (m + p / 2) ≠ 0 := mul_ne_zero (by norm_num) hs
  rw [div_pow, hden, div_eq_iff h8s]
  linear_combination -hres

-- ============================================================
-- SECTION V: Explicit solvability of the depressed quartic over ℂ
-- ============================================================

/-- **Every depressed quartic is solvable over `ℂ`.**  Ferrari's construction
    produces an explicit root from any resolvent root with nonzero shift. -/
theorem ferrari_solvable (p q r m : ℂ)
    (h : IsResolventRoot p q r m) (hs : m + p / 2 ≠ 0) :
    ∃ x : ℂ, x ^ 4 + p * x ^ 2 + q * x + r = 0 := by
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (2 * (m + p / 2)) (n := 2) (by norm_num)
  have hw0 : w ≠ 0 := by
    intro hw0
    apply hs
    have hz : (2 : ℂ) * (m + p / 2) = 0 := by rw [← hw, hw0]; ring
    rcases mul_eq_zero.1 hz with h2 | h2
    · exact absurd h2 (by norm_num)
    · exact h2
  obtain ⟨e, hwe, he2⟩ := exists_ferrari_data p q r m w hs hw0 hw h
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq
    (w ^ 2 - 4 * ((m + p / 2) + p / 2 + e)) (n := 2) (by norm_num)
  exact ⟨(w + d) / 2,
    ferrari_root_Q1 p q r (m + p / 2) w e d ((w + d) / 2) hw hwe he2 hd (Or.inl rfl)⟩

end FerrariQuarticRoots
