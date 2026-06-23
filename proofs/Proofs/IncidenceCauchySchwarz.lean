/-
  The Elementary Incidence Bound (Cauchy–Schwarz)

  Given a finite set of `points` and a finite set of `lines` with an incidence
  relation in which **any two distinct lines meet in at most one common point**,
  the number of incidences `I` satisfies the elementary bound

        I² ≤ |points| · |lines|² + |points| · I,

  equivalently (over the reals)  I ≤ |points| + |lines|·√|points|.

  This is the classical Cauchy–Schwarz incidence bound. It is the statement that
  the Szemerédi–Trotter theorem and the crossing-number inequality *strengthen*:
  Szemerédi–Trotter improves the exponent to give `I = O((mn)^{2/3} + m + n)`.
  This file proves the elementary bound itself — the honest, infrastructure-free
  half of the open question "can the crossing-number inequality be pushed to the
  Szemerédi–Trotter form" (prob-method-applications OQ-02). The crossing-number
  route requires a Mathlib formalization of planar graph drawings that does not
  yet exist; the bound below needs none of it.

  The argument is purely combinatorial — no geometry, only the axiom that two
  distinct lines determine at most one point:

    1.  For each point `p`, `deg p ^ 2 = (#ordered pairs of distinct lines
        through p) + deg p`.
    2.  Summing over points, the ordered-distinct-line-pairs term equals
        `∑_{ℓ₁ ≠ ℓ₂} #{p on both}`, which the hypothesis bounds by `|lines|²`.
    3.  Hence `∑ deg p ² ≤ |lines|² + I`.
    4.  Cauchy–Schwarz: `I² = (∑ deg p)² ≤ |points| · ∑ deg p ²`.

  Status: 0 sorries, 0 axioms. No `native_decide`.
-/
import Mathlib

namespace ProbMethod.Incidence

open Finset BigOperators

variable {P L : Type*} [Fintype P] [Fintype L] [DecidableEq P] [DecidableEq L]
variable (Inc : P → L → Prop) [∀ p ℓ, Decidable (Inc p ℓ)]

/-- The **degree** of a point: the number of lines through it. -/
def deg (p : P) : ℕ := (univ.filter (fun ℓ => Inc p ℓ)).card

/-- The total number of **incidences** `I(P, L)`. -/
def incidences : ℕ := ∑ p : P, deg Inc p

/-- Degree as a sum of `0/1` indicators over lines. -/
theorem deg_eq_sum (p : P) :
    deg Inc p = ∑ ℓ : L, (if Inc p ℓ then (1 : ℕ) else 0) := by
  rw [deg, Finset.card_filter]

-- ═══════════════════════════════════════════════════
-- Part I: the per-point identity  deg p ² = cherry p + deg p
-- ═══════════════════════════════════════════════════

/-- `cherry p` counts the **ordered pairs of distinct lines** both through `p`. -/
def cherry (p : P) : ℕ :=
  ∑ ℓ₁ : L, ∑ ℓ₂ : L,
    (if ℓ₁ ≠ ℓ₂ then (if Inc p ℓ₁ then 1 else 0) * (if Inc p ℓ₂ then 1 else 0) else 0)

/-- **Per-point identity.** Squaring the degree counts ordered pairs of lines
    through `p`; the diagonal (`ℓ₁ = ℓ₂`) contributes `deg p`, the off-diagonal
    contributes `cherry p`. -/
theorem deg_sq (p : P) : deg Inc p * deg Inc p = cherry Inc p + deg Inc p := by
  have hdeg : deg Inc p = ∑ ℓ : L, (if Inc p ℓ then (1 : ℕ) else 0) := deg_eq_sum Inc p
  -- expand the square into a double sum
  have hexpand : deg Inc p * deg Inc p
      = ∑ ℓ₁ : L, ∑ ℓ₂ : L,
          (if Inc p ℓ₁ then (1 : ℕ) else 0) * (if Inc p ℓ₂ then 1 else 0) := by
    rw [hdeg, Finset.sum_mul_sum]
  -- split the double sum into diagonal / off-diagonal pieces
  have step :
      (∑ ℓ₁ : L, ∑ ℓ₂ : L,
        (if Inc p ℓ₁ then (1 : ℕ) else 0) * (if Inc p ℓ₂ then 1 else 0))
        = (∑ ℓ₁ : L, ∑ ℓ₂ : L,
            (if ℓ₁ = ℓ₂ then
              (if Inc p ℓ₁ then (1 : ℕ) else 0) * (if Inc p ℓ₂ then 1 else 0) else 0))
          + (∑ ℓ₁ : L, ∑ ℓ₂ : L,
            (if ℓ₁ ≠ ℓ₂ then
              (if Inc p ℓ₁ then (1 : ℕ) else 0) * (if Inc p ℓ₂ then 1 else 0) else 0)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ℓ₁ _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ℓ₂ _ => ?_)
    by_cases h : ℓ₁ = ℓ₂ <;> simp [h]
  -- the diagonal sum collapses to `deg p`
  have hdiag :
      (∑ ℓ₁ : L, ∑ ℓ₂ : L,
        (if ℓ₁ = ℓ₂ then
          (if Inc p ℓ₁ then (1 : ℕ) else 0) * (if Inc p ℓ₂ then 1 else 0) else 0))
        = deg Inc p := by
    have hone : ∀ ℓ₁ : L,
        (∑ ℓ₂ : L, (if ℓ₁ = ℓ₂ then
          (if Inc p ℓ₁ then (1 : ℕ) else 0) * (if Inc p ℓ₂ then 1 else 0) else 0))
          = (if Inc p ℓ₁ then (1 : ℕ) else 0) := by
      intro ℓ₁
      rw [Finset.sum_ite_eq univ ℓ₁
        (fun ℓ₂ => (if Inc p ℓ₁ then (1 : ℕ) else 0) * (if Inc p ℓ₂ then 1 else 0))]
      simp only [mem_univ, if_true]
      by_cases hI : Inc p ℓ₁ <;> simp [hI]
    rw [Finset.sum_congr rfl (fun ℓ₁ _ => hone ℓ₁)]
    exact (deg_eq_sum Inc p).symm
  rw [hexpand, step, hdiag]
  unfold cherry
  ring

-- ═══════════════════════════════════════════════════
-- Part II: the cherry sum is bounded by |lines|²
-- ═══════════════════════════════════════════════════

/-- The hypothesis "two distinct lines meet in at most one point", stated as a
    bound on the number of points incident to a fixed pair of distinct lines. -/
def TwoLinesMeetOnce : Prop :=
  ∀ ℓ₁ ℓ₂ : L, ℓ₁ ≠ ℓ₂ →
    (univ.filter (fun p => Inc p ℓ₁ ∧ Inc p ℓ₂)).card ≤ 1

/-- **Cherry bound.** Under the once-meeting hypothesis the total number of
    (point, ordered pair of distinct lines through it) configurations is at most
    `|lines|²`: swap the order of summation and bound each line-pair's common
    points by `1`. -/
theorem sum_cherry_le (h : TwoLinesMeetOnce Inc) :
    (∑ p : P, cherry Inc p) ≤ Fintype.card L * Fintype.card L := by
  -- rewrite cherry and swap the point sum inside
  have hswap :
      (∑ p : P, cherry Inc p)
        = ∑ ℓ₁ : L, ∑ ℓ₂ : L,
            (if ℓ₁ ≠ ℓ₂ then
              (univ.filter (fun p => Inc p ℓ₁ ∧ Inc p ℓ₂)).card else 0) := by
    unfold cherry
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ℓ₁ _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ℓ₂ _ => ?_)
    -- the condition `ℓ₁ ≠ ℓ₂` is independent of `p`: pull it out of the sum
    rw [Finset.sum_ite_irrel]
    split_ifs with hc
    · rw [Finset.card_filter]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases h1 : Inc p ℓ₁ <;> by_cases h2 : Inc p ℓ₂ <;> simp [h1, h2]
    · simp
  rw [hswap]
  -- each inner term is ≤ 1, so the double sum is ≤ |L| * |L|
  calc
    (∑ ℓ₁ : L, ∑ ℓ₂ : L,
        (if ℓ₁ ≠ ℓ₂ then
          (univ.filter (fun p => Inc p ℓ₁ ∧ Inc p ℓ₂)).card else 0))
        ≤ ∑ ℓ₁ : L, ∑ ℓ₂ : L, 1 := by
          refine Finset.sum_le_sum (fun ℓ₁ _ => Finset.sum_le_sum (fun ℓ₂ _ => ?_))
          by_cases hne : ℓ₁ ≠ ℓ₂
          · rw [if_pos hne]; exact h ℓ₁ ℓ₂ hne
          · rw [if_neg hne]; exact Nat.zero_le 1
    _ = Fintype.card L * Fintype.card L := by
          simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

-- ═══════════════════════════════════════════════════
-- Part III: ∑ deg p ² ≤ |lines|² + I
-- ═══════════════════════════════════════════════════

/-- Summing the per-point identity and applying the cherry bound:
    `∑ deg p ² ≤ |lines|² + I`. -/
theorem sum_deg_sq_le (h : TwoLinesMeetOnce Inc) :
    (∑ p : P, deg Inc p * deg Inc p)
      ≤ Fintype.card L * Fintype.card L + incidences Inc := by
  have hid : (∑ p : P, deg Inc p * deg Inc p)
      = (∑ p : P, cherry Inc p) + incidences Inc := by
    rw [incidences, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun p _ => deg_sq Inc p)
  rw [hid]
  exact Nat.add_le_add_right (sum_cherry_le Inc h) _

-- ═══════════════════════════════════════════════════
-- Part IV: the Cauchy–Schwarz incidence bound
-- ═══════════════════════════════════════════════════

/-- **Elementary incidence bound (Cauchy–Schwarz form).**
    For a finite incidence structure in which any two distinct lines share at
    most one point, the number of incidences `I` obeys
    `I² ≤ |points| · |lines|² + |points| · I`.

    This is the bound that the Szemerédi–Trotter theorem and the
    crossing-number inequality sharpen. -/
theorem incidence_bound (h : TwoLinesMeetOnce Inc) :
    incidences Inc ^ 2
      ≤ Fintype.card P * Fintype.card L ^ 2 + Fintype.card P * incidences Inc := by
  -- Cauchy–Schwarz over ℝ with the all-ones weight vector
  have hCS : (incidences Inc : ℝ) ^ 2
      ≤ Fintype.card P * ∑ p : P, ((deg Inc p : ℝ)) ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ
      (fun p : P => (deg Inc p : ℝ)) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one] at hcs
    -- hcs : (∑ p, deg p)^2 ≤ (∑ p, deg p ^ 2) * |P|
    have hI : (incidences Inc : ℝ) = ∑ p : P, (deg Inc p : ℝ) := by
      rw [incidences]; push_cast; rfl
    rw [hI]
    calc (∑ p : P, (deg Inc p : ℝ)) ^ 2
          ≤ (∑ p : P, (deg Inc p : ℝ) ^ 2) * (Fintype.card P : ℝ) := hcs
      _ = (Fintype.card P : ℝ) * ∑ p : P, (deg Inc p : ℝ) ^ 2 := by ring
  -- transport the ℕ degree-square bound into ℝ
  have hNat := sum_deg_sq_le Inc h
  have hcast : (∑ p : P, ((deg Inc p : ℝ)) ^ 2)
      ≤ ((Fintype.card L * Fintype.card L + incidences Inc : ℕ) : ℝ) := by
    have : (∑ p : P, ((deg Inc p : ℝ)) ^ 2)
        = ((∑ p : P, deg Inc p * deg Inc p : ℕ) : ℝ) := by
      push_cast
      refine Finset.sum_congr rfl (fun p _ => ?_)
      ring
    rw [this]
    exact_mod_cast hNat
  -- assemble the real inequality and descend to ℕ
  have hReal : (incidences Inc : ℝ) ^ 2
      ≤ (Fintype.card P * Fintype.card L ^ 2 + Fintype.card P * incidences Inc : ℕ) := by
    calc (incidences Inc : ℝ) ^ 2
          ≤ Fintype.card P * ∑ p : P, ((deg Inc p : ℝ)) ^ 2 := hCS
      _ ≤ (Fintype.card P : ℝ)
            * ((Fintype.card L * Fintype.card L + incidences Inc : ℕ) : ℝ) := by
            apply mul_le_mul_of_nonneg_left hcast (by positivity)
      _ = (Fintype.card P * Fintype.card L ^ 2 + Fintype.card P * incidences Inc : ℕ) := by
            push_cast; ring
  exact_mod_cast hReal

-- ═══════════════════════════════════════════════════
-- Part V: real-analytic corollary  I ≤ |points| + |lines|·√|points|
-- ═══════════════════════════════════════════════════

/-- **Square-root form.** Solving the quadratic bound gives the familiar
    `I ≤ |points| + |lines| · √|points|`. -/
theorem incidence_bound_sqrt (h : TwoLinesMeetOnce Inc) :
    (incidences Inc : ℝ)
      ≤ Fintype.card P + Fintype.card L * Real.sqrt (Fintype.card P) := by
  set m : ℝ := (Fintype.card P : ℝ) with hm
  set ℓ : ℝ := (Fintype.card L : ℝ) with hℓ
  set I : ℝ := (incidences Inc : ℝ) with hI
  have hmnn : 0 ≤ m := by rw [hm]; positivity
  have hℓnn : 0 ≤ ℓ := by rw [hℓ]; positivity
  -- the polynomial bound, cast to ℝ
  have hpoly : I ^ 2 ≤ m * ℓ ^ 2 + m * I := by
    have := incidence_bound Inc h
    rw [hm, hℓ, hI]; exact_mod_cast this
  rcases le_or_gt I m with hcase | hcase
  · -- if `I ≤ m` the bound is immediate since `ℓ·√m ≥ 0`
    have : (0 : ℝ) ≤ ℓ * Real.sqrt m := mul_nonneg hℓnn (Real.sqrt_nonneg m)
    linarith
  · -- the interesting case `m < I`: then `(I - m)² ≤ ℓ²·m`, take square roots
    have hkey : (I - m) ^ 2 ≤ ℓ ^ 2 * m := by nlinarith [hpoly, hcase, hmnn]
    have hb : (0 : ℝ) ≤ ℓ * Real.sqrt m := mul_nonneg hℓnn (Real.sqrt_nonneg m)
    have hsq2 : (I - m) ^ 2 ≤ (ℓ * Real.sqrt m) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hmnn]; exact hkey
    have h4 : I - m ≤ ℓ * Real.sqrt m := by
      calc I - m ≤ |I - m| := le_abs_self _
        _ = Real.sqrt ((I - m) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt ((ℓ * Real.sqrt m) ^ 2) := Real.sqrt_le_sqrt hsq2
        _ = |ℓ * Real.sqrt m| := Real.sqrt_sq_eq_abs _
        _ = ℓ * Real.sqrt m := abs_of_nonneg hb
    linarith

end ProbMethod.Incidence
