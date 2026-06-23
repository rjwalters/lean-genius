import Mathlib.Tactic
import Mathlib.Data.Rat.Defs

/-
# Erdős Problem #1005 (OQ-03): The Farey Adjacency Criterion via Denominator Sums

## Parent

Erdős #1005 studies *runs of consecutive Farey fractions*. The single most
basic structural fact any run analysis rests on is the answer to:

> Given two Farey fractions of order `n`, when are they **adjacent** in `F_n`
> (no order-`n` fraction strictly between them)?

The parent entry (`Erdos1005Problem.lean`) supplies the **unimodular** package:
the gap formula `c/d - a/b = 1/(bd)`, mediant coprimality, and the fact that
the mediant lies strictly between two unimodular neighbours. What it does *not*
supply -- and what actually controls adjacency -- is the denominator arithmetic.

(This file is self-contained: it re-declares the small `FareyFraction`
scaffold from the parent rather than importing it, because the parent's
`import Mathlib.Data.Rat.Basic` no longer resolves under Mathlib `v4.26.0`.
The definitions below mirror the parent exactly.)

## This file

We prove the classical **denominator-sum criterion**:

* `intermediate_denom_ge` -- if `a/b < p/q < c/d` and the outer pair is
  unimodular (`bc - ad = 1`), then **`q ≥ b + d`**. Any fraction squeezed
  between two unimodular neighbours has denominator at least the sum of theirs.
  This is the engine; it is pure integer arithmetic and follows from the
  identity `q·(bc - ad) = d·(pb - aq) + b·(cq - pd)`.

* `farey_adjacent_of_denom_sum_gt` -- if a unimodular pair has `b + d > n`,
  then **no** Farey fraction of order `n` lies strictly between them: they are
  adjacent in `F_n`.

* `mediant_lt_n_not_adjacent` -- sharpness. If `b + d ≤ n`, the mediant
  `(a+c)/(b+d)` is itself a Farey fraction of order `n` strictly between them,
  so the pair is **not** adjacent.

* `farey_adjacency_iff` -- combining the two: a unimodular pair `a/b < c/d` is
  adjacent in `F_n` **iff** `b + d > n`. The mediant first appears at order
  exactly `b + d` (Stern–Brocot insertion order).

Every theorem below is fully machine-checked: 0 sorries, 0 axioms,
no `native_decide`.

Reference: https://erdosproblems.com/1005
-/

namespace Erdos1005OQ03

-- ══════════════════════════════════════════════════════════════════
-- § 1: Farey fractions (mirrors the parent scaffold)
-- ══════════════════════════════════════════════════════════════════

/-- A Farey fraction of order `n`: a pair `(p, q)` with `0 ≤ p ≤ q`,
    `1 ≤ q ≤ n`, and `gcd(p, q) = 1`. -/
structure FareyFraction (n : ℕ) where
  p : ℕ
  q : ℕ
  hq_pos : 1 ≤ q
  hq_le : q ≤ n
  hp_le : p ≤ q
  hcoprime : Nat.Coprime p q

/-- The rational value of a Farey fraction. -/
def FareyFraction.toRat {n : ℕ} (f : FareyFraction n) : ℚ :=
  f.p / f.q

/-- Two unimodular neighbours satisfy `bc - ad = 1`. -/
def IsConsecutiveFarey {n : ℕ} (f g : FareyFraction n) : Prop :=
  g.p * f.q - f.p * g.q = 1

-- ══════════════════════════════════════════════════════════════════
-- § 2: Mediant facts (mirrors the parent; reused for sharpness)
-- ══════════════════════════════════════════════════════════════════

/-- The mediant of a unimodular pair is in lowest terms: if `bc = ad + 1`
    then `gcd(a+c, b+d) = 1`. -/
theorem mediant_coprime {a b c d : ℕ} (h : b * c = a * d + 1) :
    Nat.Coprime (a + c) (b + d) := by
  rw [Nat.Coprime]
  set g := Nat.gcd (a + c) (b + d) with hg
  have h1 : g ∣ b * (a + c) := dvd_mul_of_dvd_right (Nat.gcd_dvd_left (a + c) (b + d)) b
  have h2 : g ∣ a * (b + d) := dvd_mul_of_dvd_right (Nat.gcd_dvd_right (a + c) (b + d)) a
  have heq : b * (a + c) = a * (b + d) + 1 := by nlinarith
  rw [heq] at h1
  exact Nat.dvd_one.mp ((Nat.dvd_add_right h2).mp h1)

-- ══════════════════════════════════════════════════════════════════
-- § 3: Order is cross-multiplication
-- ══════════════════════════════════════════════════════════════════

/-- Strict order of two Farey fractions is cross-multiplication of the
    numerator/denominator pairs (denominators are positive). -/
theorem toRat_lt_iff {n : ℕ} (f g : FareyFraction n) :
    f.toRat < g.toRat ↔ f.p * g.q < g.p * f.q := by
  unfold FareyFraction.toRat
  have hf : (0 : ℚ) < f.q := Nat.cast_pos.mpr f.hq_pos
  have hg : (0 : ℚ) < g.q := Nat.cast_pos.mpr g.hq_pos
  rw [div_lt_div_iff₀ hf hg]
  constructor <;> intro h <;> exact_mod_cast h

/-- The mediant `(a+c)/(b+d)` of a unimodular pair `a/b < c/d` lies strictly
    between them. -/
theorem mediant_between {n : ℕ} (f g : FareyFraction n)
    (hlt : f.toRat < g.toRat) :
    f.toRat < (f.p + g.p : ℚ) / (f.q + g.q : ℚ) ∧
    (f.p + g.p : ℚ) / (f.q + g.q : ℚ) < g.toRat := by
  have hcross : f.p * g.q < g.p * f.q := (toRat_lt_iff f g).mp hlt
  unfold FareyFraction.toRat
  have hfq : (0 : ℚ) < f.q := Nat.cast_pos.mpr f.hq_pos
  have hgq : (0 : ℚ) < g.q := Nat.cast_pos.mpr g.hq_pos
  have hsum : (0 : ℚ) < (f.q + g.q : ℚ) := by positivity
  have hcrossQ : (f.p : ℚ) * g.q < (g.p : ℚ) * f.q := by exact_mod_cast hcross
  refine ⟨?_, ?_⟩
  · rw [div_lt_div_iff₀ hfq hsum]; nlinarith
  · rw [div_lt_div_iff₀ hsum hgq]; nlinarith

-- ══════════════════════════════════════════════════════════════════
-- § 4: The denominator-sum criterion
-- ══════════════════════════════════════════════════════════════════

/-- **Key lemma.** If `a/b < p/q < c/d` and the outer pair is unimodular
    (`bc - ad = 1`), then the inner denominator satisfies `q ≥ b + d`.

    Proof: from the strict inequalities, `pb - aq ≥ 1` and `cq - pd ≥ 1`
    (as integers), and the identity
    `q·(bc - ad) = d·(pb - aq) + b·(cq - pd)` collapses, via `bc - ad = 1`,
    to `q = d·(pb - aq) + b·(cq - pd) ≥ d + b`. -/
theorem intermediate_denom_ge {n : ℕ} (f g h : FareyFraction n)
    (huni : IsConsecutiveFarey f g)
    (h1 : f.toRat < h.toRat) (h2 : h.toRat < g.toRat) :
    f.q + g.q ≤ h.q := by
  -- Unimodular relation as a clean ℕ equation.
  have hcb : g.p * f.q = f.p * g.q + 1 := by
    have := huni; unfold IsConsecutiveFarey at this; omega
  -- Strict orders → ℕ inequalities.
  have hfh : f.p * h.q < h.p * f.q := (toRat_lt_iff f h).mp h1
  have hhg : h.p * g.q < g.p * h.q := (toRat_lt_iff h g).mp h2
  -- integer versions
  have hcbZ : (g.p : ℤ) * f.q = (f.p : ℤ) * g.q + 1 := by exact_mod_cast hcb
  have h1Z : (f.p : ℤ) * h.q + 1 ≤ (h.p : ℤ) * f.q := by exact_mod_cast hfh
  have h2Z : (h.p : ℤ) * g.q + 1 ≤ (g.p : ℤ) * h.q := by exact_mod_cast hhg
  have hbZ : (1 : ℤ) ≤ (f.q : ℤ) := by exact_mod_cast f.hq_pos
  have hdZ : (1 : ℤ) ≤ (g.q : ℤ) := by exact_mod_cast g.hq_pos
  -- The collapsing identity (uses bc - ad = 1).
  have key : (h.q : ℤ)
      = (g.q : ℤ) * ((h.p : ℤ) * f.q - (f.p : ℤ) * h.q)
        + (f.q : ℤ) * ((g.p : ℤ) * h.q - (h.p : ℤ) * g.q) := by
    linear_combination (-(h.q : ℤ)) * hcbZ
  -- q = d·(pb - aq) + b·(cq - pd) ≥ d·1 + b·1 = d + b.
  have t1 : (1 : ℤ) ≤ (h.p : ℤ) * f.q - (f.p : ℤ) * h.q := by linarith
  have t2 : (1 : ℤ) ≤ (g.p : ℤ) * h.q - (h.p : ℤ) * g.q := by linarith
  have bound : (f.q : ℤ) + g.q ≤ h.q := by
    nlinarith [mul_le_mul_of_nonneg_left t1 (by linarith : (0:ℤ) ≤ (g.q : ℤ)),
               mul_le_mul_of_nonneg_left t2 (by linarith : (0:ℤ) ≤ (f.q : ℤ)), key]
  exact_mod_cast bound

/-- **Adjacency criterion (sufficiency).** A unimodular pair `a/b < c/d` whose
    denominators sum past the order, `b + d > n`, is adjacent in `F_n`: no
    Farey fraction of order `n` lies strictly between them. -/
theorem farey_adjacent_of_denom_sum_gt {n : ℕ} (f g : FareyFraction n)
    (huni : IsConsecutiveFarey f g) (hsum : n < f.q + g.q) :
    ∀ h : FareyFraction n, ¬ (f.toRat < h.toRat ∧ h.toRat < g.toRat) := by
  rintro h ⟨h1, h2⟩
  have hge : f.q + g.q ≤ h.q := intermediate_denom_ge f g h huni h1 h2
  exact absurd (le_trans hge h.hq_le) (by omega)

/-- **Sharpness.** If a unimodular pair `a/b < c/d` has `b + d ≤ n`, then the
    mediant `(a+c)/(b+d)` is a Farey fraction of order `n` lying strictly
    between them -- so the pair is **not** adjacent. The mediant first enters
    the Farey sequence at order exactly `b + d`. -/
theorem mediant_lt_n_not_adjacent {n : ℕ} (f g : FareyFraction n)
    (huni : IsConsecutiveFarey f g) (hlt : f.toRat < g.toRat)
    (hsum : f.q + g.q ≤ n) :
    ∃ h : FareyFraction n, f.toRat < h.toRat ∧ h.toRat < g.toRat := by
  -- unimodular relation in the form `mediant_coprime` expects: b*c = a*d + 1
  have hcb0 : g.p * f.q = f.p * g.q + 1 := by
    have := huni; unfold IsConsecutiveFarey at this; omega
  have hbc : f.q * g.p = f.p * g.q + 1 := by rw [Nat.mul_comm]; exact hcb0
  refine ⟨{ p := f.p + g.p
          , q := f.q + g.q
          , hq_pos := by have := f.hq_pos; omega
          , hq_le := hsum
          , hp_le := by have := f.hp_le; have := g.hp_le; omega
          , hcoprime := mediant_coprime hbc }, ?_, ?_⟩
  · have := (mediant_between f g hlt).1
    simpa [FareyFraction.toRat, Nat.cast_add] using this
  · have := (mediant_between f g hlt).2
    simpa [FareyFraction.toRat, Nat.cast_add] using this

/-- **Farey adjacency criterion (iff).** A unimodular pair `a/b < c/d` is
    adjacent in `F_n` (no order-`n` fraction strictly between) **iff**
    `b + d > n`. Equivalently, their mediant first appears at order `b + d`. -/
theorem farey_adjacency_iff {n : ℕ} (f g : FareyFraction n)
    (huni : IsConsecutiveFarey f g) (hlt : f.toRat < g.toRat) :
    (∀ h : FareyFraction n, ¬ (f.toRat < h.toRat ∧ h.toRat < g.toRat))
      ↔ n < f.q + g.q := by
  constructor
  · intro hadj
    by_contra hle
    push_neg at hle
    obtain ⟨h, hh1, hh2⟩ := mediant_lt_n_not_adjacent f g huni hlt hle
    exact hadj h ⟨hh1, hh2⟩
  · intro hsum
    exact farey_adjacent_of_denom_sum_gt f g huni hsum

end Erdos1005OQ03
