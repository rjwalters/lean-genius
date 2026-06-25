import Mathlib.Tactic

/-
# Erdős Problem #1005 (OQ-02): Mediant insertion and the Farey gap calculus

## Context

Erdős Problem #1005 asks for the asymptotics of `f(n)`, the length of the
longest run of consecutive "similarly ordered" Farey fractions of order `n`.
The known bounds are

* lower:  `f(n) ≥ (1/12 - o(1))·n`,
* upper:  `f(n) ≤ n/4 + O(1)`,

and the exact leading constant `c ∈ [1/12, 1/4]` is **open**.

The lower-bound constructions all rest on *mediant insertion*: the operation
that builds `F_{n+1}` from `F_n` by inserting, between every adjacent pair
`a/b < c/d`, their mediant `(a+c)/(b+d)`.  This file formalises the exact
arithmetic of that operation.  None of it resolves the open problem — the
constant `1/12` is a statement about runs of *similarly ordered* fractions and
remains out of reach.  What is established here is the verified gap calculus on
which any such argument is built:

* **Gap splitting.** A unimodular gap of size `1/(bd)` is split by its mediant
  into two sub-gaps of sizes `1/(b(b+d))` and `1/(d(b+d))`, in ratio `d : b`,
  and each strictly smaller than the original.
* **Minimal denominator (headline).** The mediant `(a+c)/(b+d)` is the *unique*
  fraction of smallest denominator lying strictly inside the gap: every
  rational `p/q` with `a/b < p/q < c/d` has `q ≥ b + d`, with equality forcing
  `p/q = (a+c)/(b+d)`.  Thus *no* refinement of a Farey gap can do better than
  mediant insertion — the denominator `b + d` is a hard lower bound.

Every theorem below is fully machine-checked: 0 sorries, 0 axioms (the file is
self-contained and does **not** import the `axiom longestSimilarRun` of the
parent `Erdos1005Problem.lean`).

Reference: https://erdosproblems.com/1005
-/

namespace Erdos1005OQ02

-- ══════════════════════════════════════════════════════════════════
-- § 1: Unimodular (adjacent Farey) pairs
-- ══════════════════════════════════════════════════════════════════

/-- `a/b < c/d` is a **unimodular pair** when `b·c − a·d = 1`.  This is exactly
the adjacency relation of two consecutive Farey fractions, and it forces the
value inequality `a/b < c/d`. -/
def Unimodular (a b c d : ℕ) : Prop := b * c = a * d + 1

/-- A unimodular pair is strictly increasing: `a/b < c/d`. -/
theorem unimodular_lt {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : Unimodular a b c d) : (a : ℚ) / b < (c : ℚ) / d := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  rw [div_lt_div_iff₀ hbq hdq]
  have hu : (b : ℚ) * c = a * d + 1 := by exact_mod_cast h
  nlinarith [hu]

-- ══════════════════════════════════════════════════════════════════
-- § 2: The gap formula  c/d − a/b = 1/(bd)
-- ══════════════════════════════════════════════════════════════════

/-- The size of a unimodular gap: `c/d − a/b = 1/(b·d)`. -/
theorem gap_eq {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : Unimodular a b c d) :
    (c : ℚ) / d - (a : ℚ) / b = 1 / (b * d) := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hu : (b : ℚ) * c = a * d + 1 := by exact_mod_cast h
  rw [div_sub_div _ _ hd0 hb0, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (b * d : ℚ) * hu

-- ══════════════════════════════════════════════════════════════════
-- § 3: Mediant insertion splits the gap
-- ══════════════════════════════════════════════════════════════════

/-- The mediant of a unimodular pair forms a unimodular pair with the **left**
endpoint: `a/b` and `(a+c)/(b+d)` satisfy `b·(a+c) − a·(b+d) = 1`. -/
theorem unimodular_left {a b c d : ℕ} (h : Unimodular a b c d) :
    Unimodular a b (a + c) (b + d) := by
  unfold Unimodular at h ⊢
  have h' : (b : ℤ) * c = a * d + 1 := by exact_mod_cast h
  have : (b : ℤ) * (a + c) = a * (b + d) + 1 := by linear_combination h'
  exact_mod_cast this

/-- The mediant of a unimodular pair forms a unimodular pair with the **right**
endpoint: `(a+c)/(b+d)` and `c/d` satisfy `(b+d)·c − (a+c)·d = 1`. -/
theorem unimodular_right {a b c d : ℕ} (h : Unimodular a b c d) :
    Unimodular (a + c) (b + d) c d := by
  unfold Unimodular at h ⊢
  have h' : (b : ℤ) * c = a * d + 1 := by exact_mod_cast h
  have : ((b : ℤ) + d) * c = (a + c) * d + 1 := by linear_combination h'
  exact_mod_cast this

/-- **Left sub-gap.** Inserting the mediant `(a+c)/(b+d)` creates a left gap of
size `1/(b·(b+d))`. -/
theorem mediant_gap_left {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : Unimodular a b c d) :
    (↑(a + c) : ℚ) / ↑(b + d) - (a : ℚ) / b = 1 / (b * (b + d)) := by
  have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  have hbd0 : (b : ℚ) + d ≠ 0 := by positivity
  have hu : (b : ℚ) * c = a * d + 1 := by exact_mod_cast h
  push_cast
  rw [div_sub_div _ _ hbd0 hb0, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (b * (b + d) : ℚ) * hu

/-- **Right sub-gap.** Inserting the mediant `(a+c)/(b+d)` creates a right gap of
size `1/(d·(b+d))`. -/
theorem mediant_gap_right {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : Unimodular a b c d) :
    (c : ℚ) / d - (↑(a + c) : ℚ) / ↑(b + d) = 1 / (d * (b + d)) := by
  have hd0 : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hbd0 : (b : ℚ) + d ≠ 0 := by positivity
  have hu : (b : ℚ) * c = a * d + 1 := by exact_mod_cast h
  push_cast
  rw [div_sub_div _ _ hd0 hbd0, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (d * (b + d) : ℚ) * hu

/-- The two sub-gaps sum to the original gap: `1/(b(b+d)) + 1/(d(b+d)) = 1/(bd)`.
This is `(mediant_gap_left) + (mediant_gap_right) = (gap_eq)` and shows mediant
insertion is exact — no measure is lost. -/
theorem subgaps_sum {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : Unimodular a b c d) :
    1 / (b * (b + d) : ℚ) + 1 / (d * (b + d) : ℚ) = 1 / (b * d : ℚ) := by
  have hl := mediant_gap_left hb hd h
  have hr := mediant_gap_right hb hd h
  have hg := gap_eq hb hd h
  push_cast at hl hr ⊢
  linarith [hl, hr, hg]

/-- **The mediant splits the gap in ratio `d : b`.**  The left sub-gap scaled by
`b` equals the right sub-gap scaled by `d` (both equal `1/(b+d)`); equivalently
`(left sub-gap) : (right sub-gap) = d : b`.  A *small* denominator endpoint takes
the *large* share of the gap. -/
theorem subgap_ratio {b d : ℕ} (hb : 0 < b) (hd : 0 < d) :
    (b : ℚ) * (1 / (b * (b + d))) = (d : ℚ) * (1 / (d * (b + d))) := by
  rw [mul_one_div, mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
  ring

/-- Each sub-gap is **strictly smaller** than the full gap: mediant insertion
strictly refines the partition.  Here for the left sub-gap. -/
theorem mediant_gap_left_lt {b d : ℕ} (hb : 0 < b) (hd : 0 < d) :
    1 / (b * (b + d) : ℚ) < 1 / (b * d : ℚ) := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  apply one_div_lt_one_div_of_lt (by positivity)
  nlinarith [hbq, hdq, mul_pos hbq hbq]

-- ══════════════════════════════════════════════════════════════════
-- § 4: The mediant minimises the denominator (headline)
-- ══════════════════════════════════════════════════════════════════

/-- **Key identity.** For a unimodular pair `a/b < c/d` and any `p/q`, the
denominator decomposes as
  `q = b·(c·q − p·d) + d·(p·b − a·q)`.
When `a/b < p/q < c/d` both bracketed terms are ≥ 1 integers, which is the
engine behind the denominator lower bound below.  Stated over `ℤ`. -/
theorem denom_identity {a b c d p q : ℤ} (h : b * c = a * d + 1) :
    q = b * (c * q - p * d) + d * (p * b - a * q) := by
  linear_combination (-q : ℤ) * h

/-- **Mediant minimises the denominator.**  If `a/b < c/d` is a unimodular pair
and `p/q` is *any* fraction strictly between them, then `q ≥ b + d`.

Equivalently: among all rationals in the open gap `(a/b, c/d)`, the mediant
`(a+c)/(b+d)` has the smallest denominator.  No refinement of a Farey gap can
introduce a fraction with denominator below `b + d`. -/
theorem denom_ge_of_between {a b c d p q : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hq : 0 < q) (h : Unimodular a b c d)
    (hlo : (a : ℚ) / b < (p : ℚ) / q) (hhi : (p : ℚ) / q < (c : ℚ) / d) :
    b + d ≤ q := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  -- a/b < p/q  ⇒  a·q < p·b  ⇒  (over ℤ) p·b − a·q ≥ 1
  have hY : (1 : ℤ) ≤ (p : ℤ) * b - a * q := by
    rw [div_lt_div_iff₀ hbq hqq] at hlo
    have hlt : (a : ℤ) * q < p * b := by exact_mod_cast hlo
    omega
  -- p/q < c/d  ⇒  p·d < c·q  ⇒  (over ℤ) c·q − p·d ≥ 1
  have hX : (1 : ℤ) ≤ (c : ℤ) * q - p * d := by
    rw [div_lt_div_iff₀ hqq hdq] at hhi
    have hlt : (p : ℤ) * d < c * q := by exact_mod_cast hhi
    omega
  have hu : (b : ℤ) * c = a * d + 1 := by exact_mod_cast h
  have hid := denom_identity (a := (a : ℤ)) (b := b) (c := c) (d := d)
    (p := p) (q := q) hu
  -- q = b·X + d·Y ≥ b·1 + d·1 = b + d
  have hbX : (b : ℤ) ≤ b * (c * q - p * d) :=
    le_mul_of_one_le_right (by exact_mod_cast hb.le) hX
  have hdY : (d : ℤ) ≤ d * (p * b - a * q) :=
    le_mul_of_one_le_right (by exact_mod_cast hd.le) hY
  have hge : (b : ℤ) + d ≤ q := by linarith [hid, hbX, hdY]
  exact_mod_cast hge

/-- **Equality characterises the mediant.**  If `p/q` lies strictly in the gap
of a unimodular pair and attains the minimal denominator `q = b + d`, then it is
exactly the mediant: `p = a + c`.  Hence the smallest-denominator fraction in a
Farey gap is *unique* and equals the mediant. -/
theorem eq_mediant_of_denom_eq {a b c d p q : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hq : 0 < q) (h : Unimodular a b c d)
    (hlo : (a : ℚ) / b < (p : ℚ) / q) (hhi : (p : ℚ) / q < (c : ℚ) / d)
    (hqeq : q = b + d) : p = a + c := by
  have hbq : (0 : ℚ) < b := by exact_mod_cast hb
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hqq : (0 : ℚ) < q := by exact_mod_cast hq
  have hY : (1 : ℤ) ≤ (p : ℤ) * b - a * q := by
    rw [div_lt_div_iff₀ hbq hqq] at hlo
    have hlt : (a : ℤ) * q < p * b := by exact_mod_cast hlo
    omega
  have hX : (1 : ℤ) ≤ (c : ℤ) * q - p * d := by
    rw [div_lt_div_iff₀ hqq hdq] at hhi
    have hlt : (p : ℤ) * d < c * q := by exact_mod_cast hhi
    omega
  have hu : (b : ℤ) * c = a * d + 1 := by exact_mod_cast h
  have hqz : (q : ℤ) = b + d := by exact_mod_cast hqeq
  have hb0 : (b : ℤ) ≠ 0 := by exact_mod_cast hb.ne'
  have hid := denom_identity (a := (a : ℤ)) (b := b) (c := c) (d := d)
    (p := p) (q := q) hu
  have hbX : (b : ℤ) ≤ b * (c * q - p * d) :=
    le_mul_of_one_le_right (by exact_mod_cast hb.le) hX
  have hdY : (d : ℤ) ≤ d * (p * b - a * q) :=
    le_mul_of_one_le_right (by exact_mod_cast hd.le) hY
  -- q = b+d and q = b·X + d·Y with b·X ≥ b, d·Y ≥ d ⇒ each is exactly tight
  have hdY1 : (d : ℤ) * (p * b - a * q) = d := by linarith [hid, hqz, hbX, hdY]
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hY1 : (p : ℤ) * b - a * q = 1 :=
    mul_left_cancel₀ hd0 (by rw [mul_one]; exact hdY1)
  -- p·b − a·q = 1, q = b+d, b·c = a·d+1  ⇒  p·b = (a+c)·b
  have hpb : (p : ℤ) * b = (a + c) * b := by
    linear_combination hY1 + (a : ℤ) * hqz - hu
  have hfin : (p : ℤ) = a + c := mul_right_cancel₀ hb0 hpb
  exact_mod_cast hfin

/-- **Mediant denominator, summarised.**  The mediant lies in the open gap and
attains the minimal denominator: every in-gap fraction has denominator
`≥ b + d`.  The value `b + d` is exactly the minimal denominator in
`(a/b, c/d)`. -/
theorem mediant_is_min_denominator {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : Unimodular a b c d) :
    ((a : ℚ) / b < (↑(a + c) : ℚ) / ↑(b + d) ∧
       (↑(a + c) : ℚ) / ↑(b + d) < (c : ℚ) / d) ∧
    (∀ p q : ℕ, 0 < q → (a : ℚ) / b < (p : ℚ) / q →
       (p : ℚ) / q < (c : ℚ) / d → b + d ≤ q) := by
  refine ⟨⟨?_, ?_⟩, fun p q hq hlo hhi => denom_ge_of_between hb hd hq h hlo hhi⟩
  · have hgap := mediant_gap_left hb hd h
    have hpos : (0 : ℚ) < 1 / (b * (b + d) : ℚ) := by positivity
    linarith [hgap, hpos]
  · have hgap := mediant_gap_right hb hd h
    have hpos : (0 : ℚ) < 1 / (d * (b + d) : ℚ) := by positivity
    linarith [hgap, hpos]

end Erdos1005OQ02
