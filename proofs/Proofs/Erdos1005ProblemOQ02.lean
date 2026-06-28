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
* **Depth dichotomy (§ 6–7).** Iterating insertion shows the two extreme descent
  regimes differ exponentially: a *one-sided* chain grows denominators linearly
  (`(k+1)·b + d`), admitting `Θ(n)` levels under the order cap, while a
  *balanced* (alternating) chain follows the Fibonacci recurrence — denominators
  `F_{2k+3}` doubling every two levels — admitting only `O(log n)` levels.
  Cassini's identity certifies the balanced bounding pairs as genuine Farey
  neighbours.

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

-- ══════════════════════════════════════════════════════════════════
-- § 5: Strict denominator growth and depth-two refinement (toward counting)
-- ══════════════════════════════════════════════════════════════════

/-- The mediant denominator strictly exceeds the **left** endpoint denominator. -/
theorem mediant_denom_gt_left {b d : ℕ} (hd : 0 < d) : b < b + d := by omega

/-- The mediant denominator strictly exceeds the **right** endpoint denominator. -/
theorem mediant_denom_gt_right {b d : ℕ} (hb : 0 < b) : d < b + d := by omega

/-- **Strict growth of interior denominators.**  Every fraction strictly inside a
unimodular gap has denominator strictly larger than *both* endpoint denominators:
`q ≥ b + d > max b d`.  Refinement therefore strictly increases the smallest
denominator present — the engine of any depth/counting argument. -/
theorem interior_denom_gt_max {a b c d p q : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hq : 0 < q) (h : Unimodular a b c d)
    (hlo : (a : ℚ) / b < (p : ℚ) / q) (hhi : (p : ℚ) / q < (c : ℚ) / d) :
    max b d < q := by
  have hge := denom_ge_of_between hb hd hq h hlo hhi
  omega

/-- **Depth-two bound, left sub-gap.**  The left sub-gap `(a/b, (a+c)/(b+d))` is
itself unimodular (`unimodular_left`), so any fraction strictly inside it has
denominator `≥ b + (b+d) = 2b + d`. -/
theorem denom_ge_left_subgap {a b c d p q : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hq : 0 < q) (h : Unimodular a b c d)
    (hlo : (a : ℚ) / b < (p : ℚ) / q)
    (hhi : (p : ℚ) / q < (↑(a + c) : ℚ) / ↑(b + d)) :
    b + (b + d) ≤ q := by
  have hbd : 0 < b + d := by omega
  exact denom_ge_of_between hb hbd hq (unimodular_left h) hlo hhi

/-- **Depth-two bound, right sub-gap.**  The right sub-gap `((a+c)/(b+d), c/d)` is
itself unimodular (`unimodular_right`), so any fraction strictly inside it has
denominator `≥ (b+d) + d = b + 2d`. -/
theorem denom_ge_right_subgap {a b c d p q : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hq : 0 < q) (h : Unimodular a b c d)
    (hlo : (↑(a + c) : ℚ) / ↑(b + d) < (p : ℚ) / q)
    (hhi : (p : ℚ) / q < (c : ℚ) / d) :
    (b + d) + d ≤ q := by
  have hbd : 0 < b + d := by omega
  exact denom_ge_of_between hbd hd hq (unimodular_right h) hlo hhi

/-- **Second-smallest interior denominator.**  Every fraction strictly inside the
gap *other than the mediant* falls in one of the two sub-gaps, so its denominator
is `≥ (b+d) + min b d`.  Hence the mediant is the *unique* fraction of denominator
`b+d` in the gap, and the next admissible denominator jumps by at least `min b d`.
Iterating this strict growth is precisely the depth/counting route flagged as the
next step toward the `1/12` run lower bound. -/
theorem denom_ge_of_between_ne_mediant {a b c d p q : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hq : 0 < q) (h : Unimodular a b c d)
    (hlo : (a : ℚ) / b < (p : ℚ) / q) (hhi : (p : ℚ) / q < (c : ℚ) / d)
    (hne : (p : ℚ) / q ≠ (↑(a + c) : ℚ) / ↑(b + d)) :
    (b + d) + min b d ≤ q := by
  rcases lt_or_gt_of_ne hne with hM | hM
  · -- p/q lies strictly below the mediant ⇒ inside the left sub-gap
    have hsub := denom_ge_left_subgap hb hd hq h hlo hM
    omega
  · -- p/q lies strictly above the mediant ⇒ inside the right sub-gap
    have hsub := denom_ge_right_subgap hb hd hq h hM hhi
    omega

-- ══════════════════════════════════════════════════════════════════
-- § 6: Iterated one-sided insertion — exact linear denominator growth
-- ══════════════════════════════════════════════════════════════════

/-
This section generalises the depth-two bounds of § 5 to arbitrary depth and, in
doing so, **corrects a tempting but false heuristic**: that the order-`n`
denominator cap forces only `O(log n)` mediant-refinement levels (a "Fibonacci /
golden-ratio" depth bound).  Exponential `φ^k` denominator growth is special to
*balanced* (alternating left/right) chains.  The *worst case* is the one-sided
chain `a/b, (a+c)/(b+d), (2a+c)/(2b+d), …`, whose `k`-th mediant has denominator
exactly `(k+1)·b + d` — **linear** in the depth `k`.  Concretely, the all-left
chain from the root gap `0/1 < 1/1` is `0/1, 1/2, 1/3, …, 1/n`, giving `Θ(n)`
refinement levels under the cap `q ≤ n`, not `O(log n)`.  Any genuine run-length
count must therefore distinguish balanced from one-sided descent — the two
extremes differ by an exponential factor in admissible depth.
-/

/-- **Iterated left insertion stays unimodular.**  Inserting the mediant into the
*left* sub-gap `k` times turns the unimodular pair `a/b < c/d` into
`a/b < (k·a + c)/(k·b + d)`, which is again unimodular.  No induction is needed:
the relation `b·c = a·d + 1` is invariant under `c ↦ k·a + c`, `d ↦ k·b + d`
(the added `k·a·b` cancels). -/
theorem unimodular_iterate_left (k : ℕ) {a b c d : ℕ} (h : Unimodular a b c d) :
    Unimodular a b (k * a + c) (k * b + d) := by
  unfold Unimodular at h ⊢
  have h' : (b : ℤ) * c = a * d + 1 := by exact_mod_cast h
  have : (b : ℤ) * (k * a + c) = a * (k * b + d) + 1 := by linear_combination h'
  exact_mod_cast this

/-- **Iterated right insertion stays unimodular.**  Symmetrically, inserting the
mediant into the *right* sub-gap `k` times turns `a/b < c/d` into
`(a + k·c)/(b + k·d) < c/d`, again unimodular. -/
theorem unimodular_iterate_right (k : ℕ) {a b c d : ℕ} (h : Unimodular a b c d) :
    Unimodular (a + k * c) (b + k * d) c d := by
  unfold Unimodular at h ⊢
  have h' : (b : ℤ) * c = a * d + 1 := by exact_mod_cast h
  have : ((b : ℤ) + k * d) * c = (a + k * c) * d + 1 := by linear_combination h'
  exact_mod_cast this

/-- **Depth-`k` denominator bound, left chain.**  The `k`-fold left sub-gap
`(a/b, (k·a+c)/(k·b+d))` is unimodular, so every fraction strictly inside it has
denominator `q ≥ b + (k·b + d) = (k+1)·b + d`.  The bound is **linear** in `k`:
each extra refinement level along a one-sided chain costs only `b` in
denominator, so up to `Θ(n)` such levels fit under the order-`n` cap. -/
theorem denom_ge_iterate_left (k : ℕ) {a b c d p q : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hq : 0 < q) (h : Unimodular a b c d)
    (hlo : (a : ℚ) / b < (p : ℚ) / q)
    (hhi : (p : ℚ) / q < (↑(k * a + c) : ℚ) / ↑(k * b + d)) :
    b + (k * b + d) ≤ q := by
  have hbd : 0 < k * b + d := by omega
  exact denom_ge_of_between hb hbd hq (unimodular_iterate_left k h) hlo hhi

/-- **Depth-`k` denominator bound, right chain.**  Symmetric to
`denom_ge_iterate_left`: every fraction strictly inside the `k`-fold right
sub-gap `((a+k·c)/(b+k·d), c/d)` has denominator `q ≥ (b + k·d) + d`. -/
theorem denom_ge_iterate_right (k : ℕ) {a b c d p q : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hq : 0 < q) (h : Unimodular a b c d)
    (hlo : (↑(a + k * c) : ℚ) / ↑(b + k * d) < (p : ℚ) / q)
    (hhi : (p : ℚ) / q < (c : ℚ) / d) :
    (b + k * d) + d ≤ q := by
  have hbd : 0 < b + k * d := by omega
  exact denom_ge_of_between hbd hd hq (unimodular_iterate_right k h) hlo hhi

/-- **The one-sided mediant denominator is exactly linear in depth.**  Reading
`denom_ge_iterate_left` at the successor depth, the mediant produced by `k+1`
left insertions sits at denominator `b + (k·b + d) = (k+1)·b + d`.  This exact
identity is the witness that one-sided descent grows denominators *linearly*, so
the number of admissible refinement levels under `q ≤ n` is `Θ(n)`. -/
theorem iterate_left_denom_linear (k b d : ℕ) :
    b + (k * b + d) = (k + 1) * b + d := by ring

-- ══════════════════════════════════════════════════════════════════
-- § 7: Balanced (alternating) insertion — exponential denominator growth
-- ══════════════════════════════════════════════════════════════════

/-
This section establishes the **other extreme** of the dichotomy announced in § 6.
Where the one-sided chain grows denominators *linearly* (`(k+1)·b + d`), the
*balanced* chain — the path through the Stern–Brocot tree that alternates left
and right at every level — grows them *exponentially*.

The balanced path from the root gap `0/1 < 1/1` produces the mediants
`1/2, 2/3, 3/5, 5/8, 8/13, …`: consecutive ratios of Fibonacci numbers.  The
bounding pairs along this path are exactly the consecutive Fibonacci fractions
`F_{2k}/F_{2k+1} < F_{2k+1}/F_{2k+2}`, which we show below are genuine unimodular
(adjacent Farey) pairs, so they really do arise from mediant insertion.  Their
mediant has denominator `F_{2k+1} + F_{2k+2} = F_{2k+3}`, so the denominator
obeys the Fibonacci recurrence and therefore **at least doubles every two
levels**.  Consequently only `O(log n)` balanced levels fit under the cap
`q ≤ n`, versus the `Θ(n)` one-sided levels of § 6 — an exponential separation
between the two descent strategies, and the precise content of the heuristic
that § 6 warned must *not* be applied to the worst case.
-/

/-- **Cassini's identity** (over `ℤ`).  `F_{n+1}² − F_n·F_{n+2} = (−1)ⁿ`.
This is the signed version of unimodularity for consecutive Fibonacci fractions:
the determinant of `[[F_n, F_{n+1}], [F_{n+1}, F_{n+2}]]` is `(−1)ⁿ`.  The proof
is a one-step induction: expanding `F_{n+3}` and `F_{n+2}` via the recurrence
turns the successor determinant into the negative of its predecessor. -/
theorem fib_cassini (n : ℕ) :
    (Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 2) = (-1) ^ n := by
  induction n with
  | zero => norm_num [Nat.fib_zero, Nat.fib_one, Nat.fib_two]
  | succ k ih =>
    have e2 : (Nat.fib (k + 2) : ℤ) = Nat.fib k + Nat.fib (k + 1) := by
      exact_mod_cast Nat.fib_add_two
    have e3 : (Nat.fib (k + 3) : ℤ) = Nat.fib (k + 1) + Nat.fib (k + 2) := by
      exact_mod_cast Nat.fib_add_two
    have hkey :
        (Nat.fib (k + 1 + 1) : ℤ) ^ 2 - Nat.fib (k + 1) * Nat.fib (k + 1 + 2)
          = -((Nat.fib (k + 1) : ℤ) ^ 2 - Nat.fib k * Nat.fib (k + 2)) := by
      have i1 : k + 1 + 1 = k + 2 := rfl
      have i2 : k + 1 + 2 = k + 3 := rfl
      rw [i1, i2, e3, e2]; ring
    rw [hkey, ih, pow_succ]; ring

/-- **Consecutive Fibonacci fractions are a unimodular (Farey) pair.**  Reading
Cassini at the *even* index `n = 2k` gives `F_{2k+1}² = F_{2k}·F_{2k+2} + 1`,
which is exactly `Unimodular F_{2k} F_{2k+1} F_{2k+1} F_{2k+2}`.  Thus the
balanced Stern–Brocot path consists of genuine adjacent Farey pairs, and the
minimal-denominator machinery of § 4 applies to it verbatim. -/
theorem unimodular_fib_even (k : ℕ) :
    Unimodular (Nat.fib (2 * k)) (Nat.fib (2 * k + 1))
               (Nat.fib (2 * k + 1)) (Nat.fib (2 * k + 2)) := by
  unfold Unimodular
  have hc := fib_cassini (2 * k)
  have hsign : ((-1 : ℤ)) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
  rw [hsign] at hc
  have h2 : (Nat.fib (2 * k + 1) : ℤ) * Nat.fib (2 * k + 1)
      = Nat.fib (2 * k) * Nat.fib (2 * k + 2) + 1 := by linear_combination hc
  exact_mod_cast h2

/-- **Two levels at least double the denominator.**  `2·F_k ≤ F_{k+2}`, because
`F_{k+2} = F_k + F_{k+1} ≥ F_k + F_k`.  This is the engine of exponential
growth: each pair of balanced refinement levels multiplies the denominator by at
least `2`, in sharp contrast to the additive `+b` cost of a one-sided level. -/
theorem fib_two_step_double (k : ℕ) : 2 * Nat.fib k ≤ Nat.fib (k + 2) := by
  rw [Nat.fib_add_two]
  have := Nat.fib_le_fib_succ (n := k)
  omega

/-- **Exponential lower bound on the balanced denominator.**  `2ʲ ≤ F_{2j+1}`.
The depth-`2j` balanced bounding fraction already has denominator at least `2ʲ`,
so it grows at least as fast as `2^{depth/2} = (√2)^{depth}`.  (The true rate is
`φ^{depth}`; `√2` is the clean integer floor.) -/
theorem fib_pow_lower (j : ℕ) : 2 ^ j ≤ Nat.fib (2 * j + 1) := by
  induction j with
  | zero => simp
  | succ k ih =>
    have h2 : 2 * 2 ^ k ≤ 2 * Nat.fib (2 * k + 1) := by omega
    have hd : 2 * Nat.fib (2 * k + 1) ≤ Nat.fib (2 * k + 1 + 2) :=
      fib_two_step_double (2 * k + 1)
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    have hidx : 2 * (k + 1) + 1 = 2 * k + 1 + 2 := by ring
    rw [hpow, hidx]
    omega

/-- **The balanced mediant obeys the Fibonacci recurrence.**  The mediant of the
unimodular pair `F_{2k}/F_{2k+1} < F_{2k+1}/F_{2k+2}` has denominator
`F_{2k+1} + F_{2k+2} = F_{2k+3}`: the next Fibonacci number.  So one balanced
refinement step advances the denominator index by two — the exponential
counterpart of `iterate_left_denom_linear`. -/
theorem balanced_mediant_denom (k : ℕ) :
    Nat.fib (2 * k + 1) + Nat.fib (2 * k + 2) = Nat.fib (2 * k + 3) := by
  have h : Nat.fib (2 * k + 1 + 2) = Nat.fib (2 * k + 1) + Nat.fib (2 * k + 1 + 1) :=
    Nat.fib_add_two
  simpa [show 2 * k + 1 + 2 = 2 * k + 3 from rfl,
         show 2 * k + 1 + 1 = 2 * k + 2 from rfl] using h.symm

/-- **Minimal denominator in a balanced gap.**  Specialising `denom_ge_of_between`
to the Fibonacci pair: every fraction strictly between `F_{2k}/F_{2k+1}` and
`F_{2k+1}/F_{2k+2}` has denominator `q ≥ F_{2k+3}`.  Combined with
`fib_pow_lower` this forces `q` to grow exponentially with the balanced depth. -/
theorem denom_ge_balanced (k : ℕ) {p q : ℕ} (hq : 0 < q)
    (hlo : (Nat.fib (2 * k) : ℚ) / Nat.fib (2 * k + 1) < (p : ℚ) / q)
    (hhi : (p : ℚ) / q < (Nat.fib (2 * k + 1) : ℚ) / Nat.fib (2 * k + 2)) :
    Nat.fib (2 * k + 3) ≤ q := by
  have hb : 0 < Nat.fib (2 * k + 1) := by rw [Nat.fib_pos]; omega
  have hd : 0 < Nat.fib (2 * k + 2) := by rw [Nat.fib_pos]; omega
  have hge := denom_ge_of_between hb hd hq (unimodular_fib_even k) hlo hhi
  rwa [balanced_mediant_denom] at hge

/-- **The dichotomy, quantified.**  If the depth-`2j` balanced bounding fraction
`F_{2j+1}` fits under the order cap `n` (i.e. `F_{2j+1} ≤ n`), then `2ʲ ≤ n`, so
`j ≤ log₂ n`.  Only `O(log n)` balanced levels are admissible — an *exponential*
separation from § 6, where `iterate_left_denom_linear` admits `Θ(n)` one-sided
levels under the same cap.  Any honest run-length count for `f(n)` must therefore
distinguish these two descent regimes. -/
theorem balanced_depth_log (j n : ℕ) (hcap : Nat.fib (2 * j + 1) ≤ n) :
    2 ^ j ≤ n :=
  le_trans (fib_pow_lower j) hcap

-- ══════════════════════════════════════════════════════════════════
-- § 8: Mediant chains are similarly ordered — the bridge to f(n)
-- ══════════════════════════════════════════════════════════════════

/-
Sections 1–7 develop the *metric* side of mediant insertion (gap sizes,
denominators, depth). The open problem, however, is about the *ordering* side:
`f(n)` counts the longest run of consecutive **similarly ordered** Farey
fractions, where `a/b` and `c/d` are similarly ordered iff
`(a − c)·(b − d) ≥ 0` (numerator and denominator move the same way).  This
section is the first link in the file between the two: it shows that mediant
insertion *automatically produces* similarly ordered families.

The headline is `simOrd_iterate_left_chain` / `_right_chain`: the entire
one-sided mediant chain of § 6 — of length `Θ(n)` under the order cap (§ 6) —
is **pairwise** similarly ordered.  This is exactly the combinatorial engine
behind the linear lower bound `f(n) ≥ c·n`: monotone mediant descent never
breaks similar ordering.

What this does **not** do — and the honest gap to the open constant — is supply
*consecutiveness*.  The chain `0/1, 1/2, 1/3, …, 1/n` is similarly ordered but
its members are **not** adjacent in `F_n` (e.g. `1/2, 1/3` are separated in
`F_5`).  Turning a similarly ordered mediant chain into a similarly ordered run
of *consecutive* Farey fractions is precisely where the `1/12`–`1/4` optimization
lives.  The predicate `SimOrd` below matches `similarlyOrdered` of
`Erdos1005ProblemProvable.lean` verbatim, so these lemmas plug directly into the
run definition there.
-/

/-- **Similar ordering** of `a/b` and `c/d`, as a predicate on the raw integer
data: the numerator and denominator differences have the same (weak) sign.  This
is definitionally the `similarlyOrdered` relation of
`Erdos1005ProblemProvable.lean`. -/
def SimOrd (a b c d : ℕ) : Prop :=
  ((a : ℤ) - c ≥ 0 ∧ (b : ℤ) - d ≥ 0) ∨ ((a : ℤ) - c ≤ 0 ∧ (b : ℤ) - d ≤ 0)

/-- Similar ordering is symmetric (swap the two fractions). -/
theorem simOrd_symm {a b c d : ℕ} (h : SimOrd a b c d) : SimOrd c d a b := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨by linarith, by linarith⟩
  · exact Or.inl ⟨by linarith, by linarith⟩

/-- Similar ordering is reflexive. -/
theorem simOrd_refl (a b : ℕ) : SimOrd a b a b := Or.inl ⟨by simp, by simp⟩

/-- **Product characterization.**  `SimOrd` holds iff the product of the two
differences is nonnegative, `(a − c)·(b − d) ≥ 0`.  This is the form most
convenient for arithmetic and shows `SimOrd` is exactly "same sign". -/
theorem simOrd_iff_prod {a b c d : ℕ} :
    SimOrd a b c d ↔ ((a : ℤ) - c) * ((b : ℤ) - d) ≥ 0 := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact mul_nonneg h1 h2
    · nlinarith [h1, h2]
  · intro h
    rcases le_or_gt 0 ((a : ℤ) - c) with ha | ha
    · rcases le_or_gt 0 ((b : ℤ) - d) with hb | hb
      · exact Or.inl ⟨ha, hb⟩
      · -- `(a-c) ≥ 0` and `(b-d) < 0` force `(a-c) = 0` (else product < 0)
        have : (a : ℤ) - c ≤ 0 := by nlinarith
        exact Or.inr ⟨this, by linarith⟩
    · rcases le_or_gt 0 ((b : ℤ) - d) with hb | hb
      · have : (b : ℤ) - d ≤ 0 := by nlinarith
        exact Or.inr ⟨by linarith, this⟩
      · exact Or.inr ⟨by linarith, by linarith⟩

/-- **The mediant is similarly ordered with its left parent.**  Going from `a/b`
to its mediant `(a+c)/(b+d)` increases both numerator (by `c`) and denominator
(by `d`), so the two are similarly ordered. -/
theorem simOrd_mediant_left (a b c d : ℕ) : SimOrd (a + c) (b + d) a b :=
  Or.inl ⟨by push_cast; linarith, by push_cast; linarith⟩

/-- **The mediant is similarly ordered with its right parent.**  Going from the
mediant `(a+c)/(b+d)` to `c/d` decreases both numerator (by `a`) and denominator
(by `b`), so the two are similarly ordered. -/
theorem simOrd_mediant_right (a b c d : ℕ) : SimOrd (a + c) (b + d) c d :=
  Or.inl ⟨by push_cast; linarith, by push_cast; linarith⟩

/-- **The one-sided (left) mediant chain is pairwise similarly ordered.**  Along
the § 6 left chain `eₖ = (k·a + c)/(k·b + d)`, deeper terms have larger numerator
*and* larger denominator (both grow linearly in the depth `k`), so any two terms
`eₖ` (`j ≤ k`) are similarly ordered.  Hence the **whole chain is a similarly
ordered family** — the order-side counterpart of the metric depth bounds of § 6,
and the engine of the linear lower bound on `f(n)`. -/
theorem simOrd_iterate_left_chain (a b c d j k : ℕ) (hjk : j ≤ k) :
    SimOrd (k * a + c) (k * b + d) (j * a + c) (j * b + d) := by
  have hk : (j : ℤ) ≤ k := by exact_mod_cast hjk
  refine Or.inl ⟨?_, ?_⟩
  · have : ((k : ℤ) - j) * a ≥ 0 := mul_nonneg (by linarith) (by positivity)
    push_cast; nlinarith
  · have : ((k : ℤ) - j) * b ≥ 0 := mul_nonneg (by linarith) (by positivity)
    push_cast; nlinarith

/-- **The one-sided (right) mediant chain is pairwise similarly ordered.**
Symmetric to `simOrd_iterate_left_chain` for the § 6 right chain
`eₖ = (a + k·c)/(b + k·d)`. -/
theorem simOrd_iterate_right_chain (a b c d j k : ℕ) (hjk : j ≤ k) :
    SimOrd (a + k * c) (b + k * d) (a + j * c) (b + j * d) := by
  have hk : (j : ℤ) ≤ k := by exact_mod_cast hjk
  refine Or.inl ⟨?_, ?_⟩
  · have : ((k : ℤ) - j) * c ≥ 0 := mul_nonneg (by linarith) (by positivity)
    push_cast; nlinarith
  · have : ((k : ℤ) - j) * d ≥ 0 := mul_nonneg (by linarith) (by positivity)
    push_cast; nlinarith

/-- **Similarly ordered chain under the order cap.**  Combining the order-side
fact (`simOrd_iterate_left_chain`) with the metric admissibility from § 6: every
term `eⱼ = (j·a + c)/(j·b + d)` of the left chain with depth `j ≤ k` has
denominator `≤ k·b + d`, and all such terms are pairwise similarly ordered.  So
if `k·b + d ≤ n`, the chain supplies `k + 1` pairwise similarly ordered fractions
all of order `≤ n`.  Since `k` can be taken `≈ (n − d)/b = Θ(n)`, mediant descent
produces *linearly long* similarly ordered families under the order-`n` cap.
(That these are not yet *consecutive* in `F_n` is the remaining open step — see
the section preamble.) -/
theorem simOrd_chain_admissible (a b c d k n : ℕ) (hcap : k * b + d ≤ n)
    {i j : ℕ} (hij : i ≤ j) (hjk : j ≤ k) :
    SimOrd (j * a + c) (j * b + d) (i * a + c) (i * b + d) ∧ j * b + d ≤ n := by
  refine ⟨simOrd_iterate_left_chain a b c d i j hij, ?_⟩
  have : j * b ≤ k * b := Nat.mul_le_mul_right b hjk
  omega

-- ══════════════════════════════════════════════════════════════════
-- § 9: The three-term Farey neighbour recurrence — the consecutiveness bridge
-- ══════════════════════════════════════════════════════════════════

/-
§ 8 produced similarly ordered families from *mediant* chains, but flagged the
honest gap: those chains are **not consecutive** in `F_n` (e.g. `1/2, 1/3` are
separated in `F_5`).  The open constant `1/12` is about runs of *consecutive*
Farey neighbours, so a faithful bridge must use the actual Farey successor.

This section formalises that successor.  If `a/b < c/d` are **consecutive** in
`F_n`, the fraction `e/f` immediately to the right of `c/d` is given by the
classical three-term recurrence (Hardy–Wright, *Theory of Numbers*, Thm 28–30)

* `e = k·c − a`,  `f = k·d − b`,  where `k = ⌊(n + b)/d⌋`.

We carry the recurrence in **addition form** `e + a = k·c`, `f + b = k·d`
(avoiding truncated ℕ subtraction) — these are exactly the relations the floor
`k = ⌊(n+b)/d⌋` realises.  Four metric facts and the order-side criterion are
proved, all 0-axiom:

* the successor is **again a Farey neighbour** (`farey_succ_unimodular`): the
  recurrence preserves unimodularity, so `c/d, e/f` are themselves consecutive;
* the successor lies strictly to the **right** (`farey_succ_lt`);
* the **symmetric three-term law** `d·(a+e) = c·(b+f)` (`farey_three_term`):
  the middle term `c/d` is the exact `k`-section of its two neighbours, the
  Farey form of `bₖ₋₁ + bₖ₊₁ = k·bₖ`;
* the **order-`n` cap** `f ≤ n ↔ k·d ≤ n + b` (`farey_succ_denom_le_iff`),
  which is what selects `k = ⌊(n+b)/d⌋` as the largest admissible step.

The headline is `simOrd_succ_controlling`: a *consecutive* step `c/d → e/f` is
similarly ordered **iff** `(a + c − k·c)·(b + d − k·d) ≥ 0`.  Unlike § 8 this is
genuine consecutiveness in `F_n`.  The corollary `simOrd_succ_k_eq_one` shows
the `k = 1` step is *always* similarly ordered (the product collapses to
`a·b ≥ 0`).  For `k ≥ 2` the sign of that product is exactly the quantity whose
control over a consecutive block separates the `1/12` lower bound from the `1/4`
upper bound — the precise open step is now an explicit arithmetic inequality on
the successive quotients `k`, not a vague appeal to "consecutiveness".
-/

/-- **The Farey successor is again a Farey neighbour.**  If `a/b, c/d` are
consecutive (`Unimodular a b c d`) and `e/f` is produced by the recurrence
`e + a = k·c`, `f + b = k·d`, then `c/d, e/f` are consecutive too
(`Unimodular c d e f`, i.e. `d·e = c·f + 1`).  Unimodularity is preserved by the
three-term step, so iterating it walks along genuinely adjacent fractions. -/
theorem farey_succ_unimodular {a b c d e f k : ℕ}
    (h : Unimodular a b c d) (he : e + a = k * c) (hf : f + b = k * d) :
    Unimodular c d e f := by
  unfold Unimodular at h ⊢
  zify at h he hf ⊢
  linear_combination d * he - c * hf + h

/-- **The successor lies strictly to the right of `c/d`.**  From the preserved
unimodularity `d·e = c·f + 1` we get `c·f < d·e`, i.e. `c/d < e/f`. -/
theorem farey_succ_lt {a b c d e f k : ℕ}
    (h : Unimodular a b c d) (he : e + a = k * c) (hf : f + b = k * d) :
    c * f < d * e := by
  have hu := farey_succ_unimodular h he hf
  unfold Unimodular at hu
  omega

/-- **Symmetric three-term recurrence.**  The middle fraction `c/d` is the exact
`k`-section of its two neighbours: `d·(a + e) = c·(b + f)` (both equal `k·c·d`).
Equivalently `(a + e)/(b + f) = c/d` — the Farey analogue of the denominator
recurrence `bₖ₋₁ + bₖ₊₁ = k·bₖ`. -/
theorem farey_three_term {a b c d e f k : ℕ}
    (he : e + a = k * c) (hf : f + b = k * d) :
    d * (a + e) = c * (b + f) := by
  have h1 : a + e = k * c := by omega
  have h2 : b + f = k * d := by omega
  rw [h1, h2]; ring

/-- **Order-`n` cap.**  The successor denominator `f` (with `f + b = k·d`) is
`≤ n` iff `k·d ≤ n + b`.  The largest admissible quotient is therefore
`k = ⌊(n + b)/d⌋`, which is exactly the value the classical recurrence uses to
pick the next Farey neighbour of order `n`. -/
theorem farey_succ_denom_le_iff {b d f k n : ℕ} (hf : f + b = k * d) :
    f ≤ n ↔ k * d ≤ n + b := by omega

/-- **Per-step similar-ordering criterion (headline).**  For a *consecutive*
Farey step `c/d → e/f` given by the recurrence `e + a = k·c`, `f + b = k·d`, the
pair is similarly ordered **iff** `(a + c − k·c)·(b + d − k·d) ≥ 0`.  This is the
true consecutiveness bridge: the quantity controlling whether a run continues is
now an explicit arithmetic condition on the successive quotient `k`. -/
theorem simOrd_succ_controlling {a b c d e f k : ℕ}
    (he : e + a = k * c) (hf : f + b = k * d) :
    SimOrd c d e f ↔ ((a : ℤ) + c - k * c) * ((b : ℤ) + d - k * d) ≥ 0 := by
  have He : (e : ℤ) = k * c - a := by
    have : (e : ℤ) + a = k * c := by exact_mod_cast he
    linarith
  have Hf : (f : ℤ) = k * d - b := by
    have : (f : ℤ) + b = k * d := by exact_mod_cast hf
    linarith
  have key : ((c : ℤ) - e) * ((d : ℤ) - f)
      = ((a : ℤ) + c - k * c) * ((b : ℤ) + d - k * d) := by
    rw [He, Hf]; ring
  rw [simOrd_iff_prod, key]

/-- **The `k = 1` step is always similarly ordered.**  When the successive
quotient is `1` (so `e + a = c`, `f + b = d`), the controlling product collapses
to `a·b ≥ 0`, which always holds.  Thus the shortest Farey steps never break a
similarly ordered run.  (§ 10 strengthens this: in fact *no* quotient `k` can
break it — every adjacent step is similarly ordered.) -/
theorem simOrd_succ_k_eq_one {a b c d e f : ℕ} (he : e + a = c) (hf : f + b = d) :
    SimOrd c d e f := by
  refine Or.inl ⟨?_, ?_⟩ <;> omega

-- ══════════════════════════════════════════════════════════════════
-- § 10: Every Farey-adjacent pair is similarly ordered — runs break
--        only across NON-adjacent pairs
-- ══════════════════════════════════════════════════════════════════

/-
§ 9 reduced a *single* consecutive step `c/d → e/f` to the sign of the
controlling product `(a + c − k·c)·(b + d − k·d)`, and showed the `k = 1` step is
always similarly ordered.  This section settles the sign in **full generality**:
the product is *always* `≥ 0`, because **every** unimodular (Farey-adjacent) pair
is similarly ordered — not only the `k = 1` ones.

The headline `unimodular_simOrd` proves this directly from `b·c = a·d + 1`.  A
pair can fail similar ordering in exactly two ways, and unimodularity excludes
both (each needing only `0 < b`, `0 < d`):

* `a < c ∧ d < b`  is excluded because it forces
  `b·c ≥ (a+1)·(d+1) = a·d + a + d + 1 > a·d + 1`  (`unimodular_excl_cross_left`);
* `c < a ∧ b < d`  is excluded because it forces
  `a·d ≥ (c+1)·(b+1) = b·c + b + c + 1 > b·c − 1 = a·d`  (`unimodular_excl_cross_right`),
  i.e. it would make `a/b > c/d`, contradicting adjacency.

This is a genuine **correction** to the §9 preamble, which suggested that
`k ≥ 2` steps are where runs break.  They are not: a single Farey step **never**
breaks a similarly ordered run, for any quotient `k` (`farey_succ_simOrd`), so
the §9 controlling product is unconditionally `≥ 0` (`succ_controlling_nonneg`).
The entire `1/12`–`1/4` gap therefore lives in the **non-adjacent** pairs of a
window: `isSimOrdered` (in `Erdos1005ProblemProvable.lean`) demands similar
ordering for *every* pair `j₁ < j₂` of the block, and it is precisely the
`j₂ > j₁ + 1` pairs — never the adjacent `j₂ = j₁ + 1` ones — that can fail.
-/

/-- **No "small-num / large-denom" inversion.**  For a unimodular pair
`a/b < c/d`, one cannot have `a < c` together with `d < b`: that would give
`b·c ≥ (a+1)(d+1) = a·d + a + d + 1`, contradicting `b·c = a·d + 1` (as
`a + d ≥ d ≥ 1`). -/
theorem unimodular_excl_cross_left {a b c d : ℕ} (hd : 0 < d)
    (h : Unimodular a b c d) : ¬ ((a : ℤ) < c ∧ (d : ℤ) < b) := by
  unfold Unimodular at h
  rintro ⟨h1, h2⟩
  have hz : (b : ℤ) * c = (a : ℤ) * d + 1 := by exact_mod_cast h
  have hd' : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have ha' : (0 : ℤ) ≤ a := by positivity
  have hc' : (0 : ℤ) ≤ c := by positivity
  nlinarith [mul_le_mul (show (a : ℤ) + 1 ≤ c by linarith)
              (show (d : ℤ) + 1 ≤ b by linarith) (by linarith) (by linarith),
             hz, hd', ha']

/-- **No "large-num / small-denom" inversion.**  For a unimodular pair
`a/b < c/d`, one cannot have `c < a` together with `b < d`: that would give
`a·d ≥ (c+1)(b+1) = b·c + b + c + 1`, contradicting `a·d = b·c − 1`.  (This is
the case that would make `a/b > c/d`, breaking the order.) -/
theorem unimodular_excl_cross_right {a b c d : ℕ} (hb : 0 < b)
    (h : Unimodular a b c d) : ¬ ((c : ℤ) < a ∧ (b : ℤ) < d) := by
  unfold Unimodular at h
  rintro ⟨h1, h2⟩
  have hz : (b : ℤ) * c = (a : ℤ) * d + 1 := by exact_mod_cast h
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  have ha' : (0 : ℤ) ≤ a := by positivity
  have hc' : (0 : ℤ) ≤ c := by positivity
  nlinarith [mul_le_mul (show (c : ℤ) + 1 ≤ a by linarith)
              (show (b : ℤ) + 1 ≤ d by linarith) (by linarith) (by linarith),
             hz, hb', hc']

/-- **Every Farey-adjacent pair is similarly ordered.**  A unimodular pair
`a/b < c/d` (`b·c = a·d + 1`, positive denominators) always satisfies
`SimOrd a b c d`: numerator and denominator never move in opposite directions
across a single Farey step.  This generalises `simOrd_succ_k_eq_one` (the
`k = 1` case) to *all* adjacent pairs, and is the order-side analogue of
`unimodular_lt`. -/
theorem unimodular_simOrd {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (h : Unimodular a b c d) : SimOrd a b c d := by
  rcases le_total (a : ℤ) c with hac | hca
  · rcases le_total (d : ℤ) b with hdb | hbd
    · -- `a ≤ c` and `d ≤ b`: opposite weak signs, so a factor must vanish.
      rcases lt_or_eq_of_le hac with hlt | heq
      · rcases lt_or_eq_of_le hdb with hlt2 | heq2
        · exact absurd ⟨hlt, hlt2⟩ (unimodular_excl_cross_left hd h)
        · exact Or.inr ⟨by linarith, by linarith⟩      -- d = b
      · exact Or.inl ⟨by linarith, by linarith⟩          -- a = c
    · exact Or.inr ⟨by linarith, by linarith⟩            -- a ≤ c, b ≤ d
  · rcases le_total (b : ℤ) d with hbd | hdb
    · -- `c ≤ a` and `b ≤ d`: opposite weak signs, so a factor must vanish.
      rcases lt_or_eq_of_le hca with hlt | heq
      · rcases lt_or_eq_of_le hbd with hlt2 | heq2
        · exact absurd ⟨hlt, hlt2⟩ (unimodular_excl_cross_right hb h)
        · exact Or.inl ⟨by linarith, by linarith⟩        -- b = d
      · exact Or.inr ⟨by linarith, by linarith⟩          -- c = a
    · exact Or.inl ⟨by linarith, by linarith⟩            -- c ≤ a, d ≤ b

/-- **A consecutive Farey step is always similarly ordered.**  Given a
Farey-neighbour pair `a/b, c/d` and its successor `e/f` from the three-term
recurrence (`e + a = k·c`, `f + b = k·d`), the step `c/d → e/f` satisfies
`SimOrd c d e f` for *every* quotient `k`: the successor is again a Farey
neighbour (`farey_succ_unimodular`), and adjacent pairs are always similarly
ordered (`unimodular_simOrd`).  Adjacency alone can never break a run. -/
theorem farey_succ_simOrd {a b c d e f k : ℕ} (hd : 0 < d) (hf_pos : 0 < f)
    (h : Unimodular a b c d) (he : e + a = k * c) (hfb : f + b = k * d) :
    SimOrd c d e f :=
  unimodular_simOrd hd hf_pos (farey_succ_unimodular h he hfb)

/-- **The §9 controlling product is unconditionally nonnegative.**  Combining
`simOrd_succ_controlling` with `farey_succ_simOrd`: for any genuine consecutive
step the product `(a + c − k·c)·(b + d − k·d)` is always `≥ 0`.  So the per-step
criterion of §9 is *always* satisfied — the run-length obstruction behind the
`1/12`–`1/4` gap is entirely a non-adjacent phenomenon, not a per-step one. -/
theorem succ_controlling_nonneg {a b c d e f k : ℕ} (hd : 0 < d) (hf_pos : 0 < f)
    (h : Unimodular a b c d) (he : e + a = k * c) (hfb : f + b = k * d) :
    ((a : ℤ) + c - k * c) * ((b : ℤ) + d - k * d) ≥ 0 :=
  (simOrd_succ_controlling he hfb).mp (farey_succ_simOrd hd hf_pos h he hfb)

-- ══════════════════════════════════════════════════════════════════
-- § 11: The first NON-adjacent obstruction — length-3 runs
-- ══════════════════════════════════════════════════════════════════

/-
§ 10 showed every *adjacent* Farey pair is similarly ordered, so the smallest
place a run can break is a length-3 block `a/b, c/d, e/f` of three *consecutive*
neighbours: its two adjacent pairs are free, and the only constraint is the
**outer (non-adjacent) pair** `a/b, e/f`.

Writing the successor via the §9 recurrence `e = k·c − a`, `f = k·d − b`, the
outer pair is similarly ordered **iff** `(2a − k·c)·(2b − k·d) ≥ 0`
(`simOrd_outer_iff`).  So a length-3 run is similarly ordered iff that single
arithmetic inequality on the quotient `k` holds (`simOrd_triple`).

Contrast §9/§10: the *adjacent* product `(a − (k−1)c)(b − (k−1)d)` is always
`≥ 0`, whereas the *outer* product `(2a − k·c)(2b − k·d) = (a − (k·c−a))(b − (k·d−b))`
can be negative — precisely when `k` lies strictly between `2a/c` and `2b/d`.
That interval has width `2b/d − 2a/c = 2·(b·c − a·d)/(c·d) = 2/(c·d)`, so a
length-3 break requires the successor quotient `k` to fall in an interval of
width `2/(c·d)` — the first explicit, *metric*, criterion for a run to break.
-/

/-- **Outer-pair criterion.**  With the successor recurrence `e + a = k·c`,
`f + b = k·d`, the *non-adjacent* pair `a/b, e/f` is similarly ordered **iff**
`(2a − k·c)·(2b − k·d) ≥ 0`.  (Compare `simOrd_succ_controlling` for the adjacent
pair; the `2`s are what make this product able to go negative.) -/
theorem simOrd_outer_iff {a b c d e f k : ℕ} (he : e + a = k * c) (hf : f + b = k * d) :
    SimOrd a b e f ↔ (2 * (a : ℤ) - k * c) * (2 * (b : ℤ) - k * d) ≥ 0 := by
  have He : (e : ℤ) = k * c - a := by
    have : (e : ℤ) + a = k * c := by exact_mod_cast he
    linarith
  have Hf : (f : ℤ) = k * d - b := by
    have : (f : ℤ) + b = k * d := by exact_mod_cast hf
    linarith
  have key : ((a : ℤ) - e) * ((b : ℤ) - f)
      = (2 * (a : ℤ) - k * c) * (2 * (b : ℤ) - k * d) := by
    rw [He, Hf]; ring
  rw [simOrd_iff_prod, key]

/-- **A length-3 run reduces to its outer pair.**  For three consecutive Farey
neighbours `a/b, c/d, e/f` the two adjacent pairs are *automatically* similarly
ordered (§10), so the whole block is pairwise similarly ordered iff the outer
(non-adjacent) pair `a/b, e/f` is.  This is the first point at which
non-adjacency can break a run. -/
theorem simOrd_triple_iff_outer {a b c d e f k : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hf_pos : 0 < f) (hcd : Unimodular a b c d)
    (he : e + a = k * c) (hfb : f + b = k * d) :
    (SimOrd a b c d ∧ SimOrd c d e f ∧ SimOrd a b e f) ↔ SimOrd a b e f := by
  have h1 := unimodular_simOrd hb hd hcd
  have h2 := unimodular_simOrd hd hf_pos (farey_succ_unimodular hcd he hfb)
  exact ⟨fun h => h.2.2, fun h => ⟨h1, h2, h⟩⟩

/-- **Length-3 run criterion (headline).**  Three consecutive Farey neighbours
`a/b, c/d, e/f` (with `e + a = k·c`, `f + b = k·d`) form a similarly ordered run
**iff** `(2a − k·c)·(2b − k·d) ≥ 0`.  Since the adjacent pairs are free (§10),
the only obstruction is this explicit inequality on the successor quotient `k` —
the first non-adjacent break condition, controlled by an interval of width
`2/(c·d)`. -/
theorem simOrd_triple {a b c d e f k : ℕ} (hb : 0 < b) (hd : 0 < d) (hf_pos : 0 < f)
    (hcd : Unimodular a b c d) (he : e + a = k * c) (hfb : f + b = k * d) :
    (SimOrd a b c d ∧ SimOrd c d e f ∧ SimOrd a b e f)
      ↔ (2 * (a : ℤ) - k * c) * (2 * (b : ℤ) - k * d) ≥ 0 := by
  rw [simOrd_triple_iff_outer hb hd hf_pos hcd he hfb, simOrd_outer_iff he hfb]

-- ══════════════════════════════════════════════════════════════════
-- § 12: Length-4 runs — two quotients, and the long-range obstruction
-- ══════════════════════════════════════════════════════════════════

/-
§ 11 settled the smallest run that can break, a length-3 block governed by a
*single* successor quotient `k`.  A length-4 block `a/b, c/d, e/f, g/h` is the
first run driven by **two** quotients: writing the §9 recurrence twice,

  `e = k₁·c − a`,  `f = k₁·d − b`      (first step, quotient `k₁`)
  `g = k₂·e − c`,  `h = k₂·f − d`      (second step, quotient `k₂`)

Of the six pairs, the three *adjacent* ones are free (§10).  The three
non-adjacent obstructions split into the two length-3 outer criteria of §11
(one per consecutive triple) **plus a genuinely new long-range pair** `a/b, g/h`
spanning the whole block.  Substituting the recurrences collapses the fourth
term to a closed form in the *first* pair,

  `g = (k₁·k₂ − 1)·c − k₂·a`,   `h = (k₁·k₂ − 1)·d − k₂·b`,

so the long pair is similarly ordered **iff**
`((k₂+1)·a − (k₁·k₂−1)·c)·((k₂+1)·b − (k₁·k₂−1)·d) ≥ 0` (`simOrd_long_iff`).
This is the order-side shadow of the Stern–Brocot product `k₁·k₂ − 1`: the
combined "depth" of the two steps, not either one alone, controls whether the
endpoints of a length-4 run stay similarly ordered.  The headline `simOrd_quad`
assembles the run criterion as the conjunction of the two §11 windows and this
new long-range window.
-/

/-- **Long-range criterion for a length-4 run.**  Iterating the successor
recurrence twice (`e + a = k₁·c`, `f + b = k₁·d`, then `g + c = k₂·e`,
`h + d = k₂·f`) expresses the fourth term as `g = (k₁·k₂−1)·c − k₂·a`,
`h = (k₁·k₂−1)·d − k₂·b`, so the *endpoints* `a/b, g/h` are similarly ordered
**iff** `((k₂+1)·a − (k₁·k₂−1)·c)·((k₂+1)·b − (k₁·k₂−1)·d) ≥ 0`.  The controlling
quantity is the Stern–Brocot product `k₁·k₂ − 1`, the combined depth of the two
steps. -/
theorem simOrd_long_iff {a b c d e f g h k₁ k₂ : ℕ}
    (he : e + a = k₁ * c) (hf : f + b = k₁ * d)
    (hg : g + c = k₂ * e) (hh : h + d = k₂ * f) :
    SimOrd a b g h ↔
      (((k₂ : ℤ) + 1) * a - ((k₁ : ℤ) * k₂ - 1) * c)
        * (((k₂ : ℤ) + 1) * b - ((k₁ : ℤ) * k₂ - 1) * d) ≥ 0 := by
  have He : (e : ℤ) = k₁ * c - a := by
    have : (e : ℤ) + a = k₁ * c := by exact_mod_cast he
    linarith
  have Hf : (f : ℤ) = k₁ * d - b := by
    have : (f : ℤ) + b = k₁ * d := by exact_mod_cast hf
    linarith
  have Hg : (g : ℤ) = k₂ * e - c := by
    have : (g : ℤ) + c = k₂ * e := by exact_mod_cast hg
    linarith
  have Hh : (h : ℤ) = k₂ * f - d := by
    have : (h : ℤ) + d = k₂ * f := by exact_mod_cast hh
    linarith
  have key : ((a : ℤ) - g) * ((b : ℤ) - h)
      = (((k₂ : ℤ) + 1) * a - ((k₁ : ℤ) * k₂ - 1) * c)
          * (((k₂ : ℤ) + 1) * b - ((k₁ : ℤ) * k₂ - 1) * d) := by
    rw [Hg, Hh, He, Hf]; ring
  rw [simOrd_iff_prod, key]

/-- **Length-4 run criterion (headline).**  Four consecutive Farey neighbours
`a/b, c/d, e/f, g/h` produced by two successor steps (`e + a = k₁·c`,
`f + b = k₁·d`, `g + c = k₂·e`, `h + d = k₂·f`) form a pairwise similarly ordered
run **iff** all three non-adjacent windows are nonnegative: the two length-3
windows of §11 (one per consecutive triple) and the new long-range window of
`simOrd_long_iff`.  The three adjacent pairs are automatically free (§10), so the
two quotients `k₁, k₂` interact *only* through these three explicit inequalities —
and the long-range one is controlled by the combined depth `k₁·k₂ − 1`, the first
place a run can break for reasons invisible to either single step. -/
theorem simOrd_quad {a b c d e f g h k₁ k₂ : ℕ}
    (hb : 0 < b) (hd : 0 < d) (hf_pos : 0 < f) (hh_pos : 0 < h)
    (hcd : Unimodular a b c d)
    (he : e + a = k₁ * c) (hfb : f + b = k₁ * d)
    (hg : g + c = k₂ * e) (hhd : h + d = k₂ * f) :
    (SimOrd a b c d ∧ SimOrd c d e f ∧ SimOrd e f g h
        ∧ SimOrd a b e f ∧ SimOrd c d g h ∧ SimOrd a b g h)
      ↔ ((2 * (a : ℤ) - k₁ * c) * (2 * (b : ℤ) - k₁ * d) ≥ 0
          ∧ (2 * (c : ℤ) - k₂ * e) * (2 * (d : ℤ) - k₂ * f) ≥ 0
          ∧ (((k₂ : ℤ) + 1) * a - ((k₁ : ℤ) * k₂ - 1) * c)
              * (((k₂ : ℤ) + 1) * b - ((k₁ : ℤ) * k₂ - 1) * d) ≥ 0) := by
  have hcdef : Unimodular c d e f := farey_succ_unimodular hcd he hfb
  have hefgh : Unimodular e f g h := farey_succ_unimodular hcdef hg hhd
  have s1 : SimOrd a b c d := unimodular_simOrd hb hd hcd
  have s2 : SimOrd c d e f := unimodular_simOrd hd hf_pos hcdef
  have s3 : SimOrd e f g h := unimodular_simOrd hf_pos hh_pos hefgh
  constructor
  · rintro ⟨_, _, _, h4, h5, h6⟩
    exact ⟨(simOrd_outer_iff he hfb).mp h4,
           (simOrd_outer_iff hg hhd).mp h5,
           (simOrd_long_iff he hfb hg hhd).mp h6⟩
  · rintro ⟨c1, c2, c3⟩
    exact ⟨s1, s2, s3,
           (simOrd_outer_iff he hfb).mpr c1,
           (simOrd_outer_iff hg hhd).mpr c2,
           (simOrd_long_iff he hfb hg hhd).mpr c3⟩

-- ══════════════════════════════════════════════════════════════════
-- § 13: Length-5 runs — three quotients, and the continuant Kₘ
-- ══════════════════════════════════════════════════════════════════

/-
§ 12 found that a length-4 run's long-range obstruction is governed by the
Stern–Brocot product `k₁·k₂ − 1`, the combined depth of its *two* steps.  A
length-5 block `a/b, c/d, e/f, g/h, i/j` is the first run driven by **three**
quotients: writing the §9 recurrence three times,

  `e = k₁·c − a`,  `f = k₁·d − b`      (step 1, quotient `k₁`)
  `g = k₂·e − c`,  `h = k₂·f − d`      (step 2, quotient `k₂`)
  `i = k₃·g − e`,  `j = k₃·h − f`      (step 3, quotient `k₃`)

Substituting the three recurrences collapses the *fifth* term to a closed form in
the *first* pair `a/b, c/d`,

  `i = (k₁·k₂·k₃ − k₁ − k₃)·c − (k₂·k₃ − 1)·a`,
  `j = (k₁·k₂·k₃ − k₁ − k₃)·d − (k₂·k₃ − 1)·b`,

so the long pair `a/b, i/j` is similarly ordered **iff**
`(k₂·k₃·a − (k₁·k₂·k₃ − k₁ − k₃)·c)·(k₂·k₃·b − (k₁·k₂·k₃ − k₁ − k₃)·d) ≥ 0`
(`simOrd_long3_iff`).  The coefficient of `c` here is the **continuant**
`K(k₁,k₂,k₃) = k₁·k₂·k₃ − k₁ − k₃` and the coefficient of `a` is the trailing
continuant `K(k₂,k₃) = k₂·k₃ − 1`.  This is the order-side shadow of the very
recurrence (`xₘ₊₁ = kₘ·xₘ − xₘ₋₁`) that generates Farey numerators and
denominators: the controlling quantity for the endpoints of a run is the full
**continuant of all its intervening quotients**, not any single step.  The
pattern across §11/§12/§13 is exactly the continuant ladder
`K() = 1, K(k) = k, K(k₁,k₂) = k₁k₂−1, K(k₁,k₂,k₃) = k₁k₂k₃−k₁−k₃`.

The headline `simOrd_quint` assembles the full length-5 run criterion as the
conjunction of the six non-adjacent windows: the three length-3 windows of §11
(one per consecutive triple), the two length-4 long windows of §12 (one per
consecutive quadruple), and the new length-5 continuant window of
`simOrd_long3_iff`.  The four adjacent pairs are free (§10).
-/

/-- **Three-quotient long-range criterion (length-5 run).**  Iterating the
successor recurrence three times expresses the fifth term as
`i = (k₁·k₂·k₃ − k₁ − k₃)·c − (k₂·k₃ − 1)·a`,
`j = (k₁·k₂·k₃ − k₁ − k₃)·d − (k₂·k₃ − 1)·b`, so the *endpoints* `a/b, i/j` are
similarly ordered **iff**
`(k₂·k₃·a − (k₁·k₂·k₃−k₁−k₃)·c)·(k₂·k₃·b − (k₁·k₂·k₃−k₁−k₃)·d) ≥ 0`.  The
controlling quantity is the continuant `K(k₁,k₂,k₃) = k₁·k₂·k₃ − k₁ − k₃`, the
combined depth of all three steps — the order-side counterpart of the
numerator/denominator continuant recurrence `xₘ₊₁ = kₘ·xₘ − xₘ₋₁`. -/
theorem simOrd_long3_iff {a b c d e f g h i j k₁ k₂ k₃ : ℕ}
    (he : e + a = k₁ * c) (hf : f + b = k₁ * d)
    (hg : g + c = k₂ * e) (hh : h + d = k₂ * f)
    (hi : i + e = k₃ * g) (hj : j + f = k₃ * h) :
    SimOrd a b i j ↔
      (((k₂ : ℤ) * k₃) * a - ((k₁ : ℤ) * k₂ * k₃ - k₁ - k₃) * c)
        * (((k₂ : ℤ) * k₃) * b - ((k₁ : ℤ) * k₂ * k₃ - k₁ - k₃) * d) ≥ 0 := by
  have He : (e : ℤ) = k₁ * c - a := by
    have : (e : ℤ) + a = k₁ * c := by exact_mod_cast he
    linarith
  have Hf : (f : ℤ) = k₁ * d - b := by
    have : (f : ℤ) + b = k₁ * d := by exact_mod_cast hf
    linarith
  have Hg : (g : ℤ) = k₂ * e - c := by
    have : (g : ℤ) + c = k₂ * e := by exact_mod_cast hg
    linarith
  have Hh : (h : ℤ) = k₂ * f - d := by
    have : (h : ℤ) + d = k₂ * f := by exact_mod_cast hh
    linarith
  have Hi : (i : ℤ) = k₃ * g - e := by
    have : (i : ℤ) + e = k₃ * g := by exact_mod_cast hi
    linarith
  have Hj : (j : ℤ) = k₃ * h - f := by
    have : (j : ℤ) + f = k₃ * h := by exact_mod_cast hj
    linarith
  have key : ((a : ℤ) - i) * ((b : ℤ) - j)
      = (((k₂ : ℤ) * k₃) * a - ((k₁ : ℤ) * k₂ * k₃ - k₁ - k₃) * c)
          * (((k₂ : ℤ) * k₃) * b - ((k₁ : ℤ) * k₂ * k₃ - k₁ - k₃) * d) := by
    rw [Hi, Hj, Hg, Hh, He, Hf]; ring
  rw [simOrd_iff_prod, key]

/-- **Length-5 run criterion (headline).**  Five consecutive Farey neighbours
`a/b, c/d, e/f, g/h, i/j` produced by three successor steps form a pairwise
similarly ordered run **iff** all six non-adjacent windows are nonnegative: the
three length-3 windows of §11 (one per consecutive triple), the two length-4
long windows of §12 (one per consecutive quadruple), and the new length-5
continuant window of `simOrd_long3_iff`.  The four adjacent pairs are free (§10),
so the three quotients `k₁, k₂, k₃` interact *only* through these six explicit
inequalities — and the longest-range one is controlled by the full continuant
`K(k₁,k₂,k₃) = k₁·k₂·k₃ − k₁ − k₃`. -/
theorem simOrd_quint {a b c d e f g h i j k₁ k₂ k₃ : ℕ}
    (hb : 0 < b) (hd : 0 < d) (hf_pos : 0 < f) (hh_pos : 0 < h) (hj_pos : 0 < j)
    (hcd : Unimodular a b c d)
    (he : e + a = k₁ * c) (hfb : f + b = k₁ * d)
    (hg : g + c = k₂ * e) (hhd : h + d = k₂ * f)
    (hi : i + e = k₃ * g) (hjf : j + f = k₃ * h) :
    (SimOrd a b c d ∧ SimOrd c d e f ∧ SimOrd e f g h ∧ SimOrd g h i j
        ∧ SimOrd a b e f ∧ SimOrd c d g h ∧ SimOrd e f i j
        ∧ SimOrd a b g h ∧ SimOrd c d i j ∧ SimOrd a b i j)
      ↔ ((2 * (a : ℤ) - k₁ * c) * (2 * (b : ℤ) - k₁ * d) ≥ 0
          ∧ (2 * (c : ℤ) - k₂ * e) * (2 * (d : ℤ) - k₂ * f) ≥ 0
          ∧ (2 * (e : ℤ) - k₃ * g) * (2 * (f : ℤ) - k₃ * h) ≥ 0
          ∧ (((k₂ : ℤ) + 1) * a - ((k₁ : ℤ) * k₂ - 1) * c)
              * (((k₂ : ℤ) + 1) * b - ((k₁ : ℤ) * k₂ - 1) * d) ≥ 0
          ∧ (((k₃ : ℤ) + 1) * c - ((k₂ : ℤ) * k₃ - 1) * e)
              * (((k₃ : ℤ) + 1) * d - ((k₂ : ℤ) * k₃ - 1) * f) ≥ 0
          ∧ (((k₂ : ℤ) * k₃) * a - ((k₁ : ℤ) * k₂ * k₃ - k₁ - k₃) * c)
              * (((k₂ : ℤ) * k₃) * b - ((k₁ : ℤ) * k₂ * k₃ - k₁ - k₃) * d) ≥ 0) := by
  have hcdef : Unimodular c d e f := farey_succ_unimodular hcd he hfb
  have hefgh : Unimodular e f g h := farey_succ_unimodular hcdef hg hhd
  have hghij : Unimodular g h i j := farey_succ_unimodular hefgh hi hjf
  have s1 : SimOrd a b c d := unimodular_simOrd hb hd hcd
  have s2 : SimOrd c d e f := unimodular_simOrd hd hf_pos hcdef
  have s3 : SimOrd e f g h := unimodular_simOrd hf_pos hh_pos hefgh
  have s4 : SimOrd g h i j := unimodular_simOrd hh_pos hj_pos hghij
  constructor
  · rintro ⟨_, _, _, _, w1, w2, w3, w4, w5, w6⟩
    exact ⟨(simOrd_outer_iff he hfb).mp w1,
           (simOrd_outer_iff hg hhd).mp w2,
           (simOrd_outer_iff hi hjf).mp w3,
           (simOrd_long_iff he hfb hg hhd).mp w4,
           (simOrd_long_iff hg hhd hi hjf).mp w5,
           (simOrd_long3_iff he hfb hg hhd hi hjf).mp w6⟩
  · rintro ⟨c1, c2, c3, c4, c5, c6⟩
    exact ⟨s1, s2, s3, s4,
           (simOrd_outer_iff he hfb).mpr c1,
           (simOrd_outer_iff hg hhd).mpr c2,
           (simOrd_outer_iff hi hjf).mpr c3,
           (simOrd_long_iff he hfb hg hhd).mpr c4,
           (simOrd_long_iff hg hhd hi hjf).mpr c5,
           (simOrd_long3_iff he hfb hg hhd hi hjf).mpr c6⟩

-- ══════════════════════════════════════════════════════════════════
-- § 14: The continuant — the run-length criterion for *every* length
-- ══════════════════════════════════════════════════════════════════

/-
§ 11–§ 13 computed the long-range obstruction of runs of length 3, 4, 5 one at a
time, and each was governed by a rung of the same ladder of polynomials in the
successor quotients:

  `K() = 1`,  `K(k) = k`,  `K(k₁,k₂) = k₁k₂ − 1`,  `K(k₁,k₂,k₃) = k₁k₂k₃ − k₁ − k₃`.

These are the **continuant** polynomials — the order-side shadow of the §9
numerator/denominator recurrence `xₘ₊₁ = kₘ·xₘ − xₘ₋₁` (`x` runs over the Farey
numerators or denominators).  This section replaces the per-length lemmas by ONE
statement valid for runs of arbitrary length, by

1. defining `Continuant : List ℤ → ℤ` with the head-recurrence
   `K(k₁ :: k₂ :: ks) = k₁·K(k₂ :: ks) − K(ks)`;
2. defining the iterated successor `stepSeq a c ks`, which applies the §9
   recurrence once per quotient in `ks` to the consecutive pair `(a, c)`;
3. proving the **closed form** `stepSeq a c ks = K(ks)·c − secondCont(ks)·a`
   (`stepSeq_eq_continuant`) by induction on `ks`; and
4. reading off the general endpoint window
   `(a − pₘ)·(b − qₘ) = ((1+secondCont ks)·a − K·c)·((1+secondCont ks)·b − K·d)`
   (`endpoint_window`), so a run's endpoints are similarly ordered iff that
   single continuant-controlled product is `≥ 0` (`simOrd_run_iff`).

The §11/§12/§13 windows `(2a−kc)`, `((k₂+1)a−(k₁k₂−1)c)`,
`(k₂k₃·a−(k₁k₂k₃−k₁−k₃)c)` are exactly the cases `|ks| = 1, 2, 3` — verified by
`continuant_two`, `continuant_three` and `secondCont_*` below.  This is the
structural form (run-length criterion as a continuant positivity condition) that
a density argument toward the `1/12` constant would have to control; the constant
itself remains open.
-/

/-- The (minus-sign) **continuant** of a list of quotients, with the
head-two-element recurrence `K(k₁ :: k₂ :: ks) = k₁·K(k₂ :: ks) − K(ks)` and
bases `K([]) = 1`, `K([k]) = k`.  This is the polynomial governing the §9
recurrence `xₘ₊₁ = kₘ·xₘ − xₘ₋₁`; its first rungs are the §11/§12/§13 controlling
constants `1, k, k₁k₂−1, k₁k₂k₃−k₁−k₃`. -/
def Continuant : List ℤ → ℤ
  | [] => 1
  | [k] => k
  | k₁ :: k₂ :: ks => k₁ * Continuant (k₂ :: ks) - Continuant ks

/-- The **trailing continuant** — the coefficient of `a` in the closed form for
the iterated successor.  `secondCont (k :: ks) = K(ks)`, and `secondCont [] = 0`
(the empty list is the base term `c`, carrying no `a`-contribution).  This
`0`-base is what fixes the one-element edge case of the continuant recurrence. -/
def secondCont : List ℤ → ℤ
  | [] => 0
  | _ :: ks => Continuant ks

/-- `Continuant` obeys the single-step recurrence
`K(k :: ks) = k·K(ks) − secondCont ks` in *every* case.  For `ks = []` this reads
`K([k]) = k·1 − 0 = k`; the `secondCont [] = 0` convention is exactly what makes
the one-element case agree with the general recurrence (a naive "two shorter
tails" form would wrongly give `k − 1`). -/
theorem continuant_cons (k : ℤ) (ks : List ℤ) :
    Continuant (k :: ks) = k * Continuant ks - secondCont ks := by
  cases ks with
  | nil => simp [Continuant, secondCont]
  | cons r rs => simp [Continuant, secondCont]

/-- The **iterated successor term**.  Starting from consecutive numerators (or
denominators) `t₀ = a`, `t₁ = c`, `stepSeq a c ks` applies the §9 recurrence
`tₘ₊₁ = kₘ·tₘ − tₘ₋₁` once per quotient in `ks`, returning the final term
`t_{|ks|+1}`.  (E.g. `stepSeq a c [k] = k·c − a` is the §9/§11 successor `e`.) -/
def stepSeq (a c : ℤ) : List ℤ → ℤ
  | [] => c
  | k :: ks => stepSeq c (k * c - a) ks

/-- **Continuant closed form for the iterated successor (headline).**  The term
reached after applying the quotient list `ks` to a consecutive pair `(a, c)` is
`stepSeq a c ks = K(ks)·c − secondCont(ks)·a`.  This collapses the per-length
explicit formulas of §11/§12/§13 — `e = k·c − a`, `g = (k₁k₂−1)·c − k₂·a`,
`i = (k₁k₂k₃−k₁−k₃)·c − (k₂k₃−1)·a` — into a single statement, valid for runs of
*every* length, with the controlling coefficients reading off the continuant
ladder. -/
theorem stepSeq_eq_continuant (ks : List ℤ) (a c : ℤ) :
    stepSeq a c ks = Continuant ks * c - secondCont ks * a := by
  induction ks generalizing a c with
  | nil => simp [stepSeq, Continuant, secondCont]
  | cons k rest ih =>
    rw [stepSeq, ih c (k * c - a), continuant_cons k rest]
    simp only [secondCont]
    ring

/-- **General endpoint window (run of arbitrary length).**  Running `|ks|`
successor steps from the consecutive numerator pair `(a, c)` and denominator pair
`(b, d)` reaches endpoint numerator `pₘ = stepSeq a c ks` and denominator
`qₘ = stepSeq b d ks`, and the §10/§11 product `(a − pₘ)·(b − qₘ)` factors as
`((1+secondCont ks)·a − K·c)·((1+secondCont ks)·b − K·d)` with `K = Continuant ks`.
So the endpoints of a length-`(|ks|+1)` run are similarly ordered iff this one
continuant-controlled product is nonnegative — the §11/§12/§13 windows being
`|ks| = 1, 2, 3`. -/
theorem endpoint_window (ks : List ℤ) (a b c d : ℤ) :
    (a - stepSeq a c ks) * (b - stepSeq b d ks)
      = ((1 + secondCont ks) * a - Continuant ks * c)
        * ((1 + secondCont ks) * b - Continuant ks * d) := by
  rw [stepSeq_eq_continuant, stepSeq_eq_continuant]; ring

/-- **General run endpoint criterion.**  If a `|ks|`-step run from `a/b, c/d`
reaches endpoint `p/q` with `(p : ℤ) = stepSeq a c ks` and `(q : ℤ) = stepSeq b d ks`,
then the endpoints `a/b, p/q` are similarly ordered **iff** the continuant window
`((1+secondCont ks)·a − K·c)·((1+secondCont ks)·b − K·d) ≥ 0` holds, where
`K = Continuant ks`.  Specializing `ks = [k]`, `[k₁,k₂]`, `[k₁,k₂,k₃]` recovers
`simOrd_outer_iff`, `simOrd_long_iff`, `simOrd_long3_iff` respectively. -/
theorem simOrd_run_iff {a b c d p q : ℕ} {ks : List ℤ}
    (hp : (p : ℤ) = stepSeq (a : ℤ) (c : ℤ) ks)
    (hq : (q : ℤ) = stepSeq (b : ℤ) (d : ℤ) ks) :
    SimOrd a b p q ↔
      ((1 + secondCont ks) * (a : ℤ) - Continuant ks * (c : ℤ))
        * ((1 + secondCont ks) * (b : ℤ) - Continuant ks * (d : ℤ)) ≥ 0 := by
  rw [simOrd_iff_prod, hp, hq, endpoint_window]

-- The continuant ladder: rungs 0–3 are the §11/§12/§13 controlling constants.

/-- Rung 0: `K([]) = 1`. -/
theorem continuant_nil : Continuant [] = 1 := rfl

/-- Rung 1: `K([k]) = k` — the §11 single-step depth. -/
theorem continuant_one (k : ℤ) : Continuant [k] = k := rfl

/-- Rung 2: `K([k₁,k₂]) = k₁k₂ − 1` — the §12 Stern–Brocot product. -/
theorem continuant_two (k₁ k₂ : ℤ) : Continuant [k₁, k₂] = k₁ * k₂ - 1 := by
  simp [continuant_cons, continuant_nil, secondCont]

/-- Rung 3: `K([k₁,k₂,k₃]) = k₁k₂k₃ − k₁ − k₃` — the §13 continuant. -/
theorem continuant_three (k₁ k₂ k₃ : ℤ) :
    Continuant [k₁, k₂, k₃] = k₁ * k₂ * k₃ - k₁ - k₃ := by
  rw [continuant_cons, continuant_two]; simp [secondCont, continuant_one]; ring

/-- Trailing continuant, rung 1: `secondCont [k] = 1` — the §11 coefficient of `a`
(`e = k·c − 1·a`). -/
theorem secondCont_one (k : ℤ) : secondCont [k] = 1 := rfl

/-- Trailing continuant, rung 2: `secondCont [k₁,k₂] = k₂` — the §12 coefficient of
`a` (`g = (k₁k₂−1)·c − k₂·a`). -/
theorem secondCont_two (k₁ k₂ : ℤ) : secondCont [k₁, k₂] = k₂ := rfl

/-- Trailing continuant, rung 3: `secondCont [k₁,k₂,k₃] = k₂k₃ − 1` — the §13
coefficient of `a` (`i = (k₁k₂k₃−k₁−k₃)·c − (k₂k₃−1)·a`). -/
theorem secondCont_three (k₁ k₂ k₃ : ℤ) : secondCont [k₁, k₂, k₃] = k₂ * k₃ - 1 := by
  simp [secondCont, continuant_two]

/-- **Subsumption check (length-3 / §11).**  The general endpoint window at
`ks = [k]` is exactly the §11 outer window `(2a − k·c)·(2b − k·d)`: with one step
`p = stepSeq a c [k] = k·c − a`, so `a − p = 2a − k·c`. -/
theorem endpoint_window_one (k a b c d : ℤ) :
    (a - stepSeq a c [k]) * (b - stepSeq b d [k])
      = (2 * a - k * c) * (2 * b - k * d) := by
  rw [endpoint_window, secondCont_one, continuant_one]; ring

/-- **Subsumption check (length-4 / §12).**  At `ks = [k₁,k₂]` the general window
is the §12 long window `((k₂+1)a − (k₁k₂−1)c)·((k₂+1)b − (k₁k₂−1)d)`. -/
theorem endpoint_window_two (k₁ k₂ a b c d : ℤ) :
    (a - stepSeq a c [k₁, k₂]) * (b - stepSeq b d [k₁, k₂])
      = ((k₂ + 1) * a - (k₁ * k₂ - 1) * c)
        * ((k₂ + 1) * b - (k₁ * k₂ - 1) * d) := by
  rw [endpoint_window, secondCont_two, continuant_two]; ring

/-- **Subsumption check (length-5 / §13).**  At `ks = [k₁,k₂,k₃]` the general
window is the §13 continuant window
`(k₂k₃·a − (k₁k₂k₃−k₁−k₃)c)·(k₂k₃·b − (k₁k₂k₃−k₁−k₃)d)`. -/
theorem endpoint_window_three (k₁ k₂ k₃ a b c d : ℤ) :
    (a - stepSeq a c [k₁, k₂, k₃]) * (b - stepSeq b d [k₁, k₂, k₃])
      = ((k₂ * k₃) * a - (k₁ * k₂ * k₃ - k₁ - k₃) * c)
        * ((k₂ * k₃) * b - (k₁ * k₂ * k₃ - k₁ - k₃) * d) := by
  rw [endpoint_window, secondCont_three, continuant_three]; ring

end Erdos1005OQ02
