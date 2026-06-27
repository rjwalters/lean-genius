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

end Erdos1005OQ02
