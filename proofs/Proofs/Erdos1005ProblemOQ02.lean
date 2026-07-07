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

/-! ## §15: Depth-`m` unimodularity of the iterated Farey walk

§9's `farey_succ_unimodular` shows a *single* Farey-successor step preserves
unimodularity (`b·c = a·d + 1`).  The §14 `stepSeq` recurrence walks along
arbitrarily many successive Farey neighbours by applying that step once per
quotient in a list `ks`.  This section proves that the walk's
**cross-determinant `nₘ·dₘ₊₁ − nₘ₊₁·dₘ` is invariant under every step**, so a
unimodular start stays unimodular at *every* depth.

This is the depth-uniform form of §9's consecutiveness bridge: it certifies that
the entire §14 quotient-list walk consists of genuinely *consecutive* Farey
fractions (each adjacent pair unimodular), not merely similarly-ordered ones.
Concretely it is the order-`m` Stern–Brocot invariant, the determinant shadow of
the step matrix `[[k, −1], [1, 0]]` (which has determinant `1`).

The bookkeeping uses `stepPair`, returning the final consecutive *pair*
`(t_{|ks|}, t_{|ks|+1})` of the §14 recurrence; its second component is exactly
`stepSeq a c ks` (the §14 final term), and its first is the penultimate term,
which the determinant invariant needs. -/

/-- The iterated §9/§14 successor returning the final consecutive **pair**
`(t_{|ks|}, t_{|ks|+1})` (for a numerator seed `(a, c)`, or a denominator seed
`(b, d)`).  Its second component is `stepSeq a c ks`; the first is the penultimate
term, needed to state the walk's unimodular invariant. -/
def stepPair (a c : ℤ) : List ℤ → ℤ × ℤ
  | [] => (a, c)
  | k :: ks => stepPair c (k * c - a) ks

/-- `stepPair`'s second component is exactly `stepSeq` — the §14 final term. -/
theorem stepPair_snd (ks : List ℤ) (a c : ℤ) :
    (stepPair a c ks).2 = stepSeq a c ks := by
  induction ks generalizing a c with
  | nil => rfl
  | cons k ks ih => simp only [stepPair, stepSeq]; exact ih c (k * c - a)

/-- **Depth-`m` unimodularity (the headline).**  Running the §14 recurrence on a
numerator seed `(a, c)` and a denominator seed `(b, d)` through the *same* quotient
list `ks`, the cross-determinant of the final consecutive pairs equals the seed
cross-determinant:
`nₘ·dₘ₊₁ − nₘ₊₁·dₘ = a·d − b·c`.
Each step's matrix `[[k, −1], [1, 0]]` has determinant `1`, so the invariant is
preserved exactly — proved by list induction with the seed pair threaded through
the recurrence `(a, c) ↦ (c, k·c − a)`. -/
theorem stepPair_cross (ks : List ℤ) (a b c d : ℤ) :
    (stepPair a c ks).1 * (stepPair b d ks).2
        - (stepPair a c ks).2 * (stepPair b d ks).1
      = a * d - b * c := by
  induction ks generalizing a b c d with
  | nil => simp only [stepPair]; ring
  | cons k ks ih =>
      simp only [stepPair]
      rw [ih c d (k * c - a) (k * d - b)]; ring

/-- **Unimodularity is preserved at every depth.**  If the seed consecutive pair
`a/b < c/d` is unimodular (`b·c = a·d + 1`, the §1 `Unimodular` convention), then
so is the final consecutive pair of the depth-`|ks|` walk: its cross-determinant
is `−1`.  Hence iterating the §14 recurrence from a Farey-adjacent pair lands on a
Farey-adjacent pair at every depth — the consecutiveness §9 supplies one step at a
time, now uniform in the run length. -/
theorem stepPair_cross_unimodular (ks : List ℤ) {a b c d : ℤ}
    (h : b * c = a * d + 1) :
    (stepPair a c ks).1 * (stepPair b d ks).2
        - (stepPair a c ks).2 * (stepPair b d ks).1 = -1 := by
  rw [stepPair_cross]; omega

/-- **Subsumption check (§9).**  At `ks = [k]` the walk's consecutive pair is
`(c, k·c − a)` for numerators and `(d, k·d − b)` for denominators, and the
depth-`m` invariant reduces to the §9 single-step determinant
`c·(k·d − b) − (k·c − a)·d = a·d − b·c`. -/
theorem stepPair_cross_one (k a b c d : ℤ) :
    (stepPair a c [k]).1 * (stepPair b d [k]).2
        - (stepPair a c [k]).2 * (stepPair b d [k]).1 = a * d - b * c :=
  stepPair_cross [k] a b c d

/-! ## §16: The continuant matrix — Cassini and reversal symmetry

§14's `Continuant` and `secondCont` arose as the controlling coefficients of the
§9 successor recurrence `tₘ₊₁ = kₘ·tₘ − tₘ₋₁`, equivalently the 2×2 step matrix
`M(k) = [[k, −1], [1, 0]]` (determinant `1`).  This section makes that matrix
representation explicit and reads two structural facts off it that the per-rung
algebra of §11–§13 could only sample:

* **Cassini / determinant invariant.**  Each step matrix has determinant `1`, so
  the ordered product `P(ks) = M(k₁)·⋯·M(kₙ)` has determinant `1` at every depth.
  Its top-left and bottom-left entries are exactly `Continuant ks` and
  `secondCont ks`, giving the continuant Cassini identity
  `K(ks)·(P ks).d − (P ks).b·secondCont(ks) = 1`.  This is the determinant route
  the §15 note flagged as the correct replacement for the (false) blanket
  "continuant positivity" target — the §14 windows' sign structure is governed by
  a `det = 1` invariant, never by `K ≥ 1`.

* **Reversal symmetry (headline).**  `K(ks.reverse) = K(ks)`.  The step matrix is
  *not* symmetric, but it satisfies `M(k)ᵀ = J·M(k)·J` with `J = diag(1, −1)`
  (`J² = I`), so the map `φ(X) = J·Xᵀ·J` fixes every `M(k)` while reversing
  products (`φ(XY) = φ(Y)·φ(X)`).  Hence `P(ks.reverse) = φ(P ks)`, and the
  top-left entry of `φ(X)` equals that of `X`, forcing `K(ks.reverse) = K(ks)`.
  This is the palindrome structure of the run-length windows: a length-`(|ks|+1)`
  run and its reverse are governed by the *same* continuant. -/

/-- A 2×2 integer matrix `[[a, b], [c, d]]`, used as the step-matrix carrier for
the §14 continuant.  A bespoke structure (rather than `Matrix (Fin 2) (Fin 2) ℤ`)
keeps every entry-level proof a one-line `ext`/`ring`. -/
@[ext] structure Mat2 where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ

namespace Mat2

/-- Matrix multiplication `[[a,b],[c,d]]·[[a',b'],[c',d']]`. -/
def mul (X Y : Mat2) : Mat2 :=
  ⟨X.a * Y.a + X.b * Y.c, X.a * Y.b + X.b * Y.d,
   X.c * Y.a + X.d * Y.c, X.c * Y.b + X.d * Y.d⟩

/-- The identity matrix. -/
def one : Mat2 := ⟨1, 0, 0, 1⟩

/-- The transpose `[[a,c],[b,d]]`. -/
def transpose (X : Mat2) : Mat2 := ⟨X.a, X.c, X.b, X.d⟩

/-- Conjugation by `J = diag(1, −1)`: `J·X·J = [[a,−b],[−c,d]]`. -/
def conj (X : Mat2) : Mat2 := ⟨X.a, -X.b, -X.c, X.d⟩

/-- The anti-automorphism `φ(X) = J·Xᵀ·J = [[a,−c],[−b,d]]`. -/
def phi (X : Mat2) : Mat2 := ⟨X.a, -X.c, -X.b, X.d⟩

/-- The determinant `a·d − b·c`. -/
def det (X : Mat2) : ℤ := X.a * X.d - X.b * X.c

theorem mul_assoc (X Y Z : Mat2) : mul (mul X Y) Z = mul X (mul Y Z) := by
  ext <;> simp only [mul] <;> ring

theorem one_mul (X : Mat2) : mul one X = X := by
  ext <;> simp only [mul, one] <;> ring

theorem mul_one (X : Mat2) : mul X one = X := by
  ext <;> simp only [mul, one] <;> ring

/-- `φ` reverses products: `φ(XY) = φ(Y)·φ(X)`. -/
theorem phi_mul (X Y : Mat2) : phi (mul X Y) = mul (phi Y) (phi X) := by
  ext <;> simp only [phi, mul] <;> ring

theorem phi_one : phi one = one := by ext <;> simp [phi, one]

/-- The determinant is multiplicative — the Cassini engine. -/
theorem det_mul (X Y : Mat2) : det (mul X Y) = det X * det Y := by
  simp only [det, mul]; ring

theorem det_one : det one = 1 := by simp [det, one]

end Mat2

/-- The §9/§14 step matrix `M(k) = [[k, −1], [1, 0]]`, determinant `1`. -/
def stepMat (k : ℤ) : Mat2 := ⟨k, -1, 1, 0⟩

theorem det_stepMat (k : ℤ) : Mat2.det (stepMat k) = 1 := by
  simp [Mat2.det, stepMat]

/-- `φ` fixes every step matrix — the conjugation symmetry `M(k)ᵀ = J·M(k)·J`. -/
theorem phi_stepMat (k : ℤ) : Mat2.phi (stepMat k) = stepMat k := by
  simp [Mat2.phi, stepMat]

/-- The ordered product `P(ks) = M(k₁)·⋯·M(kₙ)` of step matrices. -/
def contMat : List ℤ → Mat2
  | [] => Mat2.one
  | k :: ks => Mat2.mul (stepMat k) (contMat ks)

theorem contMat_singleton (k : ℤ) : contMat [k] = stepMat k := by
  simp [contMat, Mat2.mul_one]

/-- `contMat` is multiplicative on concatenation — the matrix product respects
list append. -/
theorem contMat_append (xs ys : List ℤ) :
    contMat (xs ++ ys) = Mat2.mul (contMat xs) (contMat ys) := by
  induction xs with
  | nil => simp [contMat, Mat2.one_mul]
  | cons k xs ih =>
    simp only [List.cons_append, contMat, ih, Mat2.mul_assoc]

/-- **Continuant entries.**  The top-left entry of the step-matrix product is the
§14 `Continuant`, and the bottom-left entry is `secondCont` — the matrix
representation of the §14 recurrence. -/
theorem contMat_entries (ks : List ℤ) :
    (contMat ks).a = Continuant ks ∧ (contMat ks).c = secondCont ks := by
  induction ks with
  | nil => exact ⟨rfl, rfl⟩
  | cons k ks ih =>
    refine ⟨?_, ?_⟩
    · simp only [contMat, Mat2.mul, stepMat, ih.1, ih.2, continuant_cons]; ring
    · simp only [contMat, Mat2.mul, stepMat, ih.1, secondCont]; ring

theorem contMat_a (ks : List ℤ) : (contMat ks).a = Continuant ks :=
  (contMat_entries ks).1

theorem contMat_c (ks : List ℤ) : (contMat ks).c = secondCont ks :=
  (contMat_entries ks).2

/-- **The reversal bridge.**  Reversing the quotient list applies `φ` to the
step-matrix product: `P(ks.reverse) = φ(P ks)`.  Proved by list induction using
that `φ` reverses products and fixes each step matrix. -/
theorem contMat_reverse (ks : List ℤ) :
    contMat ks.reverse = Mat2.phi (contMat ks) := by
  induction ks with
  | nil => simp [contMat, Mat2.phi_one]
  | cons k ks ih =>
    rw [List.reverse_cons, contMat_append, contMat_singleton, ih,
      show contMat (k :: ks) = Mat2.mul (stepMat k) (contMat ks) from rfl,
      Mat2.phi_mul, phi_stepMat]

/-- **Continuant reversal symmetry (headline).**  `K(ks.reverse) = K(ks)`: the
continuant is invariant under reversing its quotient list.  Reading the top-left
entry of the reversal bridge `P(ks.reverse) = φ(P ks)`, which `φ` leaves fixed.
This is the palindrome symmetry of the §14 run-length windows. -/
theorem continuant_reverse (ks : List ℤ) :
    Continuant ks.reverse = Continuant ks := by
  have h := congrArg Mat2.a (contMat_reverse ks)
  simpa only [contMat_a, Mat2.phi] using h

/-- The reversal symmetry also identifies the top-right entry of the product:
`(P ks).b = −secondCont(ks.reverse)`.  (The bottom-left entry of `P(ks.reverse)`
is `secondCont(ks.reverse)`, and the reversal bridge maps it to `−(P ks).b`.) -/
theorem contMat_b (ks : List ℤ) : (contMat ks).b = - secondCont ks.reverse := by
  have h := congrArg Mat2.c (contMat_reverse ks)
  simp only [contMat_c, Mat2.phi] at h
  linarith [h]

/-- **Determinant invariant.**  `det P(ks) = 1` at every depth — each step matrix
has determinant `1` and the determinant is multiplicative. -/
theorem det_contMat (ks : List ℤ) : Mat2.det (contMat ks) = 1 := by
  induction ks with
  | nil => simp [contMat, Mat2.det_one]
  | cons k ks ih => rw [contMat, Mat2.det_mul, det_stepMat, ih]; ring

/-- **Continuant Cassini identity (headline).**  Spelling out `det P(ks) = 1` with
the continuant entries gives
`K(ks)·(P ks).d − (P ks).b·secondCont(ks) = 1`,
and substituting `(P ks).b = −secondCont(ks.reverse)`,
`K(ks)·(P ks).d + secondCont(ks.reverse)·secondCont(ks) = 1`.
This is the `det = 1` invariant the §15 note named as the correct replacement for
the false blanket "continuant positivity" target: the §14 windows are governed by
a Cassini determinant, not by any sign condition on `K` itself. -/
theorem continuant_cassini (ks : List ℤ) :
    Continuant ks * (contMat ks).d
        + secondCont ks.reverse * secondCont ks = 1 := by
  have h := det_contMat ks
  simp only [Mat2.det, contMat_a, contMat_c, contMat_b] at h
  linear_combination h

/-- **Continuant addition formula (Euler's composition law).**  Reading the
top-left entry of the matrix product `contMat (xs ++ ys) = contMat xs · contMat ys`
gives the classic continuant composition identity
`K(xs ++ ys) = K(xs)·K(ys) − secondCont(xs.reverse)·secondCont(ys)`.
Since `secondCont(xs.reverse) = K(xs.dropLast)` (the *leading* continuant, by
`continuant_reverse`) and `secondCont(ys) = K(ys.tail)`, this is exactly Euler's
`K(xs ++ ys) = K(xs)·K(ys) − K(xs.dropLast)·K(ys.tail)`.  It splits the §14
run-length window of a concatenated quotient list into the product of the two
sub-walk continuants minus a single junction term — the algebraic engine behind
both the reversal symmetry and any density count over a Stern–Brocot path. -/
theorem continuant_append (xs ys : List ℤ) :
    Continuant (xs ++ ys)
      = Continuant xs * Continuant ys - secondCont xs.reverse * secondCont ys := by
  have h := congrArg Mat2.a (contMat_append xs ys)
  simp only [contMat_a, Mat2.mul, contMat_b, contMat_c] at h
  linear_combination h
/-! ## §17: Continuant positivity and growth in the large-quotient regime

The run-length criterion `simOrd_run_iff` (§14) controls a length-`(|ks|+1)` run
through the continuant window
`((1+secondCont ks)·a − K·c)·((1+secondCont ks)·b − K·d) ≥ 0` with
`K = Continuant ks`.  To bound the *density* side of the open `1/12`–`1/4` problem
one must understand the sign and size of `K` and `secondCont` as the quotient list
varies.  Iteration 14's proposed blanket bound `K(ks) ≥ 1` for all-`≥1` lists is
**false**: the minus-sign continuant of an all-`1` (balanced/Fibonacci) list is the
period-6 sequence `1, 1, 0, −1, −1, 0, …` — e.g. `K([1,1]) = 0`, `K([1,1,1]) = −1`
(witnesses `continuant_ones_two`, `continuant_ones_three` below).  Positivity is a
phenomenon of *large* quotients, the regime opposite to the balanced extreme.

This section proves that on the **large-quotient regime** `ks` with every entry
`≥ 2`, the continuant pair is controlled: the trailing continuant is dominated by
the leading one (`0 ≤ secondCont ks < Continuant ks`), the continuant is strictly
positive, strictly increasing under prepending another quotient `≥ 2`, and grows at
least linearly (`Continuant ks ≥ |ks| + 1`).  This is the "break forced by a large
quotient" structural handle the parent state called for: it certifies that in the
all-`≥ 2` regime the continuant has a *definite sign* (so the windows' sign
structure is decided by the seed alone, not by continuant cancellation), and that
the continuant — and hence by the §14 closed form the run endpoints — grow with the
run length, making long large-quotient runs metrically expensive.

This section is logically independent of the parallel §16 continuant-matrix /
Cassini work (PR #31083): it depends only on the §14 `Continuant` / `secondCont`
recurrences (`continuant_cons`).

**Honest boundary (unchanged).** This bounds the continuant's sign and size in one
quotient regime; it does *not* count the density of admissible quotient lists keeping
every non-adjacent window nonnegative — that count is the open `1/12`–`1/4` step. -/

/-- **Core invariant (large-quotient regime).**  For a quotient list with every
entry `≥ 2`, the trailing continuant is nonnegative and *strictly* dominated by the
leading continuant: `0 ≤ secondCont ks < Continuant ks`.  Proved by induction on the
single-step recurrences `secondCont (k::ks) = K(ks)` and
`K(k::ks) = k·K(ks) − secondCont ks` (`continuant_cons`): the map on the pair
`(s, K) ↦ (K, k·K − s)` preserves `0 ≤ s < K` whenever `k ≥ 2`, since then
`k·K − s ≥ 2K − s > K` and `K ≥ s + 1 > 0`.  The strict domination `s < K` is the
seed of every positivity and growth statement below. -/
theorem secondCont_lt_continuant (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    0 ≤ secondCont ks ∧ secondCont ks < Continuant ks := by
  induction ks with
  | nil =>
      refine ⟨?_, ?_⟩
      · show (0 : ℤ) ≤ 0; exact le_refl 0
      · show (0 : ℤ) < 1; norm_num
  | cons k rest ih =>
      have hrest : ∀ j ∈ rest, (2 : ℤ) ≤ j := fun j hj => h j (List.mem_cons_of_mem k hj)
      have hk : (2 : ℤ) ≤ k := h k (by simp)
      obtain ⟨hs0, hsK⟩ := ih hrest
      refine ⟨?_, ?_⟩
      · -- `secondCont (k :: rest)` is defeq `Continuant rest`, which exceeds `secondCont rest ≥ 0`.
        show (0 : ℤ) ≤ Continuant rest
        linarith [hs0, hsK]
      · rw [continuant_cons]
        -- `secondCont (k :: rest)` is defeq `Continuant rest`; goal: `K < k·K − s`.
        show Continuant rest < k * Continuant rest - secondCont rest
        nlinarith [hs0, hsK, hk,
          mul_nonneg (show (0 : ℤ) ≤ k - 2 by linarith)
            (show (0 : ℤ) ≤ Continuant rest by linarith)]

/-- **Strict positivity (large-quotient regime).**  Every all-`≥ 2` continuant is
`≥ 1`.  In this regime the §14 windows therefore never degenerate through a vanishing
continuant — the cancellation that makes the all-`1` extreme oscillate cannot occur. -/
theorem continuant_pos (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    0 < Continuant ks :=
  lt_of_le_of_lt (secondCont_lt_continuant ks h).1 (secondCont_lt_continuant ks h).2

/-- The trailing continuant is nonnegative on the large-quotient regime. -/
theorem secondCont_nonneg (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    0 ≤ secondCont ks :=
  (secondCont_lt_continuant ks h).1

/-- **Strict monotonicity under prepending.**  In the large-quotient regime,
prepending another quotient `k ≥ 2` strictly increases the continuant:
`Continuant ks < Continuant (k :: ks)`.  Since `K(k::ks) = k·K − secondCont ks` and
`k ≥ 2` with `0 ≤ secondCont ks < K`, we have `k·K − secondCont ks ≥ 2K − secondCont ks > K`.
The continuant is therefore strictly increasing along the run. -/
theorem continuant_strict_mono {k : ℤ} {ks : List ℤ}
    (hk : (2 : ℤ) ≤ k) (h : ∀ j ∈ ks, (2 : ℤ) ≤ j) :
    Continuant ks < Continuant (k :: ks) := by
  rw [continuant_cons]
  obtain ⟨hs0, hsK⟩ := secondCont_lt_continuant ks h
  nlinarith [hs0, hsK, hk,
    mul_nonneg (show (0 : ℤ) ≤ k - 2 by linarith)
      (show (0 : ℤ) ≤ Continuant ks by linarith)]

/-- **Linear growth lower bound.**  In the large-quotient regime the continuant is at
least `|ks| + 1`: each prepended quotient `≥ 2` adds at least `1`
(`K(k::ks) ≥ K(ks) + 1`, from strict monotonicity over `ℤ`), starting from
`K([]) = 1`.  So a depth-`m` large-quotient run carries a continuant `≥ m + 1`, and by
the §14 closed form `stepSeq a c ks = K·c − secondCont·a` the run endpoints inherit
this growth — long large-quotient runs are metrically expensive, capped by the
order-`n` Farey ceiling. -/
theorem continuant_ge_length (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    (ks.length : ℤ) + 1 ≤ Continuant ks := by
  induction ks with
  | nil => simp [Continuant]
  | cons k rest ih =>
      have hrest : ∀ j ∈ rest, (2 : ℤ) ≤ j := fun j hj => h j (List.mem_cons_of_mem k hj)
      have hk : (2 : ℤ) ≤ k := h k (by simp)
      have hmono := continuant_strict_mono hk hrest
      have hlen := ih hrest
      simp only [List.length_cons]
      omega

/-- **Why `k ≥ 2` is essential (balanced extreme, witness 1).**  The all-`1`
continuant vanishes already at length two: `K([1,1]) = 1·1 − 1 = 0`.  Blanket
positivity `K(ks) ≥ 1` therefore fails the moment a quotient drops to `1`. -/
theorem continuant_ones_two : Continuant [1, 1] = 0 := by decide

/-- **Why `k ≥ 2` is essential (balanced extreme, witness 2).**  One step further the
all-`1` continuant turns *negative*: `K([1,1,1]) = 1 − 1 − 1 = −1`.  Together with
`continuant_ones_two` these exhibit the period-6 orbit `1,1,0,−1,−1,0,…` of the
balanced extreme, the regime where §17's positivity provably does not hold. -/
theorem continuant_ones_three : Continuant [1, 1, 1] = -1 := by decide

/-! ## §18: The bottom-right entry and the pure-continuant Cassini

§16 identified three of the four entries of the step-matrix product `P(ks)` —
`.a = Continuant ks`, `.c = secondCont ks`, `.b = −secondCont ks.reverse` — but left
the bottom-right entry `.d`, the coefficient carrying the Cassini determinant, as an
opaque matrix entry; the §16 note named "identify `(contMat ks).d` in closed
continuant form" as the next direction.  This section closes that thread.

Prepending a quotient shifts the matrix down-right, so `.d` of `P(k :: ks)` is just
the *old* top-right entry `.b` of `P(ks)`: `(P(k::ks)).d = −secondCont ks.reverse`.
With §16's `.a/.b/.c` this identifies **every** entry of the continuant matrix as a
signed continuant of a sublist (`contMat_cons_eq`), and turns the §16 determinant
Cassini into the classical three-term continuant Cassini

`K(L.dropLast)·K(L.tail) − K(L)·K(L.tail.dropLast) = 1`   (`continuant_cassini_classical`)

relating three consecutive continuants of a length-`≥ 2` quotient list `L` — the
recognizable textbook form of the §16 `det P = 1` invariant, now fully expressed in
the §14 continuant ladder with no residual matrix entry.

This section is downstream of §16 only (the matrix entries and reversal symmetry);
it adds no new axioms and introduces no `Continuant`/`secondCont` machinery beyond
the §14 definitions and the §16 reversal bridge. -/

/-- **The fourth entry.**  Prepending `k` shifts the bottom-right entry to the old
top-right entry: `(P(k::ks)).d = (P ks).b = −secondCont ks.reverse`.  (Bottom-right
of `M(k)·X` is `1·X.b + 0·X.d = X.b`, since `M(k) = [[k,−1],[1,0]]`.)  Together with
§16's `contMat_a/_b/_c` this identifies all four entries of the continuant matrix. -/
theorem contMat_d (k : ℤ) (ks : List ℤ) :
    (contMat (k :: ks)).d = - secondCont ks.reverse := by
  have e : (contMat (k :: ks)).d = (contMat ks).b := by
    show (Mat2.mul (stepMat k) (contMat ks)).d = (contMat ks).b
    simp only [Mat2.mul, stepMat]; ring
  rw [e, contMat_b]

/-- **Full continuant-matrix identification.**  Every entry of the step-matrix
product is a signed continuant of a sublist:
`P(k::ks) = [[K(k::ks), −secondCont (k::ks).reverse], [secondCont (k::ks), −secondCont ks.reverse]]`.
The complete entry-level reading of §16's `contMat`, now including the bottom-right
corner. -/
theorem contMat_cons_eq (k : ℤ) (ks : List ℤ) :
    contMat (k :: ks) =
      ⟨Continuant (k :: ks), - secondCont (k :: ks).reverse,
       secondCont (k :: ks), - secondCont ks.reverse⟩ := by
  ext
  · exact contMat_a _
  · exact contMat_b _
  · exact contMat_c _
  · exact contMat_d k ks

/-- **Pure-continuant Cassini (no residual matrix entry).**  Spelling out
`det P(k::ks) = 1` with all four entries now in continuant form gives
`secondCont (k::ks).reverse · secondCont (k::ks) − Continuant (k::ks) · secondCont ks.reverse = 1`.
Unlike §16's `continuant_cassini`, every term here is a §14 continuant-ladder value;
the opaque `(P ks).d` has been eliminated. -/
theorem continuant_cassini_full (k : ℤ) (ks : List ℤ) :
    secondCont (k :: ks).reverse * secondCont (k :: ks)
      - Continuant (k :: ks) * secondCont ks.reverse = 1 := by
  have h := det_contMat (k :: ks)
  rw [Mat2.det, contMat_a, contMat_b, contMat_c, contMat_d k ks] at h
  linear_combination h

/-- `(l.dropLast).reverse = l.reverse.tail` — reversing then dropping the last is
reversing the tail (a pure `List` rearrangement, via `List.dropLast_reverse`). -/
theorem dropLast_reverse_eq (l : List ℤ) : (l.dropLast).reverse = l.reverse.tail := by
  have h := @List.dropLast_reverse ℤ l.reverse
  rw [List.reverse_reverse] at h
  rw [h, List.reverse_reverse]

/-- For a nonempty list `m`, `secondCont m = Continuant m.tail` (the defining
recurrence `secondCont (x :: xs) = Continuant xs`, stated tail-first). -/
theorem secondCont_eq_continuant_tail {m : List ℤ} (hm : m ≠ []) :
    secondCont m = Continuant m.tail := by
  cases m with
  | nil => exact absurd rfl hm
  | cons x xs => rfl

/-- **Trailing-of-reverse is the leading continuant.**  For nonempty `l`,
`secondCont l.reverse = Continuant l.dropLast`: the trailing continuant of the
reversed list is the *leading* continuant of the original.  (`secondCont` reads the
tail of the reverse, which is the reverse of the dropLast, and `Continuant` is
reversal-invariant by §16.)  This is the bridge prose in §16 (`secondCont xs.reverse
= K(xs.dropLast)`), now a lemma. -/
theorem secondCont_reverse_eq {l : List ℤ} (hl : l ≠ []) :
    secondCont l.reverse = Continuant l.dropLast := by
  have hrev : l.reverse ≠ [] := by simpa using hl
  rw [secondCont_eq_continuant_tail hrev, ← dropLast_reverse_eq, continuant_reverse]

/-- **Continuant Cassini, classical three-term form (headline).**  For a quotient
list `L = k :: j :: rest` of length `≥ 2`,
`K(L.dropLast)·K(L.tail) − K(L)·K(L.tail.dropLast) = 1`.
This is the textbook continuant Cassini identity — the determinant `det P(L) = 1` of
§16 rewritten entirely in the §14 continuant ladder, relating the three consecutive
continuants `K(L.dropLast)`, `K(L)`, `K(L.tail)` and the interior `K(L.tail.dropLast)`.
It specializes `continuant_cassini_full` through `secondCont_reverse_eq`, completing
the program of expressing the run-length windows' determinant invariant purely in
continuants. -/
theorem continuant_cassini_classical (k j : ℤ) (rest : List ℤ) :
    Continuant (k :: j :: rest).dropLast * Continuant (k :: j :: rest).tail
      - Continuant (k :: j :: rest) * Continuant (k :: j :: rest).tail.dropLast = 1 := by
  have h := continuant_cassini_full k (j :: rest)
  rw [secondCont_reverse_eq (l := k :: j :: rest) (by simp),
      secondCont_reverse_eq (l := j :: rest) (by simp)] at h
  -- `secondCont (k :: j :: rest) = Continuant (j :: rest) = Continuant (k::j::rest).tail`
  -- and `(k::j::rest).tail.dropLast = (j::rest).dropLast`, both definitional.
  simpa using h

/-! ## §19: Coprimality of consecutive continuants (reduced Farey fractions)

The Cassini determinant `det P(ks) = 1` of §16 is, read as a Bézout identity, exactly
the statement that the continuant pair `(Continuant ks, secondCont ks)` is *coprime*:
`Continuant ks · (P ks).d + secondCont ks.reverse · secondCont ks = 1` exhibits an
integer combination of `Continuant ks` and `secondCont ks` equal to `1`.  Since the
§9 Farey successor is the fraction with numerator/denominator continuants and
`secondCont (k :: ks) = Continuant ks` (the trailing continuant is the leading
continuant of the tail), this says **consecutive continuants are coprime** — the
mediants along a Stern–Brocot / Farey path are automatically in lowest terms, with no
common factor to cancel.  This is the arithmetic counterpart of §16's geometric
`det = 1`: unimodularity ⇒ coprimality ⇒ reduced fractions.

This section is a direct corollary of §16 `continuant_cassini`; it adds the Mathlib
`IsCoprime` API connection and no new axioms. -/

/-- **Consecutive continuants are coprime.**  `IsCoprime (Continuant ks) (secondCont ks)`:
the §16 Cassini `Continuant ks · (P ks).d + secondCont ks.reverse · secondCont ks = 1`
is precisely a Bézout witness for coprimality of the continuant pair. -/
theorem continuant_isCoprime (ks : List ℤ) :
    IsCoprime (Continuant ks) (secondCont ks) :=
  ⟨(contMat ks).d, secondCont ks.reverse, by linear_combination continuant_cassini ks⟩

/-- **Reduced Farey fraction (consecutive-continuant form).**  The leading and
trailing continuants of a nonempty quotient list are coprime:
`IsCoprime (Continuant (k :: ks)) (Continuant ks)`.  Because the §9 Farey successor
of a consecutive pair has these two continuants as denominator and numerator, the
mediant produced along any Stern–Brocot path is automatically in lowest terms. -/
theorem continuant_tail_isCoprime (k : ℤ) (ks : List ℤ) :
    IsCoprime (Continuant (k :: ks)) (Continuant ks) := by
  have h := continuant_isCoprime (k :: ks)
  rwa [show secondCont (k :: ks) = Continuant ks from rfl] at h

/-- **Coprimality is reversal-symmetric.**  Pairing §16's `continuant_reverse` with
coprimality: the continuant of a quotient list is coprime to the trailing continuant
of the reversed list as well — `IsCoprime (Continuant ks) (secondCont ks.reverse)`.
(The two Bézout cofactors swap roles relative to `continuant_isCoprime`.) -/
theorem continuant_isCoprime_reverse (ks : List ℤ) :
    IsCoprime (Continuant ks) (secondCont ks.reverse) :=
  ⟨(contMat ks).d, secondCont ks, by linear_combination continuant_cassini ks⟩

/-! ## §20: Sharpness of the §17 linear growth bound — the all-`2` minimum

§17's `continuant_ge_length` shows a length-`m` quotient list with every entry `≥ 2`
has `Continuant ≥ m + 1`.  This section shows that bound is **attained**, and so is
sharp: the constant list `[2, 2, …, 2]` realises `Continuant = m + 1` exactly — the
Pell ladder `1, 2, 3, 4, …` in which each large-quotient step adds *exactly* one — and
raising any leading quotient only increases the continuant.  Hence the exponential
growth of `continuant_strict_mono`'s larger-quotient neighbours is a phenomenon of
strictly larger quotients: the metric "cheapest" long large-quotient run is the
all-`2` ladder, the minimiser of the §17 regime.  This pins down which large-quotient
runs are the binding constraint for the order-`n` Farey ceiling.

Depends only on the §14 `continuant_cons` recurrence and §17 `continuant_pos`. -/

/-- **Exact value on the all-`2` list (joint with trailing continuant).**  The
constant quotient list `[2,…,2]` of length `n` has `Continuant = n + 1` and
`secondCont = n`: the Pell ladder `1, 2, 3, 4, …` in which each step adds exactly `1`.
Proved by induction threading both continuants through `continuant_cons`. -/
theorem continuant_secondCont_replicate_two (n : ℕ) :
    Continuant (List.replicate n 2) = (n : ℤ) + 1
      ∧ secondCont (List.replicate n 2) = (n : ℤ) := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ m ih =>
    obtain ⟨hK, hs⟩ := ih
    rw [List.replicate_succ]
    refine ⟨?_, ?_⟩
    · rw [continuant_cons, hK, hs]; push_cast; ring
    · -- `secondCont (2 :: replicate m 2)` is defeq `Continuant (replicate m 2)`.
      have hdef : secondCont (2 :: List.replicate m 2)
          = Continuant (List.replicate m 2) := rfl
      rw [hdef, hK]; push_cast; ring

/-- `Continuant [2,…,2] = n + 1` — the §17 linear bound `continuant_ge_length` is
**attained** by the constant all-`2` list. -/
theorem continuant_replicate_two (n : ℕ) :
    Continuant (List.replicate n 2) = (n : ℤ) + 1 :=
  (continuant_secondCont_replicate_two n).1

/-- **The §17 linear bound is sharp.**  There is a length-`n` quotient list with every
entry `≥ 2` whose continuant equals exactly `n + 1` — the all-`2` list.  Hence
`continuant_ge_length`'s `Continuant ≥ |ks| + 1` cannot be improved in the
large-quotient regime. -/
theorem continuant_ge_length_sharp (n : ℕ) :
    ∃ ks : List ℤ, ks.length = n ∧ (∀ k ∈ ks, (2 : ℤ) ≤ k)
      ∧ Continuant ks = (n : ℤ) + 1 := by
  refine ⟨List.replicate n 2, by simp, ?_, continuant_replicate_two n⟩
  intro k hk
  have : k = 2 := List.eq_of_mem_replicate hk
  omega

/-- **Monotonicity in the leading quotient (large-quotient regime).**  Raising the
first quotient cannot decrease the continuant: for a tail `ks` with every entry `≥ 2`
and `k ≤ k'`, `Continuant (k :: ks) ≤ Continuant (k' :: ks)`.  The difference is
`(k' − k)·Continuant ks ≥ 0` by §17 `continuant_pos`.  Together with
`continuant_replicate_two` this exhibits the all-`2` list as the continuant-minimiser
among large-quotient lists sharing a fixed all-`2` tail. -/
theorem continuant_head_mono {k k' : ℤ} {ks : List ℤ}
    (hkk : k ≤ k') (h : ∀ j ∈ ks, (2 : ℤ) ≤ j) :
    Continuant (k :: ks) ≤ Continuant (k' :: ks) := by
  rw [continuant_cons, continuant_cons]
  have hpos : 0 < Continuant ks := continuant_pos ks h
  nlinarith [mul_nonneg (sub_nonneg.mpr hkk) (le_of_lt hpos)]

-- ══════════════════════════════════════════════════════════════════
-- § 21: The balanced extreme — all-ones continuant is period-6 and bounded
-- ══════════════════════════════════════════════════════════════════

/-
§ 17 exhibited the two regimes of the continuant.  In the **large-quotient**
regime (every entry `≥ 2`) it is strictly positive and grows at least linearly
(`continuant_ge_length`, sharp via the all-`2` ladder `continuant_replicate_two`).
The opposite, **balanced** extreme is the all-`1` list, where §17 recorded only
the two witnesses `continuant_ones_two` (`K[1,1] = 0`) and `continuant_ones_three`
(`K[1,1,1] = −1`), noting they sit on the period-6 orbit `1,1,0,−1,−1,0,…` of the
rotation matrix `[[1,−1],[1,0]]` but proving only those two points.

This section promotes the witnesses to the full statement.  Writing
`aₙ = K(1ⁿ)`, `sₙ = secondCont(1ⁿ)`, the §14 single-step recurrence
`continuant_cons` specialises (every quotient `= 1`) to the coupled linear system
`aₙ₊₁ = aₙ − sₙ`, `sₙ₊₁ = aₙ`, i.e. `aₙ₊₁ = aₙ − aₙ₋₁`.  Its companion matrix is
the order-6 rotation, whose sixth power is the identity, so the pair is
**6-periodic**; the continuant therefore takes only the three values `−1, 0, 1`
and, unlike the all-`2` ladder, never grows.  This is the exact quantitative form
of the §15/§17 dichotomy: a long run of small quotients keeps the continuant
bounded, whereas a regime of large quotients forces linear growth — the structural
reason the open `1/12`–`1/4` optimisation must trade the two regimes against the
order-`n` denominator cap (a similarly ordered run cannot be both long and
metrically cheap at once).
-/

/-- All-ones trailing continuant: `secondCont(1ⁿ⁺¹) = K(1ⁿ)`.  Immediate from the
`secondCont (_ :: ks) = Continuant ks` convention. -/
theorem secondCont_replicate_one (m : ℕ) :
    secondCont (List.replicate (m + 1) 1) = Continuant (List.replicate m 1) := by
  rw [List.replicate_succ]; rfl

/-- All-ones continuant single-step recurrence `aₙ₊₁ = aₙ − sₙ`: every quotient
being `1`, the §14 `continuant_cons` loses its leading factor. -/
theorem continuant_replicate_one_succ (m : ℕ) :
    Continuant (List.replicate (m + 1) 1)
      = Continuant (List.replicate m 1) - secondCont (List.replicate m 1) := by
  rw [List.replicate_succ, continuant_cons]; ring

/-- **The all-ones continuant is period-6 (joint headline).**  Both the continuant
`aₙ = K(1ⁿ)` and its trailing companion `sₙ = secondCont(1ⁿ)` satisfy
`a₍ₙ₊₆₎ = aₙ` and `s₍ₙ₊₆₎ = sₙ`.  The coupled recurrence `aₙ₊₁ = aₙ − sₙ`,
`sₙ₊₁ = aₙ` is the order-6 rotation `[[1,−1],[1,0]]`, whose sixth power is the
identity; unfolding six steps reduces the claim to linear integer arithmetic that
`omega` discharges. -/
theorem continuant_secondCont_replicate_one (n : ℕ) :
    Continuant (List.replicate (n + 6) 1) = Continuant (List.replicate n 1)
      ∧ secondCont (List.replicate (n + 6) 1) = secondCont (List.replicate n 1) := by
  have c1 : Continuant (List.replicate (n + 1) 1)
      = Continuant (List.replicate n 1) - secondCont (List.replicate n 1) :=
    continuant_replicate_one_succ n
  have s1 : secondCont (List.replicate (n + 1) 1) = Continuant (List.replicate n 1) :=
    secondCont_replicate_one n
  have c2 : Continuant (List.replicate (n + 2) 1)
      = Continuant (List.replicate (n + 1) 1) - secondCont (List.replicate (n + 1) 1) :=
    continuant_replicate_one_succ (n + 1)
  have s2 : secondCont (List.replicate (n + 2) 1) = Continuant (List.replicate (n + 1) 1) :=
    secondCont_replicate_one (n + 1)
  have c3 : Continuant (List.replicate (n + 3) 1)
      = Continuant (List.replicate (n + 2) 1) - secondCont (List.replicate (n + 2) 1) :=
    continuant_replicate_one_succ (n + 2)
  have s3 : secondCont (List.replicate (n + 3) 1) = Continuant (List.replicate (n + 2) 1) :=
    secondCont_replicate_one (n + 2)
  have c4 : Continuant (List.replicate (n + 4) 1)
      = Continuant (List.replicate (n + 3) 1) - secondCont (List.replicate (n + 3) 1) :=
    continuant_replicate_one_succ (n + 3)
  have s4 : secondCont (List.replicate (n + 4) 1) = Continuant (List.replicate (n + 3) 1) :=
    secondCont_replicate_one (n + 3)
  have c5 : Continuant (List.replicate (n + 5) 1)
      = Continuant (List.replicate (n + 4) 1) - secondCont (List.replicate (n + 4) 1) :=
    continuant_replicate_one_succ (n + 4)
  have s5 : secondCont (List.replicate (n + 5) 1) = Continuant (List.replicate (n + 4) 1) :=
    secondCont_replicate_one (n + 4)
  have c6 : Continuant (List.replicate (n + 6) 1)
      = Continuant (List.replicate (n + 5) 1) - secondCont (List.replicate (n + 5) 1) :=
    continuant_replicate_one_succ (n + 5)
  have s6 : secondCont (List.replicate (n + 6) 1) = Continuant (List.replicate (n + 5) 1) :=
    secondCont_replicate_one (n + 5)
  constructor <;> omega

/-- The all-ones continuant alone is period-6: `K(1ⁿ⁺⁶) = K(1ⁿ)`. -/
theorem continuant_replicate_one_period (n : ℕ) :
    Continuant (List.replicate (n + 6) 1) = Continuant (List.replicate n 1) :=
  (continuant_secondCont_replicate_one n).1

/-- Period-6 across any multiple of `6`: `K(1^(6q+r)) = K(1ʳ)`, by induction on the
number of full turns `q` of the rotation orbit. -/
theorem continuant_replicate_one_six_mul (q r : ℕ) :
    Continuant (List.replicate (6 * q + r) 1) = Continuant (List.replicate r 1) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hidx : 6 * (q + 1) + r = (6 * q + r) + 6 := by ring
    rw [hidx, continuant_replicate_one_period, ih]

/-- **Closed form via residue mod 6.**  `K(1ⁿ)` depends only on `n % 6`, so the
period-6 orbit `1,1,0,−1,−1,0` (for `n % 6 = 0,…,5`) determines every value. -/
theorem continuant_replicate_one_mod (n : ℕ) :
    Continuant (List.replicate n 1) = Continuant (List.replicate (n % 6) 1) := by
  conv_lhs => rw [← Nat.div_add_mod n 6]
  exact continuant_replicate_one_six_mul (n / 6) (n % 6)

/-- **The balanced extreme stays bounded.**  For *every* length `n`,
`K(1ⁿ) ∈ {1, 0, −1}` — the all-ones continuant never grows.  This is the sharp
contrast with the all-`2` ladder `continuant_replicate_two` (`K = n + 1`, linear
growth): the §17 dichotomy made fully quantitative on its two extremes. -/
theorem continuant_replicate_one_bounded (n : ℕ) :
    Continuant (List.replicate n 1) = 1 ∨ Continuant (List.replicate n 1) = 0
      ∨ Continuant (List.replicate n 1) = -1 := by
  rw [continuant_replicate_one_mod n]
  have h6 : n % 6 < 6 := by omega
  set r := n % 6 with hr
  clear_value r
  interval_cases r <;> decide

/-- `|K(1ⁿ)| ≤ 1` for all `n` — the bound packaged as an absolute value, the
order-side statement that the balanced extreme is metrically flat. -/
theorem continuant_replicate_one_abs_le_one (n : ℕ) :
    |Continuant (List.replicate n 1)| ≤ 1 := by
  rcases continuant_replicate_one_bounded n with h | h | h <;> rw [h] <;> decide

/-! ## §22: The boundary of the positive cone — leading `1`s in a large-quotient run

§20/§21 nailed the two pure extremes (all-`2` linear `K = n + 1`, all-`1` period-6 with
`|K| ≤ 1`).  This section characterises the **boundary** between them: starting from a
large-quotient (all-`≥ 2`) tail — where §17 `continuant_pos` gives `0 < K` — how many
leading quotients may drop to `1` before positivity is lost?

The answer is **exactly one**.  Two closed-form identities collapse a leading-`1` prefix
onto the tail's two continuants:

* `K(1 :: ks) = K(ks) − secondCont ks`   (one leading `1`),
* `K(1 :: 1 :: ks) = − secondCont ks`     (two leading `1`s).

The §17 core invariant `0 ≤ secondCont ks < Continuant ks` (`secondCont_lt_continuant`)
then reads off the sign immediately: with a single leading `1` the continuant stays
`> 0` (the strict domination `secondCont < K`), but a *second* consecutive `1` flips it to
`− secondCont ks ≤ 0` — strictly negative as soon as the tail is nonempty.  This is the
precise crossing point from §17's positive cone into the §21 period-6 orbit; the
empty-tail edge `K(1 :: 1 :: []) = 0` recovers the §21 witness `continuant_ones_two`.

Depends only on the §14 recurrence `continuant_cons` and the §17 invariant
`secondCont_lt_continuant` / `secondCont_nonneg` / `continuant_pos`. -/

/-- **One leading `1` (closed form).**  Prepending a single `1` subtracts the trailing
continuant: `K(1 :: ks) = K(ks) − secondCont ks`.  A pure instance of `continuant_cons`
with `k = 1`. -/
theorem continuant_one_cons (ks : List ℤ) :
    Continuant (1 :: ks) = Continuant ks - secondCont ks := by
  rw [continuant_cons]; ring

/-- **Two leading `1`s (closed form).**  A second consecutive `1` cancels the leading
continuant entirely: `K(1 :: 1 :: ks) = − secondCont ks`.  Indeed
`K(1::1::ks) = K(1::ks) − secondCont (1::ks) = (K(ks) − secondCont ks) − K(ks)`, using
`secondCont (1 :: ks) = Continuant ks`. -/
theorem continuant_one_one_cons (ks : List ℤ) :
    Continuant (1 :: 1 :: ks) = - secondCont ks := by
  rw [continuant_one_cons (1 :: ks), continuant_one_cons ks]
  simp only [secondCont]
  ring

/-- **A single leading `1` preserves positivity.**  On a large-quotient tail
(`∀ k ∈ ks, 2 ≤ k`, so §17 gives `secondCont ks < Continuant ks`), one leading `1`
keeps the continuant strictly positive: `0 < K(1 :: ks)`.  By `continuant_one_cons`,
`K(1::ks) = K(ks) − secondCont ks > 0` by the strict domination. -/
theorem continuant_one_cons_pos (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    0 < Continuant (1 :: ks) := by
  rw [continuant_one_cons]
  have hd := secondCont_lt_continuant ks h
  linarith [hd.2]

/-- **A second consecutive `1` destroys positivity.**  On the same large-quotient tail,
`K(1 :: 1 :: ks) = − secondCont ks ≤ 0` (`continuant_one_one_cons` plus
`secondCont_nonneg`).  So at most one leading quotient may drop to `1` while staying in
§17's positive cone — the sharp boundary into the §21 period-6 orbit. -/
theorem continuant_one_one_cons_nonpos (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    Continuant (1 :: 1 :: ks) ≤ 0 := by
  rw [continuant_one_one_cons]
  have := secondCont_nonneg ks h
  linarith

/-- **Strict crossing (nonempty tail).**  When the large-quotient tail is nonempty the
second leading `1` makes the continuant *strictly* negative: `K(1 :: 1 :: ks) < 0`.  The
trailing continuant of a nonempty all-`≥ 2` list is positive
(`secondCont (k :: rest) = Continuant rest > 0` by `continuant_pos`), so
`− secondCont ks < 0`.  The empty-tail edge `K([1,1]) = 0` (§21 `continuant_ones_two`) is
thus the *only* place the two-leading-`1` value touches zero; any large-quotient tail
pushes it strictly below. -/
theorem continuant_one_one_cons_neg (ks : List ℤ) (hne : ks ≠ [])
    (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    Continuant (1 :: 1 :: ks) < 0 := by
  rw [continuant_one_one_cons]
  obtain ⟨k, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [secondCont]
  have hrest : ∀ j ∈ rest, (2 : ℤ) ≤ j := fun j hj => h j (List.mem_cons_of_mem k hj)
  have := continuant_pos rest hrest
  linarith

/-! ## §23: Leading `1`s on an arbitrary tail — the period-6 rotation, in full

§22 read off the *boundary* of §17's positive cone from the two closed forms
`K(1 :: ks) = K(ks) − secondCont ks` and `K(1 :: 1 :: ks) = − secondCont ks`,
proving that **exactly one** leading `1` keeps a large-quotient tail positive.  §21
established that the *pure* all-`1` list (`ks = []`) is period-6 with orbit
`1, 1, 0, −1, −1, 0`.  This section unifies the two: prepending `j` leading `1`s to an
**arbitrary** tail `ks` is the order-6 rotation `[[1,−1],[1,0]]` acting on the pair
`(aⱼ, sⱼ) = (K(1ʲ ++ ks), secondCont(1ʲ ++ ks))`.

Writing the §14 single-step recurrences with every leading quotient `= 1` gives the
coupled system `aⱼ₊₁ = aⱼ − sⱼ`, `sⱼ₊₁ = aⱼ` — identical to §21's all-`1` system but now
seeded at the arbitrary pair `(K(ks), secondCont ks)` rather than `(1, 0)`.  Its
companion is the order-6 rotation, so the pair is **6-periodic in the prefix length**
`j`, and the continuant runs through the explicit orbit

  `K(ks), K(ks) − secondCont ks, − secondCont ks, − K(ks), secondCont ks − K(ks), secondCont ks`.

Substituting `ks = []` (`K = 1`, `secondCont = 0`) recovers §21's `1, 1, 0, −1, −1, 0`
exactly; `j = 1, 2` recover the §22 closed forms.  On a large-quotient tail the sign of
each orbit value is then fixed by the §17 invariant `0 < secondCont ks < K(ks)`
(`secondCont_lt_continuant` + `continuant_pos`): the continuant is `> 0` precisely for
`j ≡ 0, 1, 5 (mod 6)` and `< 0` for `j ≡ 2, 3, 4`, never zero.  This is the full
mixed leading-`1` / large-quotient sign classification — the §22 boundary promoted to a
periodic law, the structural reason a leading run of small quotients can neither grow
the continuant nor keep it one-signed.

Depends only on the §14 recurrence `continuant_cons`, the §22 closed forms, and the §17
invariant `secondCont_lt_continuant` / `continuant_pos`. -/

/-- The trailing continuant of a cons is the continuant of the tail (definitional,
named so it rewrites only explicit cons-form occurrences and leaves a bare
`secondCont xs` on a variable list untouched). -/
theorem secondCont_cons (k : ℤ) (ks : List ℤ) : secondCont (k :: ks) = Continuant ks :=
  rfl

/-- **Three leading `1`s (closed form).**  `K(1 :: 1 :: 1 :: ks) = − K(ks)`: the third
consecutive `1` negates the tail continuant, the half-turn of the order-6 rotation. -/
theorem continuant_three_ones_cons (ks : List ℤ) :
    Continuant (1 :: 1 :: 1 :: ks) = - Continuant ks := by
  rw [continuant_one_one_cons (1 :: ks), secondCont_cons]

/-- **Four leading `1`s (closed form).**  `K(1⁴ :: ks) = secondCont ks − K(ks)`. -/
theorem continuant_four_ones_cons (ks : List ℤ) :
    Continuant (1 :: 1 :: 1 :: 1 :: ks) = secondCont ks - Continuant ks := by
  rw [continuant_one_cons (1 :: 1 :: 1 :: ks), continuant_three_ones_cons,
      secondCont_cons, continuant_one_one_cons]
  ring

/-- **Five leading `1`s (closed form).**  `K(1⁵ :: ks) = secondCont ks`; the sixth
leading `1` returns to `K(ks)` (the period closes — see
`continuant_secondCont_replicate_one_append`). -/
theorem continuant_five_ones_cons (ks : List ℤ) :
    Continuant (1 :: 1 :: 1 :: 1 :: 1 :: ks) = secondCont ks := by
  rw [continuant_one_cons (1 :: 1 :: 1 :: 1 :: ks), continuant_four_ones_cons,
      secondCont_cons, continuant_three_ones_cons]
  ring

/-- Trailing-continuant single step under a leading `1` on an arbitrary tail:
`secondCont(1ʲ⁺¹ ++ ks) = K(1ʲ ++ ks)`.  Immediate from `secondCont (_ :: xs) = K(xs)`. -/
theorem secondCont_replicate_one_append (j : ℕ) (ks : List ℤ) :
    secondCont (List.replicate (j + 1) 1 ++ ks)
      = Continuant (List.replicate j 1 ++ ks) := by
  rw [List.replicate_succ, List.cons_append]; rfl

/-- Continuant single step under a leading `1` on an arbitrary tail:
`aⱼ₊₁ = aⱼ − sⱼ`, the §14 recurrence `continuant_cons` with the leading factor `= 1`. -/
theorem continuant_replicate_one_succ_append (j : ℕ) (ks : List ℤ) :
    Continuant (List.replicate (j + 1) 1 ++ ks)
      = Continuant (List.replicate j 1 ++ ks)
        - secondCont (List.replicate j 1 ++ ks) := by
  rw [List.replicate_succ, List.cons_append, continuant_cons]; ring

/-- **The leading-`1` pair is period-6 (joint headline).**  For *every* tail `ks` and
prefix length `j`, both `aⱼ = K(1ʲ ++ ks)` and its companion `sⱼ = secondCont(1ʲ ++ ks)`
satisfy `aⱼ₊₆ = aⱼ` and `sⱼ₊₆ = sⱼ`.  The coupled recurrence `aⱼ₊₁ = aⱼ − sⱼ`,
`sⱼ₊₁ = aⱼ` is the order-6 rotation `[[1,−1],[1,0]]`, whose sixth power is the identity;
unfolding six steps reduces the claim to linear integer arithmetic that `omega`
discharges.  Specialising `ks = []` gives §21's `continuant_secondCont_replicate_one`. -/
theorem continuant_secondCont_replicate_one_append (j : ℕ) (ks : List ℤ) :
    Continuant (List.replicate (j + 6) 1 ++ ks)
        = Continuant (List.replicate j 1 ++ ks)
      ∧ secondCont (List.replicate (j + 6) 1 ++ ks)
        = secondCont (List.replicate j 1 ++ ks) := by
  have c1 : Continuant (List.replicate (j + 1) 1 ++ ks)
      = Continuant (List.replicate j 1 ++ ks) - secondCont (List.replicate j 1 ++ ks) :=
    continuant_replicate_one_succ_append j ks
  have s1 : secondCont (List.replicate (j + 1) 1 ++ ks)
      = Continuant (List.replicate j 1 ++ ks) :=
    secondCont_replicate_one_append j ks
  have c2 : Continuant (List.replicate (j + 2) 1 ++ ks)
      = Continuant (List.replicate (j + 1) 1 ++ ks)
        - secondCont (List.replicate (j + 1) 1 ++ ks) :=
    continuant_replicate_one_succ_append (j + 1) ks
  have s2 : secondCont (List.replicate (j + 2) 1 ++ ks)
      = Continuant (List.replicate (j + 1) 1 ++ ks) :=
    secondCont_replicate_one_append (j + 1) ks
  have c3 : Continuant (List.replicate (j + 3) 1 ++ ks)
      = Continuant (List.replicate (j + 2) 1 ++ ks)
        - secondCont (List.replicate (j + 2) 1 ++ ks) :=
    continuant_replicate_one_succ_append (j + 2) ks
  have s3 : secondCont (List.replicate (j + 3) 1 ++ ks)
      = Continuant (List.replicate (j + 2) 1 ++ ks) :=
    secondCont_replicate_one_append (j + 2) ks
  have c4 : Continuant (List.replicate (j + 4) 1 ++ ks)
      = Continuant (List.replicate (j + 3) 1 ++ ks)
        - secondCont (List.replicate (j + 3) 1 ++ ks) :=
    continuant_replicate_one_succ_append (j + 3) ks
  have s4 : secondCont (List.replicate (j + 4) 1 ++ ks)
      = Continuant (List.replicate (j + 3) 1 ++ ks) :=
    secondCont_replicate_one_append (j + 3) ks
  have c5 : Continuant (List.replicate (j + 5) 1 ++ ks)
      = Continuant (List.replicate (j + 4) 1 ++ ks)
        - secondCont (List.replicate (j + 4) 1 ++ ks) :=
    continuant_replicate_one_succ_append (j + 4) ks
  have s5 : secondCont (List.replicate (j + 5) 1 ++ ks)
      = Continuant (List.replicate (j + 4) 1 ++ ks) :=
    secondCont_replicate_one_append (j + 4) ks
  have c6 : Continuant (List.replicate (j + 6) 1 ++ ks)
      = Continuant (List.replicate (j + 5) 1 ++ ks)
        - secondCont (List.replicate (j + 5) 1 ++ ks) :=
    continuant_replicate_one_succ_append (j + 5) ks
  have s6 : secondCont (List.replicate (j + 6) 1 ++ ks)
      = Continuant (List.replicate (j + 5) 1 ++ ks) :=
    secondCont_replicate_one_append (j + 5) ks
  constructor <;> omega

/-- The leading-`1` continuant alone is period-6: `K(1ʲ⁺⁶ ++ ks) = K(1ʲ ++ ks)`. -/
theorem continuant_replicate_one_append_period (j : ℕ) (ks : List ℤ) :
    Continuant (List.replicate (j + 6) 1 ++ ks)
      = Continuant (List.replicate j 1 ++ ks) :=
  (continuant_secondCont_replicate_one_append j ks).1

/-- Period-6 across any multiple of `6`: `K(1^(6q+r) ++ ks) = K(1ʳ ++ ks)`, by induction
on the number of full turns `q` of the rotation orbit. -/
theorem continuant_replicate_one_append_six_mul (q r : ℕ) (ks : List ℤ) :
    Continuant (List.replicate (6 * q + r) 1 ++ ks)
      = Continuant (List.replicate r 1 ++ ks) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hidx : 6 * (q + 1) + r = (6 * q + r) + 6 := by ring
    rw [hidx, continuant_replicate_one_append_period, ih]

/-- **Closed form via residue mod 6.**  `K(1ʲ ++ ks)` depends only on `j % 6` — the
prefix length matters solely through its position on the order-6 orbit. -/
theorem continuant_replicate_one_append_mod (j : ℕ) (ks : List ℤ) :
    Continuant (List.replicate j 1 ++ ks)
      = Continuant (List.replicate (j % 6) 1 ++ ks) := by
  conv_lhs => rw [← Nat.div_add_mod j 6]
  exact continuant_replicate_one_append_six_mul (j / 6) (j % 6) ks

/-- **The full leading-`1` orbit (closed form).**  For every tail `ks`, the continuant
`K(1ʲ ++ ks)` runs through the six explicit values of the order-6 rotation orbit seeded
at `(K(ks), secondCont ks)`, selected by `j % 6`:
`K, K − s, −s, −K, s − K, s` (with `s = secondCont ks`).  Substituting `ks = []`
(`K = 1`, `s = 0`) yields §21's orbit `1, 1, 0, −1, −1, 0`; `j % 6 = 1, 2` are the §22
closed forms `continuant_one_cons` / `continuant_one_one_cons`. -/
theorem continuant_replicate_one_append_orbit (j : ℕ) (ks : List ℤ) :
    Continuant (List.replicate j 1 ++ ks)
      = (if j % 6 = 0 then Continuant ks
         else if j % 6 = 1 then Continuant ks - secondCont ks
         else if j % 6 = 2 then - secondCont ks
         else if j % 6 = 3 then - Continuant ks
         else if j % 6 = 4 then secondCont ks - Continuant ks
         else secondCont ks) := by
  rw [continuant_replicate_one_append_mod j ks]
  have h6 : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  set r := j % 6 with hr
  clear_value r
  interval_cases r
  · simp
  · simpa using continuant_one_cons ks
  · simpa using continuant_one_one_cons ks
  · simpa using continuant_three_ones_cons ks
  · simpa using continuant_four_ones_cons ks
  · simpa using continuant_five_ones_cons ks

/-- **Sign classification (large-quotient tail).**  On a nonempty all-`≥ 2` tail the §17
invariant `0 < secondCont ks < K(ks)` fixes the sign of every orbit value: the continuant
`K(1ʲ ++ ks)` is strictly positive **iff** `j ≡ 0, 1, 5 (mod 6)`.  The complementary
residues `j ≡ 2, 3, 4` give a strictly negative value (`continuant_replicate_one_append_ne_zero`),
so the leading-`1` run alternates sign in a fixed period-6 pattern and is never zero —
§22's "exactly one leading `1` preserves positivity" promoted to the full periodic law. -/
theorem continuant_replicate_one_append_pos_iff (j : ℕ) (ks : List ℤ)
    (hne : ks ≠ []) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    0 < Continuant (List.replicate j 1 ++ ks)
      ↔ (j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 5) := by
  rw [continuant_replicate_one_append_orbit]
  have hpos : 0 < Continuant ks := continuant_pos ks h
  have hsc : 0 < secondCont ks := by
    obtain ⟨k, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [secondCont]
    exact continuant_pos rest (fun m hm => h m (List.mem_cons_of_mem k hm))
  have hlt : secondCont ks < Continuant ks := (secondCont_lt_continuant ks h).2
  have h6 : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  set r := j % 6 with hr
  clear_value r
  interval_cases r <;> simp <;> omega

/-- **The leading-`1` orbit never vanishes on a large-quotient tail.**  For a nonempty
all-`≥ 2` tail, `K(1ʲ ++ ks) ≠ 0` for *every* prefix length `j`: the empty-tail zeros of
§21's orbit (`K[1,1] = 0`, etc.) are an artefact of `ks = []`; any large-quotient tail
pushes every orbit value strictly off zero. -/
theorem continuant_replicate_one_append_ne_zero (j : ℕ) (ks : List ℤ)
    (hne : ks ≠ []) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    Continuant (List.replicate j 1 ++ ks) ≠ 0 := by
  rw [continuant_replicate_one_append_orbit]
  have hpos : 0 < Continuant ks := continuant_pos ks h
  have hsc : 0 < secondCont ks := by
    obtain ⟨k, rest, rfl⟩ := List.exists_cons_of_ne_nil hne
    simp only [secondCont]
    exact continuant_pos rest (fun m hm => h m (List.mem_cons_of_mem k hm))
  have hlt : secondCont ks < Continuant ks := (secondCont_lt_continuant ks h).2
  have h6 : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  set r := j % 6 with hr
  clear_value r
  interval_cases r <;> simp <;> omega

/-! ## §24: Trailing `1`s — the period-6 law transfers to suffixes via reversal

§23 governs a leading-`1` run `1ʲ ++ ks`.  The §16 reversal bridge
`continuant_reverse : K(ks.reverse) = K(ks)` upgrades this to a **trailing**-`1` run
`ks ++ 1ʲ` for free: since `(ks ++ 1ʲ).reverse = 1ʲ ++ ks.reverse` (reversing fixes the
all-`1` block), appending `j` trailing `1`s to a tail is *exactly* prepending `j` leading
`1`s to the reversed tail.  The continuant is reversal-invariant, so the whole §23 orbit
carries over with `ks` replaced by `ks.reverse`.  The sign classification is even cleaner:
membership is reversal-invariant (`ks.reverse` is again all-`≥ 2` and nonempty), so the
period-6 positivity law `j ≡ 0, 1, 5 (mod 6)` holds for trailing `1`s with the **identical**
residues and no reference to `secondCont` at all — the period-6 rotation brackets a
large-quotient block on *both* ends in the same way. -/

/-- **Reversal bridge for a trailing-`1` run.**  Appending `j` trailing `1`s to `ks`
equals prepending `j` leading `1`s to `ks.reverse`. -/
theorem continuant_append_replicate_one_eq (j : ℕ) (ks : List ℤ) :
    Continuant (ks ++ List.replicate j 1)
      = Continuant (List.replicate j 1 ++ ks.reverse) := by
  rw [← continuant_reverse (ks ++ List.replicate j 1), List.reverse_append,
    List.reverse_replicate]

/-- **Period-6 orbit for a trailing-`1` run (headline).**  The §23 orbit transferred
through the reversal bridge: `K(ks ++ 1ʲ)` cycles with period 6 in `j`, with the same
shape `[K, K − s, − s, − K, s − K, s]` but now `s = secondCont ks.reverse` and
`K = K(ks)` (using `K(ks.reverse) = K(ks)`). -/
theorem continuant_append_replicate_one_orbit (j : ℕ) (ks : List ℤ) :
    Continuant (ks ++ List.replicate j 1)
      = (if j % 6 = 0 then Continuant ks
         else if j % 6 = 1 then Continuant ks - secondCont ks.reverse
         else if j % 6 = 2 then - secondCont ks.reverse
         else if j % 6 = 3 then - Continuant ks
         else if j % 6 = 4 then secondCont ks.reverse - Continuant ks
         else secondCont ks.reverse) := by
  rw [continuant_append_replicate_one_eq, continuant_replicate_one_append_orbit,
    continuant_reverse]

/-- **Sign classification for a trailing-`1` run (large-quotient tail).**  On a nonempty
all-`≥ 2` tail, `K(ks ++ 1ʲ) > 0` **iff** `j ≡ 0, 1, 5 (mod 6)` — the *same* residues as
the leading-`1` law §23, since `ks.reverse` is again nonempty and all-`≥ 2`. -/
theorem continuant_append_replicate_one_pos_iff (j : ℕ) (ks : List ℤ)
    (hne : ks ≠ []) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    0 < Continuant (ks ++ List.replicate j 1)
      ↔ (j % 6 = 0 ∨ j % 6 = 1 ∨ j % 6 = 5) := by
  rw [continuant_append_replicate_one_eq]
  refine continuant_replicate_one_append_pos_iff j ks.reverse ?_ ?_
  · simpa using hne
  · intro k hk
    exact h k (List.mem_reverse.mp hk)

/-- **The trailing-`1` orbit never vanishes on a large-quotient tail.**  Mirrors §23's
`continuant_replicate_one_append_ne_zero` for suffixes. -/
theorem continuant_append_replicate_one_ne_zero (j : ℕ) (ks : List ℤ)
    (hne : ks ≠ []) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    Continuant (ks ++ List.replicate j 1) ≠ 0 := by
  rw [continuant_append_replicate_one_eq]
  refine continuant_replicate_one_append_ne_zero j ks.reverse ?_ ?_
  · simpa using hne
  · intro k hk
    exact h k (List.mem_reverse.mp hk)

/-! ## §25: Interior `1`-runs — the period-6 law at a Stern–Brocot junction

§23 (leading `1`s) and §24 (trailing `1`s) handled a small-quotient run at either
*end* of a quotient list.  The configuration the density count toward `1/12` actually
sums over is the **interior junction**: a `1`-run of length `j` wedged between two
arbitrary blocks, `as ++ 1ʲ ++ bs`.  This section shows the continuant of such a list
is **period-6 in `j` unconditionally** — for *every* pair of blocks `as`, `bs`, with no
large-quotient hypothesis whatsoever.

The engine is Euler's composition law `continuant_append` (§16): peeling the leading
block,
  `K(as ++ 1ʲ ++ bs) = K(as)·K(1ʲ ++ bs) − secondCont(as.reverse)·secondCont(1ʲ ++ bs)`.
Both `K(1ʲ ++ bs)` and `secondCont(1ʲ ++ bs)` are period-6 in `j` (§23's joint
`continuant_secondCont_replicate_one_append`), and `K(as)`, `secondCont(as.reverse)` are
constant in `j`; so their fixed linear combination is again period-6.  Moreover the §23
pair satisfies the *half-turn* law `(aⱼ₊₃, sⱼ₊₃) = (−aⱼ, −sⱼ)` (three steps of the
order-6 rotation `[[1,−1],[1,0]]`), which passes straight through the linear combination:
the interior continuant negates every three insertions.

Consequently the whole orbit collapses to its first three values and their negatives:
  `K(as ++ 1ʲ ++ bs)` runs through `v₀, v₁, v₂, −v₀, −v₁, −v₂` with `vᵢ = K(as ++ 1ⁱ ++ bs)`,
selected by `j % 6`, where `v₀ = K(as ++ bs)` is the *direct* junction (no inserted `1`s).
So an interior small-quotient run changes the §14 run-length window only through `j mod 6`
and a sign that flips every three insertions — it can neither grow the continuant nor
break its sign pattern aperiodically.

**Honest boundary (unchanged).**  This is a structural reduction of the *interior* `1`-run
degree of freedom to a finite (period-6, three-magnitude) set; it does **not** bound the
density of admissible quotient lists keeping every non-adjacent window nonnegative — the
open `1/12`–`1/4` constant.  What §25 buys: in any density count, an interior `1`-run may
be taken of length `≤ 5` (indeed `≤ 2` up to sign) without changing the continuant's sign,
so the junctions to enumerate are finitely many per pair of surrounding blocks. -/

/-- **Joint leading-`1` half-turn.**  Three steps of the §23 order-6 rotation negate the
pair: `K(1ʲ⁺³ ++ ks) = −K(1ʲ ++ ks)` and `secondCont(1ʲ⁺³ ++ ks) = −secondCont(1ʲ ++ ks)`.
The half-turn `[[1,−1],[1,0]]³ = −I` of the rotation, unfolded three times and closed by
`omega`.  Specialising `ks = []` gives the §21 half-period `K(1ʲ⁺³) = −K(1ʲ)`. -/
theorem continuant_secondCont_replicate_one_append_half (j : ℕ) (ks : List ℤ) :
    Continuant (List.replicate (j + 3) 1 ++ ks)
        = - Continuant (List.replicate j 1 ++ ks)
      ∧ secondCont (List.replicate (j + 3) 1 ++ ks)
        = - secondCont (List.replicate j 1 ++ ks) := by
  have c1 : Continuant (List.replicate (j + 1) 1 ++ ks)
      = Continuant (List.replicate j 1 ++ ks) - secondCont (List.replicate j 1 ++ ks) :=
    continuant_replicate_one_succ_append j ks
  have s1 : secondCont (List.replicate (j + 1) 1 ++ ks)
      = Continuant (List.replicate j 1 ++ ks) :=
    secondCont_replicate_one_append j ks
  have c2 : Continuant (List.replicate (j + 2) 1 ++ ks)
      = Continuant (List.replicate (j + 1) 1 ++ ks)
        - secondCont (List.replicate (j + 1) 1 ++ ks) :=
    continuant_replicate_one_succ_append (j + 1) ks
  have s2 : secondCont (List.replicate (j + 2) 1 ++ ks)
      = Continuant (List.replicate (j + 1) 1 ++ ks) :=
    secondCont_replicate_one_append (j + 1) ks
  have c3 : Continuant (List.replicate (j + 3) 1 ++ ks)
      = Continuant (List.replicate (j + 2) 1 ++ ks)
        - secondCont (List.replicate (j + 2) 1 ++ ks) :=
    continuant_replicate_one_succ_append (j + 2) ks
  have s3 : secondCont (List.replicate (j + 3) 1 ++ ks)
      = Continuant (List.replicate (j + 2) 1 ++ ks) :=
    secondCont_replicate_one_append (j + 2) ks
  constructor <;> omega

/-- **Interior `1`-run period-6 (headline).**  For *every* pair of blocks `as`, `bs`,
inserting six extra `1`s in the interior leaves the continuant unchanged:
`K(as ++ 1ʲ⁺⁶ ++ bs) = K(as ++ 1ʲ ++ bs)`.  Unconditional — no large-quotient hypothesis.
Proof: Euler composition `continuant_append` peels `as`, then the §23 joint period-6 of
the pair `(K, secondCont)(1ʲ ++ bs)` propagates through the fixed linear combination. -/
theorem continuant_interior_replicate_one_period (j : ℕ) (as bs : List ℤ) :
    Continuant (as ++ List.replicate (j + 6) 1 ++ bs)
      = Continuant (as ++ List.replicate j 1 ++ bs) := by
  rw [List.append_assoc as (List.replicate (j + 6) 1) bs,
      List.append_assoc as (List.replicate j 1) bs,
      continuant_append as (List.replicate (j + 6) 1 ++ bs),
      continuant_append as (List.replicate j 1 ++ bs),
      continuant_replicate_one_append_period j bs,
      (continuant_secondCont_replicate_one_append j bs).2]

/-- Period-6 across any multiple of `6`: `K(as ++ 1^(6q+r) ++ bs) = K(as ++ 1ʳ ++ bs)`. -/
theorem continuant_interior_replicate_one_six_mul (q r : ℕ) (as bs : List ℤ) :
    Continuant (as ++ List.replicate (6 * q + r) 1 ++ bs)
      = Continuant (as ++ List.replicate r 1 ++ bs) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hidx : 6 * (q + 1) + r = (6 * q + r) + 6 := by ring
    rw [hidx, continuant_interior_replicate_one_period, ih]

/-- **Closed form via residue mod 6.**  An interior `1`-run affects the continuant only
through its length mod 6: `K(as ++ 1ʲ ++ bs) = K(as ++ 1^(j%6) ++ bs)`. -/
theorem continuant_interior_replicate_one_mod (j : ℕ) (as bs : List ℤ) :
    Continuant (as ++ List.replicate j 1 ++ bs)
      = Continuant (as ++ List.replicate (j % 6) 1 ++ bs) := by
  conv_lhs => rw [← Nat.div_add_mod j 6]
  exact continuant_interior_replicate_one_six_mul (j / 6) (j % 6) as bs

/-- **Interior half-turn.**  Three interior `1`s negate the continuant:
`K(as ++ 1ʲ⁺³ ++ bs) = −K(as ++ 1ʲ ++ bs)`.  The §23 leading half-turn passed through the
Euler composition `continuant_append`. -/
theorem continuant_interior_replicate_one_half (j : ℕ) (as bs : List ℤ) :
    Continuant (as ++ List.replicate (j + 3) 1 ++ bs)
      = - Continuant (as ++ List.replicate j 1 ++ bs) := by
  rw [List.append_assoc as (List.replicate (j + 3) 1) bs,
      List.append_assoc as (List.replicate j 1) bs,
      continuant_append as (List.replicate (j + 3) 1 ++ bs),
      continuant_append as (List.replicate j 1 ++ bs),
      (continuant_secondCont_replicate_one_append_half j bs).1,
      (continuant_secondCont_replicate_one_append_half j bs).2]
  ring

/-- **The interior orbit (closed form).**  `K(as ++ 1ʲ ++ bs)` runs through the six values
`v₀, v₁, v₂, −v₀, −v₁, −v₂` with `vᵢ = K(as ++ 1ⁱ ++ bs)`, selected by `j % 6`.  `v₀` is the
*direct* junction `K(as ++ bs)` (no inserted `1`s); `v₁, v₂` are one and two inserted `1`s;
the residues `3, 4, 5` are their negations (the §25 half-turn).  Everything an interior
`1`-run can do to the continuant is captured by these three magnitudes and a sign. -/
theorem continuant_interior_replicate_one_orbit (j : ℕ) (as bs : List ℤ) :
    Continuant (as ++ List.replicate j 1 ++ bs)
      = (if j % 6 = 0 then Continuant (as ++ bs)
         else if j % 6 = 1 then Continuant (as ++ [1] ++ bs)
         else if j % 6 = 2 then Continuant (as ++ [1, 1] ++ bs)
         else if j % 6 = 3 then - Continuant (as ++ bs)
         else if j % 6 = 4 then - Continuant (as ++ [1] ++ bs)
         else - Continuant (as ++ [1, 1] ++ bs)) := by
  rw [continuant_interior_replicate_one_mod j as bs]
  have h6 : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  set r := j % 6 with hr
  clear_value r
  interval_cases r
  · simp
  · simp [List.replicate_succ]
  · simp [List.replicate_succ]
  · simpa [List.replicate_succ] using continuant_interior_replicate_one_half 0 as bs
  · simpa [List.replicate_succ] using continuant_interior_replicate_one_half 1 as bs
  · simpa [List.replicate_succ] using continuant_interior_replicate_one_half 2 as bs

/-- **Interior junction never vanishes from the run length alone.**  If the three base
junctions `K(as ++ bs)`, `K(as ++ [1] ++ bs)`, `K(as ++ [1,1] ++ bs)` are all nonzero,
then `K(as ++ 1ʲ ++ bs) ≠ 0` for *every* interior run length `j`: by the §25 orbit it is
`±` one of the three, so a vanishing window can never be created purely by lengthening an
interior `1`-run. -/
theorem continuant_interior_replicate_one_ne_zero (j : ℕ) (as bs : List ℤ)
    (h0 : Continuant (as ++ bs) ≠ 0)
    (h1 : Continuant (as ++ [1] ++ bs) ≠ 0)
    (h2 : Continuant (as ++ [1, 1] ++ bs) ≠ 0) :
    Continuant (as ++ List.replicate j 1 ++ bs) ≠ 0 := by
  rw [continuant_interior_replicate_one_orbit]
  have h6 : j % 6 < 6 := Nat.mod_lt _ (by norm_num)
  set r := j % 6 with hr
  clear_value r
  interval_cases r
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa [neg_ne_zero] using h0
  · simpa [neg_ne_zero] using h1
  · simpa [neg_ne_zero] using h2

/-! ## §26: Quotient-weighted growth — large quotients force short runs (toward `O(n/d)`)

§17's `continuant_ge_length` shows an all-`≥ 2` quotient list of length `m` carries a
continuant `≥ m + 1`: linear growth with **slope `1`**.  That suffices for a *crude*
run-length cap `m ≤ n - 1` once one knows the continuant is `≤ n` (the order-`n` Farey
ceiling), but it ignores the *size* of the quotients.  The open density constant
(van Doorn 2025, `c ∈ [1/12, 1/4]`) is governed by how the run length trades off against
the quotient floor `d`: a run whose every quotient is `≥ d` should be *shorter*, length
`O(n/d)`, because each large step inflates the denominator faster.

This section supplies the metric half of that trade-off: on the regime with every entry
`≥ d` (`d ≥ 2`) the continuant grows with **slope `d - 1`**,

  `Continuant ks ≥ (d - 1)·|ks| + 1`,

strictly sharpening §17 (which is the `d = 2` instance).  The induction is the §17 one
re-run with the quotient floor carried through: `K(k :: rest) = k·K(rest) − secondCont rest`
with `k ≥ d` and the §17 invariant `secondCont rest + 1 ≤ K(rest)` (integrality of the
strict domination `secondCont < K`) gives `K(k :: rest) ≥ (d-1)·K(rest) + 1`, and feeding
the inductive bound `K(rest) ≥ (d-1)·|rest| + 1` closes the slope-`(d-1)` step.

The corollary `continuant_run_length_le` reads off the run-length cap: **any** continuant
upper bound `N` on such a run forces `(d - 1)·|ks| + 1 ≤ N`, i.e. `|ks| ≤ (N - 1)/(d - 1)`.
Pairing this with a concrete order-`n` continuant ceiling `Continuant ks ≤ n` (the
remaining ingredient, the order-cap side) yields the targeted `|ks| ≤ (n - 1)/(d - 1)
= O(n/d)` run-length bound — the first genuinely `d`-sensitive cap, sharper than the
slope-`1` `m ≤ n - 1`.  **Honest boundary:** this is the multiplicative-gap (metric) half;
turning it into a density statement still needs the order-cap continuant ceiling and the
count of admissible lists, the open `1/12`–`1/4` step. -/

/-- **Quotient-weighted linear growth.**  On the large-quotient regime with every entry
`≥ d` (`d ≥ 2`), the continuant grows with slope `d - 1`: `(d-1)·|ks| + 1 ≤ Continuant ks`.
The `d = 2` case is §17's `continuant_ge_length`. -/
theorem continuant_ge_length_weighted (d : ℤ) (hd : 2 ≤ d) (ks : List ℤ)
    (h : ∀ k ∈ ks, d ≤ k) :
    (d - 1) * (ks.length : ℤ) + 1 ≤ Continuant ks := by
  induction ks with
  | nil => simp [Continuant]
  | cons k rest ih =>
      have hrest : ∀ j ∈ rest, d ≤ j := fun j hj => h j (List.mem_cons_of_mem k hj)
      have hk : d ≤ k := h k (by simp)
      have hrest2 : ∀ j ∈ rest, (2 : ℤ) ≤ j := fun j hj => le_trans hd (hrest j hj)
      obtain ⟨hs0, hsK⟩ := secondCont_lt_continuant rest hrest2
      have hsK' : secondCont rest + 1 ≤ Continuant rest := Int.lt_iff_add_one_le.mp hsK
      have hIH := ih hrest
      have hLnn : (0 : ℤ) ≤ (rest.length : ℤ) := Int.natCast_nonneg _
      have hKnn : (0 : ℤ) ≤ Continuant rest := by nlinarith [hIH, hLnn, hd]
      rw [continuant_cons]
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
      nlinarith [hsK', hIH, hk, hd, hs0, hLnn, hKnn,
        mul_nonneg (show (0 : ℤ) ≤ k - d by linarith) hKnn,
        mul_nonneg (show (0 : ℤ) ≤ d - 1 by linarith)
          (show (0 : ℤ) ≤ Continuant rest - ((d - 1) * (rest.length : ℤ) + 1) by linarith),
        mul_nonneg (mul_nonneg (show (0 : ℤ) ≤ d - 2 by linarith)
          (show (0 : ℤ) ≤ d - 1 by linarith)) hLnn]

/-- **First run-length upper bound.**  Any continuant upper bound `N` on a large-quotient
run with every entry `≥ d` caps its length: `(d-1)·|ks| + 1 ≤ N`, hence `|ks| ≤ (N-1)/(d-1)`.
With the order-`n` Farey ceiling `Continuant ks ≤ n` this is the targeted `O(n/d)` cap — the
first `d`-sensitive run-length bound, sharper than the slope-`1` `m ≤ n - 1`. -/
theorem continuant_run_length_le {d N : ℤ} (hd : 2 ≤ d) (ks : List ℤ)
    (h : ∀ k ∈ ks, d ≤ k) (hcap : Continuant ks ≤ N) :
    (d - 1) * (ks.length : ℤ) + 1 ≤ N :=
  le_trans (continuant_ge_length_weighted d hd ks h) hcap

/-- §17's `continuant_ge_length` is exactly the `d = 2` instance of the weighted bound,
confirming §24 strictly generalises it. -/
theorem continuant_ge_length_eq_weighted_two (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    (ks.length : ℤ) + 1 ≤ Continuant ks := by
  have := continuant_ge_length_weighted 2 (le_refl 2) ks h
  simpa using this

/-! ## §27: The interior `1`-blow-down — a single interior `1` decrements its neighbours

§25 showed an interior `1`-*run* is period-6 in its length.  The complementary fact for a
*single* interior `1` is sharper and unconditional: a lone `1` wedged between two entries
`a, b` can be **removed**, at the cost of decrementing both neighbours.  At the step-matrix
level this is the classical Hirzebruch–Jung / minus-continued-fraction reduction
  `M(a)·M(1)·M(b) = M(a−1)·M(b−1)`,
a pure `2×2` identity (`M(k) = [[k,−1],[1,0]]`, with the middle `M(1) = [[1,−1],[1,0]]`).
Reading its top-left entry through Euler's composition `contMat_append` (§16) transports it
to the continuant of any surrounding word:
  `K(xs ++ [a, 1, b] ++ ys) = K(xs ++ [a−1, b−1] ++ ys)`.

Two structural payoffs.  (i) **Word shortening.**  The blow-down strictly shortens the
quotient list by one while keeping the continuant fixed; iterating, every interior `1`
flanked by `≥ 2` entries can be eliminated, driving any word toward the §17 large-quotient
normal form (all entries `≥ 2`) on which `K > 0`.  (ii) **The vanishing junction.**  It
exhibits the elementary zero of the minus-continuant directly: `K[2,1,2] = K[1,1] = 0`, the
`a = b = 2` blow-down — a single interior `1` between two `2`s annihilates the continuant.

This is the single-`1` companion to §25's `1`-run period-6.  Where §25 records *how the
sign and magnitude cycle* as a `1`-run lengthens, §27 records *what one interior `1` is* —
a neighbour-decrementing contraction, not a fresh degree of freedom.  The two combine: the
`v₁` magnitude of §25's period-6 orbit *is* the blow-down of the surrounding junction
(`continuant_interior_one_eq_blowdown`). -/

/-- **Step-matrix blow-down (the engine).**  `M(a)·M(1)·M(b) = M(a−1)·M(b−1)` for the
§9 step matrix `M(k) = [[k,−1],[1,0]]`.  A pure `2×2` identity, each of the four entries
closed by `ring` (top-left `ab − a − b = (a−1)(b−1) − 1`; bottom-right `−1` on both sides).
Both sides carry determinant `1`, consistent with `det M(k) = 1` and multiplicativity. -/
theorem stepMat_one_blowdown (a b : ℤ) :
    Mat2.mul (stepMat a) (Mat2.mul (stepMat 1) (stepMat b))
      = Mat2.mul (stepMat (a - 1)) (stepMat (b - 1)) := by
  ext <;> simp only [Mat2.mul, stepMat] <;> ring

/-- The blow-down at the level of the step-matrix product: `P[a,1,b] = P[a−1,b−1]`.
Just `stepMat_one_blowdown` after unfolding the three- and two-element `contMat` products
(the trailing `· one` factors collapse by `mul_one`). -/
theorem contMat_one_blowdown (a b : ℤ) :
    contMat [a, 1, b] = contMat [a - 1, b - 1] := by
  simp only [contMat, Mat2.mul_one]
  exact stepMat_one_blowdown a b

/-- **Interior `1`-blow-down (headline).**  A single interior `1` between `a` and `b` is a
neighbour-decrementing contraction of the continuant, for *any* surrounding blocks:
`K(xs ++ [a, 1, b] ++ ys) = K(xs ++ [a−1, b−1] ++ ys)`.  Unconditional — no large-quotient
hypothesis.  Reading the top-left entry of `contMat_one_blowdown` through Euler's
composition `contMat_append`, which factors the product across the inserted junction. -/
theorem continuant_interior_one_blowdown (xs ys : List ℤ) (a b : ℤ) :
    Continuant (xs ++ [a, 1, b] ++ ys) = Continuant (xs ++ [a - 1, b - 1] ++ ys) := by
  have e1 : xs ++ [a, 1, b] ++ ys = xs ++ ([a, 1, b] ++ ys) := List.append_assoc xs _ ys
  have e2 : xs ++ [a - 1, b - 1] ++ ys = xs ++ ([a - 1, b - 1] ++ ys) :=
    List.append_assoc xs _ ys
  rw [e1, e2, ← contMat_a, ← contMat_a,
      contMat_append, contMat_append, contMat_append, contMat_append,
      contMat_one_blowdown]

/-- The blow-down is a genuine *matrix* identity, so it transfers to every continuant entry,
not just the top-left: `secondCont(xs ++ [a, 1, b] ++ ys) = secondCont(xs ++ [a−1, b−1] ++ ys)`.
Reading the bottom-left entry `(P ·).c` of the same factored product. -/
theorem secondCont_interior_one_blowdown (xs ys : List ℤ) (a b : ℤ) :
    secondCont (xs ++ [a, 1, b] ++ ys) = secondCont (xs ++ [a - 1, b - 1] ++ ys) := by
  have e1 : xs ++ [a, 1, b] ++ ys = xs ++ ([a, 1, b] ++ ys) := List.append_assoc xs _ ys
  have e2 : xs ++ [a - 1, b - 1] ++ ys = xs ++ ([a - 1, b - 1] ++ ys) :=
    List.append_assoc xs _ ys
  rw [e1, e2, ← contMat_c, ← contMat_c,
      contMat_append, contMat_append, contMat_append, contMat_append,
      contMat_one_blowdown]

/-- **Leading blow-down.**  The `xs = []` specialisation:
`K(a :: 1 :: b :: ys) = K((a−1) :: (b−1) :: ys)`.  A `1` directly after the head decrements
the head and its successor. -/
theorem continuant_cons_one_blowdown (ys : List ℤ) (a b : ℤ) :
    Continuant (a :: 1 :: b :: ys) = Continuant ((a - 1) :: (b - 1) :: ys) := by
  simpa using continuant_interior_one_blowdown [] ys a b

/-- **The simplest vanishing junction.**  `K[2, 1, 2] = 0`: the `a = b = 2` blow-down sends
`[2,1,2]` to `[1,1]`, and `K[1,1] = 1·1 − 1 = 0`.  A single interior `1` between two `2`s
annihilates the minus-continuant — the elementary zero underlying the §14 run-length
windows, derived here purely from the §27 blow-down. -/
theorem continuant_two_one_two : Continuant [2, 1, 2] = 0 := by
  have h : Continuant [(2 : ℤ), 1, 2] = Continuant [(2 : ℤ) - 1, 2 - 1] :=
    continuant_cons_one_blowdown [] 2 2
  rw [h]; norm_num [Continuant]

/-- **Bridge to §25.**  The single-`1` interior junction — the `v₁` magnitude of §25's
period-6 orbit — *is* a blow-down: when the surrounding blocks meet at `a, b` (i.e. the
leading block ends in `a`, the trailing block starts with `b`),
`K((as ++ [a]) ++ [1] ++ (b :: bs)) = K(as ++ [a−1, b−1] ++ bs)`.  So `v₁` is the
neighbour-decremented junction, not an independent quantity — §25's three magnitudes
`v₀, v₁, v₂` are continuants of words differing only by such interior contractions. -/
theorem continuant_interior_one_eq_blowdown (as bs : List ℤ) (a b : ℤ) :
    Continuant ((as ++ [a]) ++ [1] ++ (b :: bs))
      = Continuant (as ++ [a - 1, b - 1] ++ bs) := by
  simpa using continuant_interior_one_blowdown as bs a b

/-! ## §28: Two-sided product bounds — the multiplicative refinement of §26

§26 gave the *additive* (slope-`d−1`) lower bound `(d−1)·|ks| + 1 ≤ Continuant ks`, the
linear shadow of how the quotient floor inflates the denominator.  The sharp statement is
*multiplicative*: in the large-quotient regime (every entry `≥ 2`) the continuant is
squeezed between two products of the quotients,

  `∏ᵢ (kᵢ − 1)  ≤  Continuant ks  ≤  ∏ᵢ kᵢ`.

Both halves run the §17/§26 single-step recurrence `K(k::rest) = k·K(rest) − secondCont rest`
against the §17 core invariant `0 ≤ secondCont rest < Continuant rest`
(`secondCont_lt_continuant`).  **Upper:** drop the nonnegative `secondCont`, giving
`K(k::rest) ≤ k·K(rest)`, then multiply the IH `K(rest) ≤ rest.prod` by `k ≥ 0`.
**Lower:** replace `secondCont rest` by its ceiling `K(rest) − 1`, giving
`K(k::rest) ≥ (k−1)·K(rest) + 1`, then multiply the IH `∏(rest−1) ≤ K(rest)` by `k − 1 ≥ 0`.

What this buys, and the **honest boundary**.  The lower product `∏(kᵢ−1)` is genuinely
multiplicative: on an all-`≥ d` run it is `≥ (d−1)^|ks|`, so pairing it with any order-`n`
continuant ceiling `K ≤ n` forces `|ks| ≤ log_{d−1} n` — a *logarithmic* run-length cap on
the large-quotient tail (`d ≥ 3`), far sharper than §26's slope-`1`/`O(n/d)` shadow.  This
is consistent with — and sharpens — the picture that the large-quotient tail carries
negligible mass.  But it is silent exactly at the bottleneck: at `d = 2` the lower factor
`∏(2−1) = 1` is trivial (matching `K[2,2,…,2] = m+1`, the slowest minus-continuant growth),
so the open `1/12`–`1/4` density constant — governed by the small-quotient regime where the
continuant grows only linearly — is untouched.  The product bounds pin the metric trade-off
where it is multiplicative, not where the density is decided. -/

/-- **Lower factor positivity.**  On the large-quotient regime each factor `kᵢ − 1 ≥ 1`, so
`1 ≤ ∏ᵢ (kᵢ − 1)`.  Combined with `prod_sub_one_le_continuant` this re-proves `continuant_pos`
multiplicatively: the continuant dominates a product of positive factors. -/
theorem prod_sub_one_one_le (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    1 ≤ (ks.map (· - 1)).prod := by
  induction ks with
  | nil => simp
  | cons k rest ih =>
      have hrest : ∀ j ∈ rest, (2 : ℤ) ≤ j := fun j hj => h j (List.mem_cons_of_mem k hj)
      have hk : (2 : ℤ) ≤ k := h k (by simp)
      have hIH := ih hrest
      simp only [List.map_cons, List.prod_cons]
      nlinarith [hIH, hk, mul_nonneg (show (0 : ℤ) ≤ k - 2 by linarith)
        (show (0 : ℤ) ≤ (rest.map (· - 1)).prod - 1 by linarith)]

/-- **Product ceiling (upper bound).**  On the large-quotient regime the continuant never
exceeds the product of its quotients: `Continuant ks ≤ ks.prod`.  Each step drops the
nonnegative `secondCont rest` from `K(k::rest) = k·K(rest) − secondCont rest ≤ k·K(rest)`,
then scales the inductive ceiling by `k ≥ 0`. -/
theorem continuant_le_prod (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    Continuant ks ≤ ks.prod := by
  induction ks with
  | nil => simp [Continuant]
  | cons k rest ih =>
      have hrest : ∀ j ∈ rest, (2 : ℤ) ≤ j := fun j hj => h j (List.mem_cons_of_mem k hj)
      have hk : (2 : ℤ) ≤ k := h k (by simp)
      have hs0 : 0 ≤ secondCont rest := secondCont_nonneg rest hrest
      have hIH := ih hrest
      rw [continuant_cons, List.prod_cons]
      nlinarith [hs0, mul_nonneg (show (0 : ℤ) ≤ k by linarith)
        (show (0 : ℤ) ≤ rest.prod - Continuant rest from sub_nonneg.mpr hIH)]

/-- **Product floor (lower bound).**  On the large-quotient regime the continuant is at
least the product of the decremented quotients: `(ks.map (· − 1)).prod ≤ Continuant ks`.
Each step replaces `secondCont rest` by its ceiling `K(rest) − 1`
(`secondCont_lt_continuant`), giving `K(k::rest) ≥ (k−1)·K(rest) + 1`, then scales the
inductive floor by `k − 1 ≥ 0`.  Multiplicative, hence strictly sharper than §26's additive
`(d−1)·|ks| + 1` on every all-`≥ d` run with `d ≥ 3`. -/
theorem prod_sub_one_le_continuant (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    (ks.map (· - 1)).prod ≤ Continuant ks := by
  induction ks with
  | nil => simp [Continuant]
  | cons k rest ih =>
      have hrest : ∀ j ∈ rest, (2 : ℤ) ≤ j := fun j hj => h j (List.mem_cons_of_mem k hj)
      have hk : (2 : ℤ) ≤ k := h k (by simp)
      obtain ⟨hs0, hsK⟩ := secondCont_lt_continuant rest hrest
      have hsK' : secondCont rest + 1 ≤ Continuant rest := Int.lt_iff_add_one_le.mp hsK
      have hIH := ih hrest
      rw [continuant_cons]
      simp only [List.map_cons, List.prod_cons]
      nlinarith [hsK', mul_nonneg (show (0 : ℤ) ≤ k - 1 by linarith)
        (show (0 : ℤ) ≤ Continuant rest - (rest.map (· - 1)).prod from sub_nonneg.mpr hIH)]

/-- **Two-sided product sandwich (headline).**  In the large-quotient regime the continuant
is pinned between the two products `∏(kᵢ − 1) ≤ Continuant ks ≤ ∏ kᵢ` — the multiplicative
refinement of §26's additive bound.  The lower factor captures the genuine geometric
inflation of the denominator (logarithmic run-length cap on the `d ≥ 3` tail); the upper is
the matching ceiling. -/
theorem continuant_prod_bounds (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    (ks.map (· - 1)).prod ≤ Continuant ks ∧ Continuant ks ≤ ks.prod :=
  ⟨prod_sub_one_le_continuant ks h, continuant_le_prod ks h⟩

/-- **Concrete sandwich.**  For `[3, 3]`: `∏(kᵢ − 1) = 4 ≤ K[3,3] = 8 ≤ 9 = ∏ kᵢ`, a strict
two-sided gap (the additive §26 floor here is only `(2)·2 + 1 = 5`, looser than the
multiplicative `4`'s sibling `(3−1)² = 4`… and the all-`≥ 3` product floor `4` is the
geometric one).  Discharged through the general sandwich. -/
theorem continuant_prod_bounds_example :
    ([3, 3].map (· - 1)).prod ≤ Continuant [3, 3]
      ∧ Continuant [3, 3] ≤ ([3, 3] : List ℤ).prod := by
  refine continuant_prod_bounds [3, 3] ?_
  intro k hk; fin_cases hk <;> norm_num

/-! ## §29: The equality locus of the product ceiling — strictness beyond length 1

§28's upper bound `Continuant ks ≤ ks.prod` is tight only at the two trivial depths:
`K([]) = 1 = ∏[]` and `K([k]) = k = ∏[k]`.  As soon as the run carries two or more
quotients the single-step minus-continuant recurrence `K(k::rest) = k·K(rest) − secondCont rest`
subtracts a *strictly positive* trailing continuant — by §22 `secondCont_cons`,
`secondCont (j::rest') = K(rest') ≥ 1` (§17 `continuant_pos`) — so the ceiling is never
attained: `Continuant ks < ks.prod` for `|ks| ≥ 2`.

The engine is a **quantitative deficit**: at each head step the product overshoots the
continuant by *at least* the trailing continuant of the tail,
`secondCont rest ≤ (k::rest).prod − Continuant (k::rest)`, because the residual
`k·(∏rest − K(rest))` is nonnegative by §28's `continuant_le_prod`.  Summed along the run
this says the §28 ceiling overshoots by the accumulated trailing continuants — the exact
multiplicative "loss" the minus-continuant pays relative to the naive product.

This pins the equality locus of the §28 sandwich's upper half (a sharp-boundary companion to
§20's sharpness of the linear floor) and is, like everything in this regime, silent at the
density bottleneck `d = 2`: the strictness is real but the overshoot it measures lives in the
large-quotient tail that carries negligible mass toward the open `1/12`–`1/4` constant. -/

/-- **Product-ceiling deficit.**  For a nonempty large-quotient run `k :: rest`, the product
overshoots the continuant by at least the trailing continuant of the tail:
`secondCont rest ≤ (k :: rest).prod − Continuant (k :: rest)`.  Unfolding the head step
`K(k::rest) = k·K(rest) − secondCont rest`, the deficit is `secondCont rest + k·(∏rest − K rest)`,
and the residual `k·(∏rest − K rest) ≥ 0` by §28 `continuant_le_prod` with `k ≥ 0`. -/
theorem continuant_prod_deficit {k : ℤ} {rest : List ℤ} (hk : (2 : ℤ) ≤ k)
    (h : ∀ x ∈ rest, (2 : ℤ) ≤ x) :
    secondCont rest ≤ (k :: rest).prod - Continuant (k :: rest) := by
  have hle : Continuant rest ≤ rest.prod := continuant_le_prod rest h
  rw [continuant_cons, List.prod_cons]
  nlinarith [mul_nonneg (show (0 : ℤ) ≤ k by linarith)
    (show (0 : ℤ) ≤ rest.prod - Continuant rest from sub_nonneg.mpr hle)]

/-- **Strict product ceiling for length ≥ 2.**  Once a large-quotient run has two or more
quotients, the continuant is *strictly* below the product of its quotients,
`Continuant ks < ks.prod`.  The deficit (`continuant_prod_deficit`) is at least the trailing
continuant `secondCont (j::rest') = K(rest') ≥ 1` (§17 `continuant_pos`), which is strictly
positive — so the §28 ceiling is never attained beyond depth `1`. -/
theorem continuant_lt_prod {ks : List ℤ} (h : ∀ k ∈ ks, (2 : ℤ) ≤ k)
    (hlen : 2 ≤ ks.length) : Continuant ks < ks.prod := by
  rcases ks with _ | ⟨k, _ | ⟨j, rest⟩⟩
  · exact absurd hlen (by decide)
  · simp only [List.length_cons, List.length_nil] at hlen; omega
  · have hk : (2 : ℤ) ≤ k := h k (by simp)
    have hrest : ∀ x ∈ (j :: rest), (2 : ℤ) ≤ x :=
      fun x hx => h x (List.mem_cons_of_mem k hx)
    have hrest' : ∀ x ∈ rest, (2 : ℤ) ≤ x :=
      fun x hx => hrest x (List.mem_cons_of_mem j hx)
    have hscpos : 1 ≤ secondCont (j :: rest) := by
      rw [secondCont_cons]; exact continuant_pos rest hrest'
    have hdef : secondCont (j :: rest) ≤ (k :: j :: rest).prod - Continuant (k :: j :: rest) :=
      continuant_prod_deficit hk hrest
    linarith

/-- **Equality locus of the product ceiling.**  In the large-quotient regime the §28 ceiling
`Continuant ks ≤ ks.prod` is an *equality* exactly at the two trivial depths `|ks| ≤ 1`
(`K[] = 1 = ∏[]`, `K[k] = k = ∏[k]`); for every deeper run it is strict.  The product ceiling
is attained only before the minus-continuant recurrence has had a chance to subtract a
trailing continuant. -/
theorem continuant_eq_prod_iff {ks : List ℤ} (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) :
    Continuant ks = ks.prod ↔ ks.length ≤ 1 := by
  constructor
  · intro heq
    by_contra hlen
    exact absurd heq (ne_of_lt (continuant_lt_prod h (by omega)))
  · intro hlen
    rcases ks with _ | ⟨k, _ | ⟨j, rest⟩⟩
    · simp [continuant_nil]
    · simp [continuant_one]
    · simp only [List.length_cons] at hlen; omega

/-- **Concrete strictness.**  For `[3, 3]` the product ceiling overshoots strictly:
`K[3,3] = 8 < 9 = ∏ kᵢ`, and the deficit `9 − 8 = 1` matches the trailing continuant
`secondCont [3] = K[] = 1`.  Discharged through the general strict bound. -/
theorem continuant_lt_prod_example :
    Continuant [3, 3] < ([3, 3] : List ℤ).prod := by
  refine continuant_lt_prod (ks := [3, 3]) ?_ (by decide)
  intro k hk; fin_cases hk <;> norm_num

/-! ## §30: Geometric growth and the logarithmic run-length cap

§26 reads off an **additive** run-length cap from the slope-`(d−1)` lower bound
`(d−1)·|ks| + 1 ≤ Continuant ks`: a continuant ceiling `K ≤ N` forces
`|ks| ≤ (N−1)/(d−1)`, an `O(N/d)` bound.  §28's product floor `∏(kᵢ−1) ≤ K` is the
sharper *multiplicative* statement, and its prose repeatedly advertises the
consequence — on an all-`≥ d` run `∏(kᵢ−1) ≥ (d−1)^|ks|`, so `K ≤ N` forces
`|ks| ≤ log_{d−1} N`, a **logarithmic** cap — but only informally.  This section
formalises that consequence.

* **Geometric floor (headline).** `(d − 1)^|ks| ≤ Continuant ks` on an all-`≥ d`
  run: the continuant grows at least geometrically with ratio `d − 1`, by chaining
  the elementary `(d−1)^|ks| ≤ ∏(kᵢ−1)` (each decremented factor is `≥ d − 1`)
  through §28's `prod_sub_one_le_continuant`.
* **Logarithmic run-length cap.** For `d ≥ 3` (so the ratio `d − 1 ≥ 2` is a genuine
  base) a continuant ceiling `N` caps the run length at `Nat.log (d−1) N` — the
  exponential sharpening of §26's `(N−1)/(d−1)`, the precise sense in which a
  large-quotient run is *logarithmically* short.

**Honest boundary** (unchanged from §26/§28): the base `d − 1` collapses to `1` at
the density bottleneck `d = 2`, where `(d−1)^|ks| = 1` is vacuous and the run grows
only linearly (`K[2,…,2] = m + 1`).  The geometric cap bites only on the `d ≥ 3`
tail, which carries negligible mass toward the open `1/12`–`1/4` constant. -/

/-- **Geometric floor on the product of decremented quotients.**  On an all-`≥ d`
run (`d ≥ 2`) every factor `kᵢ − 1 ≥ d − 1 ≥ 1`, so the product of the decremented
quotients dominates the pure power: `(d − 1)^|ks| ≤ ∏ᵢ (kᵢ − 1)`. -/
theorem pow_sub_one_le_prod_sub_one (d : ℤ) (hd : 2 ≤ d) (ks : List ℤ)
    (h : ∀ k ∈ ks, d ≤ k) :
    (d - 1) ^ ks.length ≤ (ks.map (· - 1)).prod := by
  induction ks with
  | nil => simp
  | cons k rest ih =>
      have hrest : ∀ j ∈ rest, d ≤ j := fun j hj => h j (List.mem_cons_of_mem k hj)
      have hk : d ≤ k := h k (by simp)
      have hrest2 : ∀ j ∈ rest, (2 : ℤ) ≤ j := fun j hj => le_trans hd (hrest j hj)
      have hIH := ih hrest
      have hprod1 : 1 ≤ (rest.map (· - 1)).prod := prod_sub_one_one_le rest hrest2
      have hpownn : (0 : ℤ) ≤ (d - 1) ^ rest.length := pow_nonneg (by linarith) _
      simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
      calc (d - 1) ^ rest.length * (d - 1)
          ≤ (rest.map (· - 1)).prod * (k - 1) :=
            mul_le_mul hIH (by linarith) (by linarith) (le_trans hpownn hIH)
        _ = (k - 1) * (rest.map (· - 1)).prod := by ring

/-- **Geometric continuant floor (headline).**  On the large-quotient regime with
every entry `≥ d` (`d ≥ 2`) the continuant grows at least geometrically with ratio
`d − 1`: `(d − 1)^|ks| ≤ Continuant ks`.  Chains the elementary power-vs-product
bound `pow_sub_one_le_prod_sub_one` through §28's product floor
`prod_sub_one_le_continuant`.  This is the multiplicative/geometric companion to
§26's additive slope-`(d−1)` bound. -/
theorem continuant_ge_pow (d : ℤ) (hd : 2 ≤ d) (ks : List ℤ)
    (h : ∀ k ∈ ks, d ≤ k) :
    (d - 1) ^ ks.length ≤ Continuant ks := by
  have h2 : ∀ k ∈ ks, (2 : ℤ) ≤ k := fun k hk => le_trans hd (h k hk)
  exact le_trans (pow_sub_one_le_prod_sub_one d hd ks h)
    (prod_sub_one_le_continuant ks h2)

/-- **Geometric run-length bound (power form).**  Any continuant ceiling `N` on an
all-`≥ d` run caps the *power* `(d − 1)^|ks| ≤ N` — the exponential sharpening of
§26's additive `(d−1)·|ks| + 1 ≤ N`. -/
theorem continuant_pow_run_length_le {d N : ℤ} (hd : 2 ≤ d) (ks : List ℤ)
    (h : ∀ k ∈ ks, d ≤ k) (hcap : Continuant ks ≤ N) :
    (d - 1) ^ ks.length ≤ N :=
  le_trans (continuant_ge_pow d hd ks h) hcap

/-- **Logarithmic run-length cap.**  For a genuine large-quotient floor `d ≥ 3`
(ratio `d − 1 ≥ 2`), a continuant ceiling `N` caps the run length *logarithmically*:
`|ks| ≤ Nat.log (d − 1) N`.  This is the exponential improvement over §26's
`O(N/d)` additive cap, and the precise formalisation of the "logarithmic run-length
cap" the §28 product floor was advertised to deliver. -/
theorem continuant_run_length_le_log {d N : ℤ} (hd : 3 ≤ d) (ks : List ℤ)
    (h : ∀ k ∈ ks, d ≤ k) (hcap : Continuant ks ≤ N) :
    ks.length ≤ Nat.log (d - 1).toNat N.toNat := by
  have hd2 : (2 : ℤ) ≤ d := by linarith
  have hpow : (d - 1) ^ ks.length ≤ N := continuant_pow_run_length_le hd2 ks h hcap
  have hdpos : (0 : ℤ) ≤ d - 1 := by linarith
  have hge1 : (1 : ℤ) ≤ (d - 1) ^ ks.length := one_le_pow₀ (by linarith)
  have hN0 : (0 : ℤ) ≤ N := le_trans (by linarith) hpow
  have hb : 1 < (d - 1).toNat := by omega
  have hcast : (d - 1).toNat ^ ks.length ≤ N.toNat := by
    have hZ : ((d - 1).toNat ^ ks.length : ℤ) ≤ (N.toNat : ℤ) := by
      rw [Int.toNat_of_nonneg hdpos, Int.toNat_of_nonneg hN0]
      exact hpow
    exact_mod_cast hZ
  exact (Nat.le_log_iff_pow_le hb (by omega)).mpr hcast

/-- **Concrete geometric floor.**  For the all-`3` run `[3, 3, 3]`:
`(3 − 1)^3 = 8 ≤ Continuant [3,3,3] = 21`, and the logarithmic cap at ceiling
`N = 21` gives `|ks| ≤ Nat.log 2 21 = 4`.  Both discharged through the general
bounds. -/
theorem continuant_ge_pow_example :
    (3 - 1 : ℤ) ^ ([3, 3, 3] : List ℤ).length ≤ Continuant [3, 3, 3] := by
  refine continuant_ge_pow 3 (by norm_num) [3, 3, 3] ?_
  intro k hk; fin_cases hk <;> norm_num

/-! ## §31: The geometric ceiling and the two-sided logarithmic sandwich

§30 delivered the geometric *floor* `(d − 1)^|ks| ≤ Continuant ks` on all-`≥ d` runs,
hence the *upper* logarithmic cap `|ks| ≤ log_{d−1} N` under a continuant ceiling `N`.
The matching *ceiling* comes from §28's product bound `Continuant ks ≤ ks.prod`: if every
quotient is *also* bounded above by `D`, then `ks.prod ≤ D^|ks|`, so
`Continuant ks ≤ D^|ks|`.  A continuant *floor* `N ≤ Continuant ks` then forces the run
*long*: `log_D N ≤ |ks|`.

Together the two directions pin the run length of a bounded-quotient run (`d ≤ kᵢ ≤ D`,
`3 ≤ d`) to a logarithmic band `log_D (K) ≤ |ks| ≤ log_{d−1} (K)` around the continuant —
so in the bounded-quotient regime the continuant grows *exactly* geometrically and the run
length is `Θ(log K)`, equivalently `Θ(log n)` under the order-`n` Farey cap `K ≤ n`.  This
is the honest opposite extreme to the small-quotient (all-`1`/all-`2`) regime, where the
continuant grows only linearly (`K([2,…,2]) = m + 1`, §20) and the open `1/12`–`1/4`
run-length constant lives.  It certifies that any similarly-ordered run *long* enough to
matter for `f(n)` must be built from *small* quotients: a floor of `d ≥ 3` on the quotients
collapses admissible run lengths to `O(log n)`.
-/

/-- Product of an all-`≥ 2` quotient list is at least `1` (hence positive).  Elementary
induction feeding `(k − 2)(∏rest − 1) ≥ 0` to `nlinarith`. -/
theorem one_le_prod (ks : List ℤ) (h : ∀ k ∈ ks, (2 : ℤ) ≤ k) : 1 ≤ ks.prod := by
  induction ks with
  | nil => simp
  | cons k rest ih =>
      have hrest : ∀ j ∈ rest, (2 : ℤ) ≤ j := fun j hj => h j (List.mem_cons_of_mem k hj)
      have hk : (2 : ℤ) ≤ k := h k (by simp)
      have hIH := ih hrest
      rw [List.prod_cons]
      nlinarith [mul_nonneg (show (0 : ℤ) ≤ k - 2 by linarith)
        (show (0 : ℤ) ≤ rest.prod - 1 by linarith)]

/-- Product ceiling by a uniform upper bound: if every entry lies in `[2, D]` the product is
at most `D^|ks|`.  Each head step scales `k ≤ D` against the nonnegative tail product and the
inductive ceiling. -/
theorem prod_le_pow (D : ℤ) (ks : List ℤ) (h2 : ∀ k ∈ ks, (2 : ℤ) ≤ k)
    (hD : ∀ k ∈ ks, k ≤ D) : ks.prod ≤ D ^ ks.length := by
  induction ks with
  | nil => simp
  | cons k rest ih =>
      have hrest2 : ∀ j ∈ rest, (2 : ℤ) ≤ j := fun j hj => h2 j (List.mem_cons_of_mem k hj)
      have hrestD : ∀ j ∈ rest, j ≤ D := fun j hj => hD j (List.mem_cons_of_mem k hj)
      have hk2 : (2 : ℤ) ≤ k := h2 k (by simp)
      have hkD : k ≤ D := hD k (by simp)
      have hDnn : (0 : ℤ) ≤ D := by linarith
      have hprodnn : (0 : ℤ) ≤ rest.prod := by linarith [one_le_prod rest hrest2]
      have hIH := ih hrest2 hrestD
      simp only [List.prod_cons, List.length_cons, pow_succ]
      calc k * rest.prod
          ≤ D * rest.prod := mul_le_mul_of_nonneg_right hkD hprodnn
        _ ≤ D * D ^ rest.length := mul_le_mul_of_nonneg_left hIH hDnn
        _ = D ^ rest.length * D := by ring

/-- **Geometric continuant ceiling (headline).**  On a bounded quotient regime with every
entry in `[2, D]` the continuant is at most geometric with ratio `D`:
`Continuant ks ≤ D^|ks|`.  Chains §28's product ceiling `continuant_le_prod` through the
uniform product bound `prod_le_pow`.  The upper companion to §30's floor
`continuant_ge_pow`. -/
theorem continuant_le_pow (D : ℤ) (ks : List ℤ) (h2 : ∀ k ∈ ks, (2 : ℤ) ≤ k)
    (hD : ∀ k ∈ ks, k ≤ D) : Continuant ks ≤ D ^ ks.length :=
  le_trans (continuant_le_prod ks h2) (prod_le_pow D ks h2 hD)

/-- **Geometric run-length floor (power form).**  A continuant *floor* `N ≤ Continuant ks`
on a bounded-quotient run (`kᵢ ∈ [2, D]`) forces the *power* `N ≤ D^|ks|` — the lower
companion to §30's `continuant_pow_run_length_le`. -/
theorem continuant_pow_run_length_ge {D N : ℤ} (ks : List ℤ) (h2 : ∀ k ∈ ks, (2 : ℤ) ≤ k)
    (hD : ∀ k ∈ ks, k ≤ D) (hfloor : N ≤ Continuant ks) : N ≤ D ^ ks.length :=
  le_trans hfloor (continuant_le_pow D ks h2 hD)

/-- **Logarithmic run-length floor.**  With a uniform quotient ceiling `D ≥ 2`, a continuant
floor `N ≤ Continuant ks` forces the run length *up* logarithmically: `log_D N ≤ |ks|`.  The
exact mirror of §30's `continuant_run_length_le_log`, and the second jaw of the Θ(log K)
sandwich. -/
theorem continuant_run_length_ge_log {D N : ℤ} (hDb : 2 ≤ D) (ks : List ℤ)
    (h2 : ∀ k ∈ ks, (2 : ℤ) ≤ k) (hD : ∀ k ∈ ks, k ≤ D) (hfloor : N ≤ Continuant ks) :
    Nat.log D.toNat N.toNat ≤ ks.length := by
  have hpow : N ≤ D ^ ks.length := continuant_pow_run_length_ge ks h2 hD hfloor
  have hDnn : (0 : ℤ) ≤ D := by linarith
  have hb : 1 < D.toNat := by omega
  by_cases hN : N ≤ 0
  · have hz : N.toNat = 0 := by omega
    simp [hz]
  · push_neg at hN
    have hNnn : (0 : ℤ) ≤ N := le_of_lt hN
    have hcast : N.toNat ≤ D.toNat ^ ks.length := by
      have hZ : (N.toNat : ℤ) ≤ ((D.toNat : ℤ)) ^ ks.length := by
        rw [Int.toNat_of_nonneg hNnn, Int.toNat_of_nonneg hDnn]
        exact hpow
      exact_mod_cast hZ
    calc Nat.log D.toNat N.toNat
        ≤ Nat.log D.toNat (D.toNat ^ ks.length) := Nat.log_mono_right hcast
      _ = ks.length := Nat.log_pow hb ks.length

/-- **Two-sided logarithmic sandwich (headline).**  A bounded-quotient run with every entry
in `[d, D]` and floor `d ≥ 3` has its length pinned into a logarithmic band around its own
continuant: `log_D (Continuant ks) ≤ |ks| ≤ log_{d−1} (Continuant ks)`.  The lower jaw is
§31's geometric ceiling, the upper jaw is §30's geometric floor.  Since both bases exceed
`1`, the continuant of a bounded-quotient run grows *exactly* geometrically and the run
length is `Θ(log K)` — equivalently `Θ(log n)` once the order-`n` Farey cap `Continuant ks ≤ n`
is imposed.  A quotient floor `d ≥ 3` therefore caps admissible similarly-ordered runs at
`O(log n)`, so the `Θ(n)`-long runs behind the open `1/12` lower bound must live entirely in
the small-quotient regime. -/
theorem continuant_run_length_log_sandwich {d D : ℤ} (hd : 3 ≤ d) (hdD : d ≤ D)
    (ks : List ℤ) (hlo : ∀ k ∈ ks, d ≤ k) (hhi : ∀ k ∈ ks, k ≤ D) :
    Nat.log D.toNat (Continuant ks).toNat ≤ ks.length ∧
      ks.length ≤ Nat.log (d - 1).toNat (Continuant ks).toNat := by
  have h2 : ∀ k ∈ ks, (2 : ℤ) ≤ k := fun k hk => le_trans (by linarith) (hlo k hk)
  have hDb : (2 : ℤ) ≤ D := by linarith
  exact ⟨continuant_run_length_ge_log hDb ks h2 hhi (le_refl _),
    continuant_run_length_le_log hd ks hlo (le_refl _)⟩

/-- **Concrete sandwich.**  For the all-`3` run `[3, 3, 3]` (`Continuant [3,3,3] = 21`):
`log₃ 21 = 2 ≤ 3 = |ks| ≤ 4 = log₂ 21`, so the length-`3` run sits inside the band
`[log₃ 21, log₂ 21] = [2, 4]`.  Discharged through the general sandwich. -/
theorem continuant_run_length_log_sandwich_example :
    Nat.log (3 : ℤ).toNat (Continuant [3, 3, 3]).toNat ≤ ([3, 3, 3] : List ℤ).length ∧
      ([3, 3, 3] : List ℤ).length
        ≤ Nat.log ((3 : ℤ) - 1).toNat (Continuant [3, 3, 3]).toNat :=
  continuant_run_length_log_sandwich (d := 3) (D := 3) (by norm_num) (le_refl _) [3, 3, 3]
    (by intro k hk; fin_cases hk <;> norm_num) (by intro k hk; fin_cases hk <;> norm_num)

/-! ## §32: Strict growth from the *right* end — the append dual of §17 monotonicity

§17's `continuant_strict_mono` shows prepending a quotient `k ≥ 2` strictly increases the
continuant, `K(ks) < K(k :: ks)`.  The §16 reversal bridge `continuant_reverse` upgrades this
to the **trailing** end for free: appending a quotient `k ≥ 2` is, after reversal, prepending
it to `ks.reverse` (which is again a nonempty all-`≥ 2` run, membership being reversal-invariant),
so the same strict inequality holds on the right.  Together the two monotonicities say a
large-quotient run grows strictly when extended at *either* end — and hence strictly when a run
is wrapped by quotients on both ends, the metric statement behind "long runs are expensive"
quantified two-sidedly. -/

/-- **Strict monotonicity under appending (the §17 dual).**  In the large-quotient regime
appending a quotient `k ≥ 2` on the right strictly increases the continuant:
`Continuant ks < Continuant (ks ++ [k])`.  By §16 reversal `K(ks ++ [k]) = K(k :: ks.reverse)`
and `K(ks) = K(ks.reverse)`, so this is `continuant_strict_mono` applied to the reversed run
(`ks.reverse` is again all-`≥ 2`). -/
theorem continuant_append_strict_mono {k : ℤ} {ks : List ℤ}
    (hk : (2 : ℤ) ≤ k) (h : ∀ j ∈ ks, (2 : ℤ) ≤ j) :
    Continuant ks < Continuant (ks ++ [k]) := by
  have hrev : ∀ j ∈ ks.reverse, (2 : ℤ) ≤ j :=
    fun j hj => h j (List.mem_reverse.mp hj)
  have hmono := continuant_strict_mono (ks := ks.reverse) hk hrev
  rw [continuant_reverse] at hmono
  have hrw : Continuant (ks ++ [k]) = Continuant (k :: ks.reverse) := by
    conv_lhs => rw [← continuant_reverse (ks ++ [k])]
    congr 1
    rw [List.reverse_append]
    rfl
  rw [hrw]; exact hmono

/-- **Strict growth wrapping a run on both ends.**  Bracketing a large-quotient run `ks` by
quotients `k, k' ≥ 2` on the left and right strictly increases the continuant past the
inner run: `Continuant ks < Continuant (k :: (ks ++ [k']))`.  Chains the right-append growth
`K(ks) < K(ks ++ [k'])` (`continuant_append_strict_mono`) with the prepend growth
`K(ks ++ [k']) < K(k :: (ks ++ [k']))` (§17 `continuant_strict_mono`, the bracketed run being
again all-`≥ 2`). -/
theorem continuant_lt_cons_append {k k' : ℤ} {ks : List ℤ}
    (hk : (2 : ℤ) ≤ k) (hk' : (2 : ℤ) ≤ k') (h : ∀ j ∈ ks, (2 : ℤ) ≤ j) :
    Continuant ks < Continuant (k :: (ks ++ [k'])) := by
  have hwrap : ∀ j ∈ ks ++ [k'], (2 : ℤ) ≤ j := by
    intro j hj
    rcases List.mem_append.mp hj with hjks | hj1
    · exact h j hjks
    · simpa using (List.mem_singleton.mp hj1) ▸ hk'
  calc Continuant ks
      < Continuant (ks ++ [k']) := continuant_append_strict_mono hk' h
    _ < Continuant (k :: (ks ++ [k'])) := continuant_strict_mono hk hwrap

/-- **Concrete two-ended growth.**  `K[3] = 3 < K[2,3,2] = 13`: bracketing the run `[3]` by
`2`s on both sides strictly inflates the continuant.  (`K[2,3,2] = 2·(3·2−1) − 2 = 2·5 + 3 = 13`.)
Discharged through the general two-ended bound. -/
theorem continuant_lt_cons_append_example :
    Continuant [3] < Continuant (2 :: ([3] ++ [2])) := by
  refine continuant_lt_cons_append (k := 2) (k' := 2) (ks := [3]) (by norm_num) (by norm_num) ?_
  intro j hj; fin_cases hj; norm_num

end Erdos1005OQ02

-- Axiom audit: foundational axioms only; no `Lean.ofReduceBool`, no `sorryAx`.
#print axioms Erdos1005OQ02.continuant_append_strict_mono
#print axioms Erdos1005OQ02.continuant_lt_cons_append
