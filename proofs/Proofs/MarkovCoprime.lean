/-
# Pairwise Coprimality of Markov Triples

The Markov equation `x² + y² + z² = 3xyz` (studied in `Proofs.MarkovEquation`,
where every positive solution is shown to be reachable from the root `(1,1,1)`
by *Vieta jumps* and coordinate transpositions) has a striking arithmetic
rigidity that the geometric classification does not directly expose: **the three
coordinates of any positive Markov triple are pairwise coprime.**

This file proves that fact and draws its standard consequences. The proof is a
clean *invariance* argument rather than a fresh descent:

* pairwise coprimality holds at the root `(1,1,1)` (trivially, `gcd 1 1 = 1`);
* every generating move — a transposition or a Vieta jump `z ↦ 3xy − z` —
  **preserves** pairwise coprimality, and each move is its own inverse, so the
  property is preserved *along the reachability relation in both directions*.

Since `markov_classification` (from `Proofs.MarkovEquation`) shows every positive
Markov triple is reachable from `(1,1,1)`, pairwise coprimality propagates to the
whole Markov tree.

The crucial algebraic step is that a Vieta jump shifts a coordinate by a multiple
of the *other two*:
`3xy − z = (−z) + x·(3y) = (−z) + y·(3x)`,
so `gcd(x, 3xy−z) = gcd(x, z)` and `gcd(y, 3xy−z) = gcd(y, z)` — coprimality of a
coordinate with its Vieta partner is unchanged.

## Main results

* `markov_coprime` — every positive Markov triple is pairwise coprime
  (`IsCoprime` over `ℤ`).
* `markov_gcd_eq_one` — the same stated with `Int.gcd · · = 1`.
* `markov_at_most_one_even` — no two coordinates of a Markov triple share the
  factor `2`; equivalently, **at most one Markov number in a triple is even**.

All results are elementary and fully machine-checked (0 axioms, 0 sorries).
-/
import Mathlib
import Proofs.MarkovEquation

namespace MarkovCoprime

open MarkovEquation

/-- A triple of integers is *pairwise coprime* when each of the three pairs is
coprime (`IsCoprime`, i.e. an `ℤ`-linear combination equals `1`). We phrase it on
the product type `ℤ × ℤ × ℤ` so it lines up with the `Step`/`Reachable`
machinery of `Proofs.MarkovEquation`. -/
def Coprime3 (p : ℤ × ℤ × ℤ) : Prop :=
  IsCoprime p.1 p.2.1 ∧ IsCoprime p.2.1 p.2.2 ∧ IsCoprime p.1 p.2.2

/-! ## The Vieta jump preserves coprimality with the jumped coordinate -/

/-- Coprimality of the first coordinate with the third is invariant under the
Vieta jump `z ↦ 3xy − z`, because `3xy − z` differs from `−z` by the multiple
`x·(3y)` of `x`. -/
theorem coprime_fst_vieta (x y z : ℤ) :
    IsCoprime x (3 * x * y - z) ↔ IsCoprime x z := by
  rw [show 3 * x * y - z = (-z) + x * (3 * y) from by ring,
    IsCoprime.add_mul_left_right_iff, IsCoprime.neg_right_iff]

/-- Coprimality of the second coordinate with the third is invariant under the
Vieta jump, because `3xy − z` differs from `−z` by the multiple `y·(3x)` of `y`. -/
theorem coprime_snd_vieta (x y z : ℤ) :
    IsCoprime y (3 * x * y - z) ↔ IsCoprime y z := by
  rw [show 3 * x * y - z = (-z) + y * (3 * x) from by ring,
    IsCoprime.add_mul_left_right_iff, IsCoprime.neg_right_iff]

/-! ## Coprimality is an invariant of the Markov tree -/

/-- The root `(1,1,1)` is pairwise coprime. -/
theorem coprime3_one : Coprime3 (1, 1, 1) :=
  ⟨isCoprime_one_left, isCoprime_one_left, isCoprime_one_left⟩

/-- **Each move is coprimality-preserving (both directions).** If a single move
`Step p q` connects `p` and `q`, then `q` is pairwise coprime iff `p` is. Because
every move (transposition or Vieta jump) is its own inverse, the equivalence is
symmetric; we record the direction `Coprime3 q → Coprime3 p` needed to propagate
the property *back* from the root along a reachability path. -/
theorem coprime3_of_step {p q : ℤ × ℤ × ℤ} (hs : Step p q) (hq : Coprime3 q) :
    Coprime3 p := by
  obtain ⟨h12, h23, h13⟩ := hq
  cases hs with
  | swap12 x y z =>
    -- q = (y, x, z): reorder the three coprimalities
    exact ⟨h12.symm, h13, h23⟩
  | swap23 x y z =>
    -- q = (x, z, y): reorder the three coprimalities
    exact ⟨h13, h23.symm, h12⟩
  | vieta x y z =>
    -- q = (x, y, 3xy − z): undo the Vieta jump on the last coordinate
    exact ⟨h12, (coprime_snd_vieta x y z).1 h23, (coprime_fst_vieta x y z).1 h13⟩

/-- **Pairwise coprimality of Markov triples (triple form).** Every positive
solution of `x² + y² + z² = 3xyz` is pairwise coprime. The proof inducts on the
reachability path to the root `(1,1,1)` produced by `markov_classification`,
pushing coprimality back one move at a time via `coprime3_of_step`. -/
theorem coprime3_of_isMarkov {x y z : ℤ} (h : IsMarkov x y z) :
    Coprime3 (x, y, z) := by
  have hr : Reachable (x, y, z) (1, 1, 1) := markov_classification h
  -- Generalize the start triple so the induction index is a genuine variable.
  suffices hgen : ∀ p : ℤ × ℤ × ℤ, Reachable p (1, 1, 1) → Coprime3 p from hgen _ hr
  intro p hp
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => exact coprime3_one
  | head hstep _ ih => exact coprime3_of_step hstep ih

/-! ## Headline statements and consequences -/

/-- **Pairwise coprimality of Markov triples.** In any positive Markov triple the
three pairs `(x,y)`, `(y,z)`, `(x,z)` are each coprime over `ℤ`. -/
theorem markov_coprime {x y z : ℤ} (h : IsMarkov x y z) :
    IsCoprime x y ∧ IsCoprime y z ∧ IsCoprime x z :=
  coprime3_of_isMarkov h

/-- The first two coordinates of a Markov triple are coprime. -/
theorem markov_coprime_12 {x y z : ℤ} (h : IsMarkov x y z) : IsCoprime x y :=
  (markov_coprime h).1

/-- The last two coordinates of a Markov triple are coprime. -/
theorem markov_coprime_23 {x y z : ℤ} (h : IsMarkov x y z) : IsCoprime y z :=
  (markov_coprime h).2.1

/-- The outer two coordinates of a Markov triple are coprime. -/
theorem markov_coprime_13 {x y z : ℤ} (h : IsMarkov x y z) : IsCoprime x z :=
  (markov_coprime h).2.2

/-- **`gcd` form.** All three pairwise greatest common divisors of a Markov
triple equal `1`. -/
theorem markov_gcd_eq_one {x y z : ℤ} (h : IsMarkov x y z) :
    Int.gcd x y = 1 ∧ Int.gcd y z = 1 ∧ Int.gcd x z = 1 := by
  obtain ⟨h12, h23, h13⟩ := markov_coprime h
  exact ⟨Int.isCoprime_iff_gcd_eq_one.1 h12,
    Int.isCoprime_iff_gcd_eq_one.1 h23,
    Int.isCoprime_iff_gcd_eq_one.1 h13⟩

/-- A coprime pair of integers cannot share the (non-unit) factor `2`. -/
theorem not_two_dvd_both {a b : ℤ} (h : IsCoprime a b) : ¬ (2 ∣ a ∧ 2 ∣ b) := by
  rintro ⟨ha, hb⟩
  have hu : IsUnit (2 : ℤ) := h.isUnit_of_dvd' ha hb
  rcases Int.isUnit_iff.1 hu with h1 | h1 <;> norm_num at h1

/-- **At most one Markov number in a triple is even.** No two coordinates of a
Markov triple are simultaneously even — equivalently they cannot share the factor
`2`. Stated for all three pairs. -/
theorem markov_at_most_one_even {x y z : ℤ} (h : IsMarkov x y z) :
    ¬ (2 ∣ x ∧ 2 ∣ y) ∧ ¬ (2 ∣ y ∧ 2 ∣ z) ∧ ¬ (2 ∣ x ∧ 2 ∣ z) := by
  obtain ⟨h12, h23, h13⟩ := markov_coprime h
  exact ⟨not_two_dvd_both h12, not_two_dvd_both h23, not_two_dvd_both h13⟩

/-- The even-coordinate count of a Markov triple is at most one (`Even` phrasing
of `markov_at_most_one_even` for the first pair, the typical statement
"two Markov numbers cannot both be even"). -/
theorem markov_not_both_even {x y z : ℤ} (h : IsMarkov x y z) :
    ¬ (Even x ∧ Even y) := by
  rintro ⟨hx, hy⟩
  exact (markov_at_most_one_even h).1 ⟨hx.two_dvd, hy.two_dvd⟩

/-! ## Sanity checks on the small Markov triples -/

example : IsCoprime (2 : ℤ) 5 := markov_coprime_12 markov_two_five_twentynine
example : Int.gcd (2 : ℤ) 29 = 1 := (markov_gcd_eq_one markov_two_five_twentynine).2.2
example : ¬ ((2 : ℤ) ∣ 1 ∧ (2 : ℤ) ∣ 1) := (markov_at_most_one_even markov_one).1

end MarkovCoprime
