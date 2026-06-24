import Mathlib
import Proofs.CatalanNumbersOQ01OQ01OQ02

/-
# Catalan-triangle row sums are Catalan numbers: `∑_{q=0}^{p} B(p,q) = catalan (p+1)`

The parent entry (`CatalanNumbersOQ01OQ01OQ02`) introduced the generalized ballot
number / Catalan-triangle entry

  `ballot p q = C(p + q, q) - C(p + q, p + 1)`,

together with its closed form, its diagonal value `ballot n n = catalan n`, and the
boundary/vanishing facts.  This file proves the **row-sum identity**

  `∑_{q = 0}^{p} ballot p q = catalan (p + 1)`,

the classical statement that the row sums of the Catalan triangle are the Catalan
numbers (e.g. row `3` of the triangle is `1, 3, 5, 5` and `1 + 3 + 5 + 5 = 14 =
catalan 4`).

Mathlib records the Catalan numbers and the hockey-stick identity
(`Nat.sum_Icc_choose`) but not this row-sum relation, nor the Catalan triangle
itself.  The proof here is **independent of the Catalan-triangle recurrence**:
it sums the two binomial pieces of `ballot p q` separately, evaluating each with
the hockey-stick (Zhu Shijie) identity, and then reconciles the two closed forms
with a single application of Pascal's rule.

## Strategy

Write `S = ∑_{q=0}^{p} ballot p q`.  Because `q ≤ p` throughout the range, every
subtraction defining `ballot p q` is genuine (`ballot_genuine`), so

  `S + ∑_{q=0}^{p} C(p+q, p+1) = ∑_{q=0}^{p} C(p+q, q)`.

The two right-hand sums are diagonal binomial sums.  Reindexing `m = p + q`
(`Finset.sum_Ico_eq_sum_range`) and applying the hockey-stick identity
`Nat.sum_Icc_choose` evaluates them in closed form:

* `sum_choose_diag` : `∑_{q=0}^{p} C(p+q, q) = C(2p+1, p+1)`;
* `sum_choose_upper`: `∑_{q=0}^{p} C(p+q, p+1) = C(2p+1, p+2)`.

Finally `catalan_succ_eq_choose_sub` shows
`catalan (p+1) + C(2p+1, p+2) = C(2p+1, p+1)` from `ballot_diag` and Pascal's
rule, after which `omega` closes the row sum.

Everything is over `ℕ`, fully machine-checked, `0`-axiom.
-/

open Finset

namespace CatalanRowSum

/-- **Diagonal binomial sum.**  `∑_{q=0}^{p} C(p+q, q) = C(2p+1, p+1)`.

Using the symmetry `C(p+q, q) = C(p+q, p)`, the sum is `∑_{m=p}^{2p} C(m, p)`,
which the hockey-stick identity `Nat.sum_Icc_choose` evaluates to `C(2p+1, p+1)`. -/
theorem sum_choose_diag (p : ℕ) :
    ∑ q ∈ range (p + 1), (p + q).choose q = (2 * p + 1).choose (p + 1) := by
  -- Replace each term `C(p+q, q)` by `C(p+q, p)` via symmetry.
  have hsymm : ∀ q ∈ range (p + 1), (p + q).choose q = (p + q).choose p := by
    intro q _; exact (Nat.choose_symm_add).symm
  rw [Finset.sum_congr rfl hsymm]
  -- Reindex `m = p + q` to turn `range (p+1)` into `Icc p (2p)`.
  have hrange : ∑ q ∈ range (p + 1), (p + q).choose p
      = ∑ m ∈ Ico p (2 * p + 1), m.choose p := by
    rw [Finset.sum_Ico_eq_sum_range, show 2 * p + 1 - p = p + 1 from by omega]
  rw [hrange]
  -- `Ico p (2p+1) = Icc p (2p)`, then hockey-stick.
  rw [Nat.Ico_succ_right, Nat.sum_Icc_choose]

/-- **Upper-index binomial sum.**  `∑_{q=0}^{p} C(p+q, p+1) = C(2p+1, p+2)`.

As `m = p + q` ranges over `Icc p (2p)`, the summand `C(m, p+1)` vanishes at the
lower endpoint `m = p` (since `p < p+1`), so the sum equals `∑_{m=p+1}^{2p} C(m, p+1)`,
which the hockey-stick identity evaluates to `C(2p+1, p+2)`. -/
theorem sum_choose_upper (p : ℕ) :
    ∑ q ∈ range (p + 1), (p + q).choose (p + 1) = (2 * p + 1).choose (p + 2) := by
  -- Peel off the `q = 0` term, which vanishes (`p < p + 1`).
  rw [Finset.sum_range_succ',
    Nat.choose_eq_zero_of_lt (show p + 0 < p + 1 by omega), add_zero]
  -- `p + (q + 1) = (p + 1) + q`, so the remaining sum starts the index at `p + 1`.
  have hcongr : ∀ q ∈ range p, (p + (q + 1)).choose (p + 1) = ((p + 1) + q).choose (p + 1) := by
    intro q _; congr 1; omega
  rw [Finset.sum_congr rfl hcongr]
  -- Reindex `m = (p + 1) + q` into `Icc (p+1) (2p)`, then hockey-stick.
  have hrange : ∑ q ∈ range p, ((p + 1) + q).choose (p + 1)
      = ∑ m ∈ Ico (p + 1) (p + 1 + p), m.choose (p + 1) := by
    rw [Finset.sum_Ico_eq_sum_range, show p + 1 + p - (p + 1) = p from by omega]
  rw [hrange, show p + 1 + p = (2 * p) + 1 from by ring, Nat.Ico_succ_right,
    Nat.sum_Icc_choose]

/-- **Catalan via Pascal.**  `catalan (p+1) + C(2p+1, p+2) = C(2p+1, p+1)`.

From `ballot_diag (p+1)`, `catalan (p+1) = C(2p+2, p+1) - C(2p+2, p+2)`.  Expanding
both `C(2p+2, ·)` with Pascal's rule and using the symmetry `C(2p+1, p) = C(2p+1, p+1)`
collapses the right side to `C(2p+1, p+1) - C(2p+1, p+2)`. -/
theorem catalan_succ_eq_choose_sub (p : ℕ) :
    catalan (p + 1) + (2 * p + 1).choose (p + 2) = (2 * p + 1).choose (p + 1) := by
  -- Genuine additive partition at the diagonal `(p+1, p+1)`:
  -- `catalan (p+1) + C(2p+2, p+2) = C(2p+2, p+1)`.
  have e1 : (p + 1) + (p + 1) = 2 * p + 2 := by ring
  have e2 : (p + 1) + 1 = p + 2 := by ring
  have hg := ballot_genuine (p := p + 1) (q := p + 1) (le_refl _)
  rw [e1, e2] at hg
  -- hg : (2p+2).choose (p+2) ≤ (2p+2).choose (p+1)
  have hd := ballot_diag (p + 1)
  rw [ballot, e1, e2] at hd
  -- hd : (2p+2).choose (p+1) - (2p+2).choose (p+2) = catalan (p+1)
  -- Pascal expansions of the `2p+2 = (2p+1)+1` coefficients.
  have hp1 : (2 * p + 2).choose (p + 1)
      = (2 * p + 1).choose p + (2 * p + 1).choose (p + 1) := by
    rw [show 2 * p + 2 = (2 * p + 1) + 1 from by ring, Nat.choose_succ_succ (2 * p + 1) p]
  have hp2 : (2 * p + 2).choose (p + 2)
      = (2 * p + 1).choose (p + 1) + (2 * p + 1).choose (p + 2) := by
    rw [show 2 * p + 2 = (2 * p + 1) + 1 from by ring, show p + 2 = (p + 1) + 1 from by ring,
      Nat.choose_succ_succ (2 * p + 1) (p + 1)]
  -- Symmetry `C(2p+1, p) = C(2p+1, p+1)`.
  have hsym : (2 * p + 1).choose p = (2 * p + 1).choose (p + 1) := by
    have h := Nat.choose_symm (n := 2 * p + 1) (k := p) (by omega)
    rw [show 2 * p + 1 - p = p + 1 from by omega] at h
    exact h.symm
  omega

/-- **Row sum of the Catalan triangle.**  `∑_{q=0}^{p} ballot p q = catalan (p+1)`.

The row sums of the Catalan triangle are the Catalan numbers.  Proof: the genuine
additive partition `ballot p q + C(p+q, p+1) = C(p+q, q)` (valid since `q ≤ p`)
sums to `S + C(2p+1, p+2) = C(2p+1, p+1)`; comparing with
`catalan (p+1) + C(2p+1, p+2) = C(2p+1, p+1)` gives `S = catalan (p+1)`. -/
theorem ballot_row_sum (p : ℕ) :
    ∑ q ∈ range (p + 1), ballot p q = catalan (p + 1) := by
  -- Termwise genuine partition: `ballot p q + C(p+q, p+1) = C(p+q, q)`.
  have hpart : ∀ q ∈ range (p + 1),
      ballot p q + (p + q).choose (p + 1) = (p + q).choose q := by
    intro q hq
    have hqp : q ≤ p := by
      rw [Finset.mem_range] at hq; omega
    have hg := ballot_genuine hqp
    rw [ballot]
    omega
  have hsum : (∑ q ∈ range (p + 1), ballot p q) + ∑ q ∈ range (p + 1), (p + q).choose (p + 1)
      = ∑ q ∈ range (p + 1), (p + q).choose q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl hpart
  rw [sum_choose_upper, sum_choose_diag] at hsum
  -- `S + C(2p+1, p+2) = C(2p+1, p+1)` and `catalan (p+1) + C(2p+1, p+2) = C(2p+1, p+1)`.
  have hcat := catalan_succ_eq_choose_sub p
  omega

/-- Sanity check: row `3` of the Catalan triangle is `1, 3, 5, 5`, summing to
`14` (`= catalan 4`). -/
example : ∑ q ∈ range 4, ballot 3 q = 14 := by decide

/-- Sanity check: row `4` sums to `42` (`= catalan 5`). -/
example : ∑ q ∈ range 5, ballot 4 q = 42 := by decide

end CatalanRowSum
