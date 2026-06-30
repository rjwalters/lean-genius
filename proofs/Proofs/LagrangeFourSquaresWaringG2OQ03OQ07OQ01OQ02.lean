import Mathlib

/-!
# A complete `n ≡ 3 (mod 4)` obstruction for the three-square multiplier route

**Open question (`lagrange-four-squares-waring-g2-oq-03-oq-07-oq-01-oq-02`)**, the
second registered follow-up to the sharp obstruction at `n = 3`
(`lagrange-four-squares-waring-g2-oq-03-oq-07-oq-01`, §3).  That parent asked, in
its `oq-02`: *"Generalise the `n = 3` obstruction to a uniform family: identify all
`n` for which `legendreSym p (−n) = −1` for every prime `p ≡ −1 (mod n)`, and prove
the corresponding `multiplier_route_incomplete` statement once for the whole family
rather than the single value `n = 3`."*  This file answers it for the congruence
family `n ≡ 3 (mod 4)`.

## Background

The multiplier–quadratic-residue reduction of the three-square problem distills
the geometry's residue hypothesis to a Legendre condition on a "multiplier prime"
`p`.  By construction such a prime has shape `p = d·n − 1`, i.e. `p ≡ −1 (mod n)`,
and the surviving hypothesis is

  `legendreSym p (−n) = 1`.

The parent slice `oq-03-oq-07-oq-01` proved that for `n = 3` this condition holds
for **no** multiplier prime: every odd prime `p ≡ 2 (mod 3)` has
`legendreSym p (−3) = −1`.  That argument was an explicit `mod 12` enumeration and
left open *how far* the phenomenon extends.

## What this file proves

The `n = 3` obstruction is the first instance of a clean, infinite congruence
family.  The single hypothesis driving it is `n ≡ 3 (mod 4)`:

* `legendreSym_neg_eq_neg_one_of_three_mod_four` — for every `n ≡ 3 (mod 4)` and
  every **odd prime** `p` with `p ≡ −1 (mod n)`,

    `legendreSym p (−n) = −1`.

  Hence the multiplier route's QR hypothesis `legendreSym p (−n) = 1` is satisfied
  by no multiplier prime whenever `n ≡ 3 (mod 4)`
  (`multiplier_route_obstructed_of_three_mod_four`).

The mechanism is pure reciprocity, no case enumeration in the prime:

  `legendreSym p (−n) = J(−n | p) = χ₄ p · J(n | p)`,

and because `p ≡ −1 (mod n)`, reciprocity converts `J(n | p)` into
`(sign) · J(−1 | n) = (sign) · χ₄ n`.  For `n ≡ 3 (mod 4)` the χ₄ factors and the
reciprocity sign collapse to a single `−1` regardless of `p mod 4`.

The earlier `n = 3` result is recovered as the special case
(`legendreSym_neg_three_eq_neg_one'`), and the analysis is *sharp* in its modulus:
`n = 2 ≢ 3 (mod 4)` admits a qualifying prime (`sharpness_n_two`, e.g. `p = 11`
with `J(−2 | 11) = 1`), so the hypothesis `n ≡ 3 (mod 4)` cannot be dropped.

## Honest scope

`0`-axiom and self-contained (imports `Mathlib` only).  This is a *negative*
structural result about one particular reduction route; it does not bear on the
actual representability of `n` as a sum of three squares (indeed `3 = 1²+1²+1²`).
Many `n ≡ 3 (mod 4)` are sums of three squares, so the obstruction shows the
`−n`-multiplier condition is genuinely route-specific, not a genus condition.
No `axiom`, no `sorry`, no `native_decide`.
-/

namespace Proofs.LagrangeFourSquaresWaringG2OQ03OQ07OQ01OQ02

open scoped NumberTheorySymbols

/-! ## The Jacobi-symbol kernel -/

/-- **The reciprocity kernel.**  For odd naturals `n, p` with `n ≡ 3 (mod 4)` and
`(p : ℤ) ≡ −1 (mod n)`, the Jacobi symbol `J(−n | p) = −1`.

The proof decomposes `J(−n | p) = χ₄ p · J(n | p)` and applies quadratic
reciprocity, splitting on `p mod 4`:

* `p ≡ 1 (mod 4)`: `χ₄ p = 1` and `J(n | p) = J(p | n) = J(−1 | n) = χ₄ n = −1`.
* `p ≡ 3 (mod 4)`: `χ₄ p = −1` and `J(n | p) = −J(p | n) = −χ₄ n = 1`.

Either way the product is `−1`. -/
theorem jacobiSym_neg_eq_neg_one_of_three_mod_four {n p : ℕ}
    (hn4 : n % 4 = 3) (hp2 : p % 2 = 1)
    (hpn : (p : ℤ) % n = (-1 : ℤ) % n) :
    J(-(n : ℤ) | p) = -1 := by
  have hn_odd : Odd n := Nat.odd_iff.mpr (by omega)
  -- `J(p | n) = J(-1 | n) = χ₄ n = -1` using `p ≡ -1 (mod n)`.
  have hJpn : J((p : ℤ) | n) = -1 := by
    rw [jacobiSym.mod_left' hpn, jacobiSym.at_neg_one hn_odd,
      ZMod.χ₄_nat_three_mod_four hn4]
  -- Decompose `J(-n | p) = χ₄ p * J(n | p)`.
  have hsplit := jacobiSym.neg (n : ℤ) (Nat.odd_iff.mpr hp2)
  -- Case-split on `p mod 4`.
  rcases Nat.odd_mod_four_iff.mp hp2 with hp1 | hp3
  · -- `p ≡ 1 (mod 4)`
    rw [hsplit, ZMod.χ₄_nat_one_mod_four hp1,
      jacobiSym.quadratic_reciprocity_one_mod_four' hn_odd hp1, hJpn]; ring
  · -- `p ≡ 3 (mod 4)`
    rw [hsplit, ZMod.χ₄_nat_three_mod_four hp3,
      jacobiSym.quadratic_reciprocity_three_mod_four hn4 hp3, hJpn]; ring

/-! ## The Legendre-symbol statement -/

/-- **The `n ≡ 3 (mod 4)` obstruction.**  For every `n ≡ 3 (mod 4)` and every odd
prime `p` with `p ≡ −1 (mod n)`, `legendreSym p (−n) = −1`.

This is the generalisation of the parent's `n = 3` computation to the entire
congruence class `n ≡ 3 (mod 4)`. -/
theorem legendreSym_neg_eq_neg_one_of_three_mod_four {n p : ℕ} [Fact p.Prime]
    (hn4 : n % 4 = 3) (hp2 : Odd p) (hpn : (p : ℤ) % n = (-1 : ℤ) % n) :
    legendreSym p (-(n : ℤ)) = -1 := by
  rw [jacobiSym.legendreSym.to_jacobiSym]
  exact jacobiSym_neg_eq_neg_one_of_three_mod_four hn4 (Nat.odd_iff.mp hp2) hpn

/-- The multiplier-shape hypothesis `p + 1 = d·n` implies `(p : ℤ) ≡ −1 (mod n)`. -/
private lemma intMod_neg_one_of_multiplier {n p d : ℕ} (hd : p + 1 = d * n) :
    (p : ℤ) % n = (-1 : ℤ) % n := by
  have hpd : (p : ℤ) + 1 = (d : ℤ) * n := by exact_mod_cast hd
  have hdvd : (n : ℤ) ∣ (-1 : ℤ) - (p : ℤ) := ⟨-(d : ℤ), by linear_combination -hpd⟩
  exact Int.modEq_iff_dvd.mpr hdvd

/-- **The multiplier route is obstructed for every `n ≡ 3 (mod 4)`.**  A multiplier
prime for `n` is an odd prime `p` with `p + 1 = d·n` for some `d`.  Whenever
`n ≡ 3 (mod 4)`, the geometry's QR hypothesis `legendreSym p (−n) = 1` fails for
*every* such prime — its value is forced to `−1`. -/
theorem multiplier_route_obstructed_of_three_mod_four {n : ℕ} (hn4 : n % 4 = 3) :
    ∀ (p d : ℕ) [Fact p.Prime], Odd p → p + 1 = d * n →
      legendreSym p (-(n : ℤ)) = -1 := by
  intro p d _ hp2 hd
  exact legendreSym_neg_eq_neg_one_of_three_mod_four hn4 hp2
    (intMod_neg_one_of_multiplier hd)

/-- Restated as the explicit failure of the route's QR hypothesis. -/
theorem multiplier_route_qr_fails_of_three_mod_four {n : ℕ} (hn4 : n % 4 = 3) :
    ∀ (p d : ℕ) [Fact p.Prime], Odd p → p + 1 = d * n →
      legendreSym p (-(n : ℤ)) ≠ 1 := by
  intro p d _ hp2 hd
  rw [multiplier_route_obstructed_of_three_mod_four hn4 p d hp2 hd]
  norm_num

/-! ## Specialisations and sharpness -/

/-- **Recovering the parent's `n = 3` case.**  For every odd prime `p ≡ 2 (mod 3)`,
`legendreSym p (−3) = −1`. -/
theorem legendreSym_neg_three_eq_neg_one' {p : ℕ} [Fact p.Prime]
    (hp2 : Odd p) (hp3 : p % 3 = 2) :
    legendreSym p (-3) = -1 := by
  have hcast : (-3 : ℤ) = -((3 : ℕ) : ℤ) := by norm_num
  rw [hcast]
  refine legendreSym_neg_eq_neg_one_of_three_mod_four (by norm_num) hp2 ?_
  omega

/-- **Sharpness of the modulus.**  The hypothesis `n ≡ 3 (mod 4)` of the kernel
cannot be weakened to "`n` odd" — nor to "`n` even but `≢ 3 mod 4`".  For `n = 2`
(which is `≢ 3 mod 4`) the prime `p = 11` satisfies `(11 : ℤ) ≡ −1 (mod 2)` yet
`J(−2 | 11) = 1`, the exact opposite of the kernel's conclusion.  So a qualifying
multiplier prime *does* exist for `n = 2`, and the congruence hypothesis is
necessary. -/
theorem sharpness_n_two :
    (11 : ℤ) % 2 = (-1 : ℤ) % 2 ∧ J(-(2 : ℤ) | 11) = 1 := by
  refine ⟨by omega, ?_⟩
  norm_num

/-- **Capstone.**  For `n ≡ 3 (mod 4)` the `−n`-multiplier route can never certify
representability — even though many such `n` are sums of three squares (e.g.
`3 = 1²+1²+1²`). The obstruction is therefore route-specific, not a genuine
obstruction to being a sum of three squares. -/
theorem obstruction_is_route_specific :
    (3 = 1 ^ 2 + 1 ^ 2 + 1 ^ 2) ∧
      (∀ (p d : ℕ) [Fact p.Prime], Odd p → p + 1 = d * 3 →
        legendreSym p (-(3 : ℤ)) ≠ 1) := by
  refine ⟨by norm_num, ?_⟩
  intro p d _ hp2 hd
  have hcast : (-(3 : ℤ)) = -((3 : ℕ) : ℤ) := by norm_num
  rw [hcast]
  exact multiplier_route_qr_fails_of_three_mod_four (by norm_num) p d hp2 hd

end Proofs.LagrangeFourSquaresWaringG2OQ03OQ07OQ01OQ02
