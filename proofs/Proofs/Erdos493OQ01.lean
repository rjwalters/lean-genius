/-
Erdős Problem #493 — OQ-01: Exact image and representation count of
the product-minus-sum map  (a, b) ↦ a * b - (a + b)  over a, b ≥ 2.

Parent: `Proofs.Erdos493Problem` proves only the ⊇ direction of the image,
i.e. `n ≥ 0 ⟹ HasProdMinusSum2 n` (witness a = 2, b = n + 2).

This file supplies the two backbone results of OQ-01:

* `prodMinusSum2_iff_nonneg` — the **exact image** `{a*b-(a+b) : a,b ≥ 2} = {n ≥ 0}`.
  The converse `HasProdMinusSum2 n ⟹ n ≥ 0` is new (the parent leaves it open
  and even flags the imprecision in its Part III).

* `hasProdMinusSum2_iff_factor` — the **representation ↔ factorization bijection**
  coming from the central identity `a*b-(a+b) = (a-1)(b-1) - 1`:
        n = a*b-(a+b),  a,b ≥ 2   ⟺   n+1 = u*v,  u,v ≥ 1     (u = a-1, v = b-1).
  Every counting statement (ordered count = τ(n+1), unordered = ⌈τ(n+1)/2⌉,
  uniqueness ⟺ n+1 prime or 1) is a corollary of this equivalence; see the
  knowledge base `research/problems/erdos-493-oq-01/` and the verified certificate
  `verify_prodminussum.py`.

Reference: https://erdosproblems.com/493
-/

import Proofs.Erdos493Problem
import Mathlib.Tactic

namespace Erdos493

/-- **(C1) Exact image.** The product-minus-sum representation `n = a*b-(a+b)`
with `a, b ≥ 2` exists **iff** `n ≥ 0`. The `←` direction is the parent theorem
`erdos_493_nonneg`; the `→` (converse) direction is new: from `a, b ≥ 2` we get
`a*b-(a+b) = (a-1)(b-1) - 1 ≥ 1·1 - 1 = 0`, so every negative integer is
unrepresentable. -/
theorem prodMinusSum2_iff_nonneg (n : ℤ) : HasProdMinusSum2 n ↔ n ≥ 0 := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    nlinarith [mul_nonneg (by linarith : (0 : ℤ) ≤ a - 2)
      (by linarith : (0 : ℤ) ≤ b - 2), ha, hb]
  · exact fun hn => erdos_493_nonneg n hn

/-- **Representation ↔ factorization bijection (central identity).**
`n = a*b-(a+b)` with `a, b ≥ 2` is equivalent to `n+1 = u*v` with `u, v ≥ 1`,
via the substitution `u = a-1, v = b-1`. This is the engine behind the
representation-counting results (ordered count `= τ(n+1)`, etc.). -/
theorem hasProdMinusSum2_iff_factor (n : ℤ) :
    HasProdMinusSum2 n ↔ ∃ u v : ℤ, 1 ≤ u ∧ 1 ≤ v ∧ u * v = n + 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a - 1, b - 1, by linarith, by linarith, by ring⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨u + 1, v + 1, by linarith, by linarith, by linear_combination -huv⟩

/-- Every negative integer is unrepresentable (immediate corollary of C1). -/
theorem not_hasProdMinusSum2_of_neg {n : ℤ} (hn : n < 0) : ¬ HasProdMinusSum2 n := by
  rw [prodMinusSum2_iff_nonneg]
  exact not_le.mpr hn

/-- **(C3) Diagonal (square) representation.** A representation with `a = b`
(equivalently `n = a*a - (a+a) = a² - 2a`) exists **iff** `n + 1` is a perfect
square. From the central identity `a² - 2a = (a-1)² - 1`, so `n + 1 = (a-1)²`.

This is the structural reason a *prime square* `n+1 = p²` has the extra unordered
representation `{p, p}` beyond `{1, p²}`: the perfect-square values of `n+1` are
exactly those whose factor list contains the diagonal `u = v = √(n+1)`. -/
theorem hasSquareRep_iff (n : ℤ) :
    (∃ a : ℤ, a ≥ 2 ∧ n = a * a - (a + a)) ↔ ∃ u : ℤ, 1 ≤ u ∧ n + 1 = u * u := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a - 1, by linarith, by ring⟩
  · rintro ⟨u, hu, huv⟩
    exact ⟨u + 1, by linarith, by linear_combination huv⟩

/-- **(C4) Nontrivial representation ↔ nontrivial factorization.** A representation
with *both* `a, b ≥ 3` exists **iff** `n + 1` factors as `u * v` with both
`u, v ≥ 2` (i.e. `n + 1` is composite). The "trivial" representations `(2, n+2)`
correspond exactly to the factorizations with a unit factor `u = 1`.

Hence the *unordered* representation of `n` is unique precisely when `n + 1` admits
no such nontrivial factorization — i.e. `n = 0` (`n+1 = 1`) or `n + 1` is prime. -/
theorem hasNontrivialRep_iff_factor (n : ℤ) :
    (∃ a b : ℤ, a ≥ 3 ∧ b ≥ 3 ∧ n = a * b - (a + b)) ↔
      ∃ u v : ℤ, 2 ≤ u ∧ 2 ≤ v ∧ u * v = n + 1 := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a - 1, b - 1, by linarith, by linarith, by ring⟩
  · rintro ⟨u, v, hu, hv, huv⟩
    exact ⟨u + 1, v + 1, by linarith, by linarith, by linear_combination -huv⟩

end Erdos493
