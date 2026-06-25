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
import Mathlib.NumberTheory.Divisors
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

/-! ### (C2) The ordered representation count `= τ(n+1)`

The headline counting result of OQ-01. Working over `ℕ` (where `n ≥ 0` is
automatic and the truncated subtraction is avoided by the equivalent additive
form `a*b = n + a + b`), the ordered representations of `n` as `a*b - (a+b)`
with `a, b ≥ 2` are in bijection — via `(a,b) ↦ (a-1, b-1)` — with the ordered
factorizations `n + 1 = u*v`, i.e. `Nat.divisorsAntidiagonal (n+1)`. Hence their
number is `τ(n+1) = (n+1).divisors.card`, the divisor-counting function. -/

/-- The finite set of ordered representations of `n` as `a*b - (a+b)` with
`a, b ≥ 2`, encoded by the additive form `a*b = n + a + b`. The search box
`[2, n+2]²` is exactly the right one: `orderedReps_eq_image` below shows every
factorization of `n+1` lands inside it and conversely, so no representation is
missed. -/
def orderedReps (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 2 (n + 2) ×ˢ Finset.Icc 2 (n + 2)).filter
    (fun p => p.1 * p.2 = n + p.1 + p.2)

/-- The representation set is the image of `divisorsAntidiagonal (n+1)` under the
bijection `(u,v) ↦ (u+1, v+1)`. This both identifies the count and certifies the
`[2, n+2]²` box loses no representation. -/
theorem orderedReps_eq_image (n : ℕ) :
    orderedReps n
      = (Nat.divisorsAntidiagonal (n + 1)).image (fun q => (q.1 + 1, q.2 + 1)) := by
  ext ⟨a, b⟩
  simp only [orderedReps, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_image, Nat.mem_divisorsAntidiagonal, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨⟨⟨ha2, _⟩, hb2, _⟩, hEq⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    have hexp : (a' + 1) * (b' + 1) = a' * b' + a' + b' + 1 := by ring
    rw [hexp] at hEq
    exact ⟨a', b', ⟨by omega, by omega⟩, rfl, rfl⟩
  · rintro ⟨u, v, ⟨hprod, _⟩, rfl, rfl⟩
    have hmem : (u, v) ∈ Nat.divisorsAntidiagonal (n + 1) :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, by omega⟩
    have hu_div := Nat.fst_mem_divisors_of_mem_antidiagonal hmem
    have hv_div := Nat.snd_mem_divisors_of_mem_antidiagonal hmem
    have hu1 : 1 ≤ u := Nat.pos_of_mem_divisors hu_div
    have hv1 : 1 ≤ v := Nat.pos_of_mem_divisors hv_div
    have huU : u ≤ n + 1 := Nat.divisor_le hu_div
    have hvU : v ≤ n + 1 := Nat.divisor_le hv_div
    refine ⟨⟨⟨by omega, by omega⟩, by omega, by omega⟩, ?_⟩
    have hexp : (u + 1) * (v + 1) = u * v + u + v + 1 := by ring
    rw [hexp]; omega

/-- **(C2) Ordered representation count.** The number of ordered pairs `(a, b)`
with `a, b ≥ 2` and `a*b - (a+b) = n` equals `τ(n+1)`, the number of positive
divisors of `n+1`. Each divisor `u ∣ n+1` yields the representation
`(a, b) = (u + 1, (n+1)/u + 1)`. -/
theorem orderedReps_card (n : ℕ) :
    (orderedReps n).card = (n + 1).divisors.card := by
  have hinj : Function.Injective (fun q : ℕ × ℕ => (q.1 + 1, q.2 + 1)) := by
    intro x y h
    simp only [Prod.mk.injEq, add_left_inj] at h
    exact Prod.ext h.1 h.2
  rw [orderedReps_eq_image, Finset.card_image_of_injective _ hinj,
    ← Nat.map_div_right_divisors, Finset.card_map]

end Erdos493
