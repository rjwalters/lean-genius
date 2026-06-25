/-
# Erdős Problem #52, Open Question oq-02: Sum-Product over Commutative Rings

Parent gallery entry `erdos-52` lists, among its open questions:

  "Does a polynomial sum-product bound hold in all commutative rings, or is
   it special to ℤ? The answer over 𝔽_p is qualitatively yes (Bourgain–Katz–Tao)
   but the quantitative bounds ..."

This file answers the *first half* of that question — the naive generalization
to **all** commutative rings — with a clean, fully verified **NO**.

## The obstruction: subrings are closed under both operations

The entire force of the Erdős–Szemerédi sum-product phenomenon over ℤ comes from
the fact that no finite set of integers can be simultaneously closed under
addition and multiplication (the only additively-and-multiplicatively closed
subsets of ℤ are `{0}` and ℤ itself, the latter infinite).

In a general commutative ring this fails badly. A **subring** `S` is by
definition closed under `+`, `·`, contains `0` and `1`, so for `A = S`:

  * `A + A = A`  (additive subgroup), hence `|A + A| = |A|`,
  * `A · A = A`  (closed under `·`, and `a = a·1`), hence `|A · A| = |A|`,

so the sum-product quantity `max(|A+A|, |A·A|)` equals `|A|` exactly — **purely
linear**, no super-linear growth whatsoever.

Taking `A = univ` in the finite commutative rings `ZMod m` gives an explicit
family of *arbitrarily large* sets with linear sum-product, defeating any bound
of the form `max(|A+A|,|A·A|) ≥ C · |A|^{2-ε}` with `0 < ε < 1`.

## Contents (all 0-sorry, 0-axiom)

1. Ring-valued sumset / product set, generalizing the parent's ℤ definitions.
2. `sumProductMaxR_univ`: in any finite commutative ring, the full set realizes
   `sumProductMax = Fintype.card R` (linear).
3. `exists_linear_sum_product`: arbitrarily large rings/sets with linear
   sum-product (via `ZMod m`).
4. `not_SumProductBoundAllCommRings`: the verbatim ring-analog of Erdős #52 is
   **false** — refuted by the `ZMod m` family.

## Status: VERIFIED (answers parent open question oq-02, original)
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open Finset

/-
## Section I: Ring-valued sumset and product set

These generalize the parent file's `sumset`/`productset` from `Finset ℤ` to an
arbitrary commutative ring with decidable equality.  Over `R = ℤ` they agree
with the parent definitions.
-/

variable {R : Type*} [CommRing R] [DecidableEq R]

/-- The sumset `A + A`: all pairwise sums of elements of `A`. -/
def sumsetR (A : Finset R) : Finset R :=
  (A ×ˢ A).image (fun p => p.1 + p.2)

/-- The product set `A · A`: all pairwise products of elements of `A`. -/
def productsetR (A : Finset R) : Finset R :=
  (A ×ˢ A).image (fun p => p.1 * p.2)

/-- The sum-product quantity `max(|A+A|, |A·A|)`. -/
def sumProductMaxR (A : Finset R) : ℕ :=
  max (sumsetR A).card (productsetR A).card

/-- Membership in the sumset. -/
theorem mem_sumsetR {A : Finset R} {x : R} :
    x ∈ sumsetR A ↔ ∃ a ∈ A, ∃ b ∈ A, a + b = x := by
  simp [sumsetR, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ⟨ha, hb⟩, rfl⟩

/-- Membership in the product set. -/
theorem mem_productsetR {A : Finset R} {x : R} :
    x ∈ productsetR A ↔ ∃ a ∈ A, ∃ b ∈ A, a * b = x := by
  simp [productsetR, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩; exact ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩; exact ⟨a, b, ⟨ha, hb⟩, rfl⟩

/-
## Section II: The full set of a finite commutative ring is sum-product-linear

The universe `Finset.univ` of a finite commutative ring is closed under both
operations (it is the whole ring), and contains `0` and `1`, so both the sumset
and the product set equal `univ`.
-/

/-- In any commutative ring, the sumset of the whole ring is the whole ring:
`x = x + 0` realizes every `x`. -/
@[simp] theorem sumsetR_univ [Fintype R] :
    sumsetR (univ : Finset R) = univ := by
  ext x
  simp only [Finset.mem_univ, iff_true]
  rw [mem_sumsetR]
  exact ⟨x, mem_univ x, 0, mem_univ 0, by ring⟩

/-- In any commutative ring with `1`, the product set of the whole ring is the
whole ring: `x = x · 1` realizes every `x`. -/
@[simp] theorem productsetR_univ [Fintype R] :
    productsetR (univ : Finset R) = univ := by
  ext x
  simp only [Finset.mem_univ, iff_true]
  rw [mem_productsetR]
  exact ⟨x, mem_univ x, 1, mem_univ 1, by ring⟩

/-- **Key linearity result.** In any finite commutative ring, the full set
realizes a sum-product quantity equal to its own cardinality:
`max(|R+R|, |R·R|) = |R|`.  There is *no* super-linear growth. -/
theorem sumProductMaxR_univ [Fintype R] :
    sumProductMaxR (univ : Finset R) = Fintype.card R := by
  simp [sumProductMaxR, Finset.card_univ]

/-
## Section III: An explicit arbitrarily-large family — `ZMod m`

`ZMod m` is a finite commutative ring of cardinality `m`.  Its full set has
sum-product quantity exactly `m`, so we obtain finite sets of *every* size with
purely linear sum-product behaviour.
-/

/-- The full set of `ZMod m` has sum-product quantity exactly `m`. -/
theorem sumProductMaxR_zmod (m : ℕ) [NeZero m] :
    sumProductMaxR (univ : Finset (ZMod m)) = m := by
  rw [sumProductMaxR_univ, ZMod.card]

/-- The full set of `ZMod m` has cardinality exactly `m`. -/
theorem card_univ_zmod (m : ℕ) [NeZero m] :
    (univ : Finset (ZMod m)).card = m := by
  rw [Finset.card_univ, ZMod.card]

/-- **Arbitrarily large linear-sum-product sets.** For every target size `n`
there is a finite commutative ring and a subset `A` of size `n + 2` with
`sumProductMax A = |A|`.  (Sizes `≥ 2` matching Erdős #52's hypothesis, and
unbounded as `n → ∞`.) -/
theorem exists_linear_sum_product (n : ℕ) :
    ∃ (S : Type) (_ : CommRing S) (_ : Fintype S) (_ : DecidableEq S)
      (A : Finset S), A.card = n + 2 ∧ sumProductMaxR A = n + 2 := by
  haveI : NeZero (n + 2) := ⟨by omega⟩
  exact ⟨ZMod (n + 2), inferInstance, inferInstance, inferInstance,
    univ, card_univ_zmod (n + 2), sumProductMaxR_zmod (n + 2)⟩

/-
## Section IV: The ring-analog of Erdős #52 is false

We state the verbatim generalization of the parent conjecture `ErdosProblem52`
to *all* finite commutative rings, and prove it is **false**.
-/

/-- The naive generalization of Erdős Problem #52 to all (finite) commutative
rings: for every `ε > 0` there is a constant `C > 0` with
`max(|A+A|,|A·A|) ≥ C · |A|^{2-ε}` for every finite commutative ring `R` and
every `A ⊆ R` with `|A| ≥ 2`. -/
def SumProductBoundAllCommRings : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ C : ℝ, C > 0 ∧
      ∀ (R : Type) [CommRing R] [Fintype R] [DecidableEq R] (A : Finset R),
        A.card ≥ 2 → (sumProductMaxR A : ℝ) ≥ C * (A.card : ℝ) ^ (2 - ε)

/-- **Main theorem (oq-02).** The sum-product bound does *not* hold over all
commutative rings.  Concretely, taking `ε = 1/2` (so the demanded exponent is
`3/2`), the `ZMod m` family forces `C · m^{3/2} ≤ m` for all `m ≥ 2`, i.e.
`C · √m ≤ 1` for all `m`, which is impossible since `√m → ∞`. -/
theorem not_SumProductBoundAllCommRings : ¬ SumProductBoundAllCommRings := by
  intro h
  obtain ⟨C, hC, hbound⟩ := h (1 / 2) (by norm_num)
  -- The bound, applied to `univ ⊆ ZMod m`, gives `C · m^{3/2} ≤ m` for `m ≥ 2`.
  have key : ∀ m : ℕ, 2 ≤ m → C * (m : ℝ) ^ ((2 : ℝ) - 1 / 2) ≤ (m : ℝ) := by
    intro m hm
    haveI : NeZero m := ⟨by omega⟩
    have hcard : (univ : Finset (ZMod m)).card ≥ 2 := by
      rw [card_univ_zmod]; exact hm
    have hb := hbound (ZMod m) (univ) hcard
    rw [sumProductMaxR_zmod, card_univ_zmod] at hb
    exact hb
  -- Rewrite `m^{3/2}` as `m * √m`.
  have hpow : ∀ m : ℕ, 0 < m → (m : ℝ) ^ ((2 : ℝ) - 1 / 2) = (m : ℝ) * Real.sqrt m := by
    intro m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    rw [Real.sqrt_eq_rpow]
    rw [show (2 : ℝ) - 1 / 2 = 1 + 1 / 2 by ring]
    rw [Real.rpow_add hmpos, Real.rpow_one]
  -- Hence `C · √m ≤ 1` for all `m ≥ 2`.
  have key2 : ∀ m : ℕ, 2 ≤ m → C * Real.sqrt m ≤ 1 := by
    intro m hm
    have hmpos : 0 < m := by omega
    have hmposR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
    have hk := key m hm
    rw [hpow m hmpos] at hk
    -- `C * (m * √m) ≤ m`, divide by `m > 0`.
    have : C * Real.sqrt m * (m : ℝ) ≤ 1 * (m : ℝ) := by
      rw [one_mul]; nlinarith [hk]
    exact le_of_mul_le_mul_right this hmposR
  -- Pick `m` with `√m > 1/C`, i.e. `m > (1/C)^2`, contradicting `C·√m ≤ 1`.
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 / C) ^ 2)
  set m := max n 2 with hm_def
  have hm2 : 2 ≤ m := le_max_right n 2
  have hmn : (1 / C) ^ 2 < (m : ℝ) := by
    have : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast le_max_left n 2
    linarith
  have hmposR : (0 : ℝ) ≤ (m : ℝ) := by positivity
  -- `1/C < √m`.
  have hsqrt : 1 / C < Real.sqrt m := by
    have hnn : (0 : ℝ) ≤ 1 / C := by positivity
    have hsq : (1 / C) ^ 2 < (Real.sqrt m) ^ 2 := by
      rw [Real.sq_sqrt hmposR]; exact hmn
    exact lt_of_pow_lt_pow_left₀ 2 (Real.sqrt_nonneg _) hsq
  -- Then `C·√m > 1`, contradicting `key2`.
  have hlt : 1 < C * Real.sqrt m := by
    have := (div_lt_iff₀ hC).mp hsqrt
    linarith [this]
  exact absurd (key2 m hm2) (by linarith)
