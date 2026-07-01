/-
  Angle Trisection OQ02-OQ03-OQ03:
  The 17-gon via Gauss: the arithmetic backbone of the 1796 construction.

  Parent (OQ02-OQ03, `heptadecagon_constructible`) proves *abstractly* that the
  regular 17-gon is constructible because φ(17) = 16 is a power of two.  That
  statement is silent about *how* Gauss actually did it.  This file formalizes the
  concrete combinatorial data underlying Gauss's construction — the piece a reader
  of "the 17-gon is constructible" still wants to see:

    1. `3` is a primitive root modulo 17: its powers cycle through all sixteen
       nonzero residues.  This is the ordering Gauss used to label the vertices.
    2. That ordering, listed explicitly:
         [1, 3, 9, 10, 13, 5, 15, 11, 16, 14, 8, 7, 4, 12, 2, 6].
    3. The two eight-term **Gaussian periods**: the quadratic residues (even powers
       of 3) and the non-residues (odd powers), which partition the vertices and
       are exactly the squares / non-squares mod 17.
    4. The descending **period tower** of the cyclic group (ℤ/17ℤ)ˣ:
         ⟨3⟩ ⊃ ⟨9⟩ ⊃ ⟨13⟩ ⊃ ⟨16⟩ ⊃ ⟨1⟩,   orders 16 ⊃ 8 ⊃ 4 ⊃ 2 ⊃ 1,
       each of index 2 in the previous.  This chain of index-2 subgroups is precisely
       the Galois-theoretic backbone: by the fixed-field correspondence it mirrors a
       tower ℚ ⊂ K₁ ⊂ K₂ ⊂ K₃ ⊂ K₄ = ℚ(ζ₁₇) of four quadratic extensions.  The four
       square roots those steps introduce (starting with √17) are what Gauss's nested
       radicals express, and what makes the 17-gon straightedge-and-compass
       constructible.

  Everything here is a finite, decidable statement about (ℤ/17ℤ)ˣ, so the file is
  fully machine-checked: 0 sorries, 0 axioms.

  Mathematically distinct from the family: no sibling formalizes the primitive-root
  ordering, the Gaussian-period partition, or the explicit index-2 subgroup tower
  for n = 17 — this is the number-theoretic content specific to Gauss's 17-gon,
  not the general Gauss–Wantzel degree argument (that is the parent's job).
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.QuotientGroup

open Subgroup

namespace AngleTrisectionOQ02OQ03OQ03

/-!
## Section I: 17 is a Fermat prime and φ(17) = 16 = 2⁴

The Gauss–Wantzel criterion for a prime p is: the regular p-gon is constructible iff
p is a Fermat prime, i.e. p = 2^(2^k) + 1.  For 17 = 2^(2²) + 1 we have φ(17) = 16.
-/

theorem seventeen_prime : Nat.Prime 17 := by decide

/-- 17 = 2^(2^2) + 1 is a Fermat prime (k = 2). -/
theorem seventeen_fermat : (17 : ℕ) = 2 ^ (2 ^ 2) + 1 := by norm_num

/-- φ(17) = 16 = 2⁴: the degree of the full cyclotomic field ℚ(ζ₁₇) over ℚ. -/
theorem totient_17 : Nat.totient 17 = 16 := by decide

theorem totient_17_pow2 : Nat.totient 17 = 2 ^ 4 := by decide

/-!
## Section II: `3` is a primitive root modulo 17

The multiplicative group (ℤ/17ℤ)ˣ is cyclic of order 16, and `3` is a generator:
its multiplicative order is exactly 16.  Gauss used the powers of 3 to label the
seventeen vertices of the polygon.
-/

/-- 3¹⁶ ≡ 1 (mod 17): the order of 3 divides 16 (Fermat's little theorem for p = 17). -/
theorem three_pow_16 : (3 : ZMod 17) ^ 16 = 1 := by decide

/-- 3⁸ ≡ 16 ≡ -1 (mod 17): 3 is *not* a quadratic residue, so its order is not 8. -/
theorem three_pow_8 : (3 : ZMod 17) ^ 8 = 16 := by decide

/-- **3 is a primitive root mod 17**: `orderOf 3 = 16`.

    Proof: the order divides 16 (by `three_pow_16`), and the only prime factor of 16
    is 2; since `3^(16/2) = 3^8 = -1 ≠ 1`, the order is the full 16. -/
theorem three_orderOf : orderOf (3 : ZMod 17) = 16 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) three_pow_16
  intro p hp hpd
  have hp2 : p = 2 := by
    have h16 : (16 : ℕ) = 2 ^ 4 := by norm_num
    rw [h16] at hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
  subst hp2
  decide

/-!
## Section III: Gauss's vertex ordering

Listing the powers `3^0, 3^1, …, 3^15` (mod 17) gives Gauss's cyclic ordering of the
sixteen nonzero residues — the order in which he arranged the vertices so that the
Gaussian periods appear as contiguous blocks.
-/

/-- The explicit Gauss ordering: powers of the primitive root 3, in sequence.
    `[1, 3, 9, 10, 13, 5, 15, 11, 16, 14, 8, 7, 4, 12, 2, 6]`. -/
theorem gauss_ordering :
    (List.range 16).map (fun k => (3 : ZMod 17) ^ k)
      = [1, 3, 9, 10, 13, 5, 15, 11, 16, 14, 8, 7, 4, 12, 2, 6] := by decide

/-- The powers of 3 hit every nonzero residue exactly once: the ordering is a
    permutation of the sixteen units of ℤ/17ℤ. -/
theorem gauss_ordering_nodup :
    ((List.range 16).map (fun k => (3 : ZMod 17) ^ k)).Nodup := by decide

/-- Over one period (the sixteen exponents `0 ≤ k < 16`), no power of 3 is 0:
    the ordering lands entirely in the nonzero residues, so it is a genuine
    permutation of the units of ℤ/17ℤ. -/
theorem gauss_powers_ne_zero :
    ∀ k : Fin 16, (3 : ZMod 17) ^ (k : ℕ) ≠ 0 := by decide

/-!
## Section IV: the two Gaussian periods (quadratic residues vs. non-residues)

Splitting the vertices into the eight quadratic residues (even powers of 3) and the
eight non-residues (odd powers of 3) gives Gauss's first pair of *periods* η₀, η₁.
As complex sums η₀ = Σ_{a∈QR} ζ^a, η₁ = Σ_{a∉QR} ζ^a they satisfy η₀ + η₁ = -1 and
η₀·η₁ = -4, hence the quadratic  x² + x − 4 = 0,  whose roots (-1 ± √17)/2 introduce
the first surd √17.  Here we formalize the underlying index sets and their defining
arithmetic property: they are exactly the nonzero squares and non-squares mod 17.
-/

/-- The quadratic residues mod 17 (first Gaussian period's index set): even powers of 3. -/
def periodQR : Finset (ZMod 17) := {1, 2, 4, 8, 9, 13, 15, 16}

/-- The quadratic non-residues mod 17 (second Gaussian period's index set): odd powers of 3. -/
def periodNQR : Finset (ZMod 17) := {3, 5, 6, 7, 10, 11, 12, 14}

/-- Each period has eight elements: the vertices split 8 + 8. -/
theorem periodQR_card : periodQR.card = 8 := by decide
theorem periodNQR_card : periodNQR.card = 8 := by decide

/-- The two periods are disjoint. -/
theorem periods_disjoint : Disjoint periodQR periodNQR := by decide

/-- The two periods together cover all sixteen nonzero residues. -/
theorem periods_cover :
    periodQR ∪ periodNQR = (Finset.univ : Finset (ZMod 17)).erase 0 := by decide

/-- **The QR period is exactly the nonzero squares mod 17.**
    `a` lies in the first Gaussian period iff `a ≠ 0` and `a` is a square. -/
theorem periodQR_eq_squares :
    ∀ a : ZMod 17, a ∈ periodQR ↔ (a ≠ 0 ∧ ∃ r : ZMod 17, r ^ 2 = a) := by decide

/-- The QR period is the set of even powers of the primitive root 3. -/
theorem periodQR_eq_even_powers :
    periodQR = (Finset.range 8).image (fun k => (3 : ZMod 17) ^ (2 * k)) := by decide

/-- The non-QR period is the set of odd powers of the primitive root 3. -/
theorem periodNQR_eq_odd_powers :
    periodNQR = (Finset.range 8).image (fun k => (3 : ZMod 17) ^ (2 * k + 1)) := by decide

/-!
## Section V: the order chain 16 ⊃ 8 ⊃ 4 ⊃ 2 ⊃ 1

Squaring the primitive root repeatedly, `3 → 9 → 13 → 16 → 1`, halves the order at
each step.  These are the generators of the period tower.
-/

/-- Successive squares of the primitive root: 3² = 9, (3²)² = 3⁴ = 13, 3⁸ = 16 = -1. -/
theorem square_step_1 : (3 : ZMod 17) ^ 2 = 9 := by decide
theorem square_step_2 : (3 : ZMod 17) ^ 4 = 13 := by decide
theorem square_step_3 : (3 : ZMod 17) ^ 8 = 16 := by decide

/-- `orderOf 9 = 8`: the quadratic residues form an order-8 cyclic subgroup. -/
theorem nine_orderOf : orderOf (9 : ZMod 17) = 8 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro p hp hpd
  have hp2 : p = 2 := by
    have h8 : (8 : ℕ) = 2 ^ 3 := by norm_num
    rw [h8] at hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
  subst hp2
  decide

/-- `orderOf 13 = 4`. -/
theorem thirteen_orderOf : orderOf (13 : ZMod 17) = 4 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro p hp hpd
  have hp2 : p = 2 := by
    have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
    rw [h4] at hpd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hpd)
  subst hp2
  decide

/-- `orderOf 16 = 2`: the subgroup {±1} of order 2 (complex conjugation on ζ₁₇). -/
theorem sixteen_orderOf : orderOf (16 : ZMod 17) = 2 :=
  orderOf_eq_prime (by decide) (by decide)

/-!
## Section VI: the period tower as index-2 subgroups of (ℤ/17ℤ)ˣ

Lifting to the unit group `(ZMod 17)ˣ`, the generators above yield a descending chain
of cyclic subgroups, each of index 2 in the previous:

  `zpowers u ⊃ zpowers u² ⊃ zpowers u⁴ ⊃ zpowers u⁸ ⊃ {1}`,
  cardinalities `16 ⊃ 8 ⊃ 4 ⊃ 2 ⊃ 1`.

This is the exact group-theoretic skeleton of Gauss's construction: by the Galois
correspondence for the cyclotomic extension ℚ(ζ₁₇)/ℚ (with Galois group ≅ (ℤ/17ℤ)ˣ),
these four index-2 subgroups correspond to a tower of four quadratic field extensions.
-/

/-- The primitive root `3` as a unit of `ZMod 17` (3 is coprime to 17). -/
def u3 : (ZMod 17)ˣ := ZMod.unitOfCoprime 3 (by decide)

/-- The unit `u3` reduces to `3` in `ZMod 17`. -/
theorem u3_coe : ((u3 : (ZMod 17)ˣ) : ZMod 17) = 3 := by
  simp [u3, ZMod.coe_unitOfCoprime]

/-- The unit `u3` also has order 16 (matching the primitive root `3`). -/
theorem u3_orderOf : orderOf u3 = 16 := by
  have h : orderOf ((u3 : (ZMod 17)ˣ) : ZMod 17) = 16 := by
    rw [u3_coe]; exact three_orderOf
  rwa [orderOf_units] at h

/-- Order of the successive squares of `u3`: `16 / 2^i`. -/
theorem u3_pow_orderOf (i : ℕ) (hi : i ≤ 4) :
    orderOf (u3 ^ (2 ^ i)) = 16 / 2 ^ i := by
  have hdvd : (2 ^ i) ∣ orderOf u3 := by
    rw [u3_orderOf, show (16 : ℕ) = 2 ^ 4 from by norm_num]
    exact pow_dvd_pow 2 hi
  rw [orderOf_pow_of_dvd (pow_ne_zero i (by norm_num : (2 : ℕ) ≠ 0)) hdvd, u3_orderOf]

/-- Cardinality of the `i`-th tower subgroup: `#⟨u3^(2^i)⟩ = 16 / 2^i`. -/
theorem tower_card (i : ℕ) (hi : i ≤ 4) :
    Nat.card (zpowers (u3 ^ (2 ^ i))) = 16 / 2 ^ i := by
  rw [Nat.card_zpowers, u3_pow_orderOf i hi]

/-- The tower cardinalities, explicitly: 16, 8, 4, 2, 1. -/
theorem tower_cards :
    Nat.card (zpowers (u3 ^ (2 ^ 0))) = 16 ∧
    Nat.card (zpowers (u3 ^ (2 ^ 1))) = 8 ∧
    Nat.card (zpowers (u3 ^ (2 ^ 2))) = 4 ∧
    Nat.card (zpowers (u3 ^ (2 ^ 3))) = 2 ∧
    Nat.card (zpowers (u3 ^ (2 ^ 4))) = 1 :=
  ⟨tower_card 0 (by norm_num), tower_card 1 (by norm_num), tower_card 2 (by norm_num),
   tower_card 3 (by norm_num), tower_card 4 (by norm_num)⟩

/-- Each tower subgroup is contained in the previous one:
    `⟨u3^(2^(i+1))⟩ ≤ ⟨u3^(2^i)⟩`, since `u3^(2^(i+1)) = (u3^(2^i))²`. -/
theorem tower_le (i : ℕ) :
    zpowers (u3 ^ (2 ^ (i + 1))) ≤ zpowers (u3 ^ (2 ^ i)) := by
  rw [zpowers_le]
  have : u3 ^ (2 ^ (i + 1)) = (u3 ^ (2 ^ i)) ^ 2 := by
    rw [← pow_mul, pow_succ]
  rw [this]
  exact npow_mem_zpowers _ 2

/-- The tower steps have index 2: `#⟨u3^(2^i)⟩ = 2 · #⟨u3^(2^(i+1))⟩` for `i < 4`.
    Each descent through the tower is a quadratic (degree-2) step. -/
theorem tower_index_two (i : ℕ) (hi : i < 4) :
    Nat.card (zpowers (u3 ^ (2 ^ i))) = 2 * Nat.card (zpowers (u3 ^ (2 ^ (i + 1)))) := by
  rw [tower_card i (by omega), tower_card (i + 1) (by omega)]
  interval_cases i <;> decide

/-!
## Section VII: summary — why 17 works

The four index-2 descents `16 → 8 → 4 → 2 → 1` are the four quadratic extensions in
the tower ℚ ⊂ ℚ(√17) ⊂ ⋯ ⊂ ℚ(ζ₁₇).  Because there are finitely many of them and each
has degree 2, every element of ℚ(ζ₁₇) — in particular `cos(2π/17)` and hence the
coordinates of the vertices — is expressible in nested square roots, so the regular
17-gon is straightedge-and-compass constructible.  The real subfield ℚ(cos 2π/17) sits
one order-2 quotient down (fixed field of complex conjugation `{±1} = ⟨16⟩`), with
degree φ(17)/2 = 8, requiring three quadratic steps.

`4` is the number of quadratic steps for the full cyclotomic tower; `3` for the real
(cosine) subfield.
-/

/-- The full cyclotomic tower has 4 quadratic steps: φ(17) = 2⁴. -/
theorem full_tower_steps : Nat.totient 17 = 2 ^ 4 := by decide

/-- The real (cosine) subfield has 3 quadratic steps: φ(17)/2 = 2³ = 8. -/
theorem real_subfield_degree : Nat.totient 17 / 2 = 2 ^ 3 := by decide

end AngleTrisectionOQ02OQ03OQ03
