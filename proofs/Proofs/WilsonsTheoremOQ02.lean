import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-
# Gauss-Wilson Theorem: Generalizations to Non-Prime Moduli

## What This Proves

This file extends Wilson's theorem to all moduli via the Gauss-Wilson theorem:

  ∏ (units mod n) ≡ -1 (mod n) ↔ (ℤ/nℤ)* is cyclic
                                ↔ n ∈ {1, 2, 4, p^k, 2p^k}

## Status
- [x] Prime case proven
- [x] -1 ≠ 1 for n ≥ 3
- [x] Cyclic units for primes
- [x] Gauss-Wilson abstract framework
- [x] Extended computational verification to n ≤ 300
- [x] Wilson prime verification
- [x] Self-inverse classification: {x | x² = 1} = {1, -1} in cyclic (ZMod n)ˣ
- [x] Involution product lemma: ∏ G = ∏ {x | x² = 1}
- [x] Cyclic → product = -1 (via involution lemma + self-inverse classification)
- [ ] Non-cyclic → product = 1 (1 sorry: Klein four orbit argument)
- [x] Concrete-abstract bridge (Finset.prod_nbij via ZMod.val)
-/

namespace WilsonsTheoremOQ02

open Nat Finset ZMod

-- ============================================================================
-- Part 1: Prime Case
-- ============================================================================

/-- The abstract product of all units in ZMod n (requires n > 0). -/
noncomputable def abstractUnitsProduct (n : ℕ) [NeZero n] : ZMod n :=
  ∏ x : (ZMod n)ˣ, (x : ZMod n)

-- Helper to push Units coercion through products
private theorem units_val_prod {ι : Type*} {M : Type*} [CommMonoid M]
    (s : Finset ι) (f : ι → Mˣ) :
    (↑(∏ i ∈ s, f i) : M) = ∏ i ∈ s, (↑(f i) : M) :=
  map_prod (Units.coeHom M) f s

/-- For prime p, the product of all units in ZMod p equals -1.
    This is Wilson's theorem in abstract form. -/
theorem prod_units_eq_neg_one_prime (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∏ x : (ZMod p)ˣ, (x : ZMod p) = -1 := by
  have h := FiniteField.prod_univ_units_id_eq_neg_one (K := ZMod p)
  -- h : ∏ x : (ZMod p)ˣ, x = -1  (in the units group)
  rw [show (∏ x : (ZMod p)ˣ, (x : ZMod p)) = (↑(∏ x : (ZMod p)ˣ, x) : ZMod p) from
    (units_val_prod _ _).symm]
  rw [h]
  simp

-- ============================================================================
-- Part 2: Involution Structure
-- ============================================================================

/-- In a commutative group, x² = 1 iff x = x⁻¹. -/
theorem sq_eq_one_iff_eq_inv {G : Type*} [CommGroup G] (x : G) :
    x ^ 2 = 1 ↔ x = x⁻¹ := by
  rw [sq, mul_eq_one_iff_eq_inv]

/-- The set of self-inverse (order ≤ 2) elements in (ZMod n)ˣ. -/
noncomputable def selfInverseUnits (n : ℕ) [NeZero n] : Finset (ZMod n)ˣ :=
  Finset.univ.filter (fun x => x ^ 2 = 1)

-- ============================================================================
-- Part 3: -1 ≠ 1 for n ≥ 3
-- ============================================================================

/-- In (ZMod n)ˣ for n ≥ 3, -1 ≠ 1. -/
theorem neg_one_ne_one_units {n : ℕ} (hn : n ≥ 3) :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro h
  have h1 : ((-1 : (ZMod n)ˣ) : ZMod n) = ((1 : (ZMod n)ˣ) : ZMod n) := by rw [h]
  simp only [Units.val_neg, Units.val_one] at h1
  have h2 : (n : ℤ) ∣ (-1 - 1) := by
    have := ZMod.intCast_zmod_eq_zero_iff_dvd (-1 - 1) n
    rw [show ((-1 - 1 : ℤ) : ZMod n) = (-1 : ZMod n) - 1 from by push_cast; ring] at this
    rw [h1, sub_self] at this
    exact this.mp rfl
  have h3 : (n : ℤ) ∣ 2 := by
    have : (-1 - 1 : ℤ) = -2 := by ring
    rw [this] at h2
    exact (dvd_neg.mp h2)
  have h4 : n ≤ 2 := by
    have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) h3
    omega
  omega

/-- -1 ≠ 1 in ZMod n for n ≥ 3. -/
theorem neg_one_ne_one_zmod {n : ℕ} (hn : n ≥ 3) : (-1 : ZMod n) ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro heq
  have : ((-1 : (ZMod n)ˣ) : ZMod n) = ((1 : (ZMod n)ˣ) : ZMod n) := by simp [heq]
  exact neg_one_ne_one_units hn (Units.val_injective this)

-- ============================================================================
-- Part 4: Cyclic Group Properties
-- ============================================================================

/-- For prime p, (ZMod p)ˣ is cyclic. -/
noncomputable instance isCyclic_units_prime (p : ℕ) [hp : Fact (Nat.Prime p)] :
    IsCyclic (ZMod p)ˣ := inferInstance

-- ============================================================================
-- Part 5: Self-Inverse Classification in Cyclic Groups
-- ============================================================================

/-- In a finite cyclic group, the number of solutions to x² = 1 is at most 2. -/
theorem card_sq_eq_one_le_two (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G]
    [IsCyclic G] :
    (Finset.univ.filter (fun (x : G) => x ^ 2 = 1)).card ≤ 2 :=
  IsCyclic.card_pow_eq_one_le (by norm_num : 0 < 2)

/-- For n ≥ 3, the self-inverse units in a cyclic (ZMod n)ˣ are exactly {1, -1}. -/
theorem selfInverse_units_eq_pair {n : ℕ} (hn : n ≥ 3) [NeZero n] [IsCyclic (ZMod n)ˣ] :
    Finset.univ.filter (fun (x : (ZMod n)ˣ) => x ^ 2 = 1) = {1, -1} := by
  have hcard := card_sq_eq_one_le_two (ZMod n)ˣ
  have h1_mem : (1 : (ZMod n)ˣ) ∈ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    simp [Finset.mem_filter, sq]
  have hn1_mem : (-1 : (ZMod n)ˣ) ∈ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    simp [Finset.mem_filter, sq]
  have hne : (1 : (ZMod n)ˣ) ≠ -1 := (neg_one_ne_one_units hn).symm
  have hsub : {1, -1} ⊆ Finset.univ.filter (fun (x : (ZMod n)ˣ) => x ^ 2 = 1) := by
    intro x hx
    simp [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcard_pair : ({1, -1} : Finset (ZMod n)ˣ).card = 2 := Finset.card_pair hne
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

-- ============================================================================
-- Part 6: Cyclic Group Product via Generator
-- ============================================================================

/-- Helper: In a finite commutative group, (∏ x, x)² = 1.
    Proof: The map x ↦ x⁻¹ is a permutation, so ∏ x = ∏ x⁻¹ = (∏ x)⁻¹. -/
theorem prod_univ_sq_eq_one (G : Type*) [CommGroup G] [Fintype G] :
    (∏ x : G, x) ^ 2 = 1 := by
  -- Key: ∏ x⁻¹ = (∏ x)⁻¹ (by Finset.prod_inv_distrib)
  -- Also: ∏ x⁻¹ = ∏ x (via the bijection x ↦ x⁻¹)
  -- So (∏ x)⁻¹ = ∏ x, meaning (∏ x)² = 1
  -- ∏ x = ∏ x⁻¹ (via the involution x ↦ x⁻¹ which permutes G)
  -- But ∏ x⁻¹ = (∏ x)⁻¹
  -- So ∏ x = (∏ x)⁻¹, giving (∏ x)² = 1
  suffices h : (∏ x : G, x)⁻¹ = ∏ x : G, x by
    rw [sq]
    conv_lhs => rw [← h]
    exact inv_mul_cancel _
  rw [← Finset.prod_inv_distrib]
  -- Goal: ∏ x in univ, x⁻¹ = ∏ x in univ, x
  -- The map x ↦ x⁻¹ is a bijection on univ
  apply Finset.prod_bij (fun a _ => a⁻¹)
  · intros; exact Finset.mem_univ _
  · intros a _ a' _ h; exact inv_injective h
  · intro b _; exact ⟨b⁻¹, Finset.mem_univ _, inv_inv b⟩
  · intros; rfl

/-- **Involution product lemma**: In a finite commutative group, the involution
    x ↦ x⁻¹ pairs non-self-inverse elements, so ∏ G = ∏ {x | x² = 1}.

    This is the key structural lemma for the Gauss-Wilson theorem. -/
theorem prod_eq_prod_sq_eq_one (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] :
    ∏ x : G, x = ∏ x ∈ Finset.univ.filter (fun x : G => x ^ 2 = 1), x := by
  -- ∏ G = ∏ {x | x²=1} * ∏ {x | x²≠1}
  have hsplit : ∏ x : G, x =
      (∏ x ∈ Finset.univ.filter (fun x : G => x ^ 2 = 1), x) *
      (∏ x ∈ Finset.univ.filter (fun x : G => ¬(x ^ 2 = 1)), x) :=
    (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x : G => x ^ 2 = 1) id).symm
  -- The second factor is 1 by involution x ↦ x⁻¹
  have hrest : ∏ x ∈ Finset.univ.filter (fun x : G => ¬(x ^ 2 = 1)), x = 1 := by
    apply Finset.prod_involution (fun x _ => x⁻¹)
    · -- x * x⁻¹ = 1
      intros a _
      exact mul_inv_cancel a
    · -- x ≠ x⁻¹ when x² ≠ 1
      intro a ha hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      exact fun heq => ha ((sq_eq_one_iff_eq_inv a).mpr heq.symm)
    · -- x⁻¹ ∈ S when x ∈ S
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rwa [inv_pow, inv_eq_one]
    · -- Involution: (x⁻¹)⁻¹ = x
      intros a _
      exact inv_inv a
  rw [hsplit, hrest, mul_one]

/-- The product of all units in ZMod n equals -1 when (ZMod n)ˣ is cyclic
    and n ≥ 3.

    Proof: By the involution product lemma, ∏ G = ∏ {x | x² = 1}.
    In cyclic (ZMod n)ˣ with n ≥ 3, {x | x² = 1} = {1, -1}.
    So ∏ G = 1 · (-1) = -1. -/
theorem prod_units_neg_one_of_cyclic {n : ℕ} (hn : n ≥ 3)
    [hne : NeZero n] [hcyc : IsCyclic (ZMod n)ˣ] :
    ∏ x : (ZMod n)ˣ, (x : ZMod n) = -1 := by
  suffices hprod : ∏ x : (ZMod n)ˣ, x = -1 by
    rw [show (∏ x : (ZMod n)ˣ, (x : ZMod n)) = (↑(∏ x : (ZMod n)ˣ, x) : ZMod n) from
      (units_val_prod _ _).symm, hprod]
    simp
  -- By involution product lemma: ∏ G = ∏ {x | x² = 1}
  rw [prod_eq_prod_sq_eq_one]
  -- In cyclic (ZMod n)ˣ with n ≥ 3: {x | x² = 1} = {1, -1}
  rw [selfInverse_units_eq_pair hn]
  -- ∏ {1, -1} = 1 * (-1) = -1
  rw [Finset.prod_pair (neg_one_ne_one_units hn).symm]
  exact one_mul (-1)

/-- When (ZMod n)ˣ is not cyclic and n ≥ 3, the product of units is 1.

    Proof strategy (documented for Aristotle/future sessions):
    1. By involution product lemma: ∏ G = ∏ {x | x² = 1}
    2. When not cyclic, |{x | x² = 1}| ≥ 3 (more than {1, -1})
    3. The self-inverse set S forms an elementary abelian 2-group of order ≥ 4
    4. Pick two distinct non-identity c, d ∈ S. The Klein four subgroup {1,c,d,cd}
       acts on S by left multiplication. Each orbit {e, ce, de, cde} has product
       e·ce·de·cde = c²d²e⁴ = 1.
    5. So ∏ S = ∏ (orbit products) = 1.

    The key Lean formalization challenge is partitioning the finset into orbits of
    a Klein four group action and showing each orbit product is 1. -/
theorem prod_units_one_of_not_cyclic {n : ℕ} (hn : n ≥ 3)
    [hne : NeZero n] (hncyc : ¬ IsCyclic (ZMod n)ˣ) :
    ∏ x : (ZMod n)ˣ, (x : ZMod n) = 1 := by
  suffices hprod : ∏ x : (ZMod n)ˣ, x = 1 by
    rw [show (∏ x : (ZMod n)ˣ, (x : ZMod n)) = (↑(∏ x : (ZMod n)ˣ, x) : ZMod n) from
      (units_val_prod _ _).symm, hprod]
    simp
  -- ∏ G = ∏ {x | x² = 1} by involution product lemma
  -- When not cyclic, the Klein four action argument gives product = 1
  sorry

-- ============================================================================
-- Part 7: Gauss-Wilson Abstract Theorem
-- ============================================================================

/-- **Gauss-Wilson Theorem (Abstract)**:
    For n ≥ 3, ∏ units = -1 ↔ (ZMod n)ˣ is cyclic. -/
theorem gaussWilson_abstract {n : ℕ} (hn : n ≥ 3) [hne : NeZero n] :
    (∏ x : (ZMod n)ˣ, (x : ZMod n) = -1) ↔ IsCyclic (ZMod n)ˣ := by
  constructor
  · intro hprod
    by_contra hncyc
    have h1 := prod_units_one_of_not_cyclic hn hncyc
    rw [h1] at hprod
    exact neg_one_ne_one_zmod hn hprod.symm
  · intro hcyc
    exact @prod_units_neg_one_of_cyclic n hn hne hcyc

-- ============================================================================
-- Part 8: Concrete-Abstract Bridge
-- ============================================================================

/-- The concrete units product (product of coprime naturals < n). -/
def unitsProduct (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun a => Nat.Coprime a n)).prod id

/-- For n ≥ 1, casting unitsProduct into ZMod n gives the abstract product. -/
theorem unitsProduct_cast_eq_abstract {n : ℕ} (hn : n ≥ 1) [hne : NeZero n] :
    (unitsProduct n : ZMod n) = ∏ x : (ZMod n)ˣ, (x : ZMod n) := by
  -- Cast the natural product into ZMod n
  unfold unitsProduct
  rw [Nat.cast_prod]
  -- The source set is coprime naturals < n; the target is (ZMod n)ˣ
  -- We use prod_bij with the map a ↦ ZMod.unitOfCoprime a (coprime proof)
  -- but first rewrite the RHS to use ↑u for units
  symm
  apply Finset.prod_nbij (fun u => ZMod.val (u : ZMod n))
  · -- Map sends units into the filtered set
    intro u _
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime⟩
  · -- Injective: val is injective on ZMod n, and units coerce injectively
    intro u₁ u₂ _ _ h
    have hval : (u₁ : ZMod n) = (u₂ : ZMod n) := ZMod.val_injective h
    exact Units.val_injective hval
  · -- Surjective: every coprime natural < n comes from a unit
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact ⟨ZMod.unitOfCoprime a ha.2, Finset.mem_univ _,
      by rw [Units.val_unitOfCoprime]; exact (ZMod.val_natCast_of_lt ha.1).symm⟩
  · -- Values agree: casting a through id and casting unit value agree
    intro u _
    simp [Nat.cast_id]

-- ============================================================================
-- Part 9: Computational Verification
-- ============================================================================

/-- Check if x is a power of base. -/
def isPowerOfAux (base x : ℕ) : Bool :=
  if x == 0 then false
  else if x == 1 then true
  else if base < 2 then false
  else if x % base == 0 then isPowerOfAux base (x / base)
  else false
termination_by x
decreasing_by
  simp_all
  exact Nat.div_lt_self (by omega) (by omega)

/-- Check if n has the Gauss-Wilson form. -/
def hasGaussWilsonForm (n : ℕ) : Bool :=
  if n ≤ 2 then true
  else if n == 4 then true
  else
    let p := n.minFac
    if p == 2 then
      let m := n / 2
      if m < 3 then false
      else
        let q := m.minFac
        if q < 3 then false
        else isPowerOfAux q m
    else
      isPowerOfAux p n

/-- Combined check: both sides agree. -/
def gaussWilsonCheck (n : ℕ) : Bool :=
  if n < 3 then true
  else (unitsProduct n % n == n - 1) == hasGaussWilsonForm n

-- Extended verification: n ≤ 250
theorem gaussWilson_verified_le_250 :
    ∀ n : Fin 251, n.val ≥ 3 → gaussWilsonCheck n.val = true := by native_decide

-- Extended verification: n ≤ 300
theorem gaussWilson_verified_le_300 :
    ∀ n : Fin 301, n.val ≥ 3 → gaussWilsonCheck n.val = true := by native_decide

-- ============================================================================
-- Part 10: Wilson's Theorem Connections
-- ============================================================================

/-- Wilson's theorem via abstract units product. -/
theorem wilson_via_units (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∏ x : (ZMod p)ˣ, (x : ZMod p) = -1 :=
  prod_units_eq_neg_one_prime p

/-- For n = 2, product = -1 (since -1 ≡ 1 mod 2). -/
example : ∏ x : (ZMod 2)ˣ, (x : ZMod 2) = -1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact prod_units_eq_neg_one_prime 2

-- ============================================================================
-- Part 11: Wilson Primes
-- ============================================================================

/-- Wilson quotient. -/
def wilsonQuotient (p : ℕ) : ℕ := ((p - 1).factorial + 1) / p

/-- A prime is a Wilson prime iff p² divides (p-1)! + 1. -/
def IsWilsonPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p ^ 2 ∣ (p - 1).factorial + 1

/-- 5 is a Wilson prime (4! + 1 = 25 = 5²). -/
theorem five_is_wilson_prime : IsWilsonPrime 5 := by
  unfold IsWilsonPrime
  exact ⟨by decide, by native_decide⟩

/-- 13 is a Wilson prime. -/
theorem thirteen_is_wilson_prime : IsWilsonPrime 13 := by
  unfold IsWilsonPrime
  exact ⟨by decide, by native_decide⟩

/-- No Wilson primes between 14 and 100. -/
theorem no_wilson_primes_14_to_100 :
    ∀ p : Fin 101, p.val ≥ 14 → Nat.Prime p.val →
    ¬(p.val ^ 2 ∣ (p.val - 1).factorial + 1) := by
  native_decide

/-
## Summary

### Proven (14 theorems)
1. Product = -1 for primes (via FiniteField)
2. -1 ≠ 1 for n ≥ 3 (both units and ZMod versions)
3. Self-inverse units = {1, -1} for cyclic (ZMod n)ˣ, n ≥ 3
4. Gauss-Wilson abstract biconditional (modulo non-cyclic case)
5. Computational verification for n ≤ 300
6. Wilson prime verification for 5, 13
7. No Wilson primes in [14, 100]
8. (∏ x)² = 1 in any finite commutative group
9. Involution product lemma: ∏ G = ∏ {x | x² = 1} (`prod_eq_prod_sq_eq_one`)
10. Cyclic → product = -1 (`prod_units_neg_one_of_cyclic`) - sorry-free
11. Concrete-abstract bridge (`unitsProduct_cast_eq_abstract`) - sorry-free

### Remaining Sorries (1, reduced from 5)

1. `prod_units_one_of_not_cyclic`: ¬IsCyclic → product = 1
   Strategy: ∏ G = ∏ {x | x² = 1} (proved). The self-inverse set S forms an
   elementary abelian 2-group. When not cyclic, |S| ≥ 3, so S has at least two
   distinct non-identity elements c, d. The Klein four subgroup {1,c,d,cd} acts
   on S by left multiplication with orbits {e, ce, de, cde}, each having product
   e·ce·de·cde = c²d²e⁴ = 1. So ∏ S = 1.
   Formalizing this requires Finset orbit partitioning machinery.

All verified computationally for n ≤ 300.
-/

#check @prod_units_eq_neg_one_prime
#check @prod_units_neg_one_of_cyclic
#check @gaussWilson_abstract

end WilsonsTheoremOQ02
