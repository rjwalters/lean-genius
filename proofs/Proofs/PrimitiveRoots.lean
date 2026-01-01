import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Primitive Roots Modulo Primes

## What This Proves
For any prime p, there are exactly φ(p-1) primitive roots modulo p.

A **primitive root** modulo p is an element g ∈ (ℤ/pℤ)* whose multiplicative order equals
p-1, meaning the powers g, g², g³, ..., g^(p-1) generate all non-zero residues mod p.

Equivalently, a primitive root is a generator of the cyclic group (ℤ/pℤ)*.

## Approach
- **Foundation (from Mathlib):** We combine two key results:
  1. `isCyclic_of_subgroup_isDomain`: Finite subgroups of units in integral domains are cyclic
  2. `IsCyclic.card_orderOf_eq_totient`: In a cyclic group of order n, there are exactly φ(d)
     elements of order d for each d dividing n
- **Key Insight:** Primitive roots are elements of order p-1 in a cyclic group of order p-1.
  By the cyclic group counting theorem, there are exactly φ(p-1) such elements.
- **Proof Techniques Demonstrated:** Working with cyclic groups, ZMod units, order of elements.

## Status
- [x] Complete proof
- [x] Uses Mathlib for main result
- [x] Proves extensions/corollaries
- [x] Pedagogical examples
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Mathlib.RingTheory.IntegralDomain` : Cyclic structure of finite unit subgroups
- `Mathlib.GroupTheory.SpecificGroups.Cyclic` : Counting elements by order in cyclic groups
- `Mathlib.Data.Nat.Totient` : Euler's totient function
- `Mathlib.Data.ZMod.Basic` : ZMod arithmetic

## Historical Note
The existence of primitive roots was first proved by Euler (1773) for prime moduli.
Gauss gave a complete characterization: primitive roots exist modulo n if and only if
n = 1, 2, 4, p^k, or 2p^k for odd prime p. The count φ(p-1) follows from the structure
of cyclic groups, understood fully in the 19th century.

## Why This Works
The multiplicative group (ℤ/pℤ)* has order p-1. Being cyclic, it has exactly one subgroup
of each order d dividing p-1, and each such subgroup contributes exactly φ(d) elements
of order d. Primitive roots are elements of order p-1, so there are φ(p-1) of them.

The key formula: In a cyclic group of order n, ∑_{d|n} φ(d) = n (each element has some order).
-/

namespace PrimitiveRoots

/-! ## Definitions and Setup -/

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- A primitive root modulo p is an element whose multiplicative order equals p-1.
    Equivalently, it generates the entire multiplicative group (ℤ/pℤ)*. -/
def IsPrimitiveRoot (g : (ZMod p)ˣ) : Prop :=
  orderOf g = Fintype.card (ZMod p)ˣ


/-- Alternative characterization: primitive root has order p-1. -/
theorem isPrimitiveRoot_iff (g : (ZMod p)ˣ) :
    IsPrimitiveRoot g ↔ orderOf g = p - 1 := by
  unfold IsPrimitiveRoot
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hp.out]

/-! ## The Multiplicative Group is Cyclic -/

/-- The multiplicative group of units modulo a prime is cyclic.
    This is a fundamental result that enables the counting theorem.

    The proof uses that (ZMod p)ˣ is a finite subgroup of units in an integral domain
    (ZMod p is a field for prime p), hence cyclic by a general theorem about
    finite multiplicative subgroups in integral domains. -/
instance isCyclic_units_prime : IsCyclic (ZMod p)ˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom (ZMod p)) Units.ext

/-- The order of (ℤ/pℤ)* equals p-1. -/
theorem card_units_eq_pred_prime : Fintype.card (ZMod p)ˣ = p - 1 := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hp.out]

/-! ## Existence of Primitive Roots -/

/-- There exists a primitive root modulo any prime p. -/
theorem exists_primitiveRoot : ∃ g : (ZMod p)ˣ, IsPrimitiveRoot g := by
  -- Since (ZMod p)ˣ is cyclic, it has a generator
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  use g
  unfold IsPrimitiveRoot
  -- A generator has order equal to the group order
  rwa [orderOf_eq_card_of_forall_mem_zpowers]

/-! ## The Main Theorem: Counting Primitive Roots -/

/-- **The set of primitive roots modulo p** (as elements of order p-1) -/
noncomputable def primitiveRoots : Finset (ZMod p)ˣ :=
  Finset.univ.filter (fun g => orderOf g = p - 1)

/-- **Main Theorem: There are exactly φ(p-1) primitive roots modulo p.**

    This follows from the fact that (ℤ/pℤ)* is a cyclic group of order p-1,
    and a cyclic group of order n has exactly φ(n) generators. -/
theorem card_primitiveRoots : (primitiveRoots (p := p) (hp := hp)).card = Nat.totient (p - 1) := by
  unfold primitiveRoots
  -- Apply the cyclic group counting theorem directly
  have hdvd : (p - 1) ∣ Fintype.card (ZMod p)ˣ := by
    rw [card_units_eq_pred_prime (p := p) (hp := hp)]
  have hcount := IsCyclic.card_orderOf_eq_totient (α := (ZMod p)ˣ) hdvd
  -- Convert filter card to set card
  simp only at hcount ⊢
  convert hcount using 2

/-- Alternative statement: the number of primitive roots equals φ(p-1). -/
theorem count_primitiveRoots :
    (Finset.univ.filter (fun g : (ZMod p)ˣ => orderOf g = p - 1)).card =
    Nat.totient (p - 1) :=
  card_primitiveRoots (p := p) (hp := hp)

/-! ## Corollaries and Properties -/

/-- The proportion of units that are primitive roots. -/
theorem proportion_primitiveRoots :
    (primitiveRoots (p := p) (hp := hp)).card * (p - 1) = Nat.totient (p - 1) * (p - 1) := by
  rw [card_primitiveRoots (p := p) (hp := hp)]

/-- For p = 2, there is exactly 1 primitive root (namely, 1 itself).
    Note: φ(1) = 1 by convention. -/
example : Nat.totient (2 - 1) = 1 := by native_decide

/-- For p = 3, there is exactly 1 primitive root (namely, 2).
    φ(2) = 1. -/
example : Nat.totient (3 - 1) = 1 := by native_decide

/-- For p = 5, there are exactly 2 primitive roots (2 and 3).
    φ(4) = 2. -/
example : Nat.totient (5 - 1) = 2 := by native_decide

/-- For p = 7, there are exactly 2 primitive roots.
    φ(6) = φ(2)·φ(3) = 1·2 = 2. -/
example : Nat.totient (7 - 1) = 2 := by native_decide

/-- For p = 11, there are exactly 4 primitive roots.
    φ(10) = φ(2)·φ(5) = 1·4 = 4. -/
example : Nat.totient (11 - 1) = 4 := by native_decide

/-- For p = 13, there are exactly 4 primitive roots.
    φ(12) = φ(4)·φ(3) = 2·2 = 4. -/
example : Nat.totient (13 - 1) = 4 := by native_decide

/-! ## Connection to Cyclic Group Theory -/

/-- Primitive roots are exactly the generators of (ℤ/pℤ)*. -/
theorem isPrimitiveRoot_iff_generates (g : (ZMod p)ˣ) :
    IsPrimitiveRoot g ↔ ∀ a : (ZMod p)ˣ, a ∈ Subgroup.zpowers g := by
  unfold IsPrimitiveRoot
  constructor
  · intro hg a
    -- g has order equal to the group order, so it generates everything
    have hfull : Subgroup.zpowers g = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      have hcard : Nat.card (Subgroup.zpowers g) = Fintype.card (ZMod p)ˣ := by
        rw [Nat.card_zpowers, hg]
      have := Subgroup.eq_top_of_card_eq (H := Subgroup.zpowers g) (by
        rw [hcard, Nat.card_eq_fintype_card])
      rw [this]
      exact Subgroup.mem_top x
    rw [hfull]
    exact Subgroup.mem_top a
  · intro hgen
    exact orderOf_eq_card_of_forall_mem_zpowers hgen

/-! ## Why This Matters

Primitive roots are fundamental in number theory and cryptography:

1. **Discrete Logarithms**: If g is a primitive root, every unit a can be written as
   a ≡ g^k (mod p) for a unique k ∈ {0, 1, ..., p-2}. This k is the discrete log of a.

2. **Diffie-Hellman**: Key exchange protocols rely on the difficulty of computing
   discrete logarithms in groups generated by primitive roots.

3. **Quadratic Residues**: An element a is a quadratic residue iff its discrete log
   is even. Primitive roots have odd discrete logs for half the exponents.

4. **Cyclotomic Fields**: Primitive roots modulo p correspond to primitive (p-1)th
   roots of unity under certain isomorphisms.

5. **Index Calculus**: Modern algorithms for discrete logs in (ℤ/pℤ)* use the
   structure provided by primitive roots.
-/

#check IsPrimitiveRoot
#check isPrimitiveRoot_iff
#check exists_primitiveRoot
#check primitiveRoots
#check card_primitiveRoots
#check count_primitiveRoots
#check isPrimitiveRoot_iff_generates

end PrimitiveRoots
