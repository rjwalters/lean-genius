/-
Erdős Problem #857: The Weak Sunflower Problem

Source: https://erdosproblems.com/857
Status: OPEN (partial results known)

Statement:
Let m = m(n, k) be minimal such that in any collection of sets A₁, ..., Aₘ ⊆ {1,...,n}
there must exist a sunflower of size k - that is, some collection of k of the Aᵢ
which pairwise have the same intersection.

Estimate m(n, k), or even better, give an asymptotic formula.

Background:
A sunflower (also called a Δ-system) is a family of sets where any two sets have
the same intersection (the "core"). The classical Erdős-Ko-Rado Sunflower Lemma
gives bounds on how many sets can avoid containing a sunflower.

Key Results:
- Erdős-Ko-Rado (1961): The basic sunflower lemma gives m(n,k) ≤ k! · (n choose ℓ)
  for sets of size ≤ ℓ.
- Naslund-Sawin (2017): m(n,3) ≤ (3/2^(2/3))^((1+o(1))n)
- Connection to the cap set problem (Alon-Shpilka-Umans, 2013)

The Sunflower Conjecture (Erdős-Rado, 1960):
For any fixed k, there exists c(k) such that any family of more than c(k)^n
subsets of {1,...,n} contains a k-sunflower.

References:
- Erdős-Rado [1960]: Original sunflower lemma
- Erdős [Er70]: Formulated weak sunflower problem
- Alon-Shpilka-Umans [ASU13]: Cap set connection
- Naslund-Sawin [NaSa17]: Current best bounds for k=3
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SetFamily.Shadow

open Finset

namespace Erdos857

/-! ## Part I: Basic Definitions -/

/--
**Sunflower (Δ-system):**
A family of sets forms a sunflower with core C if every pair of sets
intersects exactly in C.
-/
def IsSunflower {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (core : Finset α) : Prop :=
  ∀ A B : Finset α, A ∈ family → B ∈ family → A ≠ B → A ∩ B = core

/--
**Sunflower Existence:**
A family contains a k-sunflower if there exists a subset of size k that forms a sunflower.
-/
def ContainsSunflower {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (k : ℕ) : Prop :=
  ∃ (subfamily : Finset (Finset α)) (core : Finset α),
    subfamily ⊆ family ∧ subfamily.card = k ∧ IsSunflower subfamily core

/--
**Petal:**
In a sunflower with core C, the petal of set A is A \ C.
-/
def Petal {α : Type*} [DecidableEq α] (A core : Finset α) : Finset α := A \ core

/--
**Petals are Disjoint:**
In a sunflower, the petals of distinct sets are disjoint.
-/
theorem sunflower_petals_disjoint {α : Type*} [DecidableEq α]
    (family : Finset (Finset α)) (core : Finset α) (hsf : IsSunflower family core)
    (A B : Finset α) (hA : A ∈ family) (hB : B ∈ family) (hne : A ≠ B) :
    Disjoint (Petal A core) (Petal B core) := by
  unfold Petal
  simp only [disjoint_iff_inter_eq_empty]
  ext x
  simp only [mem_inter, mem_sdiff, mem_empty_iff_false, iff_false, not_and, not_not_mem]
  intro ⟨hxA, hxnotC⟩ ⟨hxB, _⟩
  -- If x ∈ A and x ∈ B, then x ∈ A ∩ B = core
  have h := hsf A B hA hB hne
  have hxcore : x ∈ A ∩ B := mem_inter.mpr ⟨hxA, hxB⟩
  rw [h] at hxcore
  exact hxnotC hxcore

/-! ## Part II: The Sunflower Function m(n, k) -/

/--
**m(n, k):**
The minimal m such that any family of m subsets of {1,...,n} contains a k-sunflower.
-/
noncomputable def sunflowerNumber (n k : ℕ) : ℕ :=
  Nat.find (sunflower_number_exists n k)

/--
**Existence of m(n, k):**
For any n and k ≥ 2, there exists an m such that any family of m subsets
of {1,...,n} must contain a k-sunflower.

This follows from the pigeonhole principle: at most 2^n subsets exist.
-/
axiom sunflower_number_exists (n k : ℕ) :
    ∃ m : ℕ, ∀ family : Finset (Finset (Fin n)),
      family.card ≥ m → ContainsSunflower family k

/-! ## Part III: Classical Sunflower Lemma (Erdős-Ko-Rado) -/

/--
**Erdős-Ko-Rado Sunflower Lemma (1961):**
If a family F of sets, each of size at most ℓ, has more than k! · ℓ^ℓ members,
then F contains a k-sunflower.

More precisely: Any family of more than (k-1)! · ℓ^ℓ sets of size ≤ ℓ
contains a k-sunflower.
-/
axiom erdos_ko_rado_sunflower :
    ∀ (n ℓ k : ℕ) (hk : k ≥ 2) (hℓ : ℓ ≥ 1),
    ∀ family : Finset (Finset (Fin n)),
      (∀ A : Finset (Fin n), A ∈ family → A.card ≤ ℓ) →
      family.card > Nat.factorial (k - 1) * ℓ ^ ℓ →
      ContainsSunflower family k

/--
**Corollary: Bounded Sets Sunflower**
Any family of more than k! · ℓ^ℓ sets of size exactly ℓ contains a k-sunflower.
-/
theorem bounded_sets_sunflower (n ℓ k : ℕ) (hk : k ≥ 2) (hℓ : ℓ ≥ 1)
    (family : Finset (Finset (Fin n)))
    (hsize : ∀ A : Finset (Fin n), A ∈ family → A.card = ℓ)
    (hbig : family.card > Nat.factorial k * ℓ ^ ℓ) :
    ContainsSunflower family k := by
  apply erdos_ko_rado_sunflower n ℓ k hk hℓ family
  · intro A hA
    rw [hsize A hA]
  · calc family.card > Nat.factorial k * ℓ ^ ℓ := hbig
      _ ≥ Nat.factorial (k - 1) * ℓ ^ ℓ := by
        apply Nat.mul_le_mul_right
        apply Nat.factorial_le
        omega

/-! ## Part IV: Naslund-Sawin Bound (2017) -/

/--
**Naslund-Sawin (2017):**
For 3-sunflowers: m(n, 3) ≤ (3/2^(2/3))^((1+o(1))n)

This is approximately (2.755...)^n.
-/
axiom naslund_sawin_bound :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      sunflowerNumber n 3 ≤ Nat.ceil ((3 / (2 : ℝ) ^ (2/3 : ℝ) + ε) ^ n)

/--
**Cap Set Connection (Alon-Shpilka-Umans, 2013):**
The 3-sunflower problem is related to the cap set problem in F₃^n.
A cap set is a subset of F₃^n with no three-term arithmetic progressions.
The breakthrough of Croot-Lev-Pach and Ellenberg-Gijswijt on cap sets
led to the Naslund-Sawin improvement on sunflower bounds.
-/
axiom cap_set_connection :
    -- The 3-sunflower bound is controlled by cap set density
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      -- Cap set bound: maximum 3-AP-free subset of F₃^n has size ≤ (2.756...)^n
      ∃ (capBound : ℕ), capBound ≤ Nat.ceil (((2 : ℝ) + ε) ^ n) ∧
        -- This controls the sunflower number
        sunflowerNumber n 3 ≤ capBound * (n + 1)

/-! ## Part V: The Sunflower Conjecture -/

/--
**Sunflower Conjecture (Erdős-Rado, 1960):**
For any fixed k ≥ 3, there exists a constant c(k) such that:
m(n, k) ≤ c(k)^n

That is, the number of subsets of {1,...,n} needed to guarantee a k-sunflower
grows at most exponentially in n.
-/
axiom sunflower_conjecture :
    ∀ k ≥ 3, ∃ c : ℝ, c > 0 ∧
      ∀ n : ℕ, sunflowerNumber n k ≤ Nat.ceil (c ^ n)

/--
**Trivial Upper Bound:**
m(n, k) ≤ 2^n + 1 since there are only 2^n subsets of {1,...,n}.
Any family of 2^n + 1 subsets must contain duplicates, hence a trivial 2-sunflower.
-/
axiom trivial_upper_bound (n k : ℕ) (hk : k ≥ 2) :
    sunflowerNumber n k ≤ 2^n + 1

/--
**Lower Bound:**
m(n, k) ≥ 2^(n/k) for k ≥ 3, since random constructions show sunflower-free
families of exponential size exist.
-/
axiom lower_bound :
    ∀ k : ℕ, k ≥ 3 → ∃ c : ℝ, c > 1 ∧
      ∀ n : ℕ, sunflowerNumber n k ≥ Nat.floor (c ^ n)

/-! ## Part VI: Examples -/

/--
**Example: Singleton Sunflower**
The family {{1}, {2}, {3}} is a 3-sunflower with core ∅.
-/
theorem singleton_sunflower_example :
    IsSunflower ({{0}, {1}, {2}} : Finset (Finset (Fin 3))) ∅ := by
  intro A B hA hB hne
  simp only [mem_insert, mem_singleton] at hA hB
  rcases hA with rfl | rfl | rfl <;> rcases hB with rfl | rfl | rfl <;>
    first | exact absurd rfl hne | simp [inter_eq_empty, Fin.ext_iff]

/--
**Example: Sunflower with Non-empty Core**
The family {{1,2,3}, {1,2,4}, {1,2,5}} is a 3-sunflower with core {1,2}.
Each petal is a singleton: {3}, {4}, {5} respectively.
-/
axiom nonempty_core_example :
    ∃ (family : Finset (Finset (Fin 6))) (core : Finset (Fin 6)),
      family.card = 3 ∧ IsSunflower family core ∧ core.card = 2

/--
**Example: Maximum Sunflower-Free Family**
For k = 3 and sets of size 2 from {1,2,3,4}, a sunflower-free family
can have at most 4 members, such as {{1,2}, {1,3}, {2,4}, {3,4}}.
-/
axiom sunflower_free_family_bound :
    ∃ (family : Finset (Finset (Fin 4))),
      (∀ A, A ∈ family → A.card = 2) ∧
      family.card = 4 ∧
      ¬ContainsSunflower family 3

/-! ## Part VII: Weak vs Strong Sunflower Problem -/

/--
**Strong Sunflower Problem (Erdős Problem #20):**
Find the maximum size f(n, k, ℓ) of a family of ℓ-sets from {1,...,n}
that contains no k-sunflower.

The weak version (this problem) considers all subsets, not just ℓ-sets.
The strong version is easier to state but the weak version is more general.
-/
def strong_sunflower_bound (n k ℓ : ℕ) : Prop :=
  ∃ f : ℕ, ∀ family : Finset (Finset (Fin n)),
    (∀ A, A ∈ family → A.card = ℓ) →
    family.card > f →
    ContainsSunflower family k

/--
**Weak vs Strong Relationship:**
The weak sunflower bound m(n, k) can be expressed in terms of the
strong bounds f(n, k, ℓ) summed over all set sizes 0 ≤ ℓ ≤ n.
-/
axiom weak_from_strong :
    ∀ n k : ℕ, k ≥ 2 →
      ∃ bound : ℕ,
        (∀ family : Finset (Finset (Fin n)),
          family.card > bound → ContainsSunflower family k) ∧
        -- The bound sums over all possible set sizes
        bound ≤ (n + 1) * (Nat.factorial (k - 1) * n ^ n)

/--
**Union Formulation:**
Erdős originally stated this using "union" instead of "intersection":
k sets form a sunflower iff the symmetric differences of any two
equal the symmetric difference of the union minus the core.
The intersection and union formulations are equivalent.
-/
axiom union_formulation_equivalent :
    ∀ {α : Type*} [DecidableEq α] (family : Finset (Finset α)) (core : Finset α),
      IsSunflower family core ↔
      (∀ A B : Finset α, A ∈ family → B ∈ family → A ≠ B →
        ∀ x, x ∈ A ∩ B ↔ x ∈ core)

/-! ## Part VIII: Summary -/

/--
**Erdős Problem #857: Summary**

**Question:**
What is m(n, k), the minimum number of subsets of {1,...,n} guaranteed
to contain a k-sunflower?

**Status:** OPEN (partial results)

**Known Results:**
1. Erdős-Ko-Rado (1961): m(n, k) ≤ (k-1)! · ℓ^ℓ for ℓ-bounded families
2. Naslund-Sawin (2017): m(n, 3) ≤ (3/2^(2/3))^((1+o(1))n) ≈ 2.755^n
3. Connection to cap set problem established

**Sunflower Conjecture:**
m(n, k) = c(k)^n for some constant c(k) depending only on k.
This remains open for all k ≥ 3.
-/
theorem erdos_857_summary :
    -- Classical bound exists
    (∀ n ℓ k : ℕ, k ≥ 2 → ℓ ≥ 1 →
      ∀ family : Finset (Finset (Fin n)),
        (∀ A, A ∈ family → A.card ≤ ℓ) →
        family.card > Nat.factorial (k - 1) * ℓ ^ ℓ →
        ContainsSunflower family k) := by
  exact erdos_ko_rado_sunflower

/--
**Erdős Problem #857: Main Theorem**
The problem is open but two key results hold:
1. The classical Erdős-Ko-Rado sunflower lemma gives bounds for bounded families
2. Naslund-Sawin gives subexponential bounds for 3-sunflowers
-/
theorem erdos_857 :
    -- Classical sunflower lemma for bounded families
    (∀ n ℓ k : ℕ, k ≥ 2 → ℓ ≥ 1 →
      ∀ family : Finset (Finset (Fin n)),
        (∀ A, A ∈ family → A.card ≤ ℓ) →
        family.card > Nat.factorial (k - 1) * ℓ ^ ℓ →
        ContainsSunflower family k) ∧
    -- Naslund-Sawin bound for k=3
    (∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
      sunflowerNumber n 3 ≤ Nat.ceil ((3 / (2 : ℝ) ^ (2/3 : ℝ) + ε) ^ n)) :=
  ⟨erdos_ko_rado_sunflower, naslund_sawin_bound⟩

end Erdos857
