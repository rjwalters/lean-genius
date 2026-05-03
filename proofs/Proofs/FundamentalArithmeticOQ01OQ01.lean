/-
Self-Contained Fundamental Theorem of Arithmetic via Finsupp
Open Question: fundamental-arithmetic-oq-01-oq-01

Proves the FTA using Mathlib's Nat.factorization (prime exponent map),
as an alternative to the sorted-list approach in FundamentalArithmetic.lean.

Key theorem: Every positive natural n has a unique representation as
  n = ∏ p ∈ n.primeFactors, p ^ (n.factorization p)
where n.factorization : ℕ →₀ ℕ maps each prime to its exponent in n.

The Finsupp (finite support function) approach:
- Encodes factorization algebraically as a function ℕ → ℕ with finite support
- Uniqueness follows from injectivity of the factorization map
- Complements the list approach: sorted lists vs. prime exponent maps

This file imports only Mathlib.Data.Nat.Factorization.Basic, avoiding
FundamentalArithmetic.lean and FundamentalArithmeticOQ01.lean.

References:
- Nat.factorization_prod_pow_eq_self: the reconstruction formula
- Nat.support_factorization: support equals primeFactors
- Nat.Prime.factorization: prime p has factorization = Finsupp.single p 1
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace FundamentalArithmeticOQ01OQ01

open Finsupp Nat

-- ============================================================
-- Helper: factorization distributes over Finset products
-- ============================================================

/-- Factorization distributes over Finset products of nonzero naturals:
    (∏ m ∈ s, m).factorization = ∑ m ∈ s, m.factorization -/
private lemma factorization_finset_prod (s : Finset ℕ) (h : ∀ m ∈ s, m ≠ 0) :
    (∏ m ∈ s, m).factorization = ∑ m ∈ s, m.factorization := by
  induction s using Finset.induction_on with
  | empty => simp [Nat.factorization_one]
  | insert ha ih =>
    rename_i a s _
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    rw [Nat.factorization_mul (h a (Finset.mem_insert_self a s))
      (Finset.prod_ne_zero (fun m hm => h m (Finset.mem_insert_of_mem hm)))]
    congr 1
    exact ih (fun m hm => h m (Finset.mem_insert_of_mem hm))

-- ============================================================
-- Part I: Reconstruction Formula (Existence)
-- ============================================================

/-- **FTA Existence (Finsupp form)**: Every positive natural equals the Finsupp
    product of its prime powers: n.factorization.prod (· ^ ·) = n. -/
theorem fta_reconstruction (n : ℕ) (hn : n ≠ 0) :
    n.factorization.prod (· ^ ·) = n :=
  Nat.factorization_prod_pow_eq_self hn

-- ============================================================
-- Part II: Support is Exactly the Prime Factors
-- ============================================================

/-- The support of n.factorization equals n's prime factors. -/
theorem fta_support_eq_primeFactors (n : ℕ) :
    n.factorization.support = n.primeFactors :=
  Nat.support_factorization n

/-- Every element of n.factorization.support is prime. -/
theorem fta_support_prime (n : ℕ) {p : ℕ} (hp : p ∈ n.factorization.support) :
    p.Prime := by
  rw [Nat.support_factorization] at hp
  exact Nat.prime_of_mem_primeFactors hp

/-- A prime p divides n iff p ∈ n.factorization.support. -/
theorem fta_mem_support_iff_dvd {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    p ∈ n.factorization.support ↔ p ∣ n := by
  rw [Nat.support_factorization, Nat.mem_primeFactors hn]
  exact ⟨fun h => h.2, fun h => ⟨hp, h, hn⟩⟩

-- ============================================================
-- Part III: Key Algebraic Lemma
-- ============================================================

/-- **Key identity**: If f : ℕ →₀ ℕ has prime support, then the factorization
    of its Finsupp prime-power product recovers f itself.

    Proof: At each prime a, the a-adic valuation of ∏ p^(f p) equals f a,
    since: (i) the a-th factor contributes exactly f a to the valuation,
    and (ii) all other factors p^(f p) with p ≠ a are coprime to a. -/
theorem finsupp_prime_prod_factorization (f : ℕ →₀ ℕ)
    (hf : ∀ p ∈ f.support, p.Prime) :
    (f.prod (· ^ ·)).factorization = f := by
  apply Finsupp.ext
  intro a
  simp only [Finsupp.prod]
  -- Step 1: distribute factorization over the Finset product
  have hne : ∀ p ∈ f.support, p ^ f p ≠ 0 := fun p hp =>
    pow_ne_zero (f p) (hf p hp).ne_zero
  rw [factorization_finset_prod _ hne]
  -- Step 2: distribute Finsupp apply over the sum
  simp only [Finsupp.finset_sum_apply]
  -- Step 3: compute (p ^ f p).factorization a for each prime p
  have step : ∀ p ∈ f.support, (p ^ f p).factorization a = if p = a then f p else 0 := by
    intro p hp
    have hprime : p.Prime := hf p hp
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
        hprime.factorization, Finsupp.single_apply]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl step]
  -- Step 4: collapse the indicator sum
  rw [Finset.sum_ite_eq]
  -- Step 5: if a ∉ support then f a = 0
  split_ifs with hmem
  · rfl
  · exact (Finsupp.not_mem_support_iff.mp hmem).symm

-- ============================================================
-- Part IV: Uniqueness of the Finsupp Representation
-- ============================================================

/-- **FTA Uniqueness**: If g : ℕ →₀ ℕ has prime support and
    g.prod (· ^ ·) = n, then g is exactly n's canonical factorization. -/
theorem fta_uniqueness {n : ℕ} (hn : n ≠ 0) (g : ℕ →₀ ℕ)
    (hg_prime : ∀ p ∈ g.support, p.Prime)
    (hg_prod : g.prod (· ^ ·) = n) :
    g = n.factorization := by
  calc g = (g.prod (· ^ ·)).factorization := (finsupp_prime_prod_factorization g hg_prime).symm
    _ = n.factorization := by rw [hg_prod]

-- ============================================================
-- Part V: The Full FTA (Finsupp Formulation)
-- ============================================================

/-- **Fundamental Theorem of Arithmetic (Finsupp formulation)**:
    Every positive natural n has a UNIQUE representation f : ℕ →₀ ℕ with
    prime support satisfying f.prod (· ^ ·) = n.

    This is the algebraic FTA: n encodes uniquely as a prime exponent map.
    The canonical witness is n.factorization.

    Contrast with the list FTA (FundamentalArithmetic.lean): there, the
    representation uses a sorted list of primes with repetition. Here, it
    uses a Finsupp mapping each prime to its multiplicity. Both are unique
    representations; the Finsupp form has cleaner algebraic properties. -/
theorem fundamental_theorem_of_arithmetic (n : ℕ) (hn : n ≠ 0) :
    ∃! f : ℕ →₀ ℕ,
      (∀ p ∈ f.support, p.Prime) ∧
      f.prod (· ^ ·) = n := by
  refine ⟨n.factorization, ⟨fta_support_prime n, fta_reconstruction n hn⟩, ?_⟩
  intro g ⟨hg_prime, hg_prod⟩
  exact fta_uniqueness hn g hg_prime hg_prod

-- ============================================================
-- Part VI: Corollaries
-- ============================================================

/-- If two positive naturals have equal prime exponent maps, they are equal.
    The factorization map is injective on positive naturals. -/
theorem factorization_determines_number {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0)
    (h : m.factorization = n.factorization) : m = n :=
  calc m = m.factorization.prod (· ^ ·) := (fta_reconstruction m hm).symm
    _ = n.factorization.prod (· ^ ·) := by rw [h]
    _ = n := fta_reconstruction n hn

/-- m = n iff they have equal p-adic valuations at every prime p. -/
theorem factorization_eq_iff_valuations {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    m = n ↔ ∀ p : ℕ, m.factorization p = n.factorization p := by
  constructor
  · intro h; simp [h]
  · intro h
    apply factorization_determines_number hm hn
    ext p; exact h p

/-- n = 1 iff its factorization is identically zero (no prime factors). -/
theorem factorization_eq_zero_iff_one {n : ℕ} (hn : n ≠ 0) :
    n.factorization = 0 ↔ n = 1 := by
  constructor
  · intro h
    have : n.factorization.prod (· ^ ·) = 1 := by
      rw [h]; simp [Finsupp.prod]
    rwa [fta_reconstruction n hn] at this
  · intro h; rw [h, Nat.factorization_one]

/-- The exponent of a prime p in n equals n.factorization p. -/
theorem prime_exponent_eq_factorization {n p : ℕ} (hn : n ≠ 0) (hp : p.Prime) :
    n.factorization p = (n.factorization.prod (· ^ ·)).factorization p := by
  rw [fta_reconstruction n hn]

/-- For coprime m, n: their prime exponent maps have disjoint support. -/
theorem coprime_factorization_disjoint {m n : ℕ}
    (hcop : Nat.Coprime m n) :
    Disjoint m.factorization.support n.factorization.support :=
  Nat.coprime_iff_disjoint.mp hcop

-- ============================================================
-- Part VII: Computational Examples
-- ============================================================

/-- Example: 12 = 2² · 3¹. The factorization map encodes {2 ↦ 2, 3 ↦ 1}. -/
example : (12 : ℕ).factorization = Finsupp.single 2 2 + Finsupp.single 3 1 := by
  native_decide

/-- Example: primeFactors of 30 = {2, 3, 5} (equals factorization support). -/
example : (30 : ℕ).primeFactors = {2, 3, 5} := by native_decide

/-- Example: The Finsupp product {2 ↦ 2, 3 ↦ 1}.prod (·^·) = 12. -/
example : (Finsupp.single 2 2 + Finsupp.single 3 1 : ℕ →₀ ℕ).prod (· ^ ·) = 12 := by
  native_decide

/-- Example: The factorization of 1 is the zero Finsupp. -/
example : (1 : ℕ).factorization = 0 := Nat.factorization_one

/-- Example: Coprimality via disjoint support: gcd(12, 35) = 1. -/
example : Disjoint (12 : ℕ).factorization.support (35 : ℕ).factorization.support := by
  native_decide

end FundamentalArithmeticOQ01OQ01
