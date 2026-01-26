/-!
# Erdős Problem #428: Prime Offsets with Positive Density

Is there a set A ⊆ ℕ such that for infinitely many n, all of n - a are
prime for every a ∈ A with 0 < a < n, and
  liminf |A ∩ [1,x]| / π(x) > 0?

Erdős and Graham (1980) showed this holds with limsup replacing liminf,
assuming the prime k-tuple conjecture. The liminf version remains open.

The problem asks whether a set of "prime-generating offsets" can have
positive density relative to the prime counting function.

Reference: https://erdosproblems.com/428
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

/-! ## Prime Counting and Density -/

/-- The prime counting function π(n): number of primes ≤ n. -/
noncomputable def primeCounting (n : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range (n + 1))).card

/-- The density ratio |A ∩ [1,x]| / π(x) for a set A relative to primes. -/
noncomputable def primeDensityRatio (A : Set ℕ) (n : ℕ) : ℝ :=
  (A ∩ Set.Icc 1 n).ncard / (primeCounting n : ℝ)

/-! ## Prime Offset Property -/

/-- For a given n, all offsets a ∈ A with 0 < a < n yield n - a prime. -/
def AllOffsetsPrime (A : Set ℕ) (n : ℕ) : Prop :=
  ∀ a ∈ A, 0 < a → a < n → (n - a).Prime

/-! ## Main Conjecture -/

/-- Erdős Problem 428: Does there exist A ⊆ ℕ with positive prime density
    such that AllOffsetsPrime A n holds for infinitely many n? -/
def ErdosProblem428 : Prop :=
  ∃ A : Set ℕ,
    (∃ᶠ n in Filter.atTop, AllOffsetsPrime A n) ∧
    Filter.liminf (fun n => primeDensityRatio A n) Filter.atTop > 0

/-! ## Limsup Variant -/

/-- The limsup variant: same but with limsup instead of liminf.
    This holds under the prime k-tuple conjecture (Erdős-Graham). -/
def ErdosProblem428Limsup : Prop :=
  ∃ A : Set ℕ,
    (∃ᶠ n in Filter.atTop, AllOffsetsPrime A n) ∧
    Filter.limsup (fun n => primeDensityRatio A n) Filter.atTop > 0

/-- The liminf version implies the limsup version. -/
axiom liminf_implies_limsup :
    ErdosProblem428 → ErdosProblem428Limsup

/-! ## Prime k-Tuple Conjecture -/

/-- The prime k-tuple conjecture (Hardy-Littlewood): any admissible
    k-tuple pattern occurs infinitely often. -/
def PrimeKTupleConjecture : Prop :=
  ∀ H : Finset ℕ,
    (∀ p : ℕ, p.Prime → ∃ n : ℕ, ∀ h ∈ H, ¬(p ∣ (n + h))) →
    ∃ᶠ n in Filter.atTop, ∀ h ∈ H, (n + h).Prime

/-- Erdős-Graham: the k-tuple conjecture implies the limsup variant. -/
axiom erdos_graham_limsup :
    PrimeKTupleConjecture → ErdosProblem428Limsup

/-! ## Basic Properties -/

/-- The prime counting function is positive for n ≥ 2. -/
theorem primeCounting_pos (n : ℕ) (hn : 2 ≤ n) :
    0 < primeCounting n := by
  unfold primeCounting
  apply Finset.card_pos.mpr
  exact ⟨2, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_iff.mpr ⟨by omega, fun m hm => by omega⟩⟩⟩

/-- Singleton sets always satisfy AllOffsetsPrime for appropriate n. -/
theorem singleton_offset (a : ℕ) (n : ℕ) (ha : 0 < a) (han : a < n)
    (hp : (n - a).Prime) :
    AllOffsetsPrime {a} n := by
  intro x hx hx0 hxn
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact hp

/-- The empty set trivially satisfies AllOffsetsPrime but has zero density. -/
theorem empty_trivial (n : ℕ) : AllOffsetsPrime ∅ n := by
  intro a ha
  exact absurd ha (Set.not_mem_empty a)

/-- Finite sets have zero liminf prime density. -/
axiom finite_set_zero_density (A : Set ℕ) (hA : A.Finite) :
    Filter.liminf (fun n => primeDensityRatio A n) Filter.atTop = 0
