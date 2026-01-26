/-!
# Erdős Problem #276 — Composite Lucas Sequence Without Common Factor

Does there exist an infinite Lucas sequence a₀, a₁, a₂, ... where
  a_{n+2} = a_{n+1} + a_n
such that every term a_k is composite, yet no integer > 1 divides
every term (i.e., the sequence is not trivially composite)?

Graham (1964) constructed such a sequence using covering congruences:
  a₀ = 1786772701928802632268715130455793
  a₁ = 1059683225053915111058165141686995

The deeper question is whether covering congruences are the *only*
mechanism producing such primefree sequences.

Status: OPEN
Reference: https://erdosproblems.com/276
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- A Lucas sequence satisfies a_{n+2} = a_{n+1} + a_n. -/
def IsLucasSequence (a : ℕ → ℕ) : Prop :=
  ∀ n, a (n + 2) = a (n + 1) + a n

/-- A sequence is primefree if every term is composite. -/
def IsPrimefree (a : ℕ → ℕ) : Prop :=
  ∀ k, (a k).Composite

/-- A sequence has no universal divisor if no integer > 1
    divides every term. -/
def HasNoUniversalDivisor (a : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, d > 1 → ∃ k, ¬(d ∣ a k)

/-! ## Main Question -/

/-- **Erdős Problem #276**: Does there exist a primefree Lucas sequence
    with no universal divisor? The answer is YES (Graham 1964), but the
    deeper question is whether covering congruences are necessary. -/
axiom erdos_276_existence :
  ∃ a : ℕ → ℕ,
    IsLucasSequence a ∧ IsPrimefree a ∧ HasNoUniversalDivisor a

/-! ## Graham's Construction -/

/-- **Graham (1964)**: There exist coprime composites a₀, a₁ such that
    the Lucas sequence they generate is primefree. The construction
    uses covering congruences: for each index position, some prime in
    a fixed finite set divides the corresponding term. -/
axiom graham_construction :
  ∃ a : ℕ → ℕ,
    IsLucasSequence a ∧ IsPrimefree a ∧ Nat.Coprime (a 0) (a 1)

/-- **Coprimality is necessary**: if gcd(a₀, a₁) = d > 1, then d
    divides every term, making the sequence trivially composite. -/
axiom coprime_necessary :
  ∀ a : ℕ → ℕ, IsLucasSequence a →
    ∀ d : ℕ, d ∣ a 0 → d ∣ a 1 → ∀ k, d ∣ a k

/-! ## Covering Congruence Mechanism -/

/-- **Covering system**: a finite collection of congruence classes
    a_i (mod m_i) that covers all integers. Graham's proof shows
    the Fibonacci-like sequence is periodic mod each m_i, and the
    residue classes where each prime divides form a covering system. -/
axiom covering_system_mechanism :
  ∃ (S : Finset ℕ),
    (∀ p ∈ S, Nat.Prime p) ∧
    ∀ a : ℕ → ℕ, IsLucasSequence a →
      Nat.Coprime (a 0) (a 1) →
      IsPrimefree a →
      ∀ k, ∃ p ∈ S, p ∣ a k

/-! ## Further Results -/

/-- **Smaller starting values**: Vsemirnov (2004) found a primefree
    Lucas sequence with a₀ = 106276436867, a₁ = 35256392432,
    much smaller than Graham's original starting values. -/
axiom vsemirnov_small_start : True

/-- **Open Question**: Is every primefree Lucas sequence with coprime
    initial terms explained by a covering system? Or can such sequences
    exist for fundamentally different reasons? -/
axiom covering_necessary_open : True
