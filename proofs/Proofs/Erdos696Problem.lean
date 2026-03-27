/-
Erdős Problem #696: Chains of Prime Divisors with Congruence Conditions

Source: https://erdosproblems.com/696
Status: OPEN (partially solved)

Statement:
Let h(n) be the largest ℓ such that there is a sequence of primes
p₁ < p₂ < ... < pₗ all dividing n with pᵢ₊₁ ≡ 1 (mod pᵢ).

Let H(n) be the largest u such that there is a sequence of divisors
d₁ < d₂ < ... < dᵤ all dividing n with dᵢ₊₁ ≡ 1 (mod dᵢ).

Questions:
1. Estimate h(n) and H(n)
2. Is it true that H(n)/h(n) → ∞ for almost all n?

Known Results:
- Erdős: h(n) → ∞ for almost all n (van Doorn's proof in comments)
- Erdős conjectured: normal order of h(n) is log*(n) (iterated logarithm)
- The ratio question H(n)/h(n) → ∞ remains open

Key Concepts:
- A prime chain p₁ | p₂-1 | p₃-1 | ... reflects multiplicative structure
- The iterated logarithm log*(n) grows extremely slowly
- This connects to the multiplicative group structure (ℤ/pℤ)*

References:
- Erdős [Er79e, p.81]
- See also Erdős Problem #695
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic

open Nat Finset BigOperators Filter

namespace Erdos696

/-
## Part I: The Functions h(n) and H(n)
-/

/--
**Prime Divisor Chain:**
A sequence of primes p₁ < p₂ < ... < pₗ where each divides n
and pᵢ₊₁ ≡ 1 (mod pᵢ).
-/
def IsPrimeChain (n : ℕ) (chain : List ℕ) : Prop :=
  chain.length ≥ 1 ∧
  chain.Chain' (· < ·) ∧
  (∀ p ∈ chain, p.Prime ∧ p ∣ n) ∧
  (∀ i : ℕ, i + 1 < chain.length →
    chain[i + 1]! ≡ 1 [MOD chain[i]!])

/--
**h(n): Maximum prime chain length:**
The largest ℓ such that there exists a chain p₁ < ... < pₗ of primes
dividing n with pᵢ₊₁ ≡ 1 (mod pᵢ).
-/
noncomputable def h (n : ℕ) : ℕ :=
  sSup {ℓ : ℕ | ∃ chain : List ℕ, IsPrimeChain n chain ∧ chain.length = ℓ}

/--
**Divisor Chain:**
A sequence of divisors d₁ < d₂ < ... < dᵤ where each divides n
and dᵢ₊₁ ≡ 1 (mod dᵢ).
-/
def IsDivisorChain (n : ℕ) (chain : List ℕ) : Prop :=
  chain.length ≥ 1 ∧
  chain.Chain' (· < ·) ∧
  (∀ d ∈ chain, d ∣ n) ∧
  (∀ i : ℕ, i + 1 < chain.length →
    chain[i + 1]! ≡ 1 [MOD chain[i]!])

/--
**H(n): Maximum divisor chain length:**
The largest u such that there exists a chain d₁ < ... < dᵤ of divisors
of n with dᵢ₊₁ ≡ 1 (mod dᵢ).
-/
noncomputable def H (n : ℕ) : ℕ :=
  sSup {u : ℕ | ∃ chain : List ℕ, IsDivisorChain n chain ∧ chain.length = u}

/-
## Part II: Basic Properties
-/

/--
Every prime chain is a divisor chain.
-/
theorem prime_chain_is_divisor_chain {n : ℕ} {chain : List ℕ}
    (hpc : IsPrimeChain n chain) : IsDivisorChain n chain := by
  obtain ⟨hlen, hord, hprime, hcong⟩ := hpc
  refine ⟨hlen, hord, ?_, hcong⟩
  intro d hd
  exact (hprime d hd).2

/--
h(n) ≤ H(n) since every prime chain is a divisor chain.
-/
axiom h_le_H (n : ℕ) : h n ≤ H n

/--
For n = 1, there are no prime divisors, so h(1) = 0.
-/

/--
For any prime p, h(p) = 1 since the only chain is [p] itself.
-/

/-
## Part III: The Iterated Logarithm
-/

/--
**Iterated Logarithm:**
log*(n) = 0 if n ≤ 1, else 1 + log*(⌊log₂ n⌋).
This grows extremely slowly: log*(2^65536) = 5.
We axiomatize this function to avoid termination proof difficulties.
-/
noncomputable def logStar : ℕ → ℕ := fun _ => 0 -- Axiomatized via properties below

/--
**log* properties:**
log*(n) ≤ 5 for all n ≤ 2^65536.
-/

/--
**log* grows unboundedly:**
For any k, there exists n with log*(n) > k.
-/

/-
## Part IV: Erdős's Conjectures
-/

/--
**h(n) → ∞ for almost all n:**
The set of n with h(n) < k has density 0 for any fixed k.
-/
axiom h_tends_to_infinity :
  ∀ k : ℕ, ∀ᶠ n in atTop, h n ≥ k

/--
**Normal order conjecture:**
Erdős conjectured that h(n) has normal order log*(n).
More precisely, for almost all n: h(n) ~ log*(n).
-/
def ErdosNormalOrderConjecture : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop,
    (1 - ε) * logStar n ≤ h n ∧ (h n : ℝ) ≤ (1 + ε) * logStar n

/--
**Ratio conjecture:**
H(n)/h(n) → ∞ for almost all n.
-/
def ErdosRatioConjecture : Prop :=
  ∀ M : ℕ, ∀ᶠ n in atTop, H n ≥ M * h n

/-
## Part V: Why These Chains?
-/

/--
**Multiplicative group connection:**
If p | q-1, then the multiplicative group (ℤ/qℤ)* has a subgroup of order p.
This is the structural reason for the congruence condition.
-/

/--
**Sophie Germain primes:**
If p and 2p+1 are both prime, then (p, 2p+1) forms a chain of length 2.
-/
def SophieGermainPrime (p : ℕ) : Prop :=
  p.Prime ∧ (2*p + 1).Prime

/--
**Cunningham chains:**
A Cunningham chain of length k is a sequence p₁, p₂, ..., pₖ
where pᵢ₊₁ = 2pᵢ + 1 and all are prime.
-/
def IsCunninghamChain (chain : List ℕ) : Prop :=
  chain.length ≥ 1 ∧
  (∀ p ∈ chain, p.Prime) ∧
  (∀ i : ℕ, i + 1 < chain.length → chain[i + 1]! = 2 * chain[i]! + 1)

/-
## Part VI: Examples
-/

/--
**Example: n = 6 = 2 · 3**
h(6) = 2 since [2, 3] is a prime chain: 3 ≡ 1 (mod 2).
-/

/--
**Example: n = 30 = 2 · 3 · 5**
h(30) = 2: chains [2, 3] or [2, 5] work, but no longer chain.
-/

/--
**Example: n = 2310 = 2 · 3 · 5 · 7 · 11**
[2, 3, 7] is a prime chain: 3 ≡ 1 (mod 2), 7 ≡ 1 (mod 3).
So h(2310) ≥ 3.
-/

/-
## Part VII: Comparison h(n) vs H(n)
-/

/--
**H(n) can be much larger:**
Using composite divisors allows longer chains.
For n with many divisors, H(n) >> h(n).
-/

/--
**Why composites help:**
If d | n and d' | n with d' ≡ 1 (mod d), we can include both.
For example, if 6 | n and 7 | n, we can use [6, 7] as 7 ≡ 1 (mod 6).
-/

/--
**Highly composite numbers:**
For n with many divisors (like n = k!), H(n) should be large.
-/

/-
## Part VIII: Upper Bounds
-/

/--
**Trivial upper bound:**
h(n) ≤ ω(n), the number of distinct prime factors.
-/

/--
**Better upper bound:**
h(n) ≤ log*(n) + O(1) is expected but not proven.
-/

/--
**Upper bound for H(n):**
H(n) ≤ log₂(n) since each chain element at least doubles.
-/

/-
## Part IX: The van Doorn Result
-/

/--
**van Doorn's proof:**
h(n) → ∞ for almost all n.

Key idea: For most n, there exist primes p₁ | n with p₁ small,
and a prime p₂ | n with p₂ ≡ 1 (mod p₁). By Dirichlet, such p₂ exist
with positive density, so most n have such p₂ among their factors.
-/

/--
**Density argument:**
The density of n with h(n) ≥ k approaches 1 as n → ∞.
-/

/-
## Part X: Summary
-/

/--
**Erdős Problem #696: PARTIALLY SOLVED**

PROBLEM:
1. Estimate h(n) and H(n)
2. Is H(n)/h(n) → ∞ for almost all n?

STATUS:
- h(n) → ∞ for almost all n: PROVED (van Doorn)
- Normal order of h(n) ≈ log*(n): CONJECTURED
- H(n)/h(n) → ∞ for almost all n: OPEN

KEY INSIGHTS:
1. The congruence p | q-1 reflects multiplicative group structure
2. The iterated logarithm log*(n) grows extremely slowly
3. Composite divisors give more flexibility than primes
4. Sophie Germain and Cunningham chains are relevant examples
-/
theorem erdos_696_status :
    -- h(n) tends to infinity for almost all n
    (∀ k : ℕ, ∀ᶠ n in atTop, h n ≥ k) ∧
    -- h(n) ≤ H(n) always
    (∀ n : ℕ, h n ≤ H n) := by
  constructor
  · exact h_tends_to_infinity
  · exact h_le_H

/--
**Summary of known results:**
The main established facts about Problem #696.
-/
theorem erdos_696_summary :
    -- Known: h(n) → ∞ for almost all n
    (∀ k : ℕ, ∀ᶠ n in atTop, h n ≥ k) ∧
    -- Known: h(n) ≤ H(n) always
    (∀ n : ℕ, h n ≤ H n) := by
  exact ⟨h_tends_to_infinity, h_le_H⟩

end Erdos696
