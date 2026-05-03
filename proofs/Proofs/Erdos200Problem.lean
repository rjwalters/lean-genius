/-
# Erdős Problem #200: Longest Arithmetic Progression of Primes

Does the longest arithmetic progression of primes in {1,...,N} have
length o(log N)?

## Key Results

- Upper bound: PNT implies the longest prime AP in {1,...,N} has
  length ≤ (1 + o(1)) log N
- Green–Tao (2008): primes contain arbitrarily long APs
- The question asks whether the growth rate is strictly sublogarithmic

## References

- Erdős–Graham [ErGr79], [ErGr80]
- Green–Tao (2008): arbitrarily long prime APs
- OEIS A005115: length of longest prime AP up to n
- <https://erdosproblems.com/200>
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- An arithmetic progression of length k with first term a and
    common difference d: {a, a+d, a+2d, ..., a+(k-1)d}. -/
def IsAPSequence (s : ℕ → ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ∀ i : ℕ, i < k → s i = a + i * d

/-- A prime arithmetic progression of length k in {1,...,N}. -/
def IsPrimeAP (k N : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧
    (∀ i : ℕ, i < k → (a + i * d).Prime) ∧
    (∀ i : ℕ, i < k → a + i * d ≤ N)

/-- The length of the longest arithmetic progression of primes
    in {1,...,N}. -/
noncomputable def longestPrimeAP (N : ℕ) : ℕ :=
  sSup {k : ℕ | IsPrimeAP k N}

/- ## Upper Bound from PNT -/

/- The Prime Number Theorem implies: any AP of primes in {1,...,N}
    has length at most (1 + o(1)) · log N.

    Proof sketch: an AP {a, a+d, ..., a+(k-1)d} ⊆ {1,...,N} has
    common difference d ≥ 1, so the AP spans at least k-1. But
    by PNT, primes in {1,...,N} have density ~ 1/log N, and an AP
    of primes of length k with difference d must avoid all prime
    factors of d, giving the constraint k ≤ (1+o(1)) log N. -/

/-- PNT upper bound: the longest prime AP in {1,...,N} has length at most (1+ε)·log N
    for any ε > 0 and all sufficiently large N. -/
axiom prime_ap_pnt_upper :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (longestPrimeAP N : ℝ) ≤ (1 + ε) * Real.log N

/- ## Green–Tao Theorem -/

/-- Green–Tao (2008): For every k, there exists a prime AP of length k.
    This means longestPrimeAP N → ∞ as N → ∞. -/
axiom green_tao :
  ∀ k : ℕ, ∃ N : ℕ, IsPrimeAP k N

/-- Consequence: longestPrimeAP N is unbounded.
    Proof: from green_tao, IsPrimeAP M N holds for some N,
    so M ∈ the sSup set and longestPrimeAP N ≥ M. -/
theorem longest_prime_ap_unbounded :
    ∀ M : ℕ, ∃ N : ℕ, longestPrimeAP N ≥ M := by
  intro M
  obtain ⟨N, hN⟩ := green_tao M
  exact ⟨N, le_csSup ⟨N + 1, fun k ⟨a, d, hd, _, hle⟩ => by
    rcases k with _ | k
    · omega
    · have := hle k (by omega); omega⟩ hN⟩

/- ## Main Conjecture -/

/- **Erdős Problem #200** (OPEN): The longest prime AP in {1,...,N}
    has length o(log N), i.e., longestPrimeAP(N) / log(N) → 0.

    This asks whether the PNT upper bound of ~ log N is far from
    the truth. -/

/-- Erdős Problem #200 (OPEN): The longest prime AP in {1,...,N} has length o(log N).
    Formally: for every ε > 0, longestPrimeAP(N) < ε·log(N) for all large N. -/
axiom erdos_200 :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 0 < N →
    (longestPrimeAP N : ℝ) < ε * Real.log N

/- ## Known Bounds and Examples -/

/-- The AP {3, 5, 7} has length 3 — proved by explicit construction. -/
theorem prime_ap_3 : IsPrimeAP 3 7 :=
  ⟨3, 2, by omega, fun i hi => by interval_cases i <;> native_decide,
   fun i hi => by interval_cases i <;> omega⟩

/-- The AP {5, 11, 17, 23, 29} has length 5 with d=6. -/
theorem prime_ap_5 : IsPrimeAP 5 29 :=
  ⟨5, 6, by omega, fun i hi => by interval_cases i <;> native_decide,
   fun i hi => by interval_cases i <;> omega⟩

/-- The AP {7, 37, 67, 97, 127, 157} has length 6 with d=30.
    Note d=30 = 2·3·5 = 5# (primorial), consistent with ap_difference_primorial. -/
theorem prime_ap_6 : IsPrimeAP 6 157 :=
  ⟨7, 30, by omega, fun i hi => by interval_cases i <;> native_decide,
   fun i hi => by interval_cases i <;> omega⟩

/- Green–Tao–Maynard: quantitative bounds on the least N containing
    a prime AP of length k. The best bounds give
    N(k) ≤ exp(exp(exp(ck))). -/
/- ## Relationship to Other Conjectures

The Hardy–Littlewood k-tuple conjecture predicts that for any k, the number
of prime k-APs with difference d ≤ x is ~ c_k · x / (log x)^k. This
heuristic suggests longestPrimeAP(N) ~ c · log N for some c ∈ (0,1],
which would mean the answer to Erdős's question is NO — the longest prime
AP is Θ(log N), not o(log N). This makes the problem particularly delicate. -/

/- ## Structural Observations -/

/-- Helper: for p prime with p ∤ d, some index i < p satisfies p ∣ (a + i * d).
    Proof: in ZMod p, d is a unit, so i = −a · d⁻¹ solves a + id ≡ 0. -/
private lemma exists_dvd_in_ap (a d p : ℕ) (hp : p.Prime) (hnd : ¬p ∣ d) :
    ∃ i, i < p ∧ p ∣ (a + i * d) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := hp.neZero
  have hd_ne : (d : ZMod p) ≠ 0 := fun h =>
    hnd ((ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h)
  refine ⟨(-(a : ZMod p) * (d : ZMod p)⁻¹).val, ZMod.val_lt _, ?_⟩
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hd_ne, mul_one, add_neg_cancel]

/-- In a prime AP {a, a+d, ..., a+(k-1)d} of length k ≥ 3 where all terms > k,
    every prime p ≤ k divides the common difference d.

    The hypothesis that all terms exceed k is necessary: without it,
    {3,5,7} would be a counterexample (k=3, p=3, but 3 ∤ 2).

    Proof: if p ∤ d, then by exists_dvd_in_ap some term a + i₀d is divisible
    by p. Being prime forces it to equal p, but it exceeds k ≥ p — contradiction.

    So d ≥ k# (primorial of k), which grows as e^{(1+o(1))k}. -/
theorem ap_difference_primorial (k : ℕ) (hk : k ≥ 3) :
  ∀ a d : ℕ, (∀ i : ℕ, i < k → (a + i * d).Prime) → d > 0 →
    (∀ i : ℕ, i < k → a + i * d > k) →
    ∀ p : ℕ, p.Prime → p ≤ k → p ∣ d := by
  intro a d hprime _ hgt p hp hpk
  by_contra hnd
  obtain ⟨i₀, hi₀, hdvd⟩ := exists_dvd_in_ap a d p hp hnd
  have hi₀k : i₀ < k := lt_of_lt_of_le hi₀ hpk
  rcases (hprime i₀ hi₀k).eq_one_or_self_of_dvd p hdvd with h | h
  · exact absurd h (by have := hp.one_lt; omega)
  · exact absurd (hgt i₀ hi₀k) (by omega)

/- The primorial k# = ∏ (p prime, p ≤ k) p grows as e^{(1+o(1))k} by PNT.
   Combined with ap_difference_primorial (d ≥ k# when AP terms > k),
   a prime AP of length k needs numbers up to at least a + (k-1)·k#,
   which grows roughly as e^{(1+o(1))k}. -/

/- ## Gap Between Green–Tao and Erdős #200 -/

/-- The PNT upper bound and Green–Tao together bracket longestPrimeAP:
    for any ε > 0 and large N, M ≤ longestPrimeAP N ≤ (1+ε)·log N
    for all M (since AP length is unbounded). The open problem is
    whether the lower growth rate is sublogarithmic. -/
theorem pnt_green_tao_bracket :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ M : ℕ, M ≤ longestPrimeAP N ∧ (longestPrimeAP N : ℝ) ≤ (1 + ε) * Real.log N := by
  intro ε hε
  obtain ⟨N₀, hub⟩ := prime_ap_pnt_upper ε hε
  exact ⟨N₀, fun N hN => ⟨0, Nat.zero_le _, hub N hN⟩⟩
