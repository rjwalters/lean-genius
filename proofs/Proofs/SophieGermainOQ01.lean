import Proofs.SophieGermain
import Proofs.SophieGermainOQ02
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic

/-
# Are There Infinitely Many Sophie Germain Primes?

## Open Question (sophie-germain-oq-01)

The Sophie Germain Prime Conjecture asks: is the set of Sophie Germain primes
(primes p where 2p+1 is also prime) infinite?

**Status**: OPEN — No proof or disproof is known as of 2026.

## Historical Motivation: Sophie Germain's Theorem on FLT

Sophie Germain (1776–1831) studied these primes in connection with Fermat's Last
Theorem. She proved that if p is an odd Sophie Germain prime, then any solution
x^p + y^p = z^p must satisfy p ∣ xyz (Case I of FLT holds for exponent p).
This result — applying to every Sophie Germain prime — gave the first general
progress on FLT since Euler's proof for n=3.

## What Is Known About Infinitude

The conjecture is closely analogous to the twin prime conjecture and faces the
same fundamental barrier: **Selberg's parity obstruction** (1950s). Elementary
sieves cannot distinguish between numbers with even vs. odd numbers of prime
factors, preventing them from proving infinitely many simultaneous primality
conditions.

What IS known unconditionally:
- **Brun (1919)**: The series ∑_{p SG} 1/p converges (SG primes are "sparse").
- **Sieve upper bound**: π_SG(x) = O(x / (ln x)²), matching the HL prediction up
  to constant. No unconditional lower bound better than O(1) is known.

The Hardy-Littlewood conjecture (1923) predicts:
  π_SG(x) ~ 2C₂ · x / (ln x)²
where C₂ ≈ 0.6602 is the twin prime constant.

## Key Results Formalized Here

1. **Equivalence with safe prime conjecture**: SGC ↔ infinitely many safe primes q = 2p+1
2. **No-max formulation**: SGC ↔ no natural number bounds all SG primes
3. **Extended examples**: 25 verified SG primes (15 new beyond the parent's 10)
4. **Conditional consequences**: Under SGC, safe primes are infinite, primes ≡ 11
   (mod 12) are infinite, no finite set covers all SG primes

Axiom count: 1 (inherits `sophie_germain_conjecture` from parent file).
-/

namespace SophieGermainOQ01

open SophieGermain

/-! ## The Safe Prime Conjecture -/

/-- The safe prime conjecture: there are infinitely many safe primes. -/
def SafePrimeConjecture : Prop := ∀ N : ℕ, ∃ q : ℕ, q > N ∧ IsSafePrime q

/-! ## Extended Examples of Sophie Germain Primes

The parent file verifies 10 SG primes: 2, 3, 5, 11, 23, 29, 41, 53, 83, 89.
We extend this to 25 with computational proofs. -/

theorem sg_113 : IsSophieGermainPrime 113 := by constructor <;> decide
theorem sg_131 : IsSophieGermainPrime 131 := by constructor <;> decide
theorem sg_173 : IsSophieGermainPrime 173 := by constructor <;> decide
theorem sg_191 : IsSophieGermainPrime 191 := by constructor <;> decide
theorem sg_233 : IsSophieGermainPrime 233 := by constructor <;> decide
theorem sg_239 : IsSophieGermainPrime 239 := by constructor <;> decide
theorem sg_251 : IsSophieGermainPrime 251 := by constructor <;> decide
theorem sg_281 : IsSophieGermainPrime 281 := by constructor <;> decide
theorem sg_293 : IsSophieGermainPrime 293 := by constructor <;> decide
theorem sg_359 : IsSophieGermainPrime 359 := by constructor <;> decide
theorem sg_419 : IsSophieGermainPrime 419 := by constructor <;> decide
theorem sg_431 : IsSophieGermainPrime 431 := by constructor <;> decide
theorem sg_443 : IsSophieGermainPrime 443 := by constructor <;> decide
theorem sg_491 : IsSophieGermainPrime 491 := by constructor <;> decide
theorem sg_509 : IsSophieGermainPrime 509 := by constructor <;> decide

/-- At least 25 Sophie Germain primes exist. The full list:
    {2, 3, 5, 11, 23, 29, 41, 53, 83, 89, 113, 131, 173, 191, 233,
     239, 251, 281, 293, 359, 419, 431, 443, 491, 509} -/
theorem exists_twentyfive_sg_primes :
    IsSophieGermainPrime 2 ∧ IsSophieGermainPrime 3 ∧ IsSophieGermainPrime 5 ∧
    IsSophieGermainPrime 11 ∧ IsSophieGermainPrime 23 ∧ IsSophieGermainPrime 29 ∧
    IsSophieGermainPrime 41 ∧ IsSophieGermainPrime 53 ∧ IsSophieGermainPrime 83 ∧
    IsSophieGermainPrime 89 ∧ IsSophieGermainPrime 113 ∧ IsSophieGermainPrime 131 ∧
    IsSophieGermainPrime 173 ∧ IsSophieGermainPrime 191 ∧ IsSophieGermainPrime 233 ∧
    IsSophieGermainPrime 239 ∧ IsSophieGermainPrime 251 ∧ IsSophieGermainPrime 281 ∧
    IsSophieGermainPrime 293 ∧ IsSophieGermainPrime 359 ∧ IsSophieGermainPrime 419 ∧
    IsSophieGermainPrime 431 ∧ IsSophieGermainPrime 443 ∧ IsSophieGermainPrime 491 ∧
    IsSophieGermainPrime 509 :=
  ⟨sg_2, sg_3, sg_5, sg_11, sg_23, sg_29, sg_41, sg_53, sg_83, sg_89,
   sg_113, sg_131, sg_173, sg_191, sg_233, sg_239, sg_251, sg_281, sg_293,
   sg_359, sg_419, sg_431, sg_443, sg_491, sg_509⟩

/-! ## Equivalent Formulations of the Conjecture -/

/-- SGC is equivalent to the set of SG primes being unbounded above.
    This is the most direct formulation of "infinitely many." -/
theorem sgc_iff_unbounded :
    SophieGermainConjecture ↔ ¬ ∃ M : ℕ, ∀ p : ℕ, IsSophieGermainPrime p → p ≤ M := by
  constructor
  · -- SGC → ¬∃ bound: given any claimed bound M, SGC produces a larger SG prime
    intro hsgc ⟨M, hM⟩
    obtain ⟨p, hp_gt, hp_sg⟩ := hsgc M
    exact absurd (hM p hp_sg) (by omega)
  · -- ¬∃ bound → SGC: for any N, the absence of a bound gives a SG prime > N
    intro hno N
    push_neg at hno
    obtain ⟨p, hp_sg, hp_gt⟩ := hno N
    exact ⟨p, hp_gt, hp_sg⟩

/-- Helper: (2*p+1 - 1)/2 = p for any natural p. -/
private lemma half_two_mul_add_one (p : ℕ) : (2 * p + 1 - 1) / 2 = p := by
  rw [show 2 * p + 1 - 1 = 2 * p from by omega]
  exact Nat.mul_div_cancel_left p (by decide)

/-- Helper: 2*((q-1)/2) + 1 = q when q is odd (q % 2 = 1). -/
private lemma two_mul_half_pred_add_one (q : ℕ) (hq : q % 2 = 1) :
    2 * ((q - 1) / 2) + 1 = q := by omega

/-- The Sophie Germain Conjecture implies the Safe Prime Conjecture.
    Proof: if p > N is a Sophie Germain prime, then q = 2p+1 > N is a safe prime. -/
theorem sgc_implies_safe_prime_conjecture :
    SophieGermainConjecture → SafePrimeConjecture := by
  intro hsgc N
  obtain ⟨p, hp_gt, ⟨hp_prime, hsp_prime⟩⟩ := hsgc N
  refine ⟨2 * p + 1, by omega, hsp_prime, by omega, ?_⟩
  rw [half_two_mul_add_one p]
  exact hp_prime

/-- The Safe Prime Conjecture implies the Sophie Germain Conjecture.
    Proof: a safe prime q > 2N+1 gives p = (q-1)/2 > N with both p and 2p+1 = q prime. -/
theorem safe_prime_conjecture_implies_sgc :
    SafePrimeConjecture → SophieGermainConjecture := by
  intro hspc N
  -- Request a safe prime beyond 2N+1 so that p = (q-1)/2 exceeds N
  obtain ⟨q, hq_gt, ⟨hq_prime, hq_odd, hp_prime⟩⟩ := hspc (2 * N + 1)
  refine ⟨(q - 1) / 2, ?_, hp_prime, ?_⟩
  · -- (q-1)/2 > N: from q > 2N+1 and q odd → q ≥ 2N+3 → q-1 ≥ 2N+2 → (q-1)/2 ≥ N+1
    have h_q_ge : q ≥ 2 * N + 3 := by omega
    have h_pred_ge : 2 * N + 2 ≤ q - 1 := by omega
    have h_div_mono : (2 * N + 2) / 2 ≤ (q - 1) / 2 := Nat.div_le_div_right h_pred_ge
    have h_div_val : (2 * N + 2) / 2 = N + 1 := by
      rw [show 2 * N + 2 = 2 * (N + 1) from by ring]
      exact Nat.mul_div_cancel_left (N + 1) (by decide)
    omega
  · -- Nat.Prime (2 * ((q-1)/2) + 1) = Nat.Prime q
    rw [two_mul_half_pred_add_one q hq_odd]
    exact hq_prime

/-- The Sophie Germain Conjecture and Safe Prime Conjecture are equivalent:
    the bijection p ↔ 2p+1 between SG primes and safe primes is monotone increasing. -/
theorem sgc_iff_safe_prime_conjecture :
    SophieGermainConjecture ↔ SafePrimeConjecture :=
  ⟨sgc_implies_safe_prime_conjecture, safe_prime_conjecture_implies_sgc⟩

/-- Unfolding: SGC is exactly the statement that p and 2p+1 can be simultaneously
    prime for arbitrarily large p. Useful for concise reformulations. -/
theorem sgc_iff_prime_pairs :
    SophieGermainConjecture ↔
    (∀ N : ℕ, ∃ p : ℕ, p > N ∧ Nat.Prime p ∧ Nat.Prime (2 * p + 1)) := by
  simp only [SophieGermainConjecture, IsSophieGermainPrime]

/-! ## Conditional Consequences Under the SGC Axiom -/

/-- Under the Sophie Germain Conjecture, safe primes are infinite. -/
theorem infinite_safe_primes (N : ℕ) :
    ∃ q : ℕ, q > N ∧ IsSafePrime q :=
  sgc_implies_safe_prime_conjecture sophie_germain_conjecture N

/-- Under the Sophie Germain Conjecture, primes ≡ 11 (mod 12) are infinite.
    Proof: For any SG prime p > max(N,3), the safe prime 2p+1 > N satisfies
    2p+1 ≡ 11 (mod 12) by the structure theorem in the parent file. -/
theorem infinite_primes_mod_twelve (N : ℕ) :
    ∃ q : ℕ, q > N ∧ Nat.Prime q ∧ q % 12 = 11 := by
  obtain ⟨p, hp_gt, hp_sg⟩ := sophie_germain_conjecture (max N 3)
  have hp3 : p > 3 := Nat.lt_of_le_of_lt (Nat.le_max_right N 3) hp_gt
  have hN : p > N := Nat.lt_of_le_of_lt (Nat.le_max_left N 3) hp_gt
  exact ⟨2 * p + 1, by omega, hp_sg.2, safe_prime_mod_twelve p hp_sg hp3⟩

/-- Under the Sophie Germain Conjecture, no finite set covers all SG primes:
    every Finset is missing some Sophie Germain prime. -/
theorem no_finite_cover (S : Finset ℕ) :
    ∃ p : ℕ, IsSophieGermainPrime p ∧ p ∉ S := by
  obtain ⟨p, hp_gt, hp_sg⟩ := sophie_germain_conjecture (S.sup id)
  refine ⟨p, hp_sg, ?_⟩
  intro hp_mem
  have : p ≤ S.sup id := Finset.le_sup (f := id) hp_mem
  omega

end SophieGermainOQ01
