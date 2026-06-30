import Mathlib

/-
# Erdős 307 — OQ-02-OQ-01: Disjointness of Prime Solution Sets

## Research Problem: erdos-307-oq-02-oq-01

Discharges the `prime_sets_disjoint` sorry documented in `Erdos307OQ02.lean`:

  If P and Q are finite sets of primes with
    (Σ_{p ∈ P} 1/p) · (Σ_{q ∈ Q} 1/q) = 1,
  then P ∩ Q = ∅.

The documented approach was "p-adic valuation theory". We give a fully
elementary, axiom-free proof that captures exactly the p-adic content
without invoking `padicValRat`:

  * Write Σ_{p ∈ P} 1/p = NP / DP where
      DP := ∏_{p ∈ P} p          (squarefree, the denominator)
      NP := Σ_{p ∈ P} ∏_{q ≠ p} q (the numerator).
  * The hypothesis (NP/DP)(NQ/DQ) = 1 clears denominators to the INTEGER
    identity  NP · NQ = DP · DQ.
  * For a prime p₀ ∈ P, reducing NP modulo p₀ kills every summand except
    the q = p₀ term (which is a product of primes all ≠ p₀, hence a unit
    in 𝔽_{p₀}). So p₀ ∤ NP. This is precisely v_{p₀}(Σ 1/p) = -1.
  * If p₀ ∈ P ∩ Q then p₀ ∤ NP and p₀ ∤ NQ, so p₀ ∤ NP·NQ; but p₀ ∣ DP
    and p₀ ∣ DQ give p₀ ∣ DP·DQ = NP·NQ. Contradiction.

Tags: number-theory, primes, p-adic-valuation, egyptian-fractions
-/

open Finset BigOperators

namespace Erdos307OQ02OQ01

-- ============================================================
-- Part I: Setup (mirrors the parent file)
-- ============================================================

/-- Sum of reciprocals of elements in a finite set. -/
noncomputable def reciprocalSum (S : Finset ℕ) : ℚ :=
  ∑ n ∈ S, (n : ℚ)⁻¹

/-- Product of two reciprocal sums. -/
noncomputable def reciprocalProduct (P Q : Finset ℕ) : ℚ :=
  reciprocalSum P * reciprocalSum Q

/-- A set of primes: every element is prime. -/
def IsSetOfPrimes (S : Finset ℕ) : Prop :=
  ∀ p ∈ S, Nat.Prime p

/-- The integer numerator of `reciprocalSum`:  Σ_{p ∈ P} ∏_{q ∈ P\{p}} q. -/
def primeNumer (P : Finset ℕ) : ℕ :=
  ∑ p ∈ P, ∏ q ∈ P.erase p, q

/-- The integer denominator of `reciprocalSum`:  ∏_{p ∈ P} p. -/
def primeDenom (P : Finset ℕ) : ℕ :=
  ∏ p ∈ P, p

-- ============================================================
-- Part II: The numerator / denominator identity over ℚ
-- ============================================================

/-- Clearing denominators:  (Σ 1/p) · (∏ p) = Σ_{p} ∏_{q ≠ p} q.
    Requires only that no element is `0` (true for primes). -/
lemma reciprocalSum_mul_denom (P : Finset ℕ) (hP : ∀ p ∈ P, p ≠ 0) :
    reciprocalSum P * (primeDenom P : ℚ) = (primeNumer P : ℚ) := by
  unfold reciprocalSum primeDenom primeNumer
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpne : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hP p hp)
  rw [← Finset.mul_prod_erase P (fun q => (q : ℚ)) hp, inv_mul_cancel_left₀ hpne]

/-- The cleared-denominator INTEGER identity.  From `(Σ1/p)(Σ1/q) = 1` we get
    `NP · NQ = DP · DQ` in ℕ. -/
lemma primeNumer_mul_eq (P Q : Finset ℕ)
    (hP : ∀ p ∈ P, p ≠ 0) (hQ : ∀ q ∈ Q, q ≠ 0)
    (h : reciprocalProduct P Q = 1) :
    primeNumer P * primeNumer Q = primeDenom P * primeDenom Q := by
  have hA := reciprocalSum_mul_denom P hP
  have hB := reciprocalSum_mul_denom Q hQ
  unfold reciprocalProduct at h
  have key : (primeNumer P : ℚ) * (primeNumer Q : ℚ)
      = (primeDenom P : ℚ) * (primeDenom Q : ℚ) := by
    have e : (primeNumer P : ℚ) * (primeNumer Q : ℚ)
        = (reciprocalSum P * reciprocalSum Q)
            * ((primeDenom P : ℚ) * (primeDenom Q : ℚ)) := by
      rw [← hA, ← hB]; ring
    rw [e, h, one_mul]
  exact_mod_cast key

-- ============================================================
-- Part III: The p-adic core — p₀ ∤ numerator
-- ============================================================

/-- For a prime `p₀ ∈ P` (with `P` a set of primes), `p₀` does NOT divide the
    numerator `NP`.  Equivalently `v_{p₀}(Σ_{p∈P} 1/p) = -1`.

    Proof: reduce `NP = Σ_p ∏_{q≠p} q` modulo `p₀` in the field `𝔽_{p₀}`.
    Every summand with `p ≠ p₀` contains the factor `p₀`, hence vanishes; the
    `p = p₀` summand is `∏_{q ≠ p₀} q`, a product of primes all distinct from
    `p₀`, hence a nonzero product in the field. -/
lemma prime_not_dvd_primeNumer (P : Finset ℕ) (hP : IsSetOfPrimes P)
    {p₀ : ℕ} (hp₀ : p₀ ∈ P) : ¬ (p₀ ∣ primeNumer P) := by
  have hp₀prime : Nat.Prime p₀ := hP p₀ hp₀
  haveI : Fact (Nat.Prime p₀) := ⟨hp₀prime⟩
  haveI : NeZero p₀ := ⟨hp₀prime.pos.ne'⟩
  -- Reduce `NP` modulo `p₀`: only the `p = p₀` summand survives.
  have hcast : ((primeNumer P : ℕ) : ZMod p₀) = ∏ q ∈ P.erase p₀, (q : ZMod p₀) := by
    unfold primeNumer
    push_cast
    exact Finset.sum_eq_single_of_mem p₀ hp₀ (fun b _ hbne =>
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hbne, hp₀⟩)
        (ZMod.natCast_self p₀))
  -- That surviving product is a nonempty product of nonzero units → nonzero.
  have hne : ((primeNumer P : ℕ) : ZMod p₀) ≠ 0 := by
    rw [hcast, Finset.prod_ne_zero_iff]
    intro q hq
    rw [Finset.mem_erase] at hq
    have hqprime : Nat.Prime q := hP q hq.2
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun hdvdq => hq.1 ((Nat.prime_dvd_prime_iff_eq hp₀prime hqprime).mp hdvdq).symm
  -- A divisor would force the cast to vanish.
  intro hdvd
  exact hne ((ZMod.natCast_eq_zero_iff _ _).mpr hdvd)

-- ============================================================
-- Part IV: Main theorem
-- ============================================================

/-- **prime_sets_disjoint** (was a documented sorry in `Erdos307OQ02.lean`).

    If `P, Q` are finite sets of primes whose reciprocal sums multiply to `1`,
    then `P ∩ Q = ∅`. -/
theorem prime_sets_disjoint {P Q : Finset ℕ} (hP : IsSetOfPrimes P)
    (hQ : IsSetOfPrimes Q) (hPQ : reciprocalProduct P Q = 1) :
    P ∩ Q = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p₀ hmem
  rw [Finset.mem_inter] at hmem
  obtain ⟨hp₀P, hp₀Q⟩ := hmem
  have hp₀prime : Nat.Prime p₀ := hP p₀ hp₀P
  -- p₀ divides neither numerator.
  have hnP : ¬ p₀ ∣ primeNumer P := prime_not_dvd_primeNumer P hP hp₀P
  have hnQ : ¬ p₀ ∣ primeNumer Q := prime_not_dvd_primeNumer Q hQ hp₀Q
  have hnPQ : ¬ p₀ ∣ primeNumer P * primeNumer Q := by
    rw [hp₀prime.dvd_mul]; exact not_or.mpr ⟨hnP, hnQ⟩
  -- but p₀ divides both denominators, hence their product.
  have hdP : p₀ ∣ primeDenom P := by
    unfold primeDenom; exact Finset.dvd_prod_of_mem (fun p => p) hp₀P
  have heq := primeNumer_mul_eq P Q
    (fun p hp => (hP p hp).pos.ne') (fun q hq => (hQ q hq).pos.ne') hPQ
  have hdvd : p₀ ∣ primeNumer P * primeNumer Q := by
    rw [heq]; exact hdP.mul_right _
  exact hnPQ hdvd

/-
  Result: `prime_sets_disjoint` is fully proved — 0 sorries, 0 axioms.

  This discharges item (1) of "Part VI: Documentation of Remaining Sorries"
  in `Erdos307OQ02.lean`.  The p-adic valuation content (v_{p₀} = -1 for each
  p₀ in a prime-reciprocal sum) is captured elementarily by a single mod-p₀
  reduction in `prime_not_dvd_primeNumer`, avoiding any `padicValRat` machinery.

  Remaining from the parent: `prime_set_size_lower_bound` (|P ∪ Q| ≥ 60), which
  needs a verified Mertens-type computational bound and is independent of this.
-/

end Erdos307OQ02OQ01
