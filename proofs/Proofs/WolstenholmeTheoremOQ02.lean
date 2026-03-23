/-
Babbage's Theorem: C(2p-1, p-1) ≡ 1 (mod p²) for prime p ≥ 3.

Proof via Vandermonde identity:
  C(2p, p) = ∑_{k=0}^{p} C(p,k)² by Vandermonde
  Middle terms (1 ≤ k ≤ p-1) vanish mod p² since p | C(p,k)
  So C(2p, p) ≡ 1² + 1² = 2 (mod p²)
  Since C(2p, p) = 2·C(2p-1, p-1), cancel 2 to conclude.
-/
import Mathlib

open Nat Finset

namespace BabbageProof

/-- The central-ish binomial coefficient C(2p-1, p-1) -/
def centralBinomial (p : ℕ) : ℕ := Nat.choose (2 * p - 1) (p - 1)

/-
## Step 1: C(2p, p) = 2 * C(2p-1, p-1)
-/

lemma choose_two_p_eq (p : ℕ) (hp : 1 ≤ p) :
    Nat.choose (2 * p) p = 2 * centralBinomial p := by
  unfold centralBinomial
  have h1 : 2 * p - 1 + 1 = 2 * p := by omega
  have h2 : p - 1 + 1 = p := by omega
  have hpascal : Nat.choose (2 * p) p =
      Nat.choose (2 * p - 1) (p - 1) + Nat.choose (2 * p - 1) p := by
    have key := Nat.choose_succ_succ (2 * p - 1) (p - 1)
    simp only [Nat.succ_eq_add_one, h1, h2] at key
    exact key
  have hsymm : Nat.choose (2 * p - 1) p = Nat.choose (2 * p - 1) (p - 1) := by
    have h := Nat.choose_symm (show p ≤ 2 * p - 1 from by omega)
    rw [show 2 * p - 1 - p = p - 1 from by omega] at h
    exact h.symm
  linarith

/-
## Step 2: Vandermonde gives C(2p, p) = ∑ C(p,k)²
-/

lemma vandermonde_sq (p : ℕ) :
    Nat.choose (2 * p) p =
    ∑ k ∈ Finset.range (p + 1), (Nat.choose p k) ^ 2 := by
  rw [show 2 * p = p + p from by ring, Nat.add_choose_eq,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => Nat.choose p i * Nat.choose p j) p]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.choose_symm (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), sq]

/-
## Step 3: Decompose the sum
-/

lemma range_erase_zero (p : ℕ) (_hp : 1 ≤ p) :
    (Finset.range p).erase 0 = Finset.Ico 1 p := by
  ext k
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
  omega

lemma vandermonde_decomposed (p : ℕ) (h3 : 3 ≤ p) :
    ∑ k ∈ Finset.range (p + 1), (Nat.choose p k) ^ 2 =
    1 + (∑ k ∈ Finset.Ico 1 p, (Nat.choose p k) ^ 2) + 1 := by
  rw [Finset.sum_range_succ]
  simp only [Nat.choose_self, one_pow]
  have h0mem : (0 : ℕ) ∈ Finset.range p := Finset.mem_range.mpr (by omega)
  rw [← Finset.add_sum_erase _ _ h0mem, range_erase_zero p (by omega)]
  simp [Nat.choose_zero_right]

/-
## Step 4: p² | middle terms
-/

lemma prime_dvd_choose_self (p k : ℕ) (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ∣ Nat.choose p k := by
  apply hp.dvd_choose <;> omega

lemma prime_sq_dvd_choose_sq (p k : ℕ) (hp : p.Prime) (hk0 : 0 < k) (hkp : k < p) :
    p ^ 2 ∣ (Nat.choose p k) ^ 2 := by
  obtain ⟨c, hc⟩ := prime_dvd_choose_self p k hp hk0 hkp
  exact ⟨c ^ 2, by rw [hc]; ring⟩

lemma middle_sum_dvd (p : ℕ) (hp : p.Prime) :
    p ^ 2 ∣ ∑ k ∈ Finset.Ico 1 p, (Nat.choose p k) ^ 2 := by
  apply Finset.dvd_sum
  intro k hk
  have hm := Finset.mem_Ico.mp hk
  exact prime_sq_dvd_choose_sq p k hp hm.1 hm.2

/-
## Step 5: C(2p, p) ≡ 2 (mod p²)
-/

lemma two_lt_prime_sq (p : ℕ) (h3 : 3 ≤ p) : 2 < p ^ 2 := by nlinarith

lemma choose_two_p_mod (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    Nat.choose (2 * p) p % (p ^ 2) = 2 := by
  rw [vandermonde_sq, vandermonde_decomposed p h3]
  obtain ⟨c, hc⟩ := middle_sum_dvd p hp
  rw [hc, show 1 + p ^ 2 * c + 1 = 2 + p ^ 2 * c from by ring,
      Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (two_lt_prime_sq p h3)

/-
## Step 6: Cancel 2 to get C(2p-1, p-1) ≡ 1 (mod p²)
-/

lemma coprime_two_prime_sq (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    Nat.Coprime 2 (p ^ 2) := by
  apply Nat.Coprime.pow_right
  rw [Nat.coprime_comm]
  exact Nat.coprime_two_right.mpr (hp.odd_of_ne_two (by omega))

lemma centralBinomial_pos (p : ℕ) (hp : 1 ≤ p) : 0 < centralBinomial p := by
  unfold centralBinomial
  exact Nat.choose_pos (by omega)

theorem babbage (p : ℕ) (hp : p.Prime) (h3 : 3 ≤ p) :
    centralBinomial p % (p ^ 2) = 1 := by
  have h1 : 1 ≤ p := by omega
  -- From Vandermonde: 2 * centralBinomial p ≡ 2 (mod p²)
  have hmod : 2 * centralBinomial p % (p ^ 2) = 2 := by
    rw [← choose_two_p_eq p h1]; exact choose_two_p_mod p hp h3
  -- Extract: p² * q + 2 = 2 * centralBinomial p
  have hq := Nat.div_add_mod (2 * centralBinomial p) (p ^ 2)
  rw [hmod] at hq
  -- So p² | (2 * a - 2) = 2 * (a - 1)
  have hdvd_2a : p ^ 2 ∣ 2 * (centralBinomial p - 1) := by
    refine ⟨2 * centralBinomial p / p ^ 2, ?_⟩
    have := centralBinomial_pos p h1; omega
  -- Cancel 2 using coprimality
  have hcop := (coprime_two_prime_sq p hp h3).symm
  have hdvd_a : p ^ 2 ∣ (centralBinomial p - 1) :=
    hcop.dvd_of_dvd_mul_left hdvd_2a
  -- Conclude: a = p² * q + 1, so a % p² = 1
  obtain ⟨q, hq2⟩ := hdvd_a
  have ha : centralBinomial p = p ^ 2 * q + 1 := by
    have := centralBinomial_pos p h1; omega
  rw [ha, show p ^ 2 * q + 1 = 1 + p ^ 2 * q from by ring, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by nlinarith : 1 < p ^ 2)

end BabbageProof
