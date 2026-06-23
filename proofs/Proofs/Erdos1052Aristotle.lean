/-
  Aristotle targets for Erdős Problem #1052 (Unitary Perfect Numbers)
  Routine supporting lemmas for automated proof search.
  See Erdos1052Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (divisor sums, coprimality, etc.)
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1052Aristotle

/-- A proper unitary divisor of n is a divisor d with gcd(d, n/d) = 1 and d < n. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ d.Coprime (n / d))

/-- The unitary divisor function: sum of all unitary divisors of n (including n itself). -/
def unitaryDivisorSum (n : ℕ) : ℕ :=
  ((Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d))).sum id

/-- σ*(1) = 1: the only unitary divisor of 1 is 1 itself. -/
theorem unitaryDivisorSum_one : unitaryDivisorSum 1 = 1 := by native_decide

/-
PROBLEM
σ*(p) = 1 + p for prime p: the unitary divisors of a prime are 1 and p.

PROVIDED SOLUTION
Unfold unitaryDivisorSum. Show the filter set equals {1, p} using hp.eq_one_or_self_of_dvd. Then use Finset.sum_pair.
-/
theorem unitaryDivisorSum_prime {p : ℕ} (hp : p.Prime) :
    unitaryDivisorSum p = 1 + p := by
      unfold unitaryDivisorSum;
      rw [ Finset.sum_eq_add ( 1 : ℕ ) ( p : ℕ ) ] <;> norm_num [ hp.ne_zero, hp.ne_one ];
      · exact hp.ne_one.symm;
      · intro c hc₁ hc₂ hc₃ hc₄ hc₅; rw [ Nat.dvd_prime hp ] at hc₃; aesop;
      · exact ⟨ hp.pos, by rw [ Nat.div_self hp.pos ] ; norm_num ⟩

/-
PROBLEM
If d > 1 and d ∣ p^k for prime p, then p ∣ d.

PROVIDED SOLUTION
Since d > 1, there exists a prime q dividing d. Then q | p^k, so q | p (prime dvd prime power). Since p is prime and q | p, q = p. Hence p | d.
-/
private theorem prime_dvd_of_dvd_prime_pow {p d k : ℕ} (hp : p.Prime) (hd : 1 < d) (hdvd : d ∣ p ^ k) :
    p ∣ d := by
      rw [ Nat.dvd_prime_pow hp ] at hdvd ; aesop

/-
PROBLEM
For a prime power p^k with k ≥ 1, σ*(p^k) = 1 + p^k.
    The only unitary divisors are 1 and p^k itself.

PROVIDED SOLUTION
Unfold unitaryDivisorSum. Show the filter set of unitary divisors of p^k equals {1, p^k}. For the forward direction: if d | p^k and gcd(d, p^k/d) = 1 and d ≠ 1 and d ≠ p^k, then d > 1 so p | d (by prime_dvd_of_dvd_prime_pow), and p^k/d > 1 and p^k/d | p^k so p | (p^k/d), hence p | gcd(d, p^k/d) = 1, contradiction. For the reverse: 1 and p^k are clearly unitary divisors. Then Finset.sum_pair gives the result.
-/
theorem unitaryDivisorSum_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    unitaryDivisorSum (p ^ k) = 1 + p ^ k := by
      -- By definition of unitary divisors, we consider the set of divisors of $p^k$ that are coprime to $p^k$.
      have h_unitary_divisors : (Finset.Ico 1 (p^k + 1)).filter (fun d => d ∣ p^k ∧ d.Coprime (p^k / d)) = {1, p^k} := by
        ext d
        simp [Finset.mem_filter, Finset.mem_Ico];
        constructor <;> intro h;
        · rw [ Nat.dvd_prime_pow hp ] at h;
          rcases h.2.1 with ⟨ m, hm₁, rfl ⟩ ; rcases hm₁.eq_or_lt with hm₂ | hm₂ <;> simp_all +decide [ Nat.pow_dvd_pow_iff ] ;
          exact Or.inl <| Or.inr <| Nat.eq_zero_of_not_pos fun hm₃ => absurd ( h.2.2.gcd_eq_one ▸ Nat.dvd_gcd ( dvd_pow_self _ hm₃.ne' ) ( Nat.dvd_div_of_mul_dvd <| pow_dvd_pow _ hm₂ ) ) ( by aesop ) ;
        · rcases h with ( rfl | rfl ) <;> norm_num [ hp.ne_zero, hk.ne' ];
          · exact Nat.one_le_pow _ _ hp.pos;
          · exact ⟨ Nat.one_le_pow _ _ hp.pos, by rw [ Nat.div_self ( pow_pos hp.pos _ ) ] ; norm_num ⟩;
      unfold unitaryDivisorSum;
      rw [ h_unitary_divisors, Finset.sum_pair ] ; norm_num ; linarith [ pow_lt_pow_right₀ hp.one_lt hk ]

/-
PROBLEM
The number of proper unitary divisors of a prime is 1 (just {1}).

PROVIDED SOLUTION
Unfold properUnitaryDivisors. Show the filter set equals {1} since only 1 and p divide p, and p is excluded by the d < p condition. Then card of singleton is 1.
-/
theorem card_properUnitaryDivisors_prime {p : ℕ} (hp : p.Prime) :
    (properUnitaryDivisors p).card = 1 := by
      refine' Finset.card_eq_one.mpr _;
      use 1;
      ext d
      simp [properUnitaryDivisors, hp];
      -- If $d$ is a proper unitary divisor of $p$, then $d$ must be $1$ because $p$ is prime.
      apply Iff.intro
      intro h
      have h_div : d ∣ p := h.right.left
      have h_coprime : Nat.Coprime d (p / d) := h.right.right
      have h_lt : d < p := h.left.right
      have h_one : d = 1 := by
        rw [ Nat.dvd_prime hp ] at h_div ; aesop
      exact h_one
      intro h
      simp [h];
      exact hp.one_lt

/-
PROBLEM
If d is a unitary divisor of n, then n/d is also a unitary divisor of n.

PROVIDED SOLUTION
From hd, extract d | n and gcd(d, n/d) = 1. Then n/d | n (Nat.div_dvd_of_dvd). Show n/(n/d) = d using Nat.div_div_self or direct calculation. Then gcd(n/d, d) = gcd(n/d, n/(n/d)) = gcd(d, n/d).symm = 1.
-/
theorem unitary_complement_mem {n d : ℕ} (hn : 0 < n)
    (hd : d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d))) :
    n / d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d)) := by
      simp +zetaDelta at *;
      exact ⟨ ⟨ Nat.div_pos ( by linarith ) ( by linarith ), Nat.div_le_self _ _ ⟩, Nat.div_dvd_of_dvd hd.2.1, by simpa [ Nat.div_div_self hd.2.1 ( by linarith ) ] using hd.2.2.symm ⟩

/-
PROBLEM
The unitary divisor sum of a product of two coprime numbers equals the product
    of their unitary divisor sums. This is the multiplicativity property.

PROVIDED SOLUTION
The key idea is that there is a bijection between unitary divisors of m*n and pairs (a,b) where a is a unitary divisor of m and b is a unitary divisor of n. Given coprimality of m and n, d | m*n with gcd(d, m*n/d) = 1 corresponds to (gcd(d,m), gcd(d,n)) where gcd(d,m) is a unitary divisor of m and gcd(d,n) is a unitary divisor of n, and d = gcd(d,m) * gcd(d,n).

Use Finset.sum_nbij or work with the product finset. The sum over the product of two finsets of id factors as the product of sums via Finset.sum_product or Finset.sum_mul_sum.

Alternative cleaner approach: use Finset.sum_nbij with the bijection from the product of unitary divisor sets to the unitary divisor set of m*n, mapping (a,b) to a*b. Show this is a bijection and id(a*b) = id(a) * id(b).
-/
theorem unitaryDivisorSum_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    unitaryDivisorSum (m * n) = unitaryDivisorSum m * unitaryDivisorSum n := by
      -- Let's rewrite the set of unitary divisors of $m \cdot n$ using the fact that $m$ and $n$ are coprime.
      have h_unitary_divisors : (Finset.filter (fun d => d ∣ m * n ∧ d.Coprime (m * n / d)) (Finset.Ico 1 (m * n + 1))) = Finset.image (fun (p : ℕ × ℕ) => p.1 * p.2) (Finset.filter (fun d => d ∣ m ∧ d.Coprime (m / d)) (Finset.Ico 1 (m + 1)) ×ˢ Finset.filter (fun d => d ∣ n ∧ d.Coprime (n / d)) (Finset.Ico 1 (n + 1))) := by
        ext d
        simp [Finset.mem_image];
        constructor;
        · intro hd
          obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : ℕ, a ∣ m ∧ b ∣ n ∧ d = a * b ∧ Nat.Coprime a b := by
            rw [ Nat.dvd_mul ] at hd;
            obtain ⟨ k₁, k₂, hk₁, hk₂, rfl ⟩ := hd.2.1; exact ⟨ k₁, k₂, hk₁, hk₂, rfl, hcop.coprime_dvd_left hk₁ |> Nat.Coprime.coprime_dvd_right hk₂ ⟩ ;
          -- Since $a \mid m$ and $b \mid n$, and $\gcd(a, b) = 1$, it follows that $\gcd(a, m/a) = 1$ and $\gcd(b, n/b) = 1$.
          have ha_coprime : Nat.Coprime a (m / a) := by
            obtain ⟨ k, hk ⟩ := ha; simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] ;
            simp_all +decide [ Nat.mul_assoc, Nat.mul_div_mul_left, hm.1 ];
            obtain ⟨ c, hc ⟩ := hb; simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] ;
            simp_all +decide [ Nat.mul_div_assoc, Nat.Coprime, Nat.gcd_mul_left, Nat.gcd_mul_right ];
            exact Nat.Coprime.coprime_dvd_right ( dvd_mul_right _ _ ) hd.2.2.1
          have hb_coprime : Nat.Coprime b (n / b) := by
            obtain ⟨ k, hk ⟩ := hb; simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] ;
            obtain ⟨ c, hc ⟩ := ha; simp_all +decide [ Nat.mul_div_mul_left, Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ] ;
            simp_all +decide [ Nat.mul_assoc, Nat.mul_div_mul_left, hm.1, hn.1 ];
            simp_all +decide [ Nat.mul_div_assoc, Nat.Coprime, Nat.gcd_mul_left, Nat.gcd_mul_right ];
            cases b <;> cases k <;> simp_all +decide [ Nat.coprime_mul_iff_left, Nat.coprime_mul_iff_right ];
          exact ⟨ a, b, ⟨ ⟨ ⟨ Nat.pos_of_dvd_of_pos ha hm, Nat.le_of_dvd hm ha ⟩, ha, ha_coprime ⟩, ⟨ ⟨ Nat.pos_of_dvd_of_pos hb hn, Nat.le_of_dvd hn hb ⟩, hb, hb_coprime ⟩ ⟩, hab.1.symm ⟩;
        · rintro ⟨ a, b, ⟨ ⟨ ⟨ ha₁, ha₂ ⟩, ha₃, ha₄ ⟩, ⟨ ⟨ hb₁, hb₂ ⟩, hb₃, hb₄ ⟩ ⟩, rfl ⟩ ; refine' ⟨ ⟨ Nat.mul_pos ha₁ hb₁, Nat.mul_le_mul ha₂ hb₂ ⟩, _, _ ⟩ <;> simp_all +decide [ Nat.mul_div_mul_comm, Nat.mul_dvd_mul ] ;
          apply_rules [ Nat.Coprime.mul_left, Nat.Coprime.mul_right ];
          · exact hcop.coprime_dvd_left ha₃ |> Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd hb₃ );
          · exact Nat.Coprime.coprime_dvd_left hb₃ <| Nat.Coprime.coprime_dvd_right ( Nat.div_dvd_of_dvd ha₃ ) hcop.symm;
      unfold unitaryDivisorSum;
      rw [ h_unitary_divisors, Finset.sum_image, Finset.sum_product ];
      · simp +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
      · intros p hp q hq h_eq; simp_all +decide [ Nat.Coprime, Nat.gcd_mul_left, Nat.gcd_mul_right ] ;
        -- Since $p.1 \mid m$ and $q.1 \mid m$, and $\gcd(m, n) = 1$, it follows that $p.1 = q.1$.
        have hp1_eq_q1 : p.1 = q.1 := by
          exact Nat.dvd_antisymm ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( p.1 ) ( q.2 ) from Nat.Coprime.coprime_dvd_left ( by aesop ) <| Nat.Coprime.coprime_dvd_right ( by aesop ) hcop ) <| h_eq.symm ▸ dvd_mul_right _ _ ) ( by exact Nat.Coprime.dvd_of_dvd_mul_right ( show Nat.Coprime ( q.1 ) ( p.2 ) from Nat.Coprime.coprime_dvd_left ( by aesop ) <| Nat.Coprime.coprime_dvd_right ( by aesop ) hcop ) <| h_eq.symm ▸ dvd_mul_right _ _ );
        aesop

end Erdos1052Aristotle