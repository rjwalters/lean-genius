/-
Erdős Problem #456 — Smallest Prime ≡ 1 (mod n) vs Smallest m with n | φ(m)

Let pₙ be the smallest prime ≡ 1 (mod n), and let mₙ be the smallest
positive integer such that n | φ(mₙ).

Erdős asked:
(1) Is mₙ < pₙ for almost all n?
(2) Does pₙ/mₙ → ∞ for almost all n?
(3) Are there infinitely many primes p such that p − 1 is the only n
    with mₙ = p?

Known:
- mₙ ≤ pₙ always (trivially, since φ(pₙ) = pₙ − 1 and n | pₙ − 1)
- Linnik: pₙ ≤ n^{O(1)}
- When n = q − 1 for prime q, mₙ = pₙ
- For n = 2^{2k+1}: mₙ ≤ 2n < pₙ (van Doorn)
- mₙ < pₙ for infinitely many n (Erdős)
- mₙ/n → ∞ for almost all n

**Status:** OPEN

**Reference:** https://erdosproblems.com/456

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib

open Nat

namespace Erdos456

/-
# Part 1: Core Definitions

We define the two key functions using Mathlib's Nat.totient.
-/

/-- pₙ: the smallest prime ≡ 1 (mod n).
    By Dirichlet's theorem on primes in arithmetic progressions, this exists for all n ≥ 1. -/
noncomputable def smallestPrimeMod1 (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ n ∣ (p - 1)}

/-- mₙ: the smallest positive integer m with n | φ(m) -/
noncomputable def smallestTotientDiv (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ n ∣ m.totient}

/-
# Part 2: Properties of smallestPrimeMod1
-/

/-- Dirichlet's theorem: for n ≥ 1, there exist infinitely many primes ≡ 1 (mod n) -/
axiom dirichlet_primes_mod1 (n : ℕ) (hn : 1 ≤ n) :
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ n ∣ (p - 1)

/-- The set of primes ≡ 1 (mod n) is nonempty for n ≥ 1. -/
private lemma primes_mod1_nonempty (n : ℕ) (hn : 1 ≤ n) :
    Set.Nonempty {p : ℕ | p.Prime ∧ n ∣ (p - 1)} := by
  obtain ⟨p, _, hp, hd⟩ := dirichlet_primes_mod1 n hn 0
  exact ⟨p, hp, hd⟩

/-- The set of positive m with n | φ(m) is nonempty for n ≥ 1. -/
private lemma totient_div_nonempty (n : ℕ) (hn : 1 ≤ n) :
    Set.Nonempty {m : ℕ | 0 < m ∧ n ∣ m.totient} := by
  obtain ⟨p, _, hp, hd⟩ := dirichlet_primes_mod1 n hn 0
  exact ⟨p, hp.pos, Nat.totient_prime hp ▸ hd⟩

/-- pₙ is prime: follows from sInf membership in the set of primes ≡ 1 (mod n). -/
theorem smallestPrimeMod1_prime (n : ℕ) (hn : 1 ≤ n) :
    (smallestPrimeMod1 n).Prime := by
  unfold smallestPrimeMod1
  exact (Nat.sInf_mem (primes_mod1_nonempty n hn)).1

/-- pₙ ≡ 1 (mod n): follows from sInf membership. -/
theorem smallestPrimeMod1_cong (n : ℕ) (hn : 1 ≤ n) :
    n ∣ (smallestPrimeMod1 n - 1) := by
  unfold smallestPrimeMod1
  exact (Nat.sInf_mem (primes_mod1_nonempty n hn)).2

/-- pₙ is minimal among primes ≡ 1 (mod n): follows from sInf being a lower bound. -/
theorem smallestPrimeMod1_minimal (n : ℕ) (hn : 1 ≤ n) (p : ℕ)
    (hp : p.Prime) (hcong : n ∣ (p - 1)) :
    smallestPrimeMod1 n ≤ p := by
  unfold smallestPrimeMod1
  exact Nat.sInf_le ⟨hp, hcong⟩

/-
# Part 3: Properties of smallestTotientDiv
-/

/-- mₙ is positive: follows from sInf membership in the set of positive m with n | φ(m). -/
theorem smallestTotientDiv_pos (n : ℕ) (hn : 1 ≤ n) :
    0 < smallestTotientDiv n := by
  unfold smallestTotientDiv
  exact (Nat.sInf_mem (totient_div_nonempty n hn)).1

/-- n | φ(mₙ): follows from sInf membership. -/
theorem smallestTotientDiv_divides (n : ℕ) (hn : 1 ≤ n) :
    n ∣ (smallestTotientDiv n).totient := by
  unfold smallestTotientDiv
  exact (Nat.sInf_mem (totient_div_nonempty n hn)).2

/-- mₙ is minimal among positive m with n | φ(m): follows from sInf being a lower bound. -/
theorem smallestTotientDiv_minimal (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (hm : 0 < m) (hdiv : n ∣ m.totient) :
    smallestTotientDiv n ≤ m := by
  unfold smallestTotientDiv
  exact Nat.sInf_le ⟨hm, hdiv⟩

/-- For n ≥ 2, mₙ ≥ 2: m = 1 would require n | φ(1) = 1, impossible. -/
theorem smallestTotientDiv_ge_two (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ smallestTotientDiv n := by
  by_contra h
  push_neg at h
  have hm := smallestTotientDiv_pos n (by omega : 1 ≤ n)
  have hdvd := smallestTotientDiv_divides n (by omega : 1 ≤ n)
  have : smallestTotientDiv n = 1 := by omega
  rw [this, Nat.totient_one] at hdvd
  exact absurd (Nat.le_of_dvd one_pos hdvd) (by omega)

/-
# Part 4: Known Results
-/

/-- mₙ ≤ pₙ always.
    φ(pₙ) = pₙ − 1 and n | pₙ − 1, so pₙ is in the set defining mₙ.
    By minimality of mₙ, mₙ ≤ pₙ. -/
theorem m_le_p (n : ℕ) (hn : 1 ≤ n) :
    smallestTotientDiv n ≤ smallestPrimeMod1 n := by
  apply smallestTotientDiv_minimal n hn
  · exact (smallestPrimeMod1_prime n hn).pos
  · rw [Nat.totient_prime (smallestPrimeMod1_prime n hn)]
    exact smallestPrimeMod1_cong n hn

/-- When q ≥ 3 is prime and n = q − 1, both mₙ = q and pₙ = q.
    Since q ≡ 1 (mod q−1) and is the smallest such prime (p−1 ≥ n means p ≥ q),
    pₙ = q. Since φ(m) < n for all 1 ≤ m ≤ n, no smaller m works, so mₙ = q. -/
theorem m_eq_p_of_prime_pred {q : ℕ} (hq : q.Prime) (hq3 : 3 ≤ q) :
    smallestTotientDiv (q - 1) = q ∧ smallestPrimeMod1 (q - 1) = q := by
  set n := q - 1 with hn_def
  have hn : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := by omega
  constructor
  · -- mₙ = q
    apply le_antisymm
    · -- mₙ ≤ q: m_le_p gives mₙ ≤ pₙ, and pₙ ≤ q (q is prime with n | q-1)
      calc smallestTotientDiv n ≤ smallestPrimeMod1 n := m_le_p n hn
        _ ≤ q := smallestPrimeMod1_minimal n hn q hq (dvd_refl n)
    · -- q ≤ mₙ: no m < q has n | φ(m)
      suffices h : ∀ m, 0 < m → n ∣ m.totient → q ≤ m from
        h _ (smallestTotientDiv_pos n hn) (smallestTotientDiv_divides n hn)
      intro m hm hdvd
      by_contra hlt; push_neg at hlt
      -- m < q means m ≤ n = q-1, so φ(m) < n
      have hm_le_n : m ≤ n := by omega
      have htot_lt : m.totient < n := by
        rcases le_or_lt m 1 with hm1 | hm2
        · have : m = 1 := by omega; rw [this, Nat.totient_one]; omega
        · calc m.totient < m := Nat.totient_lt hm2
            _ ≤ n := hm_le_n
      -- But n | φ(m) and φ(m) > 0 gives n ≤ φ(m) — contradiction
      exact absurd (Nat.le_of_dvd (Nat.totient_pos hm) hdvd) (by omega)
  · -- pₙ = q: q is the smallest prime ≡ 1 (mod n)
    apply le_antisymm
    · exact smallestPrimeMod1_minimal n hn q hq (dvd_refl n)
    · -- pₙ ≥ q: pₙ is prime with n | pₙ-1, so pₙ-1 ≥ n, hence pₙ ≥ n+1 = q
      have hpn_pos : 0 < smallestPrimeMod1 n - 1 := by
        have := (smallestPrimeMod1_prime n hn).two_le; omega
      have := Nat.le_of_dvd hpn_pos (smallestPrimeMod1_cong n hn)
      omega

/-- Linnik's theorem: pₙ = O(n^L) for some constant L -/
axiom linnik_bound :
  ∃ L : ℕ, ∀ n : ℕ, 1 ≤ n →
    smallestPrimeMod1 n ≤ n ^ L

/-- mₙ < pₙ for infinitely many n (Erdős) -/
axiom erdos_strict_inequality :
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
    smallestTotientDiv n < smallestPrimeMod1 n

/-- mₙ/n → ∞ for almost all n (Erdős).
    For any constant C, the set of n with mₙ ≤ C·n has density 0. -/
axiom m_over_n_diverges :
  ∀ C : ℕ, ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ M ≥ N,
    -- The number of n ≤ M with mₙ ≤ C·n is < ε·M
    ((Finset.filter (fun n => smallestTotientDiv n ≤ C * n) (Finset.range M)).card : ℚ) < ε * M

/-- Van Doorn: for n = 2^{2k+1}, mₙ ≤ 2n.
    Proof: 2n = 2^{2k+2}, φ(2^{2k+2}) = 2^{2k+1} = n, so n | φ(2n)
    and by minimality of mₙ, mₙ ≤ 2n. -/
theorem van_doorn_power_of_two (k : ℕ) :
    let n := 2 ^ (2 * k + 1)
    smallestTotientDiv n ≤ 2 * n := by
  intro n
  have hn : 1 ≤ n := Nat.one_le_two_pow
  apply smallestTotientDiv_minimal n hn (2 * n) (by omega)
  -- n | φ(2n) = φ(2^{2k+2}) = 2^{2k+1} * (2 - 1) = n
  show n ∣ (2 * 2 ^ (2 * k + 1)).totient
  rw [show 2 * 2 ^ (2 * k + 1) = 2 ^ ((2 * k + 1) + 1) from by ring]
  rw [Nat.totient_prime_pow_succ (by norm_num : Nat.Prime 2)]
  -- Goal: n ∣ 2^(2k+1) * (2 - 1) = n * 1
  exact dvd_mul_right n (2 - 1)

/-
# Part 5: Natural Density
-/

/-- "Almost all" in the natural density sense:
    P holds for all but a density-0 set of natural numbers.
    For every ε > 0, eventually the fraction of n ∈ [0, M) failing P is < ε. -/
def AlmostAll (P : ℕ → Prop) : Prop :=
  ∀ ε : ℚ, 0 < ε → ∃ N : ℕ, ∀ M ≥ N,
    ((Finset.filter (fun n => ¬P n) (Finset.range M)).card : ℚ) < ε * M

/-
# Part 6: The Erdős Conjectures (OPEN)
-/

/-- Erdős Problem 456, Part 1: mₙ < pₙ for almost all n -/
def ErdosProblem456_Part1 : Prop :=
  AlmostAll (fun n => 1 ≤ n → smallestTotientDiv n < smallestPrimeMod1 n)

/-- Erdős Problem 456, Part 2: pₙ/mₙ → ∞ for almost all n -/
def ErdosProblem456_Part2 : Prop :=
  ∀ C : ℕ, AlmostAll (fun n => 1 ≤ n →
    C * smallestTotientDiv n ≤ smallestPrimeMod1 n)

/-- Erdős Problem 456, Part 3: infinitely many primes p where
    p − 1 is the unique n with mₙ = p -/
def ErdosProblem456_Part3 : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ p.Prime ∧
    smallestTotientDiv (p - 1) = p ∧
    (∀ n : ℕ, smallestTotientDiv n = p → n = p - 1)

/-
# Part 7: Relationships Between Parts
-/

/-- Part 2 implies Part 1 -/
theorem part2_implies_part1 : ErdosProblem456_Part2 → ErdosProblem456_Part1 := by
  intro h2 ε hε
  -- Take C = 2 from Part 2: almost all n satisfy 2·mₙ ≤ pₙ
  obtain ⟨N, hN⟩ := h2 2 ε hε
  refine ⟨N, fun M hM => lt_of_le_of_lt ?_ (hN M hM)⟩
  -- {n : ¬(mₙ < pₙ)} ⊆ {n : ¬(2·mₙ ≤ pₙ)} since 2·mₙ ≤ pₙ and mₙ ≥ 1 → mₙ < pₙ
  exact_mod_cast Finset.card_le_card fun n hn => by
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    refine ⟨hn.1, fun h => hn.2 fun hn1 => ?_⟩
    have hm := smallestTotientDiv_pos n hn1
    have h2m := h hn1
    omega

/-- The infinitely-many result is weaker than the density result.
    If mₙ < pₙ for almost all n (density-1 set), then for any N there exist
    n ≥ N with mₙ < pₙ (since a density-0 set cannot contain [N, ∞)). -/
theorem part1_implies_infinitely_many :
    ErdosProblem456_Part1 → ∀ N : ℕ, ∃ n ≥ N, smallestTotientDiv n < smallestPrimeMod1 n := by
  intro h1 N
  -- wlog N ≥ 1 (if N = 0, find n ≥ 1 ≥ 0)
  suffices ∃ n, max 1 N ≤ n ∧ smallestTotientDiv n < smallestPrimeMod1 n by
    obtain ⟨n, hn, hlt⟩ := this; exact ⟨n, le_trans (le_max_right _ _) hn, hlt⟩
  set N' := max 1 N
  by_contra h_none
  push_neg at h_none
  -- h_none : ∀ n ≥ N', pₙ ≤ mₙ
  -- AlmostAll with ε = 1/2: eventually |bad ∩ [0,M)| < M/2
  obtain ⟨M₀, hM₀⟩ := h1 (1/2) (by norm_num)
  -- Choose M large enough: M ≥ M₀ and M > 2·N' (so M - N' > M/2)
  specialize hM₀ (max M₀ (2 * N' + 1)) (le_max_left _ _)
  set M := max M₀ (2 * N' + 1) at hM₀
  -- Every n ∈ [N', M) is in the bad set (since n ≥ N' ≥ 1 and pₙ ≤ mₙ)
  have h_subset : Finset.Ico N' M ⊆
      Finset.filter (fun n => ¬(1 ≤ n → smallestTotientDiv n < smallestPrimeMod1 n))
        (Finset.range M) := by
    intro n hn
    simp only [Finset.mem_Ico] at hn
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hn.2, fun h => absurd (h (le_trans (le_max_left 1 N) hn.1))
      (not_lt.mpr (h_none n hn.1))⟩
  -- |bad| ≥ |[N', M)| = M - N'
  have h_lower : (Finset.filter _ (Finset.range M)).card ≥ M - N' :=
    le_trans (by simp [Finset.card_Ico]) (Finset.card_le_card h_subset)
  -- But M - N' > M/2 (since M ≥ 2·N' + 1) and |bad| < M/2 — contradiction
  have hN'_le_M : N' ≤ M := by omega
  have h_cast : ((Finset.filter _ (Finset.range M)).card : ℚ) ≥ (M : ℚ) - N' := by
    calc ((Finset.filter _ (Finset.range M)).card : ℚ)
        ≥ ↑(M - N') := Nat.cast_le.mpr h_lower
      _ = ↑M - ↑N' := by exact_mod_cast Nat.cast_sub hN'_le_M
  have h_half : (M : ℚ) - N' > M / 2 := by
    have : (M : ℤ) ≥ 2 * N' + 1 := by exact_mod_cast le_max_right M₀ (2 * N' + 1)
    push_cast; linarith
  linarith

end Erdos456
