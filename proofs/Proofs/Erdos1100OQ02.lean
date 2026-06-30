/-
# OQ-02: The Prime-Power Equality Family for Erdős #1100

Erdős #1100 studies τ⊥(n) — the number of coprime consecutive pairs among the
sorted divisors `1 = d₁ < d₂ < ⋯ < d_τ(n) = n`. The trivial lower bound is
τ⊥(n) ≥ ω(n), with equality known to hold for infinitely many `n` via *primes*
(τ⊥(p) = 1 = ω(p)).

**Open question (this file).** Which `n` achieve the minimum τ⊥(n) = ω(n)?
The prime case is one instance of a much larger family: every **prime power**
`pᵏ` achieves equality. We prove, with **no axioms and no `sorry`**:

* `divisorList_prime_pow` : the sorted divisors of `pᵏ` are exactly `[1, p, p², …, pᵏ]`
  (= `(List.range (k+1)).map (p ^ ·)`).
* `tauPerp_prime_pow`     : τ⊥(pᵏ) = 1 for every prime `p` and `k ≥ 1`. The only
  coprime consecutive pair is `(d₁, d₂) = (1, p)`; every later pair `(pⁱ, pⁱ⁺¹)`
  has gcd `pⁱ > 1`.
* `omega_prime_pow`       : ω(pᵏ) = 1.
* `tauPerp_eq_omega_prime_pow` : τ⊥(pᵏ) = ω(pᵏ) — the equality family.
* `tau_perp_equality_prime_powers` : equality holds for arbitrarily large prime
  powers (a strict strengthening of the prime-only equality family).

These are *unconditional* exact computations; they neither assume nor approach the
genuinely open analytic questions of Erdős #1100 (growth of τ⊥(n)/ω(n), the
exp((log n)^{o(1)}) bound, g(k)), but they pin down the complete extremal-minimum
family below the conjectural growth.

The definitions of `divisorList`, `omega`, `tauPerp` mirror those of the parent file
`Erdos1100Problem.lean`; this file is kept self-contained (imports only Mathlib) so it
verifies independently.

Tags: number-theory, erdos, divisors, coprime, prime-power
-/

import Mathlib

set_option linter.unusedVariables false

open Nat Finset

namespace Erdos1100OQ02

/-! ## Definitions (mirroring `Erdos1100Problem.lean`) -/

/-- The list of divisors of `n` in increasing order. -/
noncomputable def divisorList (n : ℕ) : List ℕ :=
  (Finset.filter (· ∣ n) (Finset.range (n + 1))).sort (· ≤ ·)

/-- ω(n): the number of distinct prime divisors of `n`. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- τ⊥(n): the count of indices `i` with `gcd(dᵢ, dᵢ₊₁) = 1` among the sorted divisors. -/
noncomputable def tauPerp (n : ℕ) : ℕ :=
  let divs := divisorList n
  (List.range (divs.length - 1)).filter
    (fun i => Nat.gcd (divs.getD i 0) (divs.getD (i + 1) 0) = 1)
  |>.length

/-! ## Part I: The sorted divisors of a prime power -/

/-- `divisorList n` (sort of `{d ≤ n : d ∣ n}`) coincides with the sort of
`Nat.divisors n` for positive `n`: the only difference is `0`, which divides no
positive `n`. -/
lemma divisorList_eq_sort_divisors {n : ℕ} (hn : 0 < n) :
    divisorList n = n.divisors.sort (· ≤ ·) := by
  unfold divisorList
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨_, hd⟩; exact ⟨hd, hn.ne'⟩
  · rintro ⟨hd, _⟩; exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hn hd), hd⟩

/-- Sorting `Finset.range m` under `≤` returns `List.range m`. -/
lemma range_sort (m : ℕ) : (Finset.range m).sort (· ≤ ·) = List.range m := by
  have hnodup : (List.range m).Nodup := List.nodup_range
  have hpair : (List.range m).Pairwise (· ≤ ·) :=
    List.pairwise_lt_range.imp le_of_lt
  have := (List.toFinset_sort (· ≤ ·) hnodup).mpr hpair
  rwa [List.toFinset_range] at this

/-- **Sorted divisors of a prime power.** For a prime `p` and `k ≥ 1`, the increasing
list of divisors of `pᵏ` is `[1, p, p², …, pᵏ]`. -/
lemma divisorList_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    divisorList (p ^ k) = (List.range (k + 1)).map (p ^ ·) := by
  have hpos : 0 < p ^ k := pow_pos hp.pos k
  rw [divisorList_eq_sort_divisors hpos, Nat.divisors_prime_pow hp]
  set emb : ℕ ↪ ℕ := ⟨(p ^ ·), Nat.pow_right_injective hp.two_le⟩ with hemb
  have hmono : ∀ a ∈ Finset.range (k + 1), ∀ b ∈ Finset.range (k + 1),
      a ≤ b ↔ emb a ≤ emb b := by
    intro a _ b _
    exact (Nat.pow_le_pow_iff_right hp.one_lt).symm
  rw [← Finset.map_sort emb (Finset.range (k + 1)) (· ≤ ·) (· ≤ ·) hmono]
  rw [range_sort]
  rfl

/-! ## Part II: τ⊥ and ω of a prime power -/

/-- **ω(pᵏ) = 1** for a prime `p` and `k ≥ 1`. -/
lemma omega_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    omega (p ^ k) = 1 := by
  unfold omega
  rw [Nat.primeFactors_prime_pow hk.ne' hp]
  simp

/-- **τ⊥(pᵏ) = 1** for a prime `p` and `k ≥ 1`.

The divisors are `[1, p, …, pᵏ]`; the consecutive pair `(pⁱ, pⁱ⁺¹)` has
`gcd = pⁱ`, which equals `1` exactly when `i = 0`. So there is precisely one coprime
consecutive pair, namely `(1, p)`. -/
lemma tauPerp_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    tauPerp (p ^ k) = 1 := by
  unfold tauPerp
  rw [divisorList_prime_pow hp hk]
  set L := (List.range (k + 1)).map (p ^ ·) with hL
  have hlen : L.length = k + 1 := by rw [hL, List.length_map, List.length_range]
  change ((List.range (L.length - 1)).filter
    (fun i => decide (Nat.gcd (L.getD i 0) (L.getD (i + 1) 0) = 1))).length = 1
  rw [hlen, Nat.add_sub_cancel]
  have hget : ∀ i, i < k + 1 → L.getD i 0 = p ^ i := by
    intro i hi
    rw [hL, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
    rfl
  have hfilter : (List.range k).filter
        (fun i => decide (Nat.gcd (L.getD i 0) (L.getD (i + 1) 0) = 1))
      = (List.range k).filter (fun i => decide (i = 0)) := by
    apply List.filter_congr
    intro i hi
    have hik : i < k := List.mem_range.mp hi
    have h1 : L.getD i 0 = p ^ i := hget i (by omega)
    have h2 : L.getD (i + 1) 0 = p ^ (i + 1) := hget (i + 1) (by omega)
    have hdvd : p ^ i ∣ p ^ (i + 1) := pow_dvd_pow p (Nat.le_succ i)
    have hpe : (p ^ i = 1) ↔ (i = 0) := by
      rw [Nat.pow_eq_one]
      constructor
      · rintro (h | h)
        · exact absurd h hp.ne_one
        · exact h
      · rintro rfl; right; rfl
    refine decide_eq_decide.mpr ?_
    rw [h1, h2, Nat.gcd_eq_left hdvd]
    exact hpe
  rw [hfilter]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [List.range_succ_eq_map, List.filter_cons]
  have htail : ((List.range m).map Nat.succ).filter (fun i => decide (i = 0)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
    simp
  simp [htail]

/-! ## Part III: The equality family -/

/-- **Prime powers achieve the minimum τ⊥ = ω.** For every prime `p` and `k ≥ 1`,
`τ⊥(pᵏ) = ω(pᵏ) = 1`. -/
theorem tauPerp_eq_omega_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    tauPerp (p ^ k) = omega (p ^ k) := by
  rw [tauPerp_prime_pow hp hk, omega_prime_pow hp hk]

/-- **Equality at arbitrarily large prime powers.** For every bound `N` there is an
`n > N` with `τ⊥(n) = ω(n)`, realised by the prime power `2^(N+1)`. The
minimum-achieving family is not just the primes but all prime powers. -/
theorem tau_perp_equality_prime_powers :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ tauPerp n = omega n := by
  intro N
  exact ⟨2 ^ (N + 1), (Nat.lt_succ_self N).trans Nat.lt_two_pow_self,
    tauPerp_eq_omega_prime_pow Nat.prime_two (by omega)⟩

end Erdos1100OQ02
