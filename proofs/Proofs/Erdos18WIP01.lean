/-
  Erdős Problem #18 — Practical Numbers: an infinite family + a necessary condition

  Source: https://erdosproblems.com/18
  Parent: `Proofs/Erdos18Problem.lean` (defines `IsPractical`, `IsRepresentable`,
  `divisors`, `PracticalNumbers` and a handful of finite `decide`-checked examples).

  A positive integer `m` is *practical* if every `1 ≤ k < m` is a sum of distinct
  divisors of `m`. The parent file establishes practicality only for the finitely
  many worked examples `1, 2, 4, 6, 8` (each by `decide`). This file supplies the
  first *structural* results — statements covering infinitely many `m` at once:

  * `repr_lt_two_pow` — every `k < 2^n` is a sum of distinct powers of two drawn
    from `{2^0, …, 2^{n-1}}` (the finite binary-representation lemma).
  * `two_pow_practical` — **every power of two is practical**. This is an
    infinite family of practical numbers, proved once and for all rather than
    case-by-case.
  * `infinite_practicalNumbers` — **there are infinitely many practical numbers**
    (the powers of two, via injectivity of `n ↦ 2^n`).
  * `two_dvd_of_practical` / `even_of_practical` — a matching *necessary* condition:
    any practical `m ≥ 3` is even (to represent `2`, the divisor `2` itself must be
    used, since `1` is the only smaller divisor).

  All results are axiom-free (`#print axioms` = `[propext, Classical.choice,
  Quot.sound]`) and contain no `sorry`.
-/

import Mathlib
import Proofs.Erdos18Problem

open Set Finset Function Nat

namespace Erdos18

/- ## An infinite family: powers of two are practical -/

/-- Every `k < 2^n` is a sum of distinct powers of two drawn from `{2^0, …, 2^{n-1}}`.
This is the finite binary-representation fact underlying practicality of `2^n`. -/
theorem repr_lt_two_pow : ∀ (n k : ℕ), k < 2 ^ n →
    ∃ S : Finset ℕ, S ⊆ (Finset.range n).image (2 ^ ·) ∧ S.sum id = k := by
  intro n
  induction n with
  | zero =>
    intro k hk
    simp only [pow_zero, Nat.lt_one_iff] at hk
    subst hk
    exact ⟨∅, by simp, by simp⟩
  | succ n ih =>
    intro k hk
    have hrs : (Finset.range n).image (2 ^ ·) ⊆ (Finset.range (n + 1)).image (2 ^ ·) := by
      apply Finset.image_subset_image
      intro x hx
      rw [Finset.mem_range] at hx ⊢
      omega
    by_cases hkn : k < 2 ^ n
    · obtain ⟨S, hS, hsum⟩ := ih k hkn
      exact ⟨S, hS.trans hrs, hsum⟩
    · rw [not_lt] at hkn
      have h2 : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by rw [pow_succ]; ring
      have hk' : k - 2 ^ n < 2 ^ n := by omega
      obtain ⟨S, hS, hsum⟩ := ih (k - 2 ^ n) hk'
      have hnotmem : 2 ^ n ∉ S := by
        intro hmem
        have hx := hS hmem
        rw [Finset.mem_image] at hx
        obtain ⟨i, hi, hie⟩ := hx
        rw [Finset.mem_range] at hi
        have : (2 : ℕ) ^ i < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) hi
        omega
      refine ⟨insert (2 ^ n) S, ?_, ?_⟩
      · rw [Finset.insert_subset_iff]
        refine ⟨?_, hS.trans hrs⟩
        rw [Finset.mem_image]
        exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩
      · rw [Finset.sum_insert hnotmem, hsum]
        simp only [id_eq]
        omega

/-- The powers `{2^i : i < n}` are all divisors of `2^n`. -/
theorem image_two_pow_subset_divisors (n : ℕ) :
    (Finset.range n).image (2 ^ ·) ⊆ divisors (2 ^ n) := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  rw [Finset.mem_range] at hi
  show (2 : ℕ) ^ i ∈ (2 ^ n).divisors
  rw [Nat.mem_divisors]
  exact ⟨pow_dvd_pow 2 (le_of_lt hi), by positivity⟩

/-- **Every power of two is practical.** An infinite family of practical numbers,
proved uniformly (contrast the parent's finite `decide`-checked examples). -/
theorem two_pow_practical (n : ℕ) : IsPractical (2 ^ n) := by
  refine ⟨Nat.one_le_pow n 2 (by norm_num), ?_⟩
  intro k _ hkm
  obtain ⟨S, hS, hsum⟩ := repr_lt_two_pow n k hkm
  exact ⟨S, hS.trans (image_two_pow_subset_divisors n), hsum⟩

/-- **There are infinitely many practical numbers** — namely the powers of two. -/
theorem infinite_practicalNumbers : PracticalNumbers.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => 2 ^ n) (Nat.pow_right_injective (le_refl 2))
  intro n
  exact two_pow_practical n

/- ## A matching necessary condition: practical `m ≥ 3` is even -/

/-- **A practical number `m ≥ 3` is even.** To represent `2` as a sum of distinct
divisors of `m`, since `1` is the only divisor below `2`, the divisor `2` itself
must appear — hence `2 ∣ m`. -/
theorem two_dvd_of_practical {m : ℕ} (hm : 3 ≤ m) (h : IsPractical m) : 2 ∣ m := by
  obtain ⟨S, hS, hsum⟩ := h.2 2 (by omega) (by omega)
  have hsub12 : S ⊆ {1, 2} := by
    intro x hx
    have hxdiv : x ∈ m.divisors := hS hx
    have hxpos : 1 ≤ x := Nat.pos_of_mem_divisors hxdiv
    have hxle : x ≤ 2 := by
      have hle := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hx
      rw [hsum, id_eq] at hle
      exact hle
    interval_cases x <;> simp
  have h2mem : 2 ∈ S := by
    by_contra h2
    have hS1 : S ⊆ {1} := by
      intro x hx
      have hx12 := hsub12 hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx12 ⊢
      rcases hx12 with h1 | h2'
      · exact h1
      · exact absurd (h2' ▸ hx) h2
    have hle : S.sum id ≤ ({1} : Finset ℕ).sum id := Finset.sum_le_sum_of_subset hS1
    rw [hsum, Finset.sum_singleton, id_eq] at hle
    omega
  exact (Nat.mem_divisors.mp (hS h2mem)).1

/-- Restated: a practical number `m ≥ 3` is `Even`. -/
theorem even_of_practical {m : ℕ} (hm : 3 ≤ m) (h : IsPractical m) : Even m := by
  obtain ⟨c, hc⟩ := two_dvd_of_practical hm h
  exact ⟨c, by omega⟩

end Erdos18
