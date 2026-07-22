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

  It then adds a *closure* result — a genuine multiplication rule generating new
  practical numbers from old ones (the simplest instance of the Stewart product
  criterion `n ≤ σ(m) + 1 ⟹ mn practical`, here `n = 2`):

  * `two_mul_practical` — **if `m` is practical then so is `2m`.** Every `k < 2m`
    splits as `k = 2q + r` with `r ∈ {0,1}` and `q ≤ m - 1`; represent `q` by
    divisors of `m`, double that representation (`d ∣ m ⟹ 2d ∣ 2m`) to reach `2q`,
    and add the divisor `1` when `r = 1`.
  * `two_pow_mul_practical` — iterating: `2^n · m` is practical whenever `m` is.
    This produces infinitely many *new* families, e.g. `2^n · 6`, beyond the pure
    powers of two.

  Finally, two structural bounds:

  * `two_mul_sub_one_le_sigma` — for practical `m`, the sum of divisors obeys
    `σ(m) ≥ 2m − 1` (`m − 1` is a sum of proper divisors, plus the divisor `m`).
  * `odd_practical_eq_one` — the only *odd* practical number is `1` (immediate from
    the evenness necessary condition).

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

/- ## Closure under doubling: `m` practical ⟹ `2m` practical

The core building block is that a representation by divisors of `m` doubles to one
by divisors of `2m`: if `d ∣ m` then `2d ∣ 2m`, so `S ↦ 2·S` sends distinct
divisors of `m` to distinct divisors of `2m` while doubling the subset sum. -/

/-- Doubling a divisor-subset doubles its sum (the map `d ↦ 2d` is injective). -/
theorem sum_image_two_mul (S : Finset ℕ) :
    (S.image (2 * ·)).sum id = 2 * S.sum id := by
  rw [Finset.sum_image (fun a _ b _ hab => by omega), Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => rfl)

/-- If `S` is a set of divisors of `m`, then `2·S` is a set of divisors of `2m`
(since `d ∣ m ⟹ 2d ∣ 2m`, and `m ≠ 0` forces `2m ≠ 0`). -/
theorem image_two_mul_subset_divisors {S : Finset ℕ} {m : ℕ} (hS : S ⊆ divisors m) :
    S.image (2 * ·) ⊆ divisors (2 * m) := by
  intro x hx
  rw [Finset.mem_image] at hx
  obtain ⟨d, hd, rfl⟩ := hx
  have hdm := hS hd
  rw [divisors, Nat.mem_divisors] at hdm
  rw [divisors, Nat.mem_divisors]
  exact ⟨Nat.mul_dvd_mul_left 2 hdm.1, Nat.mul_ne_zero two_ne_zero hdm.2⟩

/-- If `q` is a sum of distinct divisors of `m`, then `2q` is a sum of distinct
divisors of `2m`. -/
theorem repr_two_mul {q m : ℕ} (h : IsRepresentable q m) :
    IsRepresentable (2 * q) (2 * m) := by
  obtain ⟨S, hS, hsum⟩ := h
  exact ⟨S.image (2 * ·), image_two_mul_subset_divisors hS,
    by rw [sum_image_two_mul, hsum]⟩

/-- If `q` is a sum of distinct divisors of `m` (with `m ≥ 1`), then `2q + 1` is a
sum of distinct divisors of `2m`: double the representation of `q`, then adjoin the
divisor `1` (which, being odd, is not among the doubled — hence even — divisors). -/
theorem repr_two_mul_add_one {q m : ℕ} (hm : 1 ≤ m) (h : IsRepresentable q m) :
    IsRepresentable (2 * q + 1) (2 * m) := by
  obtain ⟨S, hS, hsum⟩ := h
  have h1notmem : (1 : ℕ) ∉ S.image (2 * ·) := by
    rw [Finset.mem_image]; rintro ⟨d, _, hd⟩; omega
  refine ⟨insert 1 (S.image (2 * ·)), ?_, ?_⟩
  · rw [Finset.insert_subset_iff]
    refine ⟨?_, image_two_mul_subset_divisors hS⟩
    rw [divisors, Nat.mem_divisors]
    exact ⟨one_dvd _, Nat.mul_ne_zero two_ne_zero (by omega)⟩
  · rw [Finset.sum_insert h1notmem, sum_image_two_mul, hsum]
    simp only [id_eq]; omega

/-- **If `m` is practical, then `2m` is practical.** A concrete new-family generator:
the divisors of `2m` include every divisor `d` of `m` and its double `2d`, which
suffices to represent every `k < 2m`. This is the `n = 2` case of the Stewart
product criterion. -/
theorem two_mul_practical {m : ℕ} (h : IsPractical m) : IsPractical (2 * m) := by
  obtain ⟨hm1, hrep⟩ := h
  refine ⟨by omega, ?_⟩
  intro k _ hk2m
  have hqlt : k / 2 < m := by omega
  have hqrep : IsRepresentable (k / 2) m := by
    rcases Nat.eq_zero_or_pos (k / 2) with hq0 | hqpos
    · rw [hq0]; exact zero_isRepresentable m
    · exact hrep (k / 2) hqpos hqlt
  rcases Nat.mod_two_eq_zero_or_one k with h2 | h2
  · rw [show k = 2 * (k / 2) by omega]; exact repr_two_mul hqrep
  · rw [show k = 2 * (k / 2) + 1 by omega]; exact repr_two_mul_add_one hm1 hqrep

/-- Iterating `two_mul_practical`: `2^n · m` is practical whenever `m` is. -/
theorem two_pow_mul_practical (n : ℕ) {m : ℕ} (h : IsPractical m) :
    IsPractical (2 ^ n * m) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [show 2 ^ (n + 1) * m = 2 * (2 ^ n * m) by ring]
    exact two_mul_practical ih

/-- A concrete new infinite family beyond the powers of two: `2^n · 6` is practical
(e.g. `6, 12, 24, 48, …`). -/
theorem two_pow_mul_six_practical (n : ℕ) : IsPractical (2 ^ n * 6) :=
  two_pow_mul_practical n six_practical

/- ## Structural bounds -/

/-- **For practical `m`, the sum of divisors satisfies `σ(m) ≥ 2m − 1`.** Since `m − 1`
is a sum of divisors, and any such subset must avoid `m` itself (`m > m − 1`), it is a
sum of *proper* divisors; adjoining the divisor `m` gives `σ(m) ≥ (m − 1) + m`. -/
theorem two_mul_sub_one_le_sigma {m : ℕ} (h : IsPractical m) :
    2 * m - 1 ≤ (divisors m).sum id := by
  obtain ⟨hm1, hrep⟩ := h
  rcases Nat.lt_or_ge m 2 with hlt | hge
  · interval_cases m
    simp [divisors, Nat.divisors_one]
  · obtain ⟨S, hS, hsum⟩ := hrep (m - 1) (by omega) (by omega)
    have hmS : m ∉ S := by
      intro hmem
      have hle := Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le i) hmem
      rw [hsum, id_eq] at hle
      omega
    have hsub : insert m S ⊆ divisors m := by
      rw [Finset.insert_subset_iff]
      refine ⟨?_, hS⟩
      rw [divisors, Nat.mem_divisors]
      exact ⟨dvd_refl m, by omega⟩
    have hle : (insert m S).sum id ≤ (divisors m).sum id :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_insert hmS, hsum, id_eq] at hle
    omega

/-- **The only odd practical number is `1`.** A practical `m ≥ 3` is even
(`even_of_practical`), so an odd practical number is `< 3`, hence `1`. -/
theorem odd_practical_eq_one {m : ℕ} (h : IsPractical m) (hodd : Odd m) : m = 1 := by
  rcases Nat.lt_or_ge m 3 with hlt | hge
  · obtain ⟨b, hb⟩ := hodd
    have hm1 := h.1
    omega
  · exfalso
    obtain ⟨a, ha⟩ := even_of_practical hge h
    obtain ⟨b, hb⟩ := hodd
    omega

end Erdos18
