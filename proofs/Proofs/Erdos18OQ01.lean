/-
  Erdős Problem #18 — OQ-01: representability algebra and verified practical numbers

  Erdős Problem #18 (OPEN, $250) studies *practical numbers*: `m` is practical if
  every `1 ≤ k < m` is a sum of distinct divisors of `m`.  The gallery parent
  `Erdos18Problem` sets up `IsRepresentable`, `IsPractical`, and the function
  `h(m)`, and verifies that `1` and `2` are practical.  The open questions concern
  the asymptotic size of `h(m)` (Mertens/Vose-type bounds), out of elementary
  reach.  This file fills in the elementary groundwork the parent omits:

  * the **representability algebra** — `0`, every divisor, `1`, and `m` itself are
    representable (`zero_representable`, `mem_divisors_representable`,
    `one_representable`, `self_representable`);
  * a **decidable bridge** `practical_of_check` turning `IsPractical m` into a
    finite check over `(divisors m).powerset`, and the verified practical numbers
    `4`, `6`, `8` (extending the parent's `1`, `2` along OEIS A005153).

  All results are fully machine-checked (0 axioms, 0 sorries).

  Reference: Srinivasan (1948); OEIS A005153; https://erdosproblems.com/18.
-/

import Mathlib
import Proofs.Erdos18Problem

namespace Erdos18OQ01

open Erdos18 Finset

/-- **0 is representable** (by the empty set of divisors). -/
theorem zero_representable (m : ℕ) : IsRepresentable 0 m :=
  ⟨∅, Finset.empty_subset _, by simp⟩

/-- **Every divisor is representable** (as a singleton). -/
theorem mem_divisors_representable {d m : ℕ} (hd : d ∈ divisors m) :
    IsRepresentable d m :=
  ⟨{d}, Finset.singleton_subset_iff.mpr hd, by simp⟩

/-- **1 is representable** for any `m ≥ 1` (since `1 ∣ m`). -/
theorem one_representable {m : ℕ} (hm : 1 ≤ m) : IsRepresentable 1 m :=
  mem_divisors_representable (Nat.one_mem_divisors.mpr (by omega))

/-- **`m` is representable by its own divisors** for `m ≥ 1` (the singleton `{m}`). -/
theorem self_representable {m : ℕ} (hm : 1 ≤ m) : IsRepresentable m m :=
  mem_divisors_representable (Nat.mem_divisors_self m (by omega))

/-- **Decidable bridge.**  To certify `IsPractical m` it suffices to check, for
    every `1 ≤ k < m`, that some subset of `divisors m` sums to `k` — a finite,
    `decide`-able condition over `(divisors m).powerset`. -/
theorem practical_of_check {m : ℕ} (hm : 1 ≤ m)
    (h : ∀ k ∈ Finset.range m, 1 ≤ k →
      ∃ S ∈ (divisors m).powerset, S.sum id = k) :
    IsPractical m := by
  refine ⟨hm, fun k hk1 hkm => ?_⟩
  obtain ⟨S, hS, hsum⟩ := h k (Finset.mem_range.mpr hkm) hk1
  exact ⟨S, Finset.mem_powerset.mp hS, hsum⟩

/-- **4 is practical** (divisors `{1,2,4}`: `1, 2, 1+2`). -/
theorem four_practical : IsPractical 4 :=
  practical_of_check (by norm_num) (by decide)

/-- **6 is practical** (divisors `{1,2,3,6}`: `1, 2, 3, 1+3, 2+3`). -/
theorem six_practical : IsPractical 6 :=
  practical_of_check (by norm_num) (by decide)

/-- **8 is practical** (divisors `{1,2,4,8}`: `1, 2, 1+2, 4, 1+4, 2+4, 1+2+4`). -/
theorem eight_practical : IsPractical 8 :=
  practical_of_check (by norm_num) (by decide)

/-- **Every power of 2 is practical** — an explicit infinite family, generalising the
    concrete `1, 2, 4, 8, …` cases above.  The divisors of `2^n` are `1, 2, …, 2^n`, and
    every `1 ≤ k < 2^n` is a sum of distinct such powers (the binary expansion).  Proved
    by induction on `n` without invoking binary-digit machinery: a `k` in the upper half
    `[2^n, 2^(n+1))` peels off the top divisor `2^n` (which cannot already appear in a
    subset summing to `k - 2^n < 2^n`) and reduces to the lower half handled by the IH. -/
theorem two_pow_practical (n : ℕ) : IsPractical (2 ^ n) := by
  induction n with
  | zero => simpa using one_practical
  | succ n ih =>
    refine ⟨Nat.pos_of_ne_zero (by positivity), fun k hk1 hk => ?_⟩
    have hsub : divisors (2 ^ n) ⊆ divisors (2 ^ (n + 1)) :=
      Nat.divisors_subset_of_dvd (by positivity) (pow_dvd_pow 2 (Nat.le_succ n))
    rcases lt_or_ge k (2 ^ n) with hlt | hge
    · -- lower half: the IH gives a subset of `divisors (2^n) ⊆ divisors (2^(n+1))`
      obtain ⟨S, hS, hsum⟩ := ih.2 k hk1 hlt
      exact ⟨S, hS.trans hsub, hsum⟩
    · -- upper half: peel off the top divisor `2^n`
      have h2n_mem : (2 : ℕ) ^ n ∈ divisors (2 ^ (n + 1)) :=
        Nat.mem_divisors.mpr ⟨pow_dvd_pow 2 (Nat.le_succ n), by positivity⟩
      rcases eq_or_lt_of_le hge with heq | hgt
      · -- `k = 2^n`, representable as the singleton `{2^n}`
        exact ⟨{2 ^ n}, Finset.singleton_subset_iff.mpr h2n_mem, by
          rw [Finset.sum_singleton]; exact heq⟩
      · -- `2^n < k < 2^(n+1)`: reduce `k - 2^n < 2^n` via the IH, then re-add `2^n`
        have hk'1 : 1 ≤ k - 2 ^ n := by omega
        have hk'lt : k - 2 ^ n < 2 ^ n := by
          have hk2 : k < 2 ^ n * 2 := by rw [pow_succ] at hk; exact hk
          omega
        obtain ⟨S, hS, hsum⟩ := ih.2 (k - 2 ^ n) hk'1 hk'lt
        have h2n_notin : (2 : ℕ) ^ n ∉ S := by
          intro hmem
          have hle : (id (2 ^ n : ℕ)) ≤ S.sum id :=
            Finset.single_le_sum (fun i _ => Nat.zero_le _) hmem
          rw [hsum] at hle
          simp only [id_eq] at hle
          omega
        refine ⟨insert (2 ^ n) S, Finset.insert_subset_iff.mpr ⟨h2n_mem, hS.trans hsub⟩, ?_⟩
        rw [Finset.sum_insert h2n_notin, hsum]
        simp only [id_eq]; omega

end Erdos18OQ01
