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
    `4`, `6`, `8` (extending the parent's `1`, `2` along OEIS A005153);
  * the first **structural** constraint — `practical_even`: every practical number
    `m ≥ 2` is even (Srinivasan 1948), since `2` must be a sum of distinct divisors,
    and its classification corollary `odd_practical_eq_one` (`1` is the only odd
    practical number);
  * the first **infinite family** — `two_pow_practical`: every power of two `2^k`
    is practical, via `two_pow_representable` (the binary expansion of any
    `n < 2^k` selects distinct divisors of `2^k` summing to `n`).

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

/-- **Every practical number `≥ 2` is even** (Srinivasan 1948).  The first
    *structural* constraint on practical numbers, beyond the representability
    algebra and the small verified examples above.

    Proof: `2` must be a sum of distinct divisors of `m`.  For `m = 2` the claim is
    immediate; for `m ≥ 3` the representing set `S ⊆ divisors m` has `S.sum id = 2`
    with all elements positive, so every element is `≤ 2`.  If `2 ∉ S` every element
    is exactly `1`, forcing `S ⊆ {1}` and `S.sum id ≤ 1 < 2` — contradiction.  Hence
    `2 ∈ S ⊆ divisors m`, i.e. `2 ∣ m`. -/
theorem practical_even {m : ℕ} (hm : 2 ≤ m) (hp : IsPractical m) : 2 ∣ m := by
  rcases eq_or_lt_of_le hm with h2 | h3
  · exact ⟨1, by omega⟩
  · obtain ⟨S, hSsub, hSsum⟩ := hp.2 2 (by norm_num) h3
    by_contra hnot
    have h2S : 2 ∉ S := fun h2mem => hnot (Nat.dvd_of_mem_divisors (hSsub h2mem))
    have hall1 : ∀ x ∈ S, x = 1 := by
      intro x hx
      have hx1 : 1 ≤ x := Nat.pos_of_mem_divisors (hSsub hx)
      have hx2 : x ≤ 2 := by
        calc x = id x := rfl
          _ ≤ S.sum id := Finset.single_le_sum (fun i _ => Nat.zero_le _) hx
          _ = 2 := hSsum
      rcases (by omega : x = 1 ∨ x = 2) with h | h
      · exact h
      · exact absurd (h ▸ hx) h2S
    have hsub1 : S ⊆ ({1} : Finset ℕ) := fun x hx => Finset.mem_singleton.mpr (hall1 x hx)
    have hone : ({1} : Finset ℕ).sum id = 1 := by simp
    have hchain : S.sum id ≤ 1 := by
      have hle : S.sum id ≤ ({1} : Finset ℕ).sum id := Finset.sum_le_sum_of_subset hsub1
      rwa [hone] at hle
    rw [hSsum] at hchain
    exact absurd hchain (by norm_num)

/-- **Restatement of `practical_even` via `Even`.** -/
theorem practical_even' {m : ℕ} (hm : 2 ≤ m) (hp : IsPractical m) : Even m := by
  obtain ⟨c, hc⟩ := practical_even hm hp
  exact ⟨c, by omega⟩

/-- **1 is the only odd practical number.**  Combines `practical_even` (every
    practical `m ≥ 2` is even) with the base case `m = 1`; there is no odd
    practical number beyond `1`. -/
theorem odd_practical_eq_one {m : ℕ} (hp : IsPractical m) (ho : Odd m) : m = 1 := by
  rcases Nat.lt_or_ge m 2 with h | h
  · have := hp.1; omega
  · obtain ⟨d, hd⟩ := practical_even h hp
    obtain ⟨e, he⟩ := ho
    omega

/-- **Every `n < 2^k` is a sum of distinct divisors of `2^k`.**  The binary
    expansion of `n` selects distinct powers of two below `2^k`, each a divisor
    of `2^k`.  Proved by induction on `k`: when `2^k ≤ n < 2^{k+1}` the high bit
    `2^k` is peeled off and the remainder `n - 2^k < 2^k` is handled by the
    inductive hypothesis (and `2^k` is fresh, since every element of the
    remainder's representing set is `≤ n - 2^k < 2^k`). -/
theorem two_pow_representable (k : ℕ) {n : ℕ} (hn : n < 2 ^ k) :
    IsRepresentable n (2 ^ k) := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0; exact zero_representable _
  | succ k ih =>
    have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hdvd : (2 : ℕ) ^ k ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (Nat.le_succ k)
    have hsub : divisors (2 ^ k) ⊆ divisors (2 ^ (k + 1)) :=
      Nat.divisors_subset_of_dvd (by positivity) hdvd
    rcases lt_or_ge n (2 ^ k) with hlt | hge
    · obtain ⟨S, hSsub, hSsum⟩ := ih hlt
      exact ⟨S, hSsub.trans hsub, hSsum⟩
    · have hlt2 : n - 2 ^ k < 2 ^ k := by omega
      obtain ⟨S, hSsub, hSsum⟩ := ih hlt2
      have hnotmem : (2 : ℕ) ^ k ∉ S := by
        intro hmem
        have hle : (2 : ℕ) ^ k ≤ S.sum id :=
          Finset.single_le_sum (fun i _ => Nat.zero_le _) hmem
        rw [hSsum] at hle
        omega
      refine ⟨insert (2 ^ k) S, ?_, ?_⟩
      · rw [Finset.insert_subset_iff]
        exact ⟨Nat.mem_divisors.mpr ⟨hdvd, by positivity⟩, hSsub.trans hsub⟩
      · rw [Finset.sum_insert hnotmem, hSsum]
        simp only [id_eq]
        omega

/-- **Every power of two is practical** — the first *infinite* family of
    practical numbers in this file (the parent and the small examples `4,6,8`
    above cover only finitely many).  The divisors of `2^k` are exactly
    `1,2,4,…,2^k`, so the binary expansion of any `1 ≤ n < 2^k` exhibits it as a
    sum of distinct divisors (`two_pow_representable`). -/
theorem two_pow_practical (k : ℕ) : IsPractical (2 ^ k) :=
  ⟨Nat.one_le_pow k 2 (by norm_num), fun _ _ hn => two_pow_representable k hn⟩

end Erdos18OQ01
