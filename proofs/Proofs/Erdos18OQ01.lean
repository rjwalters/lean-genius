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
    `n < 2^k` selects distinct divisors of `2^k` summing to `n`);
  * a **packaging lemma** `practical_represents_le` extending representability to
    the full closed segment `0 ≤ k ≤ m` (boundary cases `0` and `m`);
  * that evenness is **necessary but not sufficient** — `not_practical_ten` /
    `even_not_sufficient`: `10` is even yet not practical (`4` is not a sum of
    distinct divisors of `10`), so the converse of `practical_even` fails.

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

/-- **A practical number represents its entire initial segment.**  The definition
    only asks for `1 ≤ k < m`; this packages the two boundary cases (`k = 0` by the
    empty set, `k = m` by the singleton `{m}`) so that *every* `k ≤ m` is a sum of
    distinct divisors of `m`.  A convenient reformulation of practicality. -/
theorem practical_represents_le {m : ℕ} (hp : IsPractical m) {k : ℕ} (hk : k ≤ m) :
    IsRepresentable k m := by
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0; exact zero_representable m
  · rcases eq_or_lt_of_le hk with heq | hlt
    · subst heq; exact self_representable hp.1
    · exact hp.2 k hpos hlt

/-! ## Evenness is necessary but not sufficient

`practical_even` shows every practical `m ≥ 2` is even.  The converse fails: `10`
is even yet not practical, because `4` is not a sum of distinct divisors of `10`
(the divisors are `{1, 2, 5, 10}`, whose subset sums skip `4`).  So evenness is a
genuine *necessary* condition that is strictly weaker than practicality. -/

/-- **`4` is not representable by divisors of `10`.**  Every divisor of `10` used
    in a subset summing to `4` is itself `≤ 4`, and the divisors of `10` in that
    range are only `1` and `2`; hence the subset lies in `{1,2}` and sums to at
    most `3 < 4`. -/
theorem four_not_representable_ten : ¬ IsRepresentable 4 10 := by
  rintro ⟨S, hSsub, hSsum⟩
  -- Each element of `S` divides `10` and is `≤ 4`, hence is `1` or `2`.
  have hbound : ∀ x ∈ S, x = 1 ∨ x = 2 := by
    intro x hx
    have hdvd : x ∣ 10 := Nat.dvd_of_mem_divisors (hSsub hx)
    have hx1 : 1 ≤ x := Nat.pos_of_mem_divisors (hSsub hx)
    have hxle : x ≤ 4 := by
      calc x = id x := rfl
        _ ≤ S.sum id := Finset.single_le_sum (fun i _ => Nat.zero_le _) hx
        _ = 4 := hSsum
    interval_cases x
    · left; rfl
    · right; rfl
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
  -- So `S ⊆ {1,2}` and its sum is at most `1 + 2 = 3`.
  have hsub : S ⊆ ({1, 2} : Finset ℕ) := fun x hx =>
    (hbound x hx).elim (fun h => by simp [h]) (fun h => by simp [h])
  have hpair : ({1, 2} : Finset ℕ).sum id = 3 := by
    rw [Finset.sum_pair (by norm_num)]; rfl
  have hle : S.sum id ≤ 3 := by
    have := Finset.sum_le_sum_of_subset (f := id) hsub
    rwa [hpair] at this
  rw [hSsum] at hle
  omega

/-- **`10` is even but not practical.**  Since `4 < 10` is not representable
    (`four_not_representable_ten`), `10` fails the practicality condition, even
    though `practical_even` would be satisfied.  This witnesses that the converse
    of `practical_even` is false: not every even number is practical. -/
theorem not_practical_ten : ¬ IsPractical 10 := fun hp =>
  four_not_representable_ten (hp.2 4 (by norm_num) (by norm_num))

/-- **Evenness does not imply practicality.**  `10` is a concrete even
    non-practical number, so `practical_even` is a strictly necessary (not
    sufficient) constraint. -/
theorem even_not_sufficient : ∃ m, Even m ∧ ¬ IsPractical m :=
  ⟨10, ⟨5, by norm_num⟩, not_practical_ten⟩

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
          Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) hmem
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

/-- **Closure under disjoint union of divisor subsets.**  If two *disjoint*
    subsets of `divisors m` sum to `a` and `b`, their union realises `a + b` as a
    sum of distinct divisors, so `a + b` is representable.  This is the additivity
    building block of the representability algebra: partitioning a divisor set
    into disjoint pieces adds the represented values. -/
theorem representable_union {m : ℕ} {S T : Finset ℕ}
    (hS : S ⊆ divisors m) (hT : T ⊆ divisors m) (hd : Disjoint S T) :
    IsRepresentable (S.sum id + T.sum id) m :=
  ⟨S ∪ T, Finset.union_subset hS hT, by rw [Finset.sum_union hd]⟩

/-- **Every representable value is at most `σ(m)`** (the sum of all divisors of
    `m`).  The representing subset `S ⊆ divisors m` has `S.sum id ≤ (divisors
    m).sum id`, so no divisor sum can exceed the total — this is the sharp upper
    end of the representable range `[0, σ(m)]`. -/
theorem representable_le_sigma {k m : ℕ} (h : IsRepresentable k m) :
    k ≤ (divisors m).sum id := by
  obtain ⟨S, hS, hsum⟩ := h
  calc k = S.sum id := hsum.symm
    _ ≤ (divisors m).sum id := Finset.sum_le_sum_of_subset hS

/-- **A practical number `m ≥ 2` satisfies `m - 1 ≤ σ(m)`.**  Since `m - 1` lies
    in `[1, m)` it is representable, so the `σ(m)` upper bound
    `representable_le_sigma` forces `m - 1 ≤ (divisors m).sum id`.  A first
    quantitative necessary condition on the sum of divisors of a practical number,
    complementing the structural `practical_even`. -/
theorem practical_pred_le_sigma {m : ℕ} (hm : 2 ≤ m) (hp : IsPractical m) :
    m - 1 ≤ (divisors m).sum id :=
  representable_le_sigma (hp.2 (m - 1) (by omega) (by omega))

/-! ## Complement symmetry of the representable set

The representable values of `m` are symmetric about `σ(m)/2`: if `k` is a sum of
distinct divisors of `m`, so is its complement `σ(m) - k` (take the divisors NOT
used).  Together with `representable_le_sigma` (every representable value is `≤
σ(m)`) this pins the representable set inside `[0, σ(m)]` and makes it invariant
under `k ↦ σ(m) - k`.  A structural companion to the additive
`representable_union` above. -/

/-- **The full divisor sum `σ(m)` is representable** — by the set of *all*
    divisors of `m`.  This is the top of the representable range `[0, σ(m)]`,
    matching the upper bound `representable_le_sigma`. -/
theorem sigma_representable (m : ℕ) : IsRepresentable ((divisors m).sum id) m :=
  ⟨divisors m, Finset.Subset.refl _, rfl⟩

/-- **Complement symmetry.**  If `k` is representable by divisors of `m`, then so
    is `σ(m) - k`: the divisors left unused by a subset summing to `k` themselves
    sum to `σ(m) - k`.  Hence the representable set is symmetric under
    `k ↦ σ(m) - k`. -/
theorem representable_compl {k m : ℕ} (h : IsRepresentable k m) :
    IsRepresentable ((divisors m).sum id - k) m := by
  obtain ⟨S, hS, hsum⟩ := h
  refine ⟨divisors m \ S, Finset.sdiff_subset, ?_⟩
  have hsd : (divisors m \ S).sum id + S.sum id = (divisors m).sum id :=
    Finset.sum_sdiff hS
  omega

/-- **Practical numbers also represent their TOP segment `[σ(m) - m, σ(m)]`.**
    `practical_represents_le` gives the bottom segment `[0, m]`; reflecting it
    through the complement symmetry `representable_compl` yields the mirror-image
    top segment.  So a practical number represents both ends of `[0, σ(m)]` in a
    full width-`m` block. -/
theorem practical_top_segment {m : ℕ} (hp : IsPractical m) {k : ℕ}
    (hlo : (divisors m).sum id - m ≤ k) (hhi : k ≤ (divisors m).sum id) :
    IsRepresentable k m := by
  -- `σ(m) - k ≤ m`, so the bottom segment represents it; complement back to `k`.
  have hk' : (divisors m).sum id - k ≤ m := by omega
  have hrep := representable_compl (practical_represents_le hp hk')
  have hcancel : (divisors m).sum id - ((divisors m).sum id - k) = k := by omega
  rwa [hcancel] at hrep

/-! ## Full representability of `[0, σ(m)]` for non-abundant practical numbers

`practical_represents_le` gives the bottom segment `[0, m]` and `practical_top_segment`
the mirror-image top segment `[σ(m) - m, σ(m)]`.  These two width-`m` blocks together
cover the whole range `[0, σ(m)]` exactly when they overlap, i.e. when `σ(m) - m ≤ m`,
i.e. `σ(m) ≤ 2m` (`m` deficient or perfect).  In that case a practical number represents
*every* value in `[0, σ(m)]` — the Stewart–Sierpiński characterisation, restricted to the
range the two elementary segments already reach. -/

/-- **A practical number with `σ(m) ≤ 2m` represents the entire interval `[0, σ(m)]`.**
When `m` is deficient or perfect the bottom segment `[0, m]`
(`practical_represents_le`) and the top segment `[σ(m) - m, σ(m)]`
(`practical_top_segment`) overlap and jointly cover `[0, σ(m)]`, so every `k ≤ σ(m)` is a
sum of distinct divisors of `m`.  (For *abundant* practical numbers `σ(m) > 2m` the two
segments leave a genuine gap; the full range still holds but requires Stewart's
ordered-divisor induction, beyond this elementary file — e.g. `12` is practical with
`σ(12) = 28 > 24`.) -/
theorem practical_represents_all_of_sigma_le {m : ℕ} (hp : IsPractical m)
    (hσ : (divisors m).sum id ≤ 2 * m) {k : ℕ} (hk : k ≤ (divisors m).sum id) :
    IsRepresentable k m := by
  by_cases hkm : k ≤ m
  · -- bottom segment `[0, m]`
    exact practical_represents_le hp hkm
  · -- `m < k ≤ σ(m)`; from `σ(m) ≤ 2m` we get `σ(m) - m ≤ m < k`, so the top segment applies
    exact practical_top_segment hp (by omega) hk

/-- **A practical perfect number represents all of `[0, σ(m)] = [0, 2m]`.**  Perfect
numbers satisfy `σ(m) = 2m ≤ 2m`, the boundary case of
`practical_represents_all_of_sigma_le`; every practical perfect number (e.g. `6`, `28`)
represents every value up to `2m` as a sum of distinct divisors. -/
theorem perfect_practical_represents_all {m : ℕ} (hp : IsPractical m)
    (hperf : (divisors m).sum id = 2 * m) {k : ℕ} (hk : k ≤ 2 * m) :
    IsRepresentable k m :=
  practical_represents_all_of_sigma_le hp (by omega) (by omega)

end Erdos18OQ01
