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

/-- **Full-range representation when the abundancy is at most `2`.**  The two known
    segments — the bottom `[0, m]` (`practical_represents_le`) and the top
    `[σ(m) - m, σ(m)]` (`practical_top_segment`) — together tile the whole range
    `[0, σ(m)]` exactly when they meet, i.e. when `σ(m) - m ≤ m`, that is
    `σ(m) ≤ 2m` (abundancy `σ(m)/m ≤ 2`).  Under that hypothesis a practical `m`
    represents *every* `k ≤ σ(m)` — a partial form of the classical fact that a
    practical number represents all of `[1, σ(m)]`.  The hypothesis holds for e.g.
    `2, 4, 8` and every `2^k` (and, with equality, for `6`), though it can fail for
    more abundant practicals such as `12` (`σ(12) = 28 > 24`). -/
theorem practical_represents_all_of_sigma_le_two_mul {m : ℕ} (hp : IsPractical m)
    (hσ : (divisors m).sum id ≤ 2 * m) {k : ℕ} (hk : k ≤ (divisors m).sum id) :
    IsRepresentable k m := by
  rcases le_or_gt k m with hle | hgt
  · exact practical_represents_le hp hle
  · exact practical_top_segment hp (by omega) hk

/-- **A practical number represents its entire bottom double-block `[0, 2m)`.**
    `practical_represents_le` covers `[0, m]`; this doubles it to `[0, 2m)` using *only*
    divisors of `m` (no divisors of `2m`).  For `m ≤ k < 2m` write `k = m + (k - m)` with
    `k - m < m`, represent the remainder `k - m` by divisors of `m`, and adjoin the divisor
    `m` itself — fresh, since the remainder's representing set sums to `k - m < m`, so none
    of its elements is `m`.  This is the `practical_two_mul` peel argument kept inside
    `divisors m`, the reusable primitive under both the doubling closure and the
    `σ`-lower-bound corollary below.  It is tight: for `m = 2ᵏ` the range `[0, 2m)` is
    exactly `[0, σ(m)]` (`σ(2ᵏ) = 2m − 1`). -/
theorem practical_represents_lt_two_mul {m : ℕ} (hp : IsPractical m) {k : ℕ}
    (hk : k < 2 * m) : IsRepresentable k m := by
  have hm1 : 1 ≤ m := hp.1
  rcases lt_or_ge k m with hlt | hge
  · exact practical_represents_le hp (le_of_lt hlt)
  · -- `m ≤ k < 2m`: peel the divisor `m`, represent the remainder `k - m < m`.
    have hj : k - m < m := by omega
    obtain ⟨S, hS, hsum⟩ := practical_represents_le hp (le_of_lt hj)
    have hmS : m ∉ S := by
      intro hmem
      have hle : m ≤ S.sum id :=
        Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) hmem
      rw [hsum] at hle
      omega
    refine ⟨insert m S, ?_, ?_⟩
    · rw [Finset.insert_subset_iff]
      exact ⟨Nat.mem_divisors.mpr ⟨dvd_refl m, by omega⟩, hS⟩
    · rw [Finset.sum_insert hmS, hsum]
      simp only [id_eq]
      omega

/-- **Every practical number satisfies `2m − 1 ≤ σ(m)`.**  Since `2m − 1 < 2m` it is
    representable (`practical_represents_lt_two_mul`), so the `σ(m)` ceiling
    `representable_le_sigma` forces `2m − 1 ≤ (divisors m).sum id`.  This sharpens
    `practical_pred_le_sigma` (`m − 1 ≤ σ(m)`) to the tight bound — practical numbers are
    "almost perfect or abundant"; equality `σ(m) = 2m − 1` holds exactly for the powers of
    two `m = 2ᵏ`. -/
theorem practical_two_mul_pred_le_sigma {m : ℕ} (hm : 1 ≤ m) (hp : IsPractical m) :
    2 * m - 1 ≤ (divisors m).sum id :=
  representable_le_sigma (practical_represents_lt_two_mul hp (by omega))

/-! ## Full-range representation up to abundancy `4`

`practical_represents_all_of_sigma_le_two_mul` shows a practical `m` represents the
*whole* range `[0, σ(m)]` when its abundancy `σ(m)/m` is at most `2`, by tiling with
the two width-`m` end segments.  The bottom *double*-block `[0, 2m)`
(`practical_represents_lt_two_mul`) is twice as wide, and reflecting it through the
complement symmetry `representable_compl` gives an equally wide top block; the two
together reach all the way up to abundancy `4`.  This band `(2, 4)` contains the bulk
of the small practicals not already covered (e.g. `12, 20, 24, 120`). -/

/-- **Practical numbers represent their entire TOP double-block `(σ(m) − 2m, σ(m)]`.**
    Reflecting the bottom double-block `[0, 2m)` (`practical_represents_lt_two_mul`)
    through the complement symmetry `representable_compl` yields a width-`2m` top
    block — twice the width of `practical_top_segment`.  Concretely, whenever
    `σ(m) − k < 2m` (with `k ≤ σ(m)`), the reflected value `σ(m) − k` lies in the
    bottom block and is representable, and complementing it back recovers `k`. -/
theorem practical_top_block {m : ℕ} (hp : IsPractical m) {k : ℕ}
    (hk : k ≤ (divisors m).sum id) (hlo : (divisors m).sum id - k < 2 * m) :
    IsRepresentable k m := by
  have hrep := representable_compl (practical_represents_lt_two_mul hp hlo)
  have hcancel : (divisors m).sum id - ((divisors m).sum id - k) = k := by omega
  rwa [hcancel] at hrep

/-- **Full-range representation when the abundancy is below `4`.**  The bottom
    double-block `[0, 2m)` (`practical_represents_lt_two_mul`) and its mirror image
    the top double-block `(σ(m) − 2m, σ(m)]` (`practical_top_block`) overlap — and so
    tile the whole range `[0, σ(m)]` — exactly when `σ(m) − 2m < 2m`, that is
    `σ(m) < 4m` (abundancy `σ(m)/m < 4`).  Under that hypothesis a practical `m`
    represents *every* `k ≤ σ(m)`.  This strictly strengthens
    `practical_represents_all_of_sigma_le_two_mul` (abundancy `≤ 2`): it additionally
    covers the band `(2, 4)`, e.g. `12` (`σ = 28 < 48`), `20` (`σ = 42 < 80`),
    `24` (`σ = 60 < 96`), and `120` (`σ = 360 < 480`). -/
theorem practical_represents_all_of_sigma_lt_four_mul {m : ℕ} (hp : IsPractical m)
    (hσ : (divisors m).sum id < 4 * m) {k : ℕ} (hk : k ≤ (divisors m).sum id) :
    IsRepresentable k m := by
  rcases lt_or_ge k (2 * m) with hlt | hge
  · exact practical_represents_lt_two_mul hp hlt
  · exact practical_top_block hp hk (by omega)

/-! ## Multiplicative closure under doubling

If `m` is practical, so is `2m`.  This is the smallest case of the
Stewart–Sierpiński multiplicative criterion (`mp` is practical when `m` is
practical and `p ≤ σ(m) + 1` is prime, here `p = 2`), and it strengthens
`two_pow_practical` from a single family to a *generator*: doubling any practical
number stays practical, so from each practical `m` the whole chain `m, 2m, 4m, …`
is practical (`practical_two_pow_mul`).  With `m = 1` this recovers the powers of
two, but it also yields new families such as `6·2^k`, `20·2^k`, `28·2^k`. -/

/-- **Doubling preserves practicality.**  If `m` is practical then `2m` is
    practical.  For a target `1 ≤ k < 2m`: if `k < m` it is already a sum of
    distinct divisors of `m ∣ 2m`; if `m ≤ k < 2m`, write `k = m + (k - m)` with
    `k - m < m`, represent the remainder `k - m` by divisors of `m`, and adjoin
    the divisor `m` of `2m` (fresh, since the remainder's representing set sums to
    `k - m < m`, so none of its elements can equal `m`). -/
theorem practical_two_mul {m : ℕ} (hp : IsPractical m) : IsPractical (2 * m) := by
  have hm1 : 1 ≤ m := hp.1
  have hmdvd : m ∣ 2 * m := ⟨2, by ring⟩
  have hsub : divisors m ⊆ divisors (2 * m) :=
    Nat.divisors_subset_of_dvd (by omega) hmdvd
  refine ⟨by omega, fun k hk1 hk2m => ?_⟩
  rcases lt_or_ge k m with hlt | hge
  · -- `k < m`: representable by divisors of `m`, which all divide `2m`.
    obtain ⟨S, hS, hsum⟩ := practical_represents_le hp (le_of_lt hlt)
    exact ⟨S, hS.trans hsub, hsum⟩
  · -- `m ≤ k < 2m`: peel the divisor `m` and represent the remainder `k - m < m`.
    have hj : k - m < m := by omega
    obtain ⟨S, hS, hsum⟩ := practical_represents_le hp (le_of_lt hj)
    have hmS : m ∉ S := by
      intro hmem
      have hle : m ≤ S.sum id :=
        Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) hmem
      rw [hsum] at hle
      omega
    refine ⟨insert m S, ?_, ?_⟩
    · rw [Finset.insert_subset_iff]
      exact ⟨Nat.mem_divisors.mpr ⟨hmdvd, by omega⟩, hS.trans hsub⟩
    · rw [Finset.sum_insert hmS, hsum]
      simp only [id_eq]
      omega

/-- **Every `2^k · m` with `m` practical is practical** — an infinite family
    generated from *any* practical number by repeated doubling
    (`practical_two_mul`).  Taking `m = 1` recovers `two_pow_practical` (the powers
    of two); taking `m = 6, 20, 28, …` gives further infinite families of
    practical numbers. -/
theorem practical_two_pow_mul {m : ℕ} (hp : IsPractical m) (k : ℕ) :
    IsPractical (2 ^ k * m) := by
  induction k with
  | zero => simpa using hp
  | succ k ih =>
    have hrw : 2 ^ (k + 1) * m = 2 * (2 ^ k * m) := by ring
    rw [hrw]
    exact practical_two_mul ih

/-! ## Multiplicative closure under products

The set of practical numbers is closed under multiplication: if `m` and `n` are
both practical, so is `m · n`.  This is the full multiplicative-closure property
(the Stewart–Sierpiński theory specialises it to prime factors); it strictly
generalises `practical_two_mul` (the case `n = 2`, since `2` is practical) and,
via `two_pow_practical`, the whole `2^k · m` generator `practical_two_pow_mul`. -/

/-- **Scaling a representation.**  If `k` is a sum of distinct divisors of `m`,
    then `c · k` is a sum of distinct divisors of `c · m` (scale each divisor used
    by the factor `c ≥ 1`).  The scaled divisors `c · d` divide `c · m` and remain
    distinct because multiplication by `c ≥ 1` is injective. -/
theorem representable_scale (c : ℕ) (hc : 1 ≤ c) {k m : ℕ}
    (h : IsRepresentable k m) : IsRepresentable (c * k) (c * m) := by
  obtain ⟨S, hS, hsum⟩ := h
  have hinj : ∀ a ∈ S, ∀ b ∈ S, c * a = c * b → a = b :=
    fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (by omega) hab
  refine ⟨S.image (c * ·), ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hdS, rfl⟩ := hx
    have hdvd : d ∣ m := Nat.dvd_of_mem_divisors (hS hdS)
    have hm0 : m ≠ 0 := (Nat.mem_divisors.mp (hS hdS)).2
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left c hdvd, Nat.mul_ne_zero (by omega) hm0⟩
  · rw [Finset.sum_image hinj]
    calc ∑ d ∈ S, id (c * d) = c * ∑ d ∈ S, d := by simp only [id_eq]; rw [Finset.mul_sum]
      _ = c * S.sum id := rfl
      _ = c * k := by rw [hsum]

/-- **Practical numbers are closed under multiplication.**  If `m` and `n` are both
    practical, so is `m · n`.  For a target `1 ≤ k < m·n`, write `k = m·q + r` with
    `r = k % m < m` and `q = k / m < n`.  Represent the quotient `q` by divisors of
    `n` and scale that representation by `m` (`representable_scale`) to get a sum of
    distinct divisors of `m·n` equal to `m·q`, each `≥ m`; represent the remainder
    `r` by divisors of `m ∣ m·n`, each `≤ r < m`.  The two divisor sets are disjoint
    (multiples of `m` vs. values `< m`), so their union represents `m·q + r = k`. -/
theorem practical_mul {m n : ℕ} (hpm : IsPractical m) (hpn : IsPractical n) :
    IsPractical (m * n) := by
  have hm1 : 1 ≤ m := hpm.1
  have hn1 : 1 ≤ n := hpn.1
  refine ⟨Nat.mul_pos hpm.1 hpn.1, fun k hk1 hkmn => ?_⟩
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hrm : k % m < m := Nat.mod_lt k (by omega)
  have hqn : k / m < n := (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.mul_comm]; exact hkmn)
  have hdecomp : m * (k / m) + k % m = k := Nat.div_add_mod k m
  -- represent quotient `q = k/m` by divisors of `n`, remainder `r = k%m` by divisors of `m`.
  obtain ⟨Sq, hSq, hSqsum⟩ := practical_represents_le hpn (le_of_lt hqn)
  obtain ⟨Sr, hSr, hSrsum⟩ := practical_represents_le hpm (le_of_lt hrm)
  -- scaled quotient set: `A = m · Sq ⊆ divisors (m·n)`, sums to `m·q`, elements `≥ m`.
  have hminj : ∀ a ∈ Sq, ∀ b ∈ Sq, m * a = m * b → a = b :=
    fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (by omega) hab
  set A := Sq.image (m * ·) with hAdef
  have hAsub : A ⊆ divisors (m * n) := by
    intro x hx
    rw [hAdef, Finset.mem_image] at hx
    obtain ⟨d, hdSq, rfl⟩ := hx
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors (hSq hdSq)
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left m hdvd, hmn0⟩
  have hAsum : A.sum id = m * (k / m) := by
    rw [hAdef, Finset.sum_image hminj]
    calc ∑ d ∈ Sq, id (m * d) = m * ∑ d ∈ Sq, d := by simp only [id_eq]; rw [Finset.mul_sum]
      _ = m * Sq.sum id := rfl
      _ = m * (k / m) := by rw [hSqsum]
  -- remainder set embeds into divisors of `m·n` since `m ∣ m·n`.
  have hBsub : Sr ⊆ divisors (m * n) :=
    hSr.trans (Nat.divisors_subset_of_dvd hmn0 ⟨n, rfl⟩)
  -- disjointness: `A`-elements are `≥ m`, `Sr`-elements are `≤ r < m`.
  have hdisj : Disjoint A Sr := by
    rw [Finset.disjoint_left]
    intro a haA haSr
    rw [hAdef, Finset.mem_image] at haA
    obtain ⟨d, hdSq, rfl⟩ := haA
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (hSq hdSq)
    have hage : m ≤ m * d := le_mul_of_one_le_right (by omega) hd1
    have hle : m * d ≤ Sr.sum id :=
      Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) haSr
    rw [hSrsum] at hle
    omega
  have hunion := representable_union hAsub hBsub hdisj
  rw [hAsum, hSrsum, hdecomp] at hunion
  exact hunion

/-- **Practical numbers are closed under powers.**  If `m` is practical then so is
    every power `m ^ k`.  This is the iterate of `practical_mul` starting from the
    trivially practical `1 = m ^ 0` (`Erdos18.one_practical`): each factor of `m`
    keeps the product practical.  In particular every practical base generates an
    infinite family of practical numbers `m, m², m³, …`. -/
theorem practical_pow {m : ℕ} (hp : IsPractical m) (k : ℕ) : IsPractical (m ^ k) := by
  induction k with
  | zero => simpa using one_practical
  | succ k ih => rw [pow_succ]; exact practical_mul ih hp

/-- **Powers of six are practical.**  Instantiating `practical_pow` at the verified
    practical base `6` gives the infinite family `1, 6, 36, 216, …` of practical
    numbers — a family with an odd prime factor, distinct from the powers of two
    `two_pow_practical`. -/
theorem six_pow_practical (k : ℕ) : IsPractical (6 ^ k) :=
  practical_pow six_practical k

/-! ## Representability transfers along divisibility of the modulus

Every representability transfer inside this file (`two_pow_representable`,
`practical_two_mul`, `practical_mul`) ends with the same inlined step: a subset of
`divisors d` is also a subset of `divisors m` whenever `d ∣ m`, so a value representable
by divisors of `d` is representable by divisors of `m`.  The lemma below names that step
once; the two examples that follow use it to round out the file's non-example
(`not_practical_three`, the smallest odd non-practical, complementing the even
`not_practical_ten`) and to exhibit a practical number produced purely by the closure
machinery (`twelve_practical = 2·6`, via `practical_two_mul`, rather than by `decide`). -/

/-- **Representability transfers to any multiple of the modulus.**  If `d ∣ m` (with
    `m ≠ 0`) and `k` is a sum of distinct divisors of `d`, then `k` is a sum of distinct
    divisors of `m` — the same subset works, since `divisors d ⊆ divisors m`.  This is the
    named form of the `hS.trans (Nat.divisors_subset_of_dvd …)` step inlined throughout
    `two_pow_representable`, `practical_two_mul`, and `practical_mul`. -/
theorem representable_of_dvd {d m k : ℕ} (hdm : d ∣ m) (hm : m ≠ 0)
    (h : IsRepresentable k d) : IsRepresentable k m := by
  obtain ⟨S, hS, hsum⟩ := h
  exact ⟨S, hS.trans (Nat.divisors_subset_of_dvd hm hdm), hsum⟩

/-- **`3` is not practical** — the smallest odd non-practical number.  Immediate from
    `odd_practical_eq_one` (`1` is the only odd practical number): `3` is odd and `≠ 1`.
    Together with `not_practical_ten` (the smallest *even* non-practical) this pins down the
    two flavours of failure. -/
theorem not_practical_three : ¬ IsPractical 3 := fun hp => by
  have := odd_practical_eq_one hp (by decide)
  omega

/-- **`12` is practical**, obtained purely from the closure machinery: `12 = 2·6` and `6`
    is practical (`six_practical`), so `practical_two_mul` gives `IsPractical (2·6)`.  A new
    verified practical number reached without any `decide`, illustrating that doubling
    generates fresh members (`12` extends the OEIS A005153 list `1,2,4,6,8` past this file's
    small examples). -/
theorem twelve_practical : IsPractical 12 := by
  have h : IsPractical (2 * 6) := practical_two_mul six_practical
  norm_num at h
  exact h

/-- **There are infinitely many practical numbers.**  The set of practical numbers is
    infinite: the powers of two `2^k` are all practical (`two_pow_practical`) and
    `k ↦ 2^k` is injective (`Nat.pow_right_injective`), so they form an infinite family
    inside `{m | IsPractical m}`.  This packages the file's first infinite family into
    the global statement that practical numbers never run out. -/
theorem practical_infinite : {m : ℕ | IsPractical m}.Infinite :=
  Set.infinite_of_injective_forall_mem
    (Nat.pow_right_injective (le_refl 2)) (fun k => two_pow_practical k)

/-- **Practical numbers are unbounded.**  For every `N` there is a practical number
    exceeding it — the power of two `2^N > N` (`Nat.lt_two_pow_self`), practical by
    `two_pow_practical`.  The explicit-witness form of `practical_infinite`. -/
theorem exists_practical_gt (N : ℕ) : ∃ m, N < m ∧ IsPractical m :=
  ⟨2 ^ N, N.lt_two_pow_self, two_pow_practical N⟩

/-! ## Sharpness of the `σ`-lower bound: powers of two are extremal

`practical_two_mul_pred_le_sigma` shows every practical `m ≥ 1` satisfies the tight
divisor-sum bound `2m − 1 ≤ σ(m)`.  Here we compute `σ(2ᵏ)` exactly and find it
*equals* `2·2ᵏ − 1`, so the powers of two — the file's flagship infinite family
(`two_pow_practical`) — attain the bound with equality.  Equivalently `2ᵏ` is a
"almost perfect" number: its proper-divisor sum is `2ᵏ − 1 = 2ᵏ − 1`, one short of
perfect.  (Whether any *other* almost-perfect numbers exist is a famous open
problem, so only this extremal direction is elementary.) -/

/-- **Geometric divisor sum.**  `∑_{i<n} 2ⁱ = 2ⁿ − 1`, the running total of powers of
    two.  Proved by induction: appending the top term `2ⁿ` to `2ⁿ − 1` gives
    `2ⁿ⁺¹ − 1`. -/
private theorem sum_range_two_pow (n : ℕ) :
    ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have : 0 < 2 ^ n := by positivity
    omega

/-- **`σ(2ᵏ) = 2ᵏ⁺¹ − 1`.**  The divisors of `2ᵏ` are exactly `1, 2, 4, …, 2ᵏ`
    (`Nat.divisors_prime_pow` for the prime `2`), whose sum is the geometric total
    `∑_{i≤k} 2ⁱ = 2ᵏ⁺¹ − 1` (`sum_range_two_pow`).  This is the exact value of the
    divisor sum for the file's flagship infinite family. -/
theorem sigma_two_pow (k : ℕ) :
    (divisors (2 ^ k)).sum id = 2 ^ (k + 1) - 1 := by
  -- `Erdos18.divisors` is definitionally `Nat.divisors`; unfold to expose the prime-power form.
  show (Nat.divisors (2 ^ k)).sum id = 2 ^ (k + 1) - 1
  rw [Nat.divisors_prime_pow Nat.prime_two, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, id_eq]
  exact sum_range_two_pow (k + 1)

/-- **`σ(2ᵏ) = 2·2ᵏ − 1`** — the same value as `sigma_two_pow`, written to match the
    general lower bound `practical_two_mul_pred_le_sigma` (`2m − 1 ≤ σ(m)`).  So the
    powers of two attain that bound with *equality*. -/
theorem sigma_two_pow_eq_two_mul_pred (k : ℕ) :
    (divisors (2 ^ k)).sum id = 2 * 2 ^ k - 1 := by
  rw [sigma_two_pow, pow_succ, Nat.mul_comm]

/-- **The lower bound `2m − 1 ≤ σ(m)` is sharp.**  Every power of two is practical
    (`two_pow_practical`) *and* meets the `practical_two_mul_pred_le_sigma` bound with
    equality (`sigma_two_pow_eq_two_mul_pred`).  Hence the bound cannot be improved:
    there are practical numbers of arbitrarily large size with `σ(m) = 2m − 1`
    exactly. -/
theorem sigma_lower_bound_tight (k : ℕ) :
    IsPractical (2 ^ k) ∧ (divisors (2 ^ k)).sum id = 2 * 2 ^ k - 1 :=
  ⟨two_pow_practical k, sigma_two_pow_eq_two_mul_pred k⟩

/-! ## The third-smallest divisor: `d₃ ≤ 4`

`practical_even` shows the smallest prime factor of a practical `m ≥ 2` is `2`
(equivalently the second-smallest divisor is `d₂ = 2`).  The next structural
constraint comes from requiring `4` itself to be a sum of distinct divisors: the
only such sums are `{4}` and `{1, 3}`, so a practical `m > 4` must be divisible by
`4` or by `3` — its third-smallest divisor is at most `4`.  Combined with
`practical_even` (`2 ∣ m`), the `3`-case sharpens to `6 ∣ m`, so **every practical
number exceeding `4` is a multiple of `4` or of `6`** (the two smallest practical
numbers above `2`).  This is the `d₃ ≤ 4` step of the classical
Stewart–Sierpiński divisor ordering, stated in divisibility form; it mirrors the
`four_not_representable_ten` obstruction (`10` fails practicality precisely because
`4 = {1,3}` needs `3 ∣ 10`, which is false, and `4 ∤ 10`). -/

/-- **A practical number `> 4` is divisible by `3` or by `4`.**  Since `4 < m`, the
    value `4` must be a sum of distinct divisors of `m` (`hp.2`).  The representing
    set `S ⊆ divisors m` has `S.sum id = 4` with all elements positive, so each is
    `≤ 4`.  If neither `3 ∈ S` nor `4 ∈ S`, every element lies in `{1, 2}`, forcing
    `S ⊆ {1, 2}` and `S.sum id ≤ 3 < 4` — contradiction.  Hence `3 ∈ S` or `4 ∈ S`,
    i.e. `3 ∣ m` or `4 ∣ m`: the third-smallest divisor of `m` is at most `4`. -/
theorem practical_three_or_four_dvd {m : ℕ} (hm : 4 < m) (hp : IsPractical m) :
    3 ∣ m ∨ 4 ∣ m := by
  obtain ⟨S, hSsub, hSsum⟩ := hp.2 4 (by norm_num) hm
  by_cases h4 : (4 : ℕ) ∈ S
  · exact Or.inr (Nat.dvd_of_mem_divisors (hSsub h4))
  by_cases h3 : (3 : ℕ) ∈ S
  · exact Or.inl (Nat.dvd_of_mem_divisors (hSsub h3))
  -- Neither `3` nor `4` is in `S`, so every element is `1` or `2`.
  exfalso
  have hsub : S ⊆ ({1, 2} : Finset ℕ) := by
    intro x hx
    have hx1 : 1 ≤ x := Nat.pos_of_mem_divisors (hSsub hx)
    have hxle : x ≤ 4 := by
      calc x = id x := rfl
        _ ≤ S.sum id := Finset.single_le_sum (fun i _ => Nat.zero_le _) hx
        _ = 4 := hSsum
    have hx3 : x ≠ 3 := by rintro rfl; exact h3 hx
    have hx4 : x ≠ 4 := by rintro rfl; exact h4 hx
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hpair : ({1, 2} : Finset ℕ).sum id = 3 := by
    rw [Finset.sum_pair (by norm_num)]; rfl
  have hle : S.sum id ≤ 3 := by
    have h := Finset.sum_le_sum_of_subset (f := id) hsub
    rwa [hpair] at h
  rw [hSsum] at hle
  omega

/-- **Every practical number `> 4` is a multiple of `4` or of `6`.**  By
    `practical_three_or_four_dvd` a practical `m > 4` satisfies `3 ∣ m ∨ 4 ∣ m`.  In
    the `4 ∣ m` case we are done; in the `3 ∣ m` case combine it with `2 ∣ m`
    (`practical_even`, valid since `m ≥ 2`) via coprimality of `2` and `3` to get
    `6 ∣ m`.  So the third-smallest divisor being `≤ 4` forces `m` into the two
    residue families `4 ∣ m` and `6 ∣ m` — the divisibility shadow of the fact that
    `4` and `6` are the two smallest practical numbers above `2`. -/
theorem practical_four_or_six_dvd {m : ℕ} (hm : 4 < m) (hp : IsPractical m) :
    4 ∣ m ∨ 6 ∣ m := by
  rcases practical_three_or_four_dvd hm hp with h3 | h4
  · refine Or.inr ?_
    have h2 : 2 ∣ m := practical_even (by omega) hp
    have h6 := Nat.Coprime.mul_dvd_of_dvd_of_dvd (show Nat.Coprime 2 3 by decide) h2 h3
    norm_num at h6
    exact h6
  · exact Or.inl h4

/-! ## First bounds on the representation function `h(m)`

Erdős Problem #18 is, at heart, about the function `h(m)` defined in the parent
`Erdos18Problem`: the minimum number of divisors of `m` that already suffice to
represent every `1 ≤ k < m` as a sum of distinct elements.  The open questions
(`h(m) < (log log m)^{O(1)}` infinitely often; `h(n!)` bounds) are analytic, but
`h` has had *no* theorems proved about it in the gallery so far.  This section
supplies the two elementary bracketing bounds and the first exact computation.

The **upper bound** `h(m) ≤ d(m)` is immediate: for practical `m` the full divisor
set already witnesses the covering condition, so its cardinality `d(m)` lies in the
`sInf` set.

The **lower bound** `m ≤ 2^{h(m)}` is a counting argument: a covering set `S` of
size `s = h(m)` must realise the `m` distinct values `0, 1, …, m-1` as distinct
subset sums, and `S` has only `2^s` subsets, so `m ≤ 2^s`.  Equivalently
`h(m) ≥ log₂ m`.

Together these pin `h(2^k)` **exactly**: the lower bound forces `h(2^k) ≥ k`, and
the `k` divisors `1, 2, …, 2^{k-1}` (the binary digits) cover `[1, 2^k)`, giving
`h(2^k) ≤ k`.  So `h(2^k) = k` — the first exact value of the Erdős #18 function in
the gallery. -/

/-- **Subset-counting bound.**  If every `k < N` is a sum of distinct elements of a
    finite set `S` (a covering of the initial segment `[0, N)`), then `N ≤ 2^{|S|}`.
    Indeed each `k < N` picks out a subset of `S` whose sum is `k`; distinct `k` give
    distinct subsets (they have distinct sums), so the `N` values inject into the
    `2^{|S|}` subsets of `S`.  This is the combinatorial core of the `h(m)` lower
    bound. -/
theorem card_le_two_pow_card_of_covers {S : Finset ℕ} {N : ℕ}
    (hcov : ∀ k, k < N → ∃ T ⊆ S, T.sum id = k) : N ≤ 2 ^ S.card := by
  classical
  -- Total choice function: for each `k` pick a subset of `S` summing to `k` (∅ otherwise).
  set g : ℕ → Finset ℕ := fun k => if h : ∃ T, T ⊆ S ∧ T.sum id = k then h.choose else ∅
    with hgdef
  have hg : ∀ k, k < N → g k ⊆ S ∧ (g k).sum id = k := by
    intro k hk
    obtain ⟨T, hT, hsum⟩ := hcov k hk
    have hex : ∃ T, T ⊆ S ∧ T.sum id = k := ⟨T, hT, hsum⟩
    rw [hgdef]
    simp only [dif_pos hex]
    exact ⟨hex.choose_spec.1, hex.choose_spec.2⟩
  -- `g` maps `range N` into `S.powerset` and is injective there (sums distinguish).
  have hmaps : Set.MapsTo g (↑(Finset.range N)) (↑(S.powerset)) := by
    intro k hk
    exact Finset.mem_powerset.mpr (hg k (Finset.mem_range.mp hk)).1
  have hinj : Set.InjOn g (Finset.range N) := by
    intro a ha b hb hab
    calc a = (g a).sum id := (hg a (Finset.mem_range.mp ha)).2.symm
      _ = (g b).sum id := by rw [hab]
      _ = b := (hg b (Finset.mem_range.mp hb)).2
  have hcard := Finset.card_le_card_of_injOn g hmaps hinj
  rwa [Finset.card_range, Finset.card_powerset] at hcard

/-- **Upper bound `h(m) ≤ d(m)`.**  For a practical `m` the *entire* divisor set
    already covers every `1 ≤ k < m` (that is exactly practicality), so its
    cardinality `d(m) = (divisors m).card` belongs to the `sInf` set defining `h`.
    Hence `h(m)` — the least such cardinality — is at most `d(m)`. -/
theorem h_le_card_divisors {m : ℕ} (hp : IsPractical m) :
    h m ≤ (divisors m).card := by
  apply Nat.sInf_le
  refine ⟨divisors m, Finset.Subset.refl _, rfl, ?_⟩
  intro k hk1 hkm
  obtain ⟨T, hT, hsum⟩ := hp.2 k hk1 hkm
  exact ⟨T, hT, hsum⟩

/-- **Lower bound `m ≤ 2^{h(m)}`.**  A practical `m` has a covering divisor set `S`
    of size `h(m)` (the `sInf` is attained, as the set is nonempty by
    `h_le_card_divisors`).  `S` must realise the `m` distinct values `0, …, m-1` as
    distinct subset sums, and `S` has only `2^{h(m)}` subsets, so `m ≤ 2^{h(m)}`
    (`card_le_two_pow_card_of_covers`).  Equivalently `h(m) ≥ log₂ m`: representing
    all of `[1, m)` needs at least logarithmically many divisors. -/
theorem le_two_pow_h {m : ℕ} (hp : IsPractical m) : m ≤ 2 ^ h m := by
  -- The `sInf` set is nonempty: the full divisor set is a covering.
  have hne : {s : ℕ | ∃ S : Finset ℕ, S ⊆ divisors m ∧ S.card = s ∧
      ∀ k, 1 ≤ k → k < m → ∃ T : Finset ℕ, T ⊆ S ∧ T.sum id = k}.Nonempty := by
    refine ⟨(divisors m).card, divisors m, Finset.Subset.refl _, rfl, ?_⟩
    intro k hk1 hkm
    obtain ⟨T, hT, hsum⟩ := hp.2 k hk1 hkm
    exact ⟨T, hT, hsum⟩
  -- Hence `h m` is attained by some covering set `S` of that size.
  obtain ⟨S, _hSsub, hScard, hcov⟩ := Nat.sInf_mem hne
  -- Extend the covering to `k = 0` (empty subset) and apply the counting bound.
  have hcov' : ∀ k, k < m → ∃ T ⊆ S, T.sum id = k := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · exact ⟨∅, Finset.empty_subset _, by simp [h0]⟩
    · exact hcov k hpos hk
  have hbound := card_le_two_pow_card_of_covers hcov'
  rwa [hScard] at hbound

/-- **`h(m) ≥ 1` for practical `m ≥ 2`.**  A single divisor has only two subset sums
    (`0` and itself), too few to cover `[1, m)` once `m ≥ 2`; formally
    `m ≤ 2^{h(m)}` with `m ≥ 2` forces `h(m) ≥ 1`. -/
theorem one_le_h {m : ℕ} (hm : 2 ≤ m) (hp : IsPractical m) : 1 ≤ h m := by
  by_contra hlt
  have h0 : h m = 0 := by omega
  have := le_two_pow_h hp
  rw [h0] at this
  simp at this
  omega

/-- **`h(1) = 0`.**  There is no `k` with `1 ≤ k < 1`, so the empty divisor set
    vacuously covers, and `0` is in the `sInf` set. -/
theorem h_one : h 1 = 0 := by
  apply Nat.le_zero.mp
  apply Nat.sInf_le
  exact ⟨∅, Finset.empty_subset _, Finset.card_empty, fun k hk1 hk2 => by omega⟩

/-- **Binary covering of `[0, 2^k)`.**  Every `n < 2^k` is a sum of distinct elements
    of `{2^0, 2^1, …, 2^{k-1}}` (the low powers of two) — its binary expansion.
    Proved by induction on `k`: for `2^k ≤ n < 2^{k+1}` peel the high bit `2^k` (fresh,
    since the remainder `n - 2^k < 2^k` is represented by strictly smaller powers). -/
theorem powers_subset_sum (k : ℕ) {n : ℕ} (hn : n < 2 ^ k) :
    ∃ T ⊆ (Finset.range k).image (2 ^ ·), T.sum id = n := by
  induction k generalizing n with
  | zero =>
    have hn0 : n = 0 := by simpa using hn
    exact ⟨∅, Finset.empty_subset _, by simp [hn0]⟩
  | succ k ih =>
    have hrange : Finset.range k ⊆ Finset.range (k + 1) := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    have hmono : (Finset.range k).image (2 ^ ·) ⊆ (Finset.range (k + 1)).image (2 ^ ·) :=
      Finset.image_subset_image hrange
    rcases lt_or_ge n (2 ^ k) with hlt | hge
    · obtain ⟨T, hT, hsum⟩ := ih hlt
      exact ⟨T, hT.trans hmono, hsum⟩
    · have hlt2 : n - 2 ^ k < 2 ^ k := by
        have : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        omega
      obtain ⟨T, hT, hsum⟩ := ih hlt2
      have hnotmem : (2 : ℕ) ^ k ∉ T := by
        intro hmem
        have hle : (2 : ℕ) ^ k ≤ T.sum id :=
          Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) hmem
        rw [hsum] at hle; omega
      refine ⟨insert (2 ^ k) T, ?_, ?_⟩
      · rw [Finset.insert_subset_iff]
        exact ⟨Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_self k), rfl⟩,
          hT.trans hmono⟩
      · rw [Finset.sum_insert hnotmem, hsum]
        simp only [id_eq]; omega

/-- **`h(2^k) ≤ k`.**  The `k` divisors `1, 2, …, 2^{k-1}` (`(range k).image (2^·)`)
    already cover `[1, 2^k)` by binary expansion (`powers_subset_sum`), so this
    `k`-element set witnesses the `sInf` bound. -/
theorem h_two_pow_le (k : ℕ) : h (2 ^ k) ≤ k := by
  apply Nat.sInf_le
  refine ⟨(Finset.range k).image (2 ^ ·), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.mem_divisors.mpr
      ⟨pow_dvd_pow 2 (Nat.le_of_lt (Finset.mem_range.mp hi)), by positivity⟩
  · have hInj : Set.InjOn (2 ^ ·) (Finset.range k) :=
      fun a _ b _ hab => Nat.pow_right_injective (le_refl 2) hab
    rw [Finset.card_image_of_injOn hInj, Finset.card_range]
  · intro n _ hn
    exact powers_subset_sum k hn

/-- **`h(2^k) = k`** — the first *exact* value of the Erdős #18 representation
    function in the gallery.  The lower bound `2^k ≤ 2^{h(2^k)}` (`le_two_pow_h`, using
    `two_pow_practical`) gives `k ≤ h(2^k)`, and the binary digits give the matching
    upper bound `h(2^k) ≤ k` (`h_two_pow_le`).  So the minimum number of divisors of
    `2^k` needed to represent everything below it is exactly `k` — attained by the
    `k` "digit" divisors `1, 2, …, 2^{k-1}`, which is one fewer than the `k+1` total
    divisors `d(2^k) = k+1` (the top divisor `2^k` is never needed). -/
theorem h_two_pow (k : ℕ) : h (2 ^ k) = k := by
  refine le_antisymm (h_two_pow_le k) ?_
  have hbound := le_two_pow_h (two_pow_practical k)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hbound

/-! ## Subadditivity of the representation function `h`

The function `h(m)` counts the *fewest* divisors of `m` needed to represent every
`1 ≤ k < m`.  This section proves it is **subadditive along products**:
`h(m·n) ≤ h(m) + h(n)` for practical `m, n`.  The witness is the concatenation of a
minimal covering set `S_m` of `m` with the `m`-scaled copy `m·S_n` of a minimal
covering set of `n` — exactly the divisor construction of `practical_mul`, but now
tracking cardinalities.  Writing `k = m·q + r` (`0 ≤ r < m`, `0 ≤ q < n`), the low
part `r` is covered inside `S_m` (elements `< m`) and the high part `m·q` inside
`m·S_n` (elements `≥ m`); the two are disjoint, so the union covers `[1, m·n)` using
`|S_m| + |S_n| = h(m) + h(n)` divisors.  Iterating gives `h(m^k) ≤ k·h(m)`. -/

/-- **A minimal covering set is attained.**  For practical `m` the `sInf` defining
    `h(m)` is over a nonempty set (the full divisor set `divisors m` covers `[1, m)`),
    so it is attained: there is a set `S ⊆ divisors m` of cardinality exactly `h(m)`
    that still represents every `1 ≤ k < m`.  This is the `Nat.sInf_mem` extraction
    inlined in `le_two_pow_h`, named here for reuse. -/
theorem exists_h_covering {m : ℕ} (hp : IsPractical m) :
    ∃ S : Finset ℕ, S ⊆ divisors m ∧ S.card = h m ∧
      ∀ k, 1 ≤ k → k < m → ∃ T : Finset ℕ, T ⊆ S ∧ T.sum id = k := by
  have hne : {s : ℕ | ∃ S : Finset ℕ, S ⊆ divisors m ∧ S.card = s ∧
      ∀ k, 1 ≤ k → k < m → ∃ T : Finset ℕ, T ⊆ S ∧ T.sum id = k}.Nonempty := by
    refine ⟨(divisors m).card, divisors m, Finset.Subset.refl _, rfl, ?_⟩
    intro k hk1 hkm
    exact hp.2 k hk1 hkm
  exact Nat.sInf_mem hne

/-- **Subadditivity `h(m·n) ≤ h(m) + h(n)`.**  Take minimal covering sets `S_m` of
    `m` (size `h(m)`) and `S_n` of `n` (size `h(n)`), guaranteed by
    `exists_h_covering`.  The set `S = S_m ∪ m·S_n ⊆ divisors (m·n)` has at most
    `h(m) + h(n)` elements and still covers `[1, m·n)`: for `1 ≤ k < m·n`, split
    `k = m·(k/m) + k%m`; represent the remainder `k%m` inside `S_m` (all such
    elements are `< m`) and the scaled quotient `m·(k/m)` inside `m·S_n` (all such
    elements are `≥ m`), disjointly.  Hence `h(m·n) ≤ |S| ≤ h(m) + h(n)`.  This is the
    counting refinement of `practical_mul`: not only is `m·n` practical, its
    representation cost is at most the sum of the factors' costs. -/
theorem h_mul_le {m n : ℕ} (hpm : IsPractical m) (hpn : IsPractical n) :
    h (m * n) ≤ h m + h n := by
  have hm1 : 1 ≤ m := hpm.1
  have hn1 : 1 ≤ n := hpn.1
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  obtain ⟨Sm, hSmsub, hSmcard, hSmcov⟩ := exists_h_covering hpm
  obtain ⟨Sn, hSnsub, hSncard, hSncov⟩ := exists_h_covering hpn
  -- Scaled copy `A = m · Sn ⊆ divisors (m·n)`, elements `≥ m`, injective image.
  have hminj : ∀ a ∈ Sn, ∀ b ∈ Sn, m * a = m * b → a = b :=
    fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (by omega) hab
  set A := Sn.image (m * ·) with hAdef
  have hAsub : A ⊆ divisors (m * n) := by
    intro x hx
    rw [hAdef, Finset.mem_image] at hx
    obtain ⟨d, hdSn, rfl⟩ := hx
    have hdvd : d ∣ n := Nat.dvd_of_mem_divisors (hSnsub hdSn)
    exact Nat.mem_divisors.mpr ⟨Nat.mul_dvd_mul_left m hdvd, hmn0⟩
  have hAcard : A.card = Sn.card := by
    rw [hAdef]
    exact Finset.card_image_of_injOn
      (fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (by omega) hab)
  -- `Sm` embeds into `divisors (m·n)` since `m ∣ m·n`.
  have hSmsub' : Sm ⊆ divisors (m * n) :=
    hSmsub.trans (Nat.divisors_subset_of_dvd hmn0 ⟨n, rfl⟩)
  set S := Sm ∪ A with hSdef
  have hSsub : S ⊆ divisors (m * n) := Finset.union_subset hSmsub' hAsub
  have hScard : S.card ≤ h m + h n := by
    calc S.card ≤ Sm.card + A.card := Finset.card_union_le _ _
      _ = h m + h n := by rw [hSmcard, hAcard, hSncard]
  -- `S` covers `[1, m·n)`.
  have hcov : ∀ k, 1 ≤ k → k < m * n → ∃ T ⊆ S, T.sum id = k := by
    intro k _hk1 hkmn
    have hrm : k % m < m := Nat.mod_lt k (by omega)
    have hqn : k / m < n :=
      (Nat.div_lt_iff_lt_mul (by omega)).mpr (by rw [Nat.mul_comm]; exact hkmn)
    have hdecomp : m * (k / m) + k % m = k := Nat.div_add_mod k m
    -- Represent remainder `r = k % m` inside `Sm` (empty subset if `r = 0`).
    obtain ⟨Tr, hTrsub, hTrsum⟩ : ∃ Tr ⊆ Sm, Tr.sum id = k % m := by
      rcases Nat.eq_zero_or_pos (k % m) with h0 | hpos
      · exact ⟨∅, Finset.empty_subset _, by simp [h0]⟩
      · exact hSmcov (k % m) hpos hrm
    -- Represent quotient `q = k / m` inside `Sn` (empty subset if `q = 0`).
    obtain ⟨Tq', hTq'sub, hTq'sum⟩ : ∃ Tq' ⊆ Sn, Tq'.sum id = k / m := by
      rcases Nat.eq_zero_or_pos (k / m) with h0 | hpos
      · exact ⟨∅, Finset.empty_subset _, by simp [h0]⟩
      · exact hSncov (k / m) hpos hqn
    -- Scale the quotient representation by `m`.
    have hTqinj : ∀ a ∈ Tq', ∀ b ∈ Tq', m * a = m * b → a = b :=
      fun a _ b _ hab => Nat.eq_of_mul_eq_mul_left (by omega) hab
    set Tq := Tq'.image (m * ·) with hTqdef
    have hTqsub : Tq ⊆ A := by
      rw [hTqdef, hAdef]
      exact Finset.image_subset_image hTq'sub
    have hTqsum : Tq.sum id = m * (k / m) := by
      rw [hTqdef, Finset.sum_image hTqinj]
      calc ∑ d ∈ Tq', id (m * d) = m * ∑ d ∈ Tq', d := by
            simp only [id_eq]; rw [Finset.mul_sum]
        _ = m * Tq'.sum id := rfl
        _ = m * (k / m) := by rw [hTq'sum]
    -- Low part `< m`, high part `≥ m`, hence disjoint.
    have hdisj : Disjoint Tr Tq := by
      rw [Finset.disjoint_left]
      intro a haTr haTq
      have hle : a ≤ Tr.sum id :=
        Finset.single_le_sum (f := id) (fun i _ => Nat.zero_le _) haTr
      rw [hTrsum] at hle
      rw [hTqdef, Finset.mem_image] at haTq
      obtain ⟨d, hdTq', rfl⟩ := haTq
      have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors (hSnsub (hTq'sub hdTq'))
      have hage : m ≤ m * d := le_mul_of_one_le_right (by omega) hd1
      omega
    refine ⟨Tr ∪ Tq, ?_, ?_⟩
    · rw [hSdef]
      exact Finset.union_subset (hTrsub.trans Finset.subset_union_left)
        (hTqsub.trans Finset.subset_union_right)
    · rw [Finset.sum_union hdisj, hTrsum, hTqsum]; omega
  calc h (m * n) ≤ S.card := Nat.sInf_le ⟨S, hSsub, rfl, hcov⟩
    _ ≤ h m + h n := hScard

/-- **`h(m^k) ≤ k · h(m)`.**  Iterating subadditivity `h_mul_le` over the practical
    powers `m^0, m^1, …` (each practical by `practical_pow`): `h(m^{k+1}) = h(m·m^k)
    ≤ h(m) + h(m^k) ≤ h(m) + k·h(m) = (k+1)·h(m)`.  So the representation cost of a
    number in the multiplicative family generated by a single practical base grows at
    most linearly in the exponent — a concrete upper envelope for `h` on `{m^k}`. -/
theorem h_pow_le {m : ℕ} (hp : IsPractical m) (k : ℕ) : h (m ^ k) ≤ k * h m := by
  induction k with
  | zero => simpa using le_of_eq h_one
  | succ k ih =>
    calc h (m ^ (k + 1)) = h (m ^ k * m) := by rw [pow_succ]
      _ ≤ h (m ^ k) + h m := h_mul_le (practical_pow hp k) hp
      _ ≤ k * h m + h m := by omega
      _ = (k + 1) * h m := by ring

/-! ## Exact values off the base-2 family, and tightness of subadditivity

`h_two_pow` pins `h(2^k) = k` on the powers of two, where the counting lower bound
`le_two_pow_h` (`m ≤ 2^{h m}`) meets the binary upper bound.  The same pincer determines
`h` on any practical `m` for which we can *exhibit* a covering set whose size already meets
the free lower bound: the general criterion `h_eq_of_covering` says that if `2^{s-1} < m` and
some `s`-element set of divisors covers `[1, m)`, then `h(m) = s`.  Applying it off the
single-base powers gives the first exact values on composite `m` — `h(6) = 3` and `h(12) = 4`
— and exhibits the subadditivity bound `h(m·n) ≤ h(m) + h(n)` as **tight**: `h(12) = h(2) +
h(6)` (`= 1 + 3`), so no strict improvement holds in general. -/

/-- **Upper-bound witness for `h`.**  Any `s`-element set `S ⊆ divisors m` that represents
    every `1 ≤ k < m` witnesses `h(m) ≤ s` (it lies in the `sInf` set).  This is the named,
    reusable form of the `Nat.sInf_le` step inlined in `h_two_pow_le`. -/
theorem h_le_of_covering {m s : ℕ} (S : Finset ℕ) (hS : S ⊆ divisors m)
    (hcard : S.card = s) (hcov : ∀ k, 1 ≤ k → k < m → ∃ T ⊆ S, T.sum id = k) :
    h m ≤ s :=
  Nat.sInf_le ⟨S, hS, hcard, hcov⟩

/-- **Exact-value criterion for `h`.**  For practical `m`, if `2^{s-1} < m` and some
    `s`-element set of divisors covers `[1, m)`, then `h(m) = s`.  The upper bound is the
    exhibited covering (`h_le_of_covering`); the lower bound is free from the counting bound
    `m ≤ 2^{h m}` (`le_two_pow_h`), since `2^{s-1} < m ≤ 2^{h m}` forces `s ≤ h m`. -/
theorem h_eq_of_covering {m s : ℕ} (hp : IsPractical m) (hlow : 2 ^ (s - 1) < m)
    (S : Finset ℕ) (hS : S ⊆ divisors m) (hcard : S.card = s)
    (hcov : ∀ k, 1 ≤ k → k < m → ∃ T ⊆ S, T.sum id = k) :
    h m = s := by
  refine le_antisymm (h_le_of_covering S hS hcard hcov) ?_
  have hb := le_two_pow_h hp
  by_contra hlt
  rw [not_le] at hlt
  have hle : h m ≤ s - 1 := by omega
  have hpow : (2 : ℕ) ^ h m ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) hle
  omega

/-- **`h(6) = 3`** — the first exact value of the Erdős #18 function off the powers of two.
    The three divisors `{1, 2, 3}` of `6` cover `[1, 6)` by subset sums, and `2^2 = 4 < 6`
    forces `h(6) ≥ 3` via `le_two_pow_h`.  Note `h(6) = 3 = d(6) − 1` (the top divisor `6`
    is unused). -/
theorem h_six : h 6 = 3 := by
  refine h_eq_of_covering six_practical (by norm_num) {1, 2, 3} (by decide) (by decide) ?_
  intro k hk1 hk6
  interval_cases k
  · exact ⟨{1}, by decide, by decide⟩
  · exact ⟨{2}, by decide, by decide⟩
  · exact ⟨{3}, by decide, by decide⟩
  · exact ⟨{1, 3}, by decide, by decide⟩
  · exact ⟨{2, 3}, by decide, by decide⟩

/-- **`h(12) = 4`.**  The four divisors `{1, 2, 4, 6}` of `12` cover `[1, 12)` by subset sums
    (`0..7` from `{1,2,4}`, shifted by `6` to reach `13`), and `2^3 = 8 < 12` forces
    `h(12) ≥ 4`.  Here `d(12) = 6`, so `h(12) = 4 = d(12) − 2`. -/
theorem h_twelve : h 12 = 4 := by
  refine h_eq_of_covering twelve_practical (by norm_num) {1, 2, 4, 6} (by decide) (by decide) ?_
  intro k hk1 hk12
  interval_cases k
  · exact ⟨{1}, by decide, by decide⟩
  · exact ⟨{2}, by decide, by decide⟩
  · exact ⟨{1, 2}, by decide, by decide⟩
  · exact ⟨{4}, by decide, by decide⟩
  · exact ⟨{1, 4}, by decide, by decide⟩
  · exact ⟨{6}, by decide, by decide⟩
  · exact ⟨{1, 6}, by decide, by decide⟩
  · exact ⟨{2, 6}, by decide, by decide⟩
  · exact ⟨{1, 2, 6}, by decide, by decide⟩
  · exact ⟨{4, 6}, by decide, by decide⟩
  · exact ⟨{1, 4, 6}, by decide, by decide⟩

/-- **Subadditivity is tight off the base-2 family.**  `h(12) = h(2) + h(6)` (`= 1 + 3 = 4`):
    the bound `h(m·n) ≤ h(m) + h(n)` (`h_mul_le`, with `12 = 2·6`) is attained, so no strict
    improvement holds in general.  Contrast the powers of two, where `h(2^k) = k = k·h(2)`
    saturates `h_pow_le` from below by exact equality throughout. -/
theorem h_twelve_eq_h_two_add_h_six : h 12 = h 2 + h 6 := by
  have h2 : h 2 = 1 := by simpa using h_two_pow 1
  rw [h_twelve, h2, h_six]

/-! ## The multiplicative submonoid of practical numbers

`practical_mul` shows the practical numbers are closed under multiplication and
`one_practical` supplies the unit, so they form a submonoid of `(ℕ, ×)`.  Packaging
the closure as a genuine `Submonoid` makes Mathlib's monoid API (e.g. `pow_mem`,
`prod_mem`) available for the practical numbers; `practical_pow` above is the
`pow_mem` instance of this structure. -/

/-- **Practical numbers form a multiplicative submonoid of `ℕ`.**  Unit: `1` is
practical (`one_practical`); closure: a product of practicals is practical
(`practical_mul`). -/
def practicalSubmonoid : Submonoid ℕ where
  carrier := {m | IsPractical m}
  one_mem' := one_practical
  mul_mem' := fun ha hb => practical_mul ha hb

@[simp] theorem mem_practicalSubmonoid {m : ℕ} :
    m ∈ practicalSubmonoid ↔ IsPractical m := Iff.rfl

end Erdos18OQ01
