/-
# Erdős Problem #10 — Open Question 02
## The reduction lemma for the Granville–Soundararajan conjecture (k = 3, odd)

**Parent.** Erdős Problem #10 — sums of a prime and powers of 2.

**Open question (oq-02).** *Granville–Soundararajan (1998).* Is every odd
integer `n > 1` the sum of a prime and **at most 3** powers of 2,
`n = p + 2^{a₁} + ⋯ + 2^{a_j}` with `p` prime and `0 ≤ j ≤ 3`? The companion
even part needs at most 4. Both are open.

## What this file formalizes

The conjecture itself is open (it needs sieve/large-sieve machinery on the
Gallagher line and is out of brute-force and near-term Lean reach). What *is*
clean and formalizable — and the natural foundation for any decision procedure
on the concrete witnesses (the smallest even integer needing 3 powers is 906;
Grechuk's 1117175146 is not a prime plus ≤ 3 powers) — is the **reduction
lemma**:

> A natural number is a sum of *at most `k`* powers of 2 **iff** it is a sum of
> at most `k` powers of 2 with **pairwise-distinct** exponents.

The forward direction is the only nontrivial half. Its engine is the single
merge identity `2^a + 2^a = 2^{a+1}`: repeatedly collapsing a duplicated
exponent strictly shrinks the multiset of exponents while preserving the sum,
so any representation reduces to one with no repeats and no more terms. The
distinct-exponent count is exactly the binary popcount, which is why the
*minimal* number of powers equals `popcount n` — the cheap finite search that
underlies the numerical evidence in
`research/problems/erdos-10-oq-02/`.

This file is **registered in `Proofs.lean`** and machine-checked under the
pinned Lean toolchain (the original draft predates the build; it has since been
elaborated cleanly). The proofs use only elementary `Multiset` algebra (no
binary-representation API).

## References

- Granville, A.; Soundararajan, K. (1998). *A binary additive problem of Erdős
  and the order of `2 mod p²`.* Ramanujan J. 2, 283–298.
- Crocker, R. (1971). *On the sum of a prime and of two powers of two.*
  Pacific J. Math. 36, 103–107.
- Erdős, P.; Graham, R. (1980). *Old and New Problems and Results in
  Combinatorial Number Theory.*
-/

import Mathlib.Tactic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Erdos10OQ02

/-! ## Part I: Sums of powers of two -/

/-- `powSum s = 2^a₁ + ⋯ + 2^a_j` where `s = {a₁, …, a_j}` is the multiset of
exponents. The empty multiset gives `0`. -/
def powSum (s : Multiset ℕ) : ℕ := (s.map (2 ^ ·)).sum

@[simp] theorem powSum_zero : powSum 0 = 0 := by simp [powSum]

@[simp] theorem powSum_cons (a : ℕ) (s : Multiset ℕ) :
    powSum (a ::ₘ s) = 2 ^ a + powSum s := by
  simp [powSum]

theorem powSum_add (s t : Multiset ℕ) :
    powSum (s + t) = powSum s + powSum t := by
  simp [powSum, Multiset.map_add, Multiset.sum_add]

/-- **Merge identity.** Replacing a duplicated exponent `a, a` by the single
exponent `a + 1` preserves the sum: `2^a + 2^a = 2^{a+1}`. This is the atomic
step of the reduction. -/
theorem powSum_merge (a : ℕ) (s : Multiset ℕ) :
    powSum (a ::ₘ a ::ₘ s) = powSum ((a + 1) ::ₘ s) := by
  simp only [powSum_cons, pow_succ]
  ring

/-! ## Part II: Representability as ≤ k powers of two -/

/-- `n` is a sum of **at most `k`** powers of two (exponents may repeat). -/
def RepWithAtMost (k n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, s.card ≤ k ∧ powSum s = n

/-- `n` is a sum of at most `k` powers of two with **pairwise-distinct**
exponents. -/
def RepDistinct (k n : ℕ) : Prop :=
  ∃ s : Multiset ℕ, s.Nodup ∧ s.card ≤ k ∧ powSum s = n

/-- Allowing one more power can only relax representability. -/
theorem repWithAtMost_mono {k n : ℕ} (h : RepWithAtMost k n) :
    RepWithAtMost (k + 1) n := by
  obtain ⟨s, hcard, hsum⟩ := h
  exact ⟨s, hcard.trans (Nat.le_succ k), hsum⟩

/-! ## Part III: The reduction lemma

Every multiset of exponents can be rewritten — using no more terms — as one
with pairwise-distinct exponents and the same `powSum`. -/

/-- **Canonicalization.** For any exponent multiset `s` there is a `Nodup`
multiset `t` with `t.card ≤ s.card` and `powSum t = powSum s`.

Proof: strong induction on `s.card`. If `s` already has no repeats we are done.
Otherwise some exponent `a` occurs at least twice, so `s = a ::ₘ a ::ₘ u`;
merging gives `(a+1) ::ₘ u`, which has strictly smaller card and the same
`powSum` by `powSum_merge`. Apply the induction hypothesis. -/
theorem exists_nodup_powSum :
    ∀ (n : ℕ) (s : Multiset ℕ), s.card = n →
      ∃ t : Multiset ℕ, t.Nodup ∧ t.card ≤ s.card ∧ powSum t = powSum s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    by_cases hnd : s.Nodup
    · exact ⟨s, hnd, le_rfl, rfl⟩
    · -- some exponent occurs at least twice
      rw [Multiset.nodup_iff_count_le_one] at hnd
      push_neg at hnd
      obtain ⟨a, ha⟩ := hnd                       -- ha : 1 < s.count a
      have hmem : a ∈ s := Multiset.count_pos.mp (by omega)
      obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem hmem   -- s = a ::ₘ t
      have hct : 1 ≤ t.count a := by
        have : s.count a = t.count a + 1 := by
          rw [ht, Multiset.count_cons_self]
        omega
      have hmem' : a ∈ t := Multiset.count_pos.mp (by omega)
      obtain ⟨u, hu⟩ := Multiset.exists_cons_of_mem hmem'  -- t = a ::ₘ u
      have hsu : s = a ::ₘ a ::ₘ u := by rw [ht, hu]
      -- the merged multiset
      set v : Multiset ℕ := (a + 1) ::ₘ u with hv
      have hcard_s : s.card = u.card + 2 := by
        rw [hsu]; simp only [Multiset.card_cons]
      have hcard_v : v.card = u.card + 1 := by
        rw [hv]; simp only [Multiset.card_cons]
      have hsum_v : powSum v = powSum s := by
        rw [hv, hsu, powSum_merge]
      -- recurse on v (strictly smaller card)
      obtain ⟨w, hw_nodup, hw_card, hw_sum⟩ :=
        ih v.card (by omega) v rfl
      refine ⟨w, hw_nodup, ?_, ?_⟩
      · omega
      · rw [hw_sum, hsum_v]

/-- **Reduction lemma.** Representability by `≤ k` powers of two is equivalent
to representability by `≤ k` *distinct* powers of two. -/
theorem repWithAtMost_iff_repDistinct (k n : ℕ) :
    RepWithAtMost k n ↔ RepDistinct k n := by
  constructor
  · rintro ⟨s, hcard, hsum⟩
    obtain ⟨t, ht_nodup, ht_card, ht_sum⟩ := exists_nodup_powSum s.card s rfl
    exact ⟨t, ht_nodup, ht_card.trans hcard, by rw [ht_sum, hsum]⟩
  · rintro ⟨s, _, hcard, hsum⟩
    exact ⟨s, hcard, hsum⟩

/-! ## Part IV: The Granville–Soundararajan statement (odd part)

With the reduction lemma in hand the conjecture can be phrased in terms of a
prime plus a *distinct*-exponent power set, which is what makes the minimal
power count computable (it equals the binary popcount of the offset). The
statement itself remains open. -/

/-- `n` is a prime plus at most `k` powers of two. -/
def IsPrimePlusKPowers (k n : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ ∃ m : ℕ, RepWithAtMost k m ∧ n = p + m

/-- **Granville–Soundararajan, odd part (open).** Every odd `n ≥ 3` is a prime
plus at most 3 powers of two. -/
def GranvilleSoundararajanOdd : Prop :=
  ∀ n : ℕ, Odd n → 3 ≤ n → IsPrimePlusKPowers 3 n

/-- The prime-plus form also transfers to the distinct representation, via the
reduction lemma. This is the shape a `decide`/`native_decide` membership check
would consume. -/
theorem isPrimePlusKPowers_iff_distinct (k n : ℕ) :
    IsPrimePlusKPowers k n ↔
      ∃ p : ℕ, p.Prime ∧ ∃ m : ℕ, RepDistinct k m ∧ n = p + m := by
  unfold IsPrimePlusKPowers
  constructor
  · rintro ⟨p, hp, m, hm, hn⟩
    exact ⟨p, hp, m, (repWithAtMost_iff_repDistinct k m).mp hm, hn⟩
  · rintro ⟨p, hp, m, hm, hn⟩
    exact ⟨p, hp, m, (repWithAtMost_iff_repDistinct k m).mpr hm, hn⟩

#check @exists_nodup_powSum
#check @repWithAtMost_iff_repDistinct
#check @isPrimePlusKPowers_iff_distinct

end Erdos10OQ02
