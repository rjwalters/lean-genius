/-
  Erdős Problem #131 — Non-Dividing Sets
  Follow-up (oq-01-oq-01-oq-01-oq-03): the EXACT Davenport constant of the cyclic
  group `ℤ/nℤ`.

  Source: https://erdosproblems.com/131
  Companion to: `Proofs.Erdos131DavenportBound` (`exists_nonempty_subset_sum_dvd`,
  the upper bound `D(ℤ/aℤ) ≤ a` in the integer-divisibility / `Finset ℕ` form used
  to sharpen the EGZ set bound).

  NOTE.  This file is deliberately SELF-CONTAINED (only `import Mathlib`); it does
  not import the companions, which keeps it independently verifiable and axiom-free.

  ## What this file adds

  The **Davenport constant** `D(G)` of a finite abelian group `G` is the least `d`
  such that every length-`d` sequence over `G` has a nonempty zero-sum subsequence.
  Mathlib has the Erdős–Ginzburg–Ziv theorem (the EGZ constant `s(ℤ/nℤ) = 2n − 1`)
  but NOT the Davenport constant.  The companion `Erdos131DavenportBound` proved
  only the upper bound `D(ℤ/aℤ) ≤ a`, and only in the special integer-divisibility
  form (a nonempty subset of any `a` *distinct naturals* has sum divisible by `a`).

  Here we prove the constant EXACTLY, in the genuine sequence setting over
  `ZMod n`, as an `IsLeast` statement:

      **`D(ℤ/nℤ) = n`**  (`davenport_constant_cyclic`).

  Concretely:
  * **Upper bound** (`davenport_upper`): every sequence `f : Fin m → ZMod n` with
    `n ≤ m` has a nonempty `s : Finset (Fin m)` with `∑ i ∈ s, f i = 0`.  Proof:
    the `m + 1` prefix sums land in `ZMod n` (an `n`-element type), so by
    pigeonhole two coincide and the index interval between them is a nonempty
    zero-sum subsequence.  (This generalises the companion's `Finset ℕ` version to
    arbitrary `ZMod n` sequences — the actual Davenport setting.)
  * **Lower bound** (`davenport_no_zerosum_const_one`): the constant sequence `1`
    of any length `m < n` has NO nonempty zero-sum subsequence — a nonempty subset
    of size `k` sums to `(k : ZMod n)` with `1 ≤ k ≤ m < n`, hence `≠ 0`.  So no
    `m < n` is a Davenport length: the bound `n` is sharp.

  Both directions are unconditional and axiom-free.
-/

import Mathlib

namespace Erdos131DavenportConstant

open Finset

/-- A sequence `f : Fin m → ZMod n` *has a nonempty zero-sum subsequence* if some
nonempty index set `s` has `∑ i ∈ s, f i = 0`.  The Davenport constant `D(ℤ/nℤ)`
is the least `m` for which EVERY such sequence has this property. -/
def HasZeroSumSubseq {n m : ℕ} (f : Fin m → ZMod n) : Prop :=
  ∃ s : Finset (Fin m), s.Nonempty ∧ ∑ i ∈ s, f i = 0

/-- **Davenport upper bound `D(ℤ/nℤ) ≤ n`.**  Every sequence of length `≥ n` over
`ℤ/nℤ` has a nonempty zero-sum subsequence.

Proof: consider the `m + 1` prefix sums `P k = ∑_{i.val < k} f i` for `k = 0,…,m`.
They take values in `ZMod n`, which has `n < m + 1` elements, so by pigeonhole
(`Fintype.exists_ne_map_eq_of_card_lt`) two indices `p < q` give `P p = P q`.  The
index interval `[p, q)` then sums to `0` and is nonempty (it contains `p`). -/
theorem davenport_upper {n m : ℕ} (hn : 1 ≤ n) (f : Fin m → ZMod n) (hm : n ≤ m) :
    HasZeroSumSubseq f := by
  haveI : NeZero n := ⟨by omega⟩
  classical
  -- From a collision of two prefix sums we extract the zero-sum interval.
  have core : ∀ p q : ℕ, p < q → q ≤ m →
      (∑ i ∈ univ.filter (fun i : Fin m => i.val < p), f i)
        = (∑ i ∈ univ.filter (fun i : Fin m => i.val < q), f i) →
      HasZeroSumSubseq f := by
    intro p q hpq hqm heq
    refine ⟨univ.filter (fun i : Fin m => p ≤ i.val ∧ i.val < q), ⟨⟨p, by omega⟩, ?_⟩, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]; omega
    · -- The interval `[p, q)` splits the prefix `[0, q)` off the prefix `[0, p)`.
      have hUnion : univ.filter (fun i : Fin m => i.val < q)
          = univ.filter (fun i : Fin m => i.val < p)
            ∪ univ.filter (fun i : Fin m => p ≤ i.val ∧ i.val < q) := by
        ext i
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      have hDisj : Disjoint (univ.filter (fun i : Fin m => i.val < p))
          (univ.filter (fun i : Fin m => p ≤ i.val ∧ i.val < q)) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi1 hi2
        omega
      have hsplit : (∑ i ∈ univ.filter (fun i : Fin m => i.val < q), f i)
          = (∑ i ∈ univ.filter (fun i : Fin m => i.val < p), f i)
            + ∑ i ∈ univ.filter (fun i : Fin m => p ≤ i.val ∧ i.val < q), f i := by
        rw [hUnion, Finset.sum_union hDisj]
      rw [← heq] at hsplit
      -- `hsplit : prefix = prefix + block`, hence `block = 0`.
      linear_combination -hsplit
  -- Pigeonhole on the `m + 1` prefix sums.
  have hcard : Fintype.card (ZMod n) < Fintype.card (Fin (m + 1)) := by
    rw [ZMod.card, Fintype.card_fin]; omega
  obtain ⟨a, b, hne, hPeq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt
      (fun k : Fin (m + 1) =>
        ∑ i ∈ univ.filter (fun i : Fin m => i.val < k.val), f i) hcard
  have hvne : a.val ≠ b.val := Fin.val_injective.ne hne
  have ha := a.isLt
  have hb := b.isLt
  rcases lt_or_gt_of_ne hvne with h | h
  · exact core a.val b.val h (by omega) hPeq
  · exact core b.val a.val h (by omega) hPeq.symm

/-- **Davenport lower bound (sharpness): `D(ℤ/nℤ) ≥ n`.**  For any `m < n` the
constant sequence `1` of length `m` over `ℤ/nℤ` has NO nonempty zero-sum
subsequence: a nonempty `s` of size `k` sums to `(k : ZMod n)` with `1 ≤ k ≤ m < n`,
so the sum is nonzero. -/
theorem davenport_no_zerosum_const_one {n m : ℕ} (hmn : m < n) :
    ¬ HasZeroSumSubseq (fun _ : Fin m => (1 : ZMod n)) := by
  haveI : NeZero n := ⟨by omega⟩
  rintro ⟨s, hne, hsum⟩
  -- The subsequence sum is just the cardinality of `s`, cast into `ZMod n`.
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hsum
  have hdvd : (n : ℕ) ∣ s.card := (ZMod.natCast_eq_zero_iff _ _).mp hsum
  have hpos : 0 < s.card := Finset.card_pos.mpr hne
  have hle : s.card ≤ m := by
    have h := Finset.card_le_univ s
    rwa [Fintype.card_fin] at h
  exact absurd hdvd (Nat.not_dvd_of_pos_of_lt hpos (by omega))

/-- **The Davenport constant of the cyclic group `ℤ/nℤ` is exactly `n`.**

`D(ℤ/nℤ) = n`, stated as: `n` is the LEAST length such that every sequence over
`ℤ/nℤ` of that length has a nonempty zero-sum subsequence.  The two halves are
`davenport_upper` (`n` works) and `davenport_no_zerosum_const_one` (no `m < n`
works, witnessed by the constant-`1` sequence). -/
theorem davenport_constant_cyclic {n : ℕ} (hn : 1 ≤ n) :
    IsLeast {m : ℕ | ∀ f : Fin m → ZMod n, HasZeroSumSubseq f} n := by
  constructor
  · -- `n` is in the set: every length-`n` sequence has a zero-sum subsequence.
    intro f
    exact davenport_upper hn f (le_refl n)
  · -- `n` is a lower bound: any length in the set is `≥ n`.
    intro m hm
    by_contra hlt
    push_neg at hlt
    exact davenport_no_zerosum_const_one hlt (hm (fun _ => 1))

/-- **Membership form of the upper bound.**  Restates `davenport_upper` as
membership in the Davenport set: every length `≥ n` is a Davenport length. -/
theorem mem_davenport_set_of_ge {n m : ℕ} (hn : 1 ≤ n) (hm : n ≤ m) :
    m ∈ {m : ℕ | ∀ f : Fin m → ZMod n, HasZeroSumSubseq f} :=
  fun f => davenport_upper hn f hm

/-- **Exact-value extraction.**  The least Davenport length is computably `n`. -/
theorem davenport_isLeast_eq {n : ℕ} (hn : 1 ≤ n)
    {d : ℕ} (hd : IsLeast {m : ℕ | ∀ f : Fin m → ZMod n, HasZeroSumSubseq f} d) :
    d = n :=
  IsLeast.unique hd (davenport_constant_cyclic hn)

/-- **The general-sequence upper bound strengthens the companion's `Finset ℕ` bound.**

Specialising `davenport_upper` to the sequence `i ↦ (g i : ZMod n)` recovers, for any
function `g : Fin m → ℕ` with `n ≤ m`, a nonempty index set whose `g`-sum is divisible
by `n` — the Davenport bound `D(ℤ/nℤ) ≤ n` in integer-divisibility form, now without
the distinctness/`Finset` restriction of the companion file. -/
theorem exists_index_subset_sum_dvd {n m : ℕ} (hn : 1 ≤ n) (g : Fin m → ℕ)
    (hm : n ≤ m) :
    ∃ s : Finset (Fin m), s.Nonempty ∧ (n : ℕ) ∣ ∑ i ∈ s, g i := by
  haveI : NeZero n := ⟨by omega⟩
  obtain ⟨s, hne, hsum⟩ := davenport_upper hn (fun i => (g i : ZMod n)) hm
  refine ⟨s, hne, ?_⟩
  have : ((∑ i ∈ s, g i : ℕ) : ZMod n) = 0 := by push_cast; simpa using hsum
  exact (ZMod.natCast_eq_zero_iff _ _).mp this

end Erdos131DavenportConstant
