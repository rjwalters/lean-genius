/-
# Explicit Dilworth chain decomposition of `{1, …, 2n}` under divisibility

The parent entry (`erdos-divisibility-pigeonhole-oq-01-oq-01`) proves that the
largest divisibility-antichain in `{1, …, N}` has size `⌈N/2⌉` by mapping each
`m` to its odd part `o(m) = ordCompl[2] m` and applying a **pigeonhole count**
into `range ⌈N/2⌉`.

This file answers that entry's first open question: *realize the underlying
Dilworth/Mirsky partition explicitly and derive the extremal bound as the
min–max consequence, rather than via the pigeonhole count.* We work in the clean
even case `N = 2n` (the original Erdős interval), where the answer is `n`.

## What is proved

Writing each `m ≥ 1` as `m = 2^k · o(m)` with **odd part** `o(m) := ordCompl[2] m`:

* `card_chains` : the fibers of `o` partition `{1, …, 2n}` into **exactly `n`**
  classes — one per odd number `≤ 2n` — i.e. a cover by `n` divisibility chains.
* `fiber_chain` : each fiber is a genuine **chain**: any two elements sharing an
  odd part are comparable under `∣` (the one with the smaller power of two
  divides the other). This comparability is what makes the cover a *chain* cover.
* `antichain_card_le` : consequently **no antichain exceeds `n`** — an antichain
  meets each chain at most once, so `o` is injective on it.
* `topHalf_antichain`, `card_topHalf` : the block `{n+1, …, 2n}` is an antichain
  of size `n`, so the bound is **attained**.
* `max_antichain_eq` : packaging the above as the Dilworth min–max equality —
  the maximum antichain size equals the minimum chain-cover size, both `n`.

Unlike the parent's bare counting argument, the chain structure (`fiber_chain`)
and the explicit `n`-chain partition (`card_chains`) are made manifest, exhibiting
the divisibility poset on `{1, …, 2n}` as a disjoint union of `n` chains.

Axiom-free: built from foundational Mathlib lemmas only (no `sorry`, no `axiom`,
no `native_decide`).
-/
import Mathlib

namespace ErdosPigeonholeChainDecomp

open Finset

/-- The **odd part** of `m`: divide out every factor of two,
`oddPart m = m / 2 ^ v₂(m)`. It is the index of the divisibility chain containing
`m`. -/
def oddPart (m : ℕ) : ℕ := ordCompl[2] m

/-- The odd part divides the number. -/
lemma oddPart_dvd (m : ℕ) : oddPart m ∣ m := Nat.ordCompl_dvd m 2

/-- The odd part never exceeds the number. -/
lemma oddPart_le (m : ℕ) : oddPart m ≤ m := Nat.ordCompl_le m 2

/-- The odd part of a positive number is positive. -/
lemma oddPart_pos {m : ℕ} (hm : m ≠ 0) : 0 < oddPart m := Nat.ordCompl_pos 2 hm

/-- The odd part is, indeed, odd. -/
lemma odd_oddPart {m : ℕ} (hm : m ≠ 0) : Odd (oddPart m) := by
  rw [Nat.odd_iff]
  exact Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hm)

/-- An odd number is its own odd part. -/
lemma oddPart_eq_self {m : ℕ} (hm : Odd m) : oddPart m = m := by
  have h2 : ¬ (2 ∣ m) := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hm)
  unfold oddPart
  rw [Nat.factorization_eq_zero_of_not_dvd h2]
  simp

/-- **Chain comparability.** Two positive numbers with the same odd part are
comparable under divisibility: `m = 2^{v₂(m)} · o(m)`, so the one with the smaller
2-adic valuation divides the other. -/
lemma dvd_or_dvd_of_oddPart_eq {a b : ℕ}
    (h : oddPart a = oddPart b) : a ∣ b ∨ b ∣ a := by
  have hfa : 2 ^ a.factorization 2 * oddPart a = a := Nat.ordProj_mul_ordCompl_eq_self a 2
  have hfb : 2 ^ b.factorization 2 * oddPart b = b := Nat.ordProj_mul_ordCompl_eq_self b 2
  rw [h] at hfa
  rcases le_total (a.factorization 2) (b.factorization 2) with hle | hle
  · left
    have hdvd : 2 ^ a.factorization 2 * oddPart b ∣ 2 ^ b.factorization 2 * oddPart b :=
      mul_dvd_mul_right (pow_dvd_pow 2 hle) (oddPart b)
    rwa [hfa, hfb] at hdvd
  · right
    have hdvd : 2 ^ b.factorization 2 * oddPart b ∣ 2 ^ a.factorization 2 * oddPart b :=
      mul_dvd_mul_right (pow_dvd_pow 2 hle) (oddPart b)
    rwa [hfa, hfb] at hdvd

/-- **The chain index set.** The odd parts occurring in `{1, …, 2n}` are exactly
the odd numbers there, namely `{2i+1 : i < n}`. -/
lemma image_oddPart_Icc (n : ℕ) :
    (Icc 1 (2 * n)).image oddPart = (range n).image (fun i => 2 * i + 1) := by
  ext x
  simp only [mem_image, mem_Icc, mem_range]
  constructor
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
    have hm0 : m ≠ 0 := by omega
    obtain ⟨i, hi⟩ := odd_oddPart hm0
    have hxle : oddPart m ≤ 2 * n := le_trans (oddPart_le m) hm2
    exact ⟨i, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨2 * i + 1, ⟨by omega, by omega⟩, oddPart_eq_self ⟨i, rfl⟩⟩

/-- **Exactly `n` chains.** The fibers of the odd-part map partition `{1, …, 2n}`
into precisely `n` divisibility chains. -/
theorem card_chains (n : ℕ) : ((Icc 1 (2 * n)).image oddPart).card = n := by
  have hinj : Function.Injective (fun i => 2 * i + 1) := by
    intro a b h; dsimp only at h; omega
  rw [image_oddPart_Icc, card_image_of_injective _ hinj, card_range]

/-- Each fiber of `oddPart` inside `{1, …, 2n}` is a divisibility chain. (The interval
hypotheses record the poset context; comparability in fact holds unconditionally.) -/
theorem fiber_chain (n : ℕ) {a b : ℕ} (_ha : a ∈ Icc 1 (2 * n)) (_hb : b ∈ Icc 1 (2 * n))
    (h : oddPart a = oddPart b) : a ∣ b ∨ b ∣ a :=
  dvd_or_dvd_of_oddPart_eq h

/-- **Upper bound via the chain partition (Mirsky/Dilworth).** A divisibility
antichain in `{1, …, 2n}` has at most `n` elements: `oddPart` is injective on it
(equal odd parts would force comparability, contradicting the antichain), and its
image lies among the `n` chain indices. -/
theorem antichain_card_le (n : ℕ) {A : Finset ℕ} (hA : A ⊆ Icc 1 (2 * n))
    (hfree : ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b) : A.card ≤ n := by
  have hinj : Set.InjOn oddPart (↑A) := by
    intro a ha b hb h
    rw [Finset.mem_coe] at ha hb
    rcases fiber_chain n (hA ha) (hA hb) h with hab | hba
    · exact hfree a ha b hb hab
    · exact (hfree b hb a ha hba).symm
  calc A.card = (A.image oddPart).card := (card_image_of_injOn hinj).symm
    _ ≤ ((Icc 1 (2 * n)).image oddPart).card := card_le_card (image_subset_image hA)
    _ = n := card_chains n

/-- **Sharpness.** The top block `{n+1, …, 2n}` is a divisibility antichain: a
proper multiple of any `a > n` is `≥ 2a > 2n`, so it leaves the block. -/
theorem topHalf_antichain (n : ℕ) :
    ∀ a ∈ Icc (n + 1) (2 * n), ∀ b ∈ Icc (n + 1) (2 * n), a ∣ b → a = b := by
  intro a ha b hb hab
  rw [mem_Icc] at ha hb
  obtain ⟨c, rfl⟩ := hab
  have hcpos : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; rw [Nat.mul_zero] at hb; omega
    · exact h0
  have hclt : c < 2 := by
    by_contra hge
    push_neg at hge
    have h2a : 2 * a ≤ a * c := by nlinarith
    omega
  have hc1 : c = 1 := by omega
  rw [hc1, mul_one]

/-- The top block has exactly `n` elements. -/
theorem card_topHalf (n : ℕ) : (Icc (n + 1) (2 * n)).card = n := by
  rw [Nat.card_Icc]; omega

/-- **Dilworth min–max for the divisibility poset on `{1, …, 2n}`.** The maximum
size of a divisibility antichain equals `n` — the number of chains in the odd-part
partition. The bound `antichain_card_le` is the min ≥ max direction; the witness
`{n+1, …, 2n}` is the attainment. -/
theorem max_antichain_eq (n : ℕ) :
    IsGreatest
      {k | ∃ A : Finset ℕ, A ⊆ Icc 1 (2 * n) ∧
        (∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b) ∧ A.card = k} n := by
  constructor
  · refine ⟨Icc (n + 1) (2 * n), ?_, topHalf_antichain n, card_topHalf n⟩
    intro x hx; rw [mem_Icc] at hx ⊢; omega
  · rintro k ⟨A, hA, hfree, rfl⟩
    exact antichain_card_le n hA hfree

end ErdosPigeonholeChainDecomp
