/-
# Explicit Dilworth chain decomposition of `{1, …, N}` for arbitrary `N`

The parent entry (`erdos-divisibility-pigeonhole-oq-01-oq-01`) proves that the
largest divisibility-antichain in `{1, …, N}` has size `⌈N/2⌉ = (N+1)/2` via a
**pigeonhole count** into `range ⌈N/2⌉`. Its first child
(`…-oq-01-oq-01-oq-01`) re-derived that bound through an **explicit chain
decomposition** — but only in the clean even case `N = 2n`, where the answer is
`n`.

This file answers that child's first open question: *generalize the explicit
chain decomposition from `{1, …, 2n}` to arbitrary `N`.* The same odd-part fibers
give a cover by exactly `⌈N/2⌉` divisibility chains, recovering the parent's
`max_antichainN_card` as a **Dilworth min–max** consequence for **every** `N`, not
only even `N = 2n`.

## What is proved

Writing each `m ≥ 1` as `m = 2^k · o(m)` with **odd part** `o(m) := ordCompl[2] m`:

* `card_chains` : the fibers of `o` partition `{1, …, N}` into **exactly `⌈N/2⌉`**
  classes — one per odd number `≤ N` — i.e. a cover by `⌈N/2⌉` divisibility chains.
* `fiber_chain` : each fiber is a genuine **chain**: any two elements sharing an
  odd part are comparable under `∣`.
* `antichain_card_le` : consequently **no antichain exceeds `⌈N/2⌉`** — an antichain
  meets each chain at most once, so `o` is injective on it.
* `topHalf_antichain`, `card_topHalf` : the block `{⌊N/2⌋+1, …, N}` is an antichain
  of size `⌈N/2⌉`, so the bound is **attained**.
* `max_antichain_eq` : packaging the above as the Dilworth min–max equality —
  the maximum antichain size equals the minimum chain-cover size, both `⌈N/2⌉`.
* `chain_cover_card_eq_max_antichain` : the explicit min–max identity, *chain-cover
  size = maximum antichain size = `(N+1)/2`*, for every `N`.
* `recovers_even_case` : specializing `N = 2n` recovers the `n`-chain partition of
  the sibling even-case file `card_chains (2*n) = n`.

This is the chain-decomposition method of the sibling file carried to full
generality: it makes the `⌈N/2⌉`-chain partition manifest and derives the extremal
bound from the min–max equality rather than the pigeonhole count, for all `N`.

Axiom-free: built from foundational Mathlib lemmas only (no `sorry`, no `axiom`,
no `native_decide`).
-/
import Mathlib

namespace ErdosPigeonholeChainDecompN

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

/-- **The chain index set.** The odd parts occurring in `{1, …, N}` are exactly
the odd numbers there, namely `{2i+1 : i < ⌈N/2⌉}` with `⌈N/2⌉ = (N+1)/2`. -/
lemma image_oddPart_Icc (N : ℕ) :
    (Icc 1 N).image oddPart = (range ((N + 1) / 2)).image (fun i => 2 * i + 1) := by
  ext x
  simp only [mem_image, mem_Icc, mem_range]
  constructor
  · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
    have hm0 : m ≠ 0 := by omega
    obtain ⟨i, hi⟩ := odd_oddPart hm0
    have hxle : oddPart m ≤ N := le_trans (oddPart_le m) hm2
    exact ⟨i, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨2 * i + 1, ⟨by omega, by omega⟩, oddPart_eq_self ⟨i, rfl⟩⟩

/-- **Exactly `⌈N/2⌉` chains.** The fibers of the odd-part map partition `{1, …, N}`
into precisely `(N+1)/2` divisibility chains. -/
theorem card_chains (N : ℕ) : ((Icc 1 N).image oddPart).card = (N + 1) / 2 := by
  have hinj : Function.Injective (fun i => 2 * i + 1) := by
    intro a b h; dsimp only at h; omega
  rw [image_oddPart_Icc, card_image_of_injective _ hinj, card_range]

/-- Each fiber of `oddPart` inside `{1, …, N}` is a divisibility chain. (The interval
hypotheses record the poset context; comparability in fact holds unconditionally.) -/
theorem fiber_chain (N : ℕ) {a b : ℕ} (_ha : a ∈ Icc 1 N) (_hb : b ∈ Icc 1 N)
    (h : oddPart a = oddPart b) : a ∣ b ∨ b ∣ a :=
  dvd_or_dvd_of_oddPart_eq h

/-- **Upper bound via the chain partition (Mirsky/Dilworth).** A divisibility
antichain in `{1, …, N}` has at most `⌈N/2⌉` elements: `oddPart` is injective on it
(equal odd parts would force comparability, contradicting the antichain), and its
image lies among the `⌈N/2⌉` chain indices. -/
theorem antichain_card_le (N : ℕ) {A : Finset ℕ} (hA : A ⊆ Icc 1 N)
    (hfree : ∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b) : A.card ≤ (N + 1) / 2 := by
  have hinj : Set.InjOn oddPart (↑A) := by
    intro a ha b hb h
    rw [Finset.mem_coe] at ha hb
    rcases fiber_chain N (hA ha) (hA hb) h with hab | hba
    · exact hfree a ha b hb hab
    · exact (hfree b hb a ha hba).symm
  calc A.card = (A.image oddPart).card := (card_image_of_injOn hinj).symm
    _ ≤ ((Icc 1 N).image oddPart).card := card_le_card (image_subset_image hA)
    _ = (N + 1) / 2 := card_chains N

/-- **Sharpness.** The top block `{⌊N/2⌋+1, …, N}` is a divisibility antichain: a
proper multiple of any `a > N/2` is `≥ 2a > N`, so it leaves the block. -/
theorem topHalf_antichain (N : ℕ) :
    ∀ a ∈ Icc (N / 2 + 1) N, ∀ b ∈ Icc (N / 2 + 1) N, a ∣ b → a = b := by
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

/-- The top block has exactly `⌈N/2⌉ = (N+1)/2` elements. -/
theorem card_topHalf (N : ℕ) : (Icc (N / 2 + 1) N).card = (N + 1) / 2 := by
  rw [Nat.card_Icc]; omega

/-- **Dilworth min–max for the divisibility poset on `{1, …, N}`.** The maximum
size of a divisibility antichain equals `⌈N/2⌉ = (N+1)/2` — the number of chains in
the odd-part partition. The bound `antichain_card_le` is the min ≥ max direction;
the witness `{⌊N/2⌋+1, …, N}` is the attainment. -/
theorem max_antichain_eq (N : ℕ) :
    IsGreatest
      {k | ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
        (∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b) ∧ A.card = k} ((N + 1) / 2) := by
  constructor
  · refine ⟨Icc (N / 2 + 1) N, ?_, topHalf_antichain N, card_topHalf N⟩
    intro x hx; rw [mem_Icc] at hx ⊢; omega
  · rintro k ⟨A, hA, hfree, rfl⟩
    exact antichain_card_le N hA hfree

/-- **Explicit Dilworth identity.** For every `N`, the size of the odd-part chain
cover equals the maximum divisibility-antichain size, both `(N+1)/2`. This packages
`card_chains` (minimum chain cover) and `max_antichain_eq` (maximum antichain) into
the single min = max statement, manifest for arbitrary `N`. -/
theorem chain_cover_card_eq_max_antichain (N : ℕ) :
    ((Icc 1 N).image oddPart).card = (N + 1) / 2 ∧
    IsGreatest
      {k | ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧
        (∀ a ∈ A, ∀ b ∈ A, a ∣ b → a = b) ∧ A.card = k} (((Icc 1 N).image oddPart).card) := by
  refine ⟨card_chains N, ?_⟩
  rw [card_chains N]
  exact max_antichain_eq N

/-- **Recovers the sibling even case.** Specializing `N = 2n` recovers the `n`-chain
partition proved in the even-case file (`…-oq-01-oq-01-oq-01`,
`ErdosPigeonholeChainDecomp.card_chains`): the odd-part fibers of `{1, …, 2n}` form
exactly `n` chains. -/
theorem recovers_even_case (n : ℕ) :
    ((Icc 1 (2 * n)).image oddPart).card = n := by
  rw [card_chains (2 * n)]; omega

end ErdosPigeonholeChainDecompN
