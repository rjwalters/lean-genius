/-
# Largest divisibility-antichain in `{1, …, N}` has size `⌈N/2⌉`

This generalizes the extremal Erdős divisibility pigeonhole from the even
interval `{1, …, 2n}` (where the answer is `n`) to an **arbitrary** upper bound
`N`. The maximum size of a divisibility-antichain (a set no two distinct members
of which are related by divisibility) in `{1, …, N}` is exactly

> `⌈N/2⌉ = (N + 1) / 2`  (natural-number division),

attained by the block of integers in `(N/2, N]`, namely `{⌊N/2⌋+1, …, N}`.

## Why `(N + 1) / 2`

* **Upper bound.** Write each `m ≥ 1` as `m = 2^k · o(m)` with odd part
  `o(m) := ordCompl[2] m`. The half-index `m ↦ (o(m) − 1)/2` sends `{1, …, N}`
  into `Finset.range ((N+1)/2)` (there are exactly `⌈N/2⌉` odd numbers `≤ N`).
  A set larger than `⌈N/2⌉` therefore has two members with equal odd part, and
  the one with the smaller power of two divides the other.

* **Construction.** The block `{⌊N/2⌋+1, …, N}` is a divisibility-antichain: a
  proper multiple of any `a > N/2` is `≥ 2a > N`, so it cannot also lie in the
  block. Its cardinality `N − ⌊N/2⌋ = ⌈N/2⌉` matches the upper bound.

Specializing `N = 2n` gives `(2n+1)/2 = n` and the block `{n+1, …, 2n}`,
recovering `ErdosDivisibilityPigeonhole.max_antichain_card` (`erdos-divisibility-
pigeonhole-oq-01`).

Axiom-free: built from foundational Mathlib lemmas only (no `sorry`, no `axiom`,
no `native_decide`).
-/
import Mathlib

namespace ErdosDivisibilityPigeonhole

open Finset

/-- For an odd `o`, halving and rebuilding recovers `o`: `2·((o−1)/2) + 1 = o`.
    This makes `o ↦ (o−1)/2` injective on odd numbers. -/
private lemma odd_recoverN {o : ℕ} (h : Odd o) : 2 * ((o - 1) / 2) + 1 = o := by
  obtain ⟨k, rfl⟩ := h; omega

/-- The odd part `ordCompl[2] m` is odd whenever `m ≠ 0`. -/
private lemma odd_ordComplN {m : ℕ} (hm : m ≠ 0) : Odd (ordCompl[2] m) := by
  rw [Nat.odd_iff]
  have h2 : ¬ (2 ∣ ordCompl[2] m) := Nat.not_dvd_ordCompl (by norm_num) hm
  omega

/-- If two positive numbers share an odd part, one divides the other: with
    `a = 2^{v₂ a}·o` and `b = 2^{v₂ b}·o`, the smaller power of two wins. -/
private lemma dvd_or_dvd_of_ordCompl_eqN {a b : ℕ}
    (h : ordCompl[2] a = ordCompl[2] b) : a ∣ b ∨ b ∣ a := by
  have ea : 2 ^ (a.factorization 2) * ordCompl[2] a = a :=
    Nat.ordProj_mul_ordCompl_eq_self a 2
  have eb : 2 ^ (b.factorization 2) * ordCompl[2] b = b :=
    Nat.ordProj_mul_ordCompl_eq_self b 2
  rcases le_total (a.factorization 2) (b.factorization 2) with hle | hle
  · left
    calc a = 2 ^ (a.factorization 2) * ordCompl[2] a := ea.symm
      _ ∣ 2 ^ (b.factorization 2) * ordCompl[2] b := by
          rw [h]; exact mul_dvd_mul_right (pow_dvd_pow 2 hle) _
      _ = b := eb
  · right
    calc b = 2 ^ (b.factorization 2) * ordCompl[2] b := eb.symm
      _ ∣ 2 ^ (a.factorization 2) * ordCompl[2] a := by
          rw [h]; exact mul_dvd_mul_right (pow_dvd_pow 2 hle) _
      _ = a := ea

/-- **General divisibility pigeonhole.** Among any `⌈N/2⌉ + 1` integers chosen
    from `{1, …, N}`, some one divides another: if `S ⊆ Icc 1 N` and
    `(N+1)/2 + 1 ≤ |S|`, then there exist distinct `a, b ∈ S` with `a ∣ b`. -/
theorem erdos_divisibility_pigeonhole_general {N : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 N) (hcard : (N + 1) / 2 + 1 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b := by
  -- The half-index of the odd part lands in `range ((N+1)/2)`.
  set f : ℕ → ℕ := fun m => (ordCompl[2] m - 1) / 2 with hf
  have hmaps : ∀ m ∈ S, f m ∈ Finset.range ((N + 1) / 2) := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp (hsub hm)
    have hmne : m ≠ 0 := by omega
    have ho_pos : 0 < ordCompl[2] m := Nat.ordCompl_pos 2 hmne
    have ho_le : ordCompl[2] m ≤ N := le_trans (Nat.ordCompl_le m 2) hm2
    rw [Finset.mem_range]
    show (ordCompl[2] m - 1) / 2 < (N + 1) / 2
    omega
  -- Pigeonhole: `range ((N+1)/2)` is strictly smaller than `S`.
  have hlt : (Finset.range ((N + 1) / 2)).card < S.card := by
    rw [Finset.card_range]; omega
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  have hane : a ≠ 0 := by
    obtain ⟨h, _⟩ := Finset.mem_Icc.mp (hsub ha); omega
  have hbne : b ≠ 0 := by
    obtain ⟨h, _⟩ := Finset.mem_Icc.mp (hsub hb); omega
  have hoa : Odd (ordCompl[2] a) := odd_ordComplN hane
  have hob : Odd (ordCompl[2] b) := odd_ordComplN hbne
  have hocc : ordCompl[2] a = ordCompl[2] b := by
    have hhalf : (ordCompl[2] a - 1) / 2 = (ordCompl[2] b - 1) / 2 := by
      have := hfab; simp only [hf] at this; exact this
    rw [← odd_recoverN hoa, ← odd_recoverN hob, hhalf]
  rcases dvd_or_dvd_of_ordCompl_eqN hocc with hd | hd
  · exact ⟨a, ha, b, hb, hab, hd⟩
  · exact ⟨b, hb, a, ha, hab.symm, hd⟩

/-- A **divisibility-antichain** in `{1, …, N}`: a finite set of integers drawn
    from `{1, …, N}`, no two distinct members of which are related by
    divisibility. -/
def IsDivAntichainN (N : ℕ) (S : Finset ℕ) : Prop :=
  S ⊆ Finset.Icc 1 N ∧ ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b

/-- `IsDivAntichainN N S` matches Mathlib's order-theoretic `IsAntichain` for
    the divisibility relation, restricted to `{1, …, N}`. -/
theorem isDivAntichainN_iff {N : ℕ} {S : Finset ℕ} :
    IsDivAntichainN N S ↔
      S ⊆ Finset.Icc 1 N ∧ IsAntichain (· ∣ ·) (S : Set ℕ) := by
  unfold IsDivAntichainN
  refine and_congr_right fun _ => ?_
  constructor
  · intro h a ha b hb hab; exact h a ha b hb hab
  · intro h a ha b hb hab; exact h ha hb hab

/-- **Upper bound.** A divisibility-antichain in `{1, …, N}` has at most
    `⌈N/2⌉ = (N+1)/2` elements: a larger one would, by
    `erdos_divisibility_pigeonhole_general`, contain a divisible pair. -/
theorem antichainN_card_le {N : ℕ} {S : Finset ℕ} (hS : IsDivAntichainN N S) :
    S.card ≤ (N + 1) / 2 := by
  by_contra h
  push_neg at h
  obtain ⟨a, ha, b, hb, hab, hdvd⟩ :=
    erdos_divisibility_pigeonhole_general hS.1 (by omega)
  exact hS.2 a ha b hb hab hdvd

/-- **Construction.** The block `{⌊N/2⌋+1, …, N}` of integers in `(N/2, N]` is a
    divisibility-antichain of size `⌈N/2⌉ = (N+1)/2`. A proper multiple of any
    `a > N/2` is at least `2a > N`, hence outside the block. -/
theorem blockN_isDivAntichain (N : ℕ) :
    IsDivAntichainN N (Finset.Icc (N / 2 + 1) N) ∧
      (Finset.Icc (N / 2 + 1) N).card = (N + 1) / 2 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x hx
    rw [Finset.mem_Icc] at hx ⊢; omega
  · intro a ha b hb hab hdvd
    rw [Finset.mem_Icc] at ha hb
    have hble : a ≤ b := Nat.le_of_dvd (by omega) hdvd
    have hlt : a < b := lt_of_le_of_ne hble hab
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : 2 ≤ c := by
      rcases c with _ | _ | c
      · simp at hc; omega
      · simp at hc; omega
      · omega
    have hba : 2 * a ≤ b := by subst hc; nlinarith [hc2]
    omega
  · rw [Nat.card_Icc]; omega

/-- **Extremal form (general `N`).** The maximum size of a divisibility-antichain
    in `{1, …, N}` is exactly `⌈N/2⌉ = (N+1)/2`: the block `{⌊N/2⌋+1, …, N}`
    attains it, and `antichainN_card_le` bounds everything else. -/
theorem max_antichainN_card (N : ℕ) :
    IsGreatest { k : ℕ | ∃ S : Finset ℕ, IsDivAntichainN N S ∧ S.card = k }
      ((N + 1) / 2) := by
  constructor
  · obtain ⟨hanti, hcard⟩ := blockN_isDivAntichain N
    exact ⟨Finset.Icc (N / 2 + 1) N, hanti, hcard⟩
  · rintro k ⟨S, hS, rfl⟩
    exact antichainN_card_le hS

/-- **Specialization to the parent.** For `N = 2n` the general bound `(N+1)/2`
    equals `n`, and the block `{⌊N/2⌋+1, …, N}` becomes `{n+1, …, 2n}` — exactly
    the extremal statement `ErdosDivisibilityPigeonhole.max_antichain_card`. -/
theorem max_antichainN_recovers_parent (n : ℕ) :
    (2 * n + 1) / 2 = n ∧ IsGreatest
      { k : ℕ | ∃ S : Finset ℕ, IsDivAntichainN (2 * n) S ∧ S.card = k } n := by
  have hhalf : (2 * n + 1) / 2 = n := by omega
  refine ⟨hhalf, ?_⟩
  have := max_antichainN_card (2 * n)
  rwa [hhalf] at this

-- Axiom audit: the extremal result depends only on the standard foundational
-- axioms (propext, Classical.choice, Quot.sound) — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms max_antichainN_card
#print axioms max_antichainN_recovers_parent

end ErdosDivisibilityPigeonhole
