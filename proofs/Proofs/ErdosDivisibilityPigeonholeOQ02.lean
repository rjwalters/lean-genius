/-
# Erdős Coprime Pigeonhole: among any `n+1` integers from `{1, …, 2n}`, two are coprime

The **coprimality dual** of the Erdős divisibility pigeonhole
(`Proofs.ErdosDivisibilityPigeonhole`). Where the divisibility version pigeonholes
on the *odd part* `ordCompl[2] m` to force a `∣`-comparable pair, here we pigeonhole
on the *consecutive-pair index* to force two **consecutive** integers — which are
automatically coprime.

> If `S ⊆ {1, 2, …, 2n}` has `|S| ≥ n + 1`, then there are two **distinct**
> elements `a, b ∈ S` with `Nat.Coprime a b`.

## Proof

Partition `{1, …, 2n}` into the `n` consecutive blocks
`{1,2}, {3,4}, …, {2n−1, 2n}`. The block of `m` is indexed by `(m−1)/2`, a map
sending `S` (of size `n+1`) into `range n`. By pigeonhole two distinct
`a, b ∈ S` land in the same block. Two distinct members of a block `{2k+1, 2k+2}`
differ by exactly `1`, so `{a, b}` are consecutive integers, hence coprime
(`gcd(m, m+1) = 1`).

## Sharpness

The bound `n+1` is best possible: the `n`-element set of **even** numbers
`{2, 4, …, 2n}` contains no coprime pair — any two share the factor `2`. This is
recorded as `erdos_coprime_pigeonhole_sharp`.

## Unification

`erdos_pigeonhole_div_and_coprime` runs both pigeonholes on the *same* hypothesis:
any `n+1`-element subset of `{1, …, 2n}` simultaneously contains a `∣`-comparable
pair **and** a coprime pair. The two extremal sets that defeat each conclusion are
dual — the top block `{n+1, …, 2n}` (no divisible pair) versus the evens
`{2, …, 2n}` (no coprime pair).

## References

* P. Erdős, problem folklore; the consecutive-pair pigeonhole is a companion to
  the divisor-chain pigeonhole. See e.g. Bóna, *A Walk Through Combinatorics*.
-/
import Mathlib
import Proofs.ErdosDivisibilityPigeonhole

namespace ErdosDivisibilityPigeonholeOQ02

open Finset

/-- An integer is coprime to its successor: `gcd(b, b+1) = 1`. -/
private lemma coprime_succ (b : ℕ) : Nat.Coprime b (b + 1) :=
  Nat.coprime_self_add_right.mpr (Nat.coprime_one_right b)

/-- Two **consecutive** integers are coprime: `gcd(m, m+1) = 1`, in either order. -/
private lemma coprime_of_consecutive {a b : ℕ} (h : a = b + 1 ∨ b = a + 1) :
    Nat.Coprime a b := by
  rcases h with h | h
  · subst h; exact (coprime_succ b).symm
  · subst h; exact coprime_succ a

/-- **Erdős Coprime Pigeonhole.** Among any `n + 1` integers chosen from
    `{1, 2, …, 2n}`, two are coprime: if `S ⊆ Icc 1 (2n)` and `n + 1 ≤ |S|`, then
    there exist distinct `a, b ∈ S` with `Nat.Coprime a b`. -/
theorem erdos_coprime_pigeonhole {n : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 (2 * n)) (hcard : n + 1 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Nat.Coprime a b := by
  -- The consecutive-block index `(m−1)/2` lands in `range n`.
  set g : ℕ → ℕ := fun m => (m - 1) / 2 with hg
  have hmaps : ∀ m ∈ S, g m ∈ Finset.range n := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp (hsub hm)
    rw [Finset.mem_range, hg]
    -- (m − 1)/2 < n ↔ m − 1 < 2n, and m ≤ 2n.
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  -- Pigeonhole: `range n` is strictly smaller than `S`.
  have hlt : (Finset.range n).card < S.card := by
    rw [Finset.card_range]; omega
  obtain ⟨a, ha, b, hb, hab, hgab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  -- Positivity from `S ⊆ Icc 1 (2n)`.
  have hane : 1 ≤ a := (Finset.mem_Icc.mp (hsub ha)).1
  have hbne : 1 ≤ b := (Finset.mem_Icc.mp (hsub hb)).1
  -- Same block index + distinct ⇒ consecutive.
  have hconsec : a = b + 1 ∨ b = a + 1 := by
    have hidx : (a - 1) / 2 = (b - 1) / 2 := by
      have := hgab; simp only [hg] at this; exact this
    omega
  exact ⟨a, ha, b, hb, hab, coprime_of_consecutive hconsec⟩

/-- **Sharpness.** The threshold `n + 1` is optimal: the `n`-element set of even
    numbers `{2, 4, …, 2n}` has no coprime pair, since every two of its members
    share the factor `2`. Hence no `n`-element bound suffices. -/
theorem erdos_coprime_pigeonhole_sharp (n : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 (2 * n) ∧ S.card = n ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ Nat.Coprime a b := by
  refine ⟨(Finset.Icc 1 n).image (fun k => 2 * k), ?_, ?_, ?_⟩
  · -- evens `2k` with `1 ≤ k ≤ n` lie in `Icc 1 (2n)`
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    rw [Finset.mem_Icc] at hk ⊢; omega
  · -- `k ↦ 2k` is injective, so the image has `n` elements
    rw [Finset.card_image_of_injective _
        (by intro x y h; have h2 : 2 * x = 2 * y := h; omega), Nat.card_Icc]
    omega
  · -- any two members are even, hence `2 ∣ gcd`, so not coprime
    intro a ha b hb _ hcop
    rw [Finset.mem_image] at ha hb
    obtain ⟨ka, _, rfl⟩ := ha
    obtain ⟨kb, _, rfl⟩ := hb
    have h2 : (2 : ℕ) ∣ Nat.gcd (2 * ka) (2 * kb) :=
      Nat.dvd_gcd ⟨ka, rfl⟩ ⟨kb, rfl⟩
    rw [Nat.Coprime] at hcop
    rw [hcop] at h2
    omega

/-- **Unification.** Both pigeonholes on the same hypothesis: any `n + 1`-element
    subset of `{1, …, 2n}` simultaneously contains a `∣`-comparable pair (parent
    `erdos_divisibility_pigeonhole`) **and** a coprime pair. -/
theorem erdos_pigeonhole_div_and_coprime {n : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 (2 * n)) (hcard : n + 1 ≤ S.card) :
    (∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b) ∧
      (∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ Nat.Coprime a b) :=
  ⟨ErdosDivisibilityPigeonhole.erdos_divisibility_pigeonhole hsub hcard,
   erdos_coprime_pigeonhole hsub hcard⟩

end ErdosDivisibilityPigeonholeOQ02
