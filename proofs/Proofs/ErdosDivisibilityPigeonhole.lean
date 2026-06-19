/-
# Erdős Divisibility Pigeonhole: among any `n+1` integers from `{1, …, 2n}`, one divides another

A classical pigeonhole gem (often attributed to Erdős; a staple competition
problem). The statement:

> If `S ⊆ {1, 2, …, 2n}` has `|S| ≥ n + 1`, then there are two **distinct**
> elements `a, b ∈ S` with `a ∣ b`.

## Proof

Write each `m ≥ 1` uniquely as `m = 2^k · o(m)` with `o(m) := ordCompl[2] m` its
**odd part**. There are exactly `n` odd numbers in `{1, …, 2n}`, namely
`1, 3, …, 2n−1`, so the map `m ↦ o(m)` sends the `n+1` elements of `S` into a set
of size `n`. By pigeonhole two distinct `a, b ∈ S` share an odd part,
`o(a) = o(b) =: o`. Then `a = 2^{v_2(a)} · o` and `b = 2^{v_2(b)} · o`; whichever
has the smaller power of two divides the other.

We avoid counting the odd numbers directly: the odd part `o = ordCompl[2] m`
satisfies `1 ≤ o ≤ m ≤ 2n`, so `(o − 1) / 2 < n`, i.e. `m ↦ (o(m) − 1)/2` lands
in `Finset.range n`. Because the odd part is *odd*, this half-map is injective on
odd parts, so a collision of half-maps recovers `o(a) = o(b)`.

## Sharpness

The bound `n+1` is best possible: the `n`-element set `{n+1, …, 2n}` contains no
pair `a ∣ b` (a proper multiple of `a ≥ n+1` already exceeds `2n`). This is
recorded as `erdos_divisibility_pigeonhole_sharp`.

## References

* P. Erdős, problem folklore; see e.g. Bóna, *A Walk Through Combinatorics*,
  the pigeonhole chapter.
-/
import Mathlib

namespace ErdosDivisibilityPigeonhole

open Finset

/-- For an odd `o`, halving `(o − 1)/2` and rebuilding recovers `o`:
    `2 · ((o − 1)/2) + 1 = o`. This makes `o ↦ (o − 1)/2` injective on odd
    numbers, the key to reading an odd part back off its half-index. -/
private lemma odd_recover {o : ℕ} (h : Odd o) : 2 * ((o - 1) / 2) + 1 = o := by
  obtain ⟨k, rfl⟩ := h
  simp [Nat.add_sub_cancel, Nat.mul_div_cancel_left]

/-- The odd part `ordCompl[2] m` is odd whenever `m ≠ 0`. -/
private lemma odd_ordCompl {m : ℕ} (hm : m ≠ 0) : Odd (ordCompl[2] m) := by
  rw [Nat.odd_iff]
  have h2 : ¬ (2 ∣ ordCompl[2] m) := Nat.not_dvd_ordCompl (by norm_num) hm
  omega

/-- If two positive numbers share an odd part (`ordCompl[2] a = ordCompl[2] b`),
    then one divides the other: with `a = 2^{v_2 a}·o` and `b = 2^{v_2 b}·o`, the
    smaller power of two wins. -/
private lemma dvd_or_dvd_of_ordCompl_eq {a b : ℕ} (_ha : a ≠ 0) (_hb : b ≠ 0)
    (h : ordCompl[2] a = ordCompl[2] b) : a ∣ b ∨ b ∣ a := by
  have ea : 2 ^ (a.factorization 2) * ordCompl[2] a = a :=
    Nat.ordProj_mul_ordCompl_eq_self a 2
  have eb : 2 ^ (b.factorization 2) * ordCompl[2] b = b :=
    Nat.ordProj_mul_ordCompl_eq_self b 2
  rcases le_total (a.factorization 2) (b.factorization 2) with hle | hle
  · left
    -- a ∣ b : 2^{v_2 a}·o ∣ 2^{v_2 b}·o since 2^{v_2 a} ∣ 2^{v_2 b}
    calc a = 2 ^ (a.factorization 2) * ordCompl[2] a := ea.symm
      _ ∣ 2 ^ (b.factorization 2) * ordCompl[2] b := by
          rw [h]; exact mul_dvd_mul_right (pow_dvd_pow 2 hle) _
      _ = b := eb
  · right
    calc b = 2 ^ (b.factorization 2) * ordCompl[2] b := eb.symm
      _ ∣ 2 ^ (a.factorization 2) * ordCompl[2] a := by
          rw [h]; exact mul_dvd_mul_right (pow_dvd_pow 2 hle) _
      _ = a := ea

/-- **Erdős Divisibility Pigeonhole.** Among any `n + 1` integers chosen from
    `{1, 2, …, 2n}`, some one divides another: if `S ⊆ Icc 1 (2n)` and
    `n + 1 ≤ |S|`, then there exist distinct `a, b ∈ S` with `a ∣ b`. -/
theorem erdos_divisibility_pigeonhole {n : ℕ} {S : Finset ℕ}
    (hsub : S ⊆ Finset.Icc 1 (2 * n)) (hcard : n + 1 ≤ S.card) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ a ∣ b := by
  -- The half-index of the odd part lands in `range n`.
  set f : ℕ → ℕ := fun m => (ordCompl[2] m - 1) / 2 with hf
  have hmaps : ∀ m ∈ S, f m ∈ Finset.range n := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp (hsub hm)
    have hmne : m ≠ 0 := by omega
    have ho_le : ordCompl[2] m ≤ 2 * n := le_trans (Nat.ordCompl_le m 2) hm2
    rw [Finset.mem_range, hf]
    -- (o − 1)/2 < n ↔ o − 1 < 2n, and o ≤ 2n.
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    omega
  -- Pigeonhole: `range n` is strictly smaller than `S`.
  have hlt : (Finset.range n).card < S.card := by
    rw [Finset.card_range]; omega
  obtain ⟨a, ha, b, hb, hab, hfab⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt hmaps
  -- Positivity of `a, b` from `S ⊆ Icc 1 (2n)`.
  have hane : a ≠ 0 := by
    obtain ⟨h, _⟩ := Finset.mem_Icc.mp (hsub ha); omega
  have hbne : b ≠ 0 := by
    obtain ⟨h, _⟩ := Finset.mem_Icc.mp (hsub hb); omega
  -- Equal half-indices of (odd) odd parts ⇒ equal odd parts.
  have hoa : Odd (ordCompl[2] a) := odd_ordCompl hane
  have hob : Odd (ordCompl[2] b) := odd_ordCompl hbne
  have hocc : ordCompl[2] a = ordCompl[2] b := by
    have hhalf : (ordCompl[2] a - 1) / 2 = (ordCompl[2] b - 1) / 2 := by
      have := hfab
      simp only [hf] at this
      exact this
    rw [← odd_recover hoa, ← odd_recover hob, hhalf]
  -- One divides the other; orient using `a ≠ b`.
  rcases dvd_or_dvd_of_ordCompl_eq hane hbne hocc with hd | hd
  · exact ⟨a, ha, b, hb, hab, hd⟩
  · exact ⟨b, hb, a, ha, hab.symm, hd⟩

/-- **Sharpness.** The threshold `n + 1` is optimal: the `n`-element set
    `{n+1, …, 2n}` has no pair `a ∣ b` with `a ≠ b`, because a proper multiple of
    any `a ≥ n+1` already exceeds `2n`. Hence no `n`-element bound suffices. -/
theorem erdos_divisibility_pigeonhole_sharp (n : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 (2 * n) ∧ S.card = n ∧
      ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b := by
  refine ⟨Finset.Icc (n + 1) (2 * n), ?_, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_Icc] at hx ⊢; omega
  · rw [Nat.card_Icc]; omega
  · intro a ha b hb hab hdvd
    rw [Finset.mem_Icc] at ha hb
    -- a ∣ b with a ≠ b and b > 0 forces b ≥ 2a, but 2a ≥ 2(n+1) > 2n ≥ b.
    have hble : a ≤ b := Nat.le_of_dvd (by omega) hdvd
    have hlt : a < b := lt_of_le_of_ne hble hab
    obtain ⟨c, hc⟩ := hdvd
    have hc2 : 2 ≤ c := by
      rcases c with _ | _ | c
      · simp at hc; omega
      · simp at hc; omega
      · omega
    -- `b = a · c` with `c ≥ 2` gives `2a ≤ c·a = a·c = b`, deterministically.
    have hmul : 2 * a ≤ c * a := mul_le_mul_right' hc2 a
    have hba : 2 * a ≤ b := by rw [hc, mul_comm a c]; exact hmul
    omega

end ErdosDivisibilityPigeonhole
