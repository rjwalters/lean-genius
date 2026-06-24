import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-
# The Davenport constant of a cyclic group: D(ℤ/nℤ) = n

## What This Proves

For a finite abelian group `G`, the **Davenport constant** `D(G)` is the smallest
integer `d` such that *every* sequence of `d` elements of `G` (repetitions allowed)
admits a **nonempty zero-sum subsequence**. It is a second fundamental zero-sum
invariant of `G`, sitting alongside the Erdős–Ginzburg–Ziv constant
`s(G)` (the smallest `d` forcing a zero-sum subsequence of length exactly `|G|`).
For the cyclic group the two are different numbers: this file proves the cyclic
Davenport value

  `D(ℤ/nℤ) = n`,

complementing the gallery's `s(ℤ/nℤ) = 2n − 1` (Erdős–Ginzburg–Ziv, sharp form).

The result is packaged as an `IsLeast` statement about the set of admissible
lengths, which is exactly the textbook definition of the Davenport constant as a
minimum. Two ingredients meet at `n`:

* **Upper bound `n ∈ DavenportSet`** (`exists_nonempty_zerosum`): any `n` elements
  `a₀, …, a_{n-1}` of `ℤ/nℤ` contain a nonempty (in fact *consecutive*) zero-sum
  block. The crux is the classical prefix-sum pigeonhole: the `n + 1` partial sums
  `P(0), …, P(n)` cannot be distinct in the `n`-element group `ℤ/nℤ`, so two of them
  coincide, `P(u) = P(v)` with `u < v`, and the intervening block
  `{k : u ≤ k < v}` is a nonempty subset summing to `P(v) − P(u) = 0`.

* **Lower bound (sharpness)** (`davenport_lower_bound`, `davenport_sharp`): no
  shorter length works. The all-ones sequence of length `n − 1` (i.e. `n − 1`
  copies of a generator) has every nonempty subsequence summing to its cardinality
  `c` with `1 ≤ c ≤ n − 1`, never `0 mod n`. Hence every admissible length is `≥ n`.

Combining the two, `n` is the least admissible length, i.e. `D(ℤ/nℤ) = n`
(`davenport_zmod`). All results are verified with `0` axioms and `0` sorries.

## Why This Is Not Already in the Gallery / Mathlib

Mathlib has neither the Davenport constant nor this prefix-sum zero-sum lemma; its
only zero-sum content is Erdős–Ginzburg–Ziv. The gallery's
`erdos-ginzburg-ziv-oq-01` computes the *EGZ* constant `s(ℤ/nℤ) = 2n − 1`; the
Davenport constant is the genuinely distinct companion invariant, with an
independent (prefix-sum, not Chevalley–Warning) proof and a different value `n`.
The neighbouring `erdos-divisibility-pigeonhole` family concerns the divisibility
relation, not zero sums, so there is no overlap.
-/

namespace Proofs.DavenportZMod

open Finset

variable (n : ℕ) [NeZero n]

/-- The prefix sum: the sum of the first `k` entries of the sequence `a`. -/
def prefixSum (a : Fin n → ZMod n) (k : ℕ) : ZMod n :=
  ∑ i ∈ univ.filter (fun i : Fin n => i.val < k), a i

/-- The set of *admissible lengths*: those `d` for which every length-`d`
sequence over `ℤ/nℤ` has a nonempty zero-sum subsequence. The Davenport constant
is by definition the least element of this set. -/
def DavenportSet (n : ℕ) : Set ℕ :=
  {d | ∀ a : Fin d → ZMod n, ∃ S : Finset (Fin d), S.Nonempty ∧ ∑ i ∈ S, a i = 0}

omit [NeZero n] in
/-- **Prefix-sum split.** For `u ≤ v`, the first `v` entries split as the first
`u` entries together with the block `[u, v)`. -/
theorem prefixSum_split (a : Fin n → ZMod n) {u v : ℕ} (huv : u ≤ v) :
    prefixSum n a v
      = prefixSum n a u + ∑ k ∈ univ.filter (fun k : Fin n => u ≤ k.val ∧ k.val < v), a k := by
  unfold prefixSum
  rw [← Finset.sum_union]
  · congr 1
    ext k
    simp only [mem_filter, mem_union, mem_univ, true_and]
    omega
  · rw [Finset.disjoint_filter]
    intro k _ h
    omega

/-- **Davenport upper bound (the crux).** Any `n` elements of `ℤ/nℤ` contain a
nonempty zero-sum subsequence — in fact a nonempty consecutive block. -/
theorem exists_nonempty_zerosum (a : Fin n → ZMod n) :
    ∃ S : Finset (Fin n), S.Nonempty ∧ ∑ i ∈ S, a i = 0 := by
  -- Pigeonhole on the `n + 1` prefix sums `P 0, …, P n` valued in the `n`-element `ZMod n`.
  have hcard : (univ : Finset (ZMod n)).card < (range (n + 1)).card := by
    rw [Finset.card_univ, ZMod.card, Finset.card_range]; omega
  obtain ⟨u, hu, v, hv, huv, hPeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard
      (f := fun k => prefixSum n a k) (fun k _ => mem_univ _)
  rw [Finset.mem_range] at hu hv
  -- Order the two colliding indices.
  wlog hlt : u < v generalizing u v
  · exact this v hv u hu (Ne.symm huv) hPeq.symm (by omega)
  -- The block `[u, v)` is a nonempty zero-sum subset.
  refine ⟨univ.filter (fun k : Fin n => u ≤ k.val ∧ k.val < v), ?_, ?_⟩
  · -- nonempty: the index with value `u` lies in `Fin n` (since `u < v ≤ n`) and in the block
    refine ⟨⟨u, by omega⟩, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    omega
  · -- zero-sum: the block sum is `P v - P u = 0`
    have hsplit := prefixSum_split n a (le_of_lt hlt)
    have : prefixSum n a u
        + ∑ k ∈ univ.filter (fun k : Fin n => u ≤ k.val ∧ k.val < v), a k
        = prefixSum n a u := by rw [← hsplit, hPeq]
    linear_combination this

/-- `n` is an admissible length: it lies in `DavenportSet n`. -/
theorem n_mem_DavenportSet : n ∈ DavenportSet n :=
  exists_nonempty_zerosum n

/-- **Sharpness witness.** The all-ones sequence of length `n - 1` (i.e. `n - 1`
copies of the generator `1`) has *no* nonempty zero-sum subsequence: every nonempty
sub-block sums to its cardinality `c` with `1 ≤ c ≤ n - 1`, never `0` in `ℤ/nℤ`. -/
theorem davenport_sharp :
    ∃ a : Fin (n - 1) → ZMod n,
      ∀ S : Finset (Fin (n - 1)), S.Nonempty → ∑ i ∈ S, a i ≠ 0 := by
  refine ⟨fun _ => 1, fun S hS hzero => ?_⟩
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at hzero
  -- `(S.card : ZMod n) = 0` forces `n ∣ S.card`, impossible for `0 < S.card < n`.
  rw [ZMod.natCast_eq_zero_iff] at hzero
  have h1 : 0 < S.card := Finset.card_pos.mpr hS
  have h2 : S.card ≤ n - 1 := by
    calc S.card ≤ (univ : Finset (Fin (n - 1))).card := Finset.card_le_card (subset_univ S)
      _ = n - 1 := by rw [Finset.card_univ, Fintype.card_fin]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have := Nat.le_of_dvd h1 hzero
  omega

omit [NeZero n] in
/-- **Davenport lower bound.** Every admissible length is at least `n`: no sequence
shorter than `n` is guaranteed a nonempty zero-sum subsequence. -/
theorem davenport_lower_bound : ∀ d ∈ DavenportSet n, n ≤ d := by
  intro d hd
  by_contra hlt
  push_neg at hlt
  -- The all-ones sequence of length `d < n` is a counterexample to `d ∈ DavenportSet n`.
  obtain ⟨S, hS, hzero⟩ := hd (fun _ => 1)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff] at hzero
  have h1 : 0 < S.card := Finset.card_pos.mpr hS
  have h2 : S.card ≤ d := by
    calc S.card ≤ (univ : Finset (Fin d)).card := Finset.card_le_card (subset_univ S)
      _ = d := by rw [Finset.card_univ, Fintype.card_fin]
  have := Nat.le_of_dvd h1 hzero
  omega

/-- **The Davenport constant of the cyclic group: `D(ℤ/nℤ) = n`.** It is the least
length forcing a nonempty zero-sum subsequence. -/
theorem davenport_zmod : IsLeast (DavenportSet n) n :=
  ⟨n_mem_DavenportSet n, davenport_lower_bound n⟩

end Proofs.DavenportZMod
