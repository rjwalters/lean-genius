/-
# Erdős Divisibility Pigeonhole — chain refinement: collisions can be confined to pairs

The parent entry (`Proofs/ErdosDivisibilityPigeonhole.lean`) proves the gem: among
any `n + 1` integers from `{1, …, 2n}`, some one divides another. The parent's
*open question* asks for a **quantitative refinement**:

> Among any `n + 1` elements of `{1, …, 2n}`, must there exist a divisibility chain
> `a₁ ∣ a₂ ∣ ⋯` whose length grows with `n`, or can the forced collisions always be
> confined to a single pair?

This file settles it: **collisions can be confined to pairs.** The threshold `n + 1`
forces a divisibility *pair* (parent theorem) but cannot force any longer chain.

## The witness

For `n ≥ 1` take `T = {n, n+1, …, 2n} = Icc n (2n)`, an `(n+1)`-element subset of
`{1, …, 2n}`.

* `T` **contains a divisibility pair**: `n ∣ 2n`, and (by the parent pigeonhole)
  *every* `(n+1)`-subset must — see `every_threshold_set_has_pair`.
* `T` **contains no 3-term chain** `a ∣ b ∣ c` of distinct elements
  (`block_no_chain3`): a proper divisor relation `a ∣ b` with `a, b ∈ [n, 2n]`
  forces `b ≥ 2a ≥ 2n`, hence `a = n`, `b = 2n`; then `b ∣ c` with `c ≤ 2n` is
  impossible. So the longest divisibility chain in `T` has length exactly `2`.

Thus no chain longer than a pair can be forced at the threshold — the first horn of
the dichotomy fails.

## The contrast

The dichotomy is genuine: the *ambient* interval `{1, …, 2n}` does contain
divisibility chains of length growing with `n`. The powers of two
`1, 2, 4, …, 2^k` (with `2^k ≤ 2n`) form a totally `∣`-ordered chain of length
`k + 1` (`ambient_has_long_chain`), so chain lengths in `{1, …, 2n}` are unbounded
as `n → ∞` (`ambient_chain_length_unbounded`). What collapses to a pair is only the
*forced* structure among `n + 1`-element subsets, not what the interval can hold.

Axiom-free: built from the parent's verified pigeonhole theorem plus foundational
Mathlib lemmas (no `sorry`, no `axiom`, no `native_decide`).
-/
import Mathlib
import Proofs.ErdosDivisibilityPigeonhole

namespace ErdosDivisibilityPigeonhole

open Finset

/-- A **3-term divisibility chain** in `S`: three elements `a, b, c ∈ S` with
`a ∣ b ∣ c` and `a ≠ b`, `b ≠ c` (so, for positive elements, `a < b < c`). -/
def HasDivChain3 (S : Finset ℕ) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, a ≠ b ∧ b ≠ c ∧ a ∣ b ∧ b ∣ c

/-- **No 3-term chain in the witness block.** For `n ≥ 1`, the set
`{n, n+1, …, 2n} = Icc n (2n)` contains no 3-term divisibility chain. A proper
divisor relation `a ∣ b` with `a, b ∈ [n, 2n]` forces `b ≥ 2a ≥ 2n`, so `a = n`,
`b = 2n`; then `b ∣ c` with `c ≤ 2n` is impossible (`c ≥ 2b = 4n > 2n`). -/
theorem block_no_chain3 {n : ℕ} (hn : 1 ≤ n) :
    ¬ HasDivChain3 (Finset.Icc n (2 * n)) := by
  rintro ⟨a, ha, b, hb, c, hc, hab, hbc, hdab, hdbc⟩
  rw [Finset.mem_Icc] at ha hb hc
  have hb0 : 0 < b := by omega
  have hc0 : 0 < c := by omega
  -- `a ∣ b` with `a ≠ b` and `a > 0` ⟹ `b ≥ 2a`.
  have hab_lt : a < b := lt_of_le_of_ne (Nat.le_of_dvd hb0 hdab) hab
  obtain ⟨d, hd⟩ := hdab
  have hd2 : 2 ≤ d := by
    rcases d with _ | _ | d
    · simp at hd; omega
    · simp at hd; omega
    · omega
  have hb2a : 2 * a ≤ b := by rw [hd, mul_comm a d]; exact mul_le_mul_right' hd2 a
  -- `b ∣ c` with `b ≠ c` and `b > 0` ⟹ `c ≥ 2b`.
  have hbc_lt : b < c := lt_of_le_of_ne (Nat.le_of_dvd hc0 hdbc) hbc
  obtain ⟨e, he⟩ := hdbc
  have he2 : 2 ≤ e := by
    rcases e with _ | _ | e
    · simp at he; omega
    · simp at he; omega
    · omega
  have hc2b : 2 * b ≤ c := by rw [he, mul_comm b e]; exact mul_le_mul_right' he2 b
  -- `2n ≤ 2a ≤ b` and `2b ≤ c ≤ 2n` are incompatible for `n ≥ 1`.
  omega

/-- **The witness block has a divisibility pair.** `n ∣ 2n` with `n ≠ 2n`, both in
`Icc n (2n)` (for `n ≥ 1`). -/
theorem block_has_pair {n : ℕ} (hn : 1 ≤ n) :
    ∃ a ∈ Finset.Icc n (2 * n), ∃ b ∈ Finset.Icc n (2 * n), a ≠ b ∧ a ∣ b := by
  refine ⟨n, ?_, 2 * n, ?_, ?_, ⟨2, by ring⟩⟩
  · rw [Finset.mem_Icc]; omega
  · rw [Finset.mem_Icc]; omega
  · omega

/-- **The forced pair is unavoidable.** By the parent pigeonhole theorem, *every*
`(n+1)`-element subset of `{1, …, 2n}` already contains a divisibility pair. The
content of the refinement below is that nothing *beyond* a pair can be forced. -/
theorem every_threshold_set_has_pair {n : ℕ} {T : Finset ℕ}
    (hsub : T ⊆ Finset.Icc 1 (2 * n)) (hcard : n + 1 ≤ T.card) :
    ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ a ∣ b :=
  erdos_divisibility_pigeonhole hsub hcard

/-- **Collisions can be confined to pairs.** For `n ≥ 1` there is an `(n+1)`-element
subset `T ⊆ {1, …, 2n}` that contains a divisibility pair (necessarily, by
`every_threshold_set_has_pair`) yet contains **no** 3-term divisibility chain. Hence
the pigeonhole threshold forces a pair but no longer chain: the longest divisibility
chain that can be forced among `(n+1)`-subsets has length exactly `2`. -/
theorem collisions_confined_to_pairs {n : ℕ} (hn : 1 ≤ n) :
    ∃ T : Finset ℕ, T ⊆ Finset.Icc 1 (2 * n) ∧ T.card = n + 1 ∧
      (∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ a ∣ b) ∧ ¬ HasDivChain3 T := by
  refine ⟨Finset.Icc n (2 * n), ?_, ?_, block_has_pair hn, block_no_chain3 hn⟩
  · intro x hx; rw [Finset.mem_Icc] at hx ⊢; omega
  · rw [Nat.card_Icc]; omega

/-- **The ambient interval holds arbitrarily long chains.** Whenever `2^k ≤ 2n`, the
powers of two `1, 2, …, 2^k` form a subset of `{1, …, 2n}` of size `k + 1` that is
totally ordered by divisibility (`a ≤ b → a ∣ b`). This is the second horn of the
dichotomy: chains in `{1, …, 2n}` itself are *not* confined to pairs. -/
theorem ambient_has_long_chain (k n : ℕ) (hk : 2 ^ k ≤ 2 * n) :
    ∃ C : Finset ℕ, C ⊆ Finset.Icc 1 (2 * n) ∧ C.card = k + 1 ∧
      ∀ a ∈ C, ∀ b ∈ C, a ≤ b → a ∣ b := by
  refine ⟨(Finset.range (k + 1)).image (2 ^ ·), ?_, ?_, ?_⟩
  · -- subset of `{1, …, 2n}`
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Icc]
    refine ⟨Nat.one_le_two_pow, ?_⟩
    calc 2 ^ i ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ ≤ 2 * n := hk
  · -- size `k + 1`
    rw [Finset.card_image_of_injective _ (Nat.pow_right_injective (le_refl 2)),
      Finset.card_range]
  · -- totally `∣`-ordered
    intro a ha b hb hle
    rw [Finset.mem_image] at ha hb
    obtain ⟨i, _, rfl⟩ := ha
    obtain ⟨j, _, rfl⟩ := hb
    have hij : i ≤ j := by
      by_contra h
      push_neg at h
      have : (2 : ℕ) ^ j < 2 ^ i := Nat.pow_lt_pow_right (by norm_num) h
      omega
    exact pow_dvd_pow 2 hij

/-- **Chain lengths in `{1, …, 2n}` are unbounded.** For every target length `k`
there is an `n` (namely `2^k`) for which `{1, …, 2n}` contains a divisibility chain
of length at least `k`. Contrasted with `collisions_confined_to_pairs`, this shows
the parent's dichotomy is real: the ambient interval has growing chains even though
the *forced* structure among `(n+1)`-subsets never exceeds a pair. -/
theorem ambient_chain_length_unbounded (k : ℕ) :
    ∃ n : ℕ, ∃ C : Finset ℕ, C ⊆ Finset.Icc 1 (2 * n) ∧ k ≤ C.card ∧
      ∀ a ∈ C, ∀ b ∈ C, a ≤ b → a ∣ b := by
  obtain ⟨C, hsub, hcard, hchain⟩ :=
    ambient_has_long_chain k (2 ^ k) (le_mul_of_one_le_left (Nat.zero_le _) one_le_two)
  exact ⟨2 ^ k, C, hsub, by omega, hchain⟩

-- Axiom audit: confirms the chain-refinement result depends only on the standard
-- foundational axioms (propext, Classical.choice, Quot.sound) — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms collisions_confined_to_pairs
#print axioms ambient_chain_length_unbounded

end ErdosDivisibilityPigeonhole
