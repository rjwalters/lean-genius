/-
Ramsey Theory — OQ-04-OQ-01: The δ-function engine of the stepping-up lemma

Source: open question of the ramseys-theorem gallery (hypergraph Ramsey, OQ-04)
Parent: Proofs/RamseysTheoremOQ04.lean  (k-uniform hypergraph Ramsey)

## Background: the Erdős–Hajnal stepping-up lemma

The stepping-up lemma is the central tool for *lower* bounds on hypergraph Ramsey
numbers: from a 2-colouring of the k-subsets of `[n]` with no large monochromatic
set it builds a 2-colouring of the (k+1)-subsets of `[2ⁿ]` with no large
monochromatic set, roughly doubling the relevant tower height. Identifying each
element of `[2ⁿ]` with its binary expansion in `{0,1}ⁿ`, the construction is driven
entirely by one gadget: for two distinct numbers `a ≠ b`, the **top differing bit**

  δ(a, b) := the highest bit position at which the binary expansions of a and b differ.

The colour of a (k+1)-set `{x₀ < x₁ < ⋯ < x_k}` is read off from the pattern of the
δ-values `δ(x₀,x₁), δ(x₁,x₂), …, δ(x_{k-1},x_k)`, and the proof that this colouring
has no large monochromatic set rests on exactly three properties of δ:

  (A) **winner bit** — if `a < b` then at bit `δ(a,b)` the larger number `b` has a `1`
      and the smaller `a` has a `0`;
  (B) **distinctness** — for `a < b < c`, `δ(a,b) ≠ δ(b,c)`;
  (C) **max law** — for `a < b < c`, `δ(a,c) = max(δ(a,b), δ(b,c))`.

(B) and (C) together say the sequence of δ-values along an increasing chain has no
repeated adjacent value and behaves like a "max", which is what forces the
monochromatic structure to collapse.

## What this file contributes (0-axiom, machine-checked)

We formalize δ purely combinatorially via `Nat.testBit` and prove (A), (B), (C),
together with existence, uniqueness, and symmetry of the top differing bit. δ is
captured relationally (`TopDiff a b i` = "`i` is the top differing bit of `a` and
`b`") to stay fully constructive — no choice, no noncomputable definitions. These
are the verified combinatorial primitives on which a future Lean formalization of
the full stepping-up colouring can be built.

All results are 0-axiom (only `propext`/`Classical.choice`/`Quot.sound`), no
`native_decide`; the finite `decide` calls are over `Bool`.
-/
import Mathlib

namespace RamseyStepUp

/-! ## Bit-level helpers -/

/-- A `Bool`-xor that evaluates to `true` means the two bits differ. -/
theorem bool_xor_true {x y : Bool} (h : (x ^^ y) = true) : x ≠ y := by
  revert h; cases x <;> cases y <;> decide

/-- A `Bool`-xor that evaluates to `false` means the two bits agree. -/
theorem bool_xor_false {x y : Bool} (h : (x ^^ y) = false) : x = y := by
  revert h; cases x <;> cases y <;> decide

/-! ## The most-significant set bit, and the top differing bit δ -/

/-- `i` is the most significant set bit of `n`: bit `i` is set and every higher bit
is clear. -/
@[reducible] def IsMSB (n i : ℕ) : Prop :=
  n.testBit i = true ∧ ∀ j, i < j → n.testBit j = false

/-- Every nonzero `n` has a most significant set bit (Mathlib's
`Nat.exists_most_significant_bit`). -/
theorem isMSB_exists {n : ℕ} (hn : n ≠ 0) : ∃ i, IsMSB n i :=
  Nat.exists_most_significant_bit hn

/-- The most significant set bit is unique. -/
theorem isMSB_unique {n i i' : ℕ} (h : IsMSB n i) (h' : IsMSB n i') : i = i' := by
  rcases lt_trichotomy i i' with hlt | heq | hgt
  · have hf := h.2 i' hlt; have ht := h'.1; rw [hf] at ht; simp at ht
  · exact heq
  · have hf := h'.2 i hgt; have ht := h.1; rw [hf] at ht; simp at ht

/-- **δ, relationally.** `TopDiff a b i` says `i` is the top bit at which `a` and `b`
differ — the most significant set bit of `a XOR b`. -/
@[reducible] def TopDiff (a b i : ℕ) : Prop := IsMSB (a ^^^ b) i

/-- δ exists for any two distinct numbers. -/
theorem topDiff_exists {a b : ℕ} (hab : a ≠ b) : ∃ i, TopDiff a b i :=
  isMSB_exists fun h => hab (Nat.xor_eq_zero_iff.mp h)

/-- δ is well-defined: the top differing bit is unique. -/
theorem topDiff_unique {a b i i' : ℕ} (h : TopDiff a b i) (h' : TopDiff a b i') :
    i = i' :=
  isMSB_unique h h'

/-- δ is symmetric: `δ(a,b) = δ(b,a)`. -/
theorem topDiff_comm {a b i : ℕ} : TopDiff a b i ↔ TopDiff b a i := by
  unfold TopDiff; rw [Nat.xor_comm a b]

/-! ## Property (A): the winner bit -/

/-- **(A) Winner bit.** If `a < b` and `i = δ(a,b)`, then at bit `i` the larger
number `b` carries a `1` and the smaller number `a` carries a `0`. This is the fact
that lets the stepping-up colouring recover the order of two elements from their top
differing bit. -/
theorem topDiff_winner {a b i : ℕ} (hab : a < b) (h : TopDiff a b i) :
    a.testBit i = false ∧ b.testBit i = true := by
  have hdiff : a.testBit i ≠ b.testBit i :=
    bool_xor_true (by rw [← Nat.testBit_xor]; exact h.1)
  have hagree : ∀ j, i < j → a.testBit j = b.testBit j :=
    fun j hj => bool_xor_false (by rw [← Nat.testBit_xor]; exact h.2 j hj)
  have hbi : b.testBit i = true := by
    by_contra hb
    simp only [Bool.not_eq_true] at hb
    rcases Bool.dichotomy (a.testBit i) with hai | hai
    · exact hdiff (hai.trans hb.symm)
    · exact absurd (Nat.lt_of_testBit i hb hai fun j hj => (hagree j hj).symm)
        (by omega)
  refine ⟨?_, hbi⟩
  rcases Bool.dichotomy (a.testBit i) with hai | hai
  · exact hai
  · exact absurd (hai.trans hbi.symm) hdiff

/-! ## Property (B): adjacent δ-values are distinct -/

/-- **(B) Distinctness.** For `a < b < c`, the two adjacent top differing bits
`δ(a,b)` and `δ(b,c)` are never equal: at a common bit `i`, the winner-bit property
would force `b` to carry both a `1` (as the larger of `a,b`) and a `0` (as the
smaller of `b,c`). -/
theorem topDiff_ne {a b c i i' : ℕ} (hab : a < b) (hbc : b < c)
    (h : TopDiff a b i) (h' : TopDiff b c i') : i ≠ i' := by
  rintro rfl
  have hb1 : b.testBit i = true := (topDiff_winner hab h).2
  have hb2 : b.testBit i = false := (topDiff_winner hbc h').1
  rw [hb1] at hb2; simp at hb2

/-! ## Property (C): the max law -/

/-- The most significant set bit of `N₁ XOR N₂`, when the two MSBs differ, sits at
`max i i'`: at that bit exactly one of `N₁, N₂` is set, and all higher bits are clear
in both. -/
theorem isMSB_xor_of_ne {N₁ N₂ i i' : ℕ} (hne : i ≠ i')
    (h₁ : IsMSB N₁ i) (h₂ : IsMSB N₂ i') : IsMSB (N₁ ^^^ N₂) (max i i') := by
  refine ⟨?_, ?_⟩
  · rw [Nat.testBit_xor]
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [max_eq_right hlt.le, h₁.2 i' hlt, h₂.1]; decide
    · rw [max_eq_left hgt.le, h₂.2 i hgt, h₁.1]; decide
  · intro j hj
    rw [Nat.testBit_xor, h₁.2 j (lt_of_le_of_lt (le_max_left i i') hj),
      h₂.2 j (lt_of_le_of_lt (le_max_right i i') hj)]
    decide

/-- **(C) Max law.** For `a < b < c`, the top differing bit of the endpoints is the
maximum of the two adjacent top differing bits: `δ(a,c) = max(δ(a,b), δ(b,c))`.
This is the identity that lets the stepping-up colouring propagate structure along an
increasing chain. -/
theorem topDiff_max {a b c i i' m : ℕ} (hab : a < b) (hbc : b < c)
    (h : TopDiff a b i) (h' : TopDiff b c i') (hm : TopDiff a c m) :
    m = max i i' := by
  have hxor : (a ^^^ b) ^^^ (b ^^^ c) = a ^^^ c := by
    rw [Nat.xor_assoc, ← Nat.xor_assoc b b c, Nat.xor_self, Nat.zero_xor]
  have key : IsMSB (a ^^^ c) (max i i') := by
    have hstep := isMSB_xor_of_ne (topDiff_ne hab hbc h h') h h'
    rwa [hxor] at hstep
  exact isMSB_unique hm key

/-! ## Summary

`TopDiff` (the top differing bit δ) is well-defined (`topDiff_exists`,
`topDiff_unique`), symmetric (`topDiff_comm`), and satisfies the three Erdős–Hajnal
stepping-up properties: the winner bit `topDiff_winner` (A), adjacent distinctness
`topDiff_ne` (B), and the max law `topDiff_max` (C). These are exactly the
combinatorial primitives the stepping-up colouring is built from. -/

end RamseyStepUp
