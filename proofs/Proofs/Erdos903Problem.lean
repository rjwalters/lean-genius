/-
Erdős Problem #903: Block Designs and the de Bruijn-Erdős Gap

Source: https://erdosproblems.com/903
Status: SOLVED

Statement:
Let n = p² + p + 1 for some prime power p, and let A₁, ..., Aₜ ⊆ {1,...,n} be
a block design (every pair x, y is contained in exactly one Aᵢ).
Is it true that if t > n then t ≥ n + p?

Answer: YES

This was a conjecture of Erdős and Sós. The classic projective plane construction
shows t = n is achievable. The de Bruijn-Erdős theorem (1948) established t ≥ n.

Erdős, Fowler, Sós, and Wilson (1985) proved this conjecture, and showed further
that unless the design comes from a projective plane with one line "broken up",
we have t ≥ n + cp where c ≈ 1.148.

Tags: combinatorics, block-designs, finite-geometry
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic

namespace Erdos903

/-
## Part 1: Basic Definitions

Block designs and the key parameters.
-/

/-- A block design on {1,...,n} is a collection of subsets (blocks) such that
    every pair of distinct elements is contained in exactly one block -/
structure BlockDesign (n : ℕ) where
  blocks : Finset (Finset ℕ)
  blocks_subset : ∀ A ∈ blocks, ∀ a ∈ A, 1 ≤ a ∧ a ≤ n
  pair_coverage : ∀ x y : ℕ, 1 ≤ x → x ≤ n → 1 ≤ y → y ≤ n → x ≠ y →
    ∃! A, A ∈ blocks ∧ x ∈ A ∧ y ∈ A

/-- The number of blocks in a design -/
def BlockDesign.numBlocks {n : ℕ} (D : BlockDesign n) : ℕ :=
  D.blocks.card

/-- A prime power: p^k for prime p and k ≥ 1 -/
def IsPrimePower (q : ℕ) : Prop :=
  ∃ p k, Nat.Prime p ∧ k ≥ 1 ∧ q = p^k

/-- Check if n has the form q² + q + 1 for prime power q -/
def IsProjectivePlaneSize (n : ℕ) : Prop :=
  ∃ q, IsPrimePower q ∧ n = q^2 + q + 1

/-
## Part 2: The de Bruijn-Erdős Theorem

Fundamental lower bound: t ≥ n.
-/

/-- de Bruijn-Erdős (1948): Every block design on n points has at least n blocks -/
axiom de_bruijn_erdos (n : ℕ) (hn : n ≥ 2) (D : BlockDesign n) :
  D.numBlocks ≥ n

/-- When equality holds, blocks partition pairs like a near-pencil or projective plane -/
def IsMinimalDesign {n : ℕ} (D : BlockDesign n) : Prop :=
  D.numBlocks = n

/-- In minimal designs, every block has the same size -/
/-
## Part 3: Projective Plane Constructions

The classic construction achieving t = n.
-/

/-- A projective plane of order q has q² + q + 1 points and q² + q + 1 lines,
    with each line containing q + 1 points -/
structure ProjectivePlane (q : ℕ) where
  points : Finset ℕ
  lines : Finset (Finset ℕ)
  num_points : points.card = q^2 + q + 1
  num_lines : lines.card = q^2 + q + 1
  line_size : ∀ L ∈ lines, L.card = q + 1
  two_points_one_line : ∀ P Q : ℕ, P ∈ points → Q ∈ points → P ≠ Q →
    ∃! L, L ∈ lines ∧ P ∈ L ∧ Q ∈ L

/-- Projective planes exist for every prime power order -/
/-- A projective plane gives a block design achieving t = n = q² + q + 1 -/
axiom projective_plane_design (q : ℕ) (hq : IsPrimePower q) :
    ∃ D : BlockDesign (q^2 + q + 1), D.numBlocks = q^2 + q + 1

/-
## Part 4: The Erdős-Sós Conjecture (Now Theorem)

If t > n, then t ≥ n + p where p is the projective plane order.
-/

/-- Erdős-Fowler-Sós-Wilson (1985): If t > n then t ≥ n + p -/
axiom efsw_1985 (p : ℕ) (hp : IsPrimePower p)
    (D : BlockDesign (p^2 + p + 1)) (h : D.numBlocks > p^2 + p + 1) :
  D.numBlocks ≥ (p^2 + p + 1) + p

/-- Stronger result: unless design is from broken projective plane,
    t ≥ n + cp where c ≈ 1.148 -/
/-
## Part 5: The Gap Structure

What values of t are achievable?
-/

/-- The set of achievable values for t given n = p² + p + 1 -/
def achievableBlocks (p : ℕ) : Set ℕ :=
  { t | ∃ D : BlockDesign (p^2 + p + 1), D.numBlocks = t }

/-- t = n is always achievable (projective plane) -/
/-- Values in (n, n+p) are NOT achievable -/
axiom gap_theorem (p : ℕ) (hp : IsPrimePower p) :
  ∀ t, p^2 + p + 1 < t → t < p^2 + p + 1 + p →
    t ∉ achievableBlocks p

/-- The first value above n that might be achievable is n + p -/
theorem first_above_n (p : ℕ) (hp : IsPrimePower p) (t : ℕ)
    (ht : t ∈ achievableBlocks p) (hn : t > p^2 + p + 1) :
    t ≥ p^2 + p + 1 + p := by
  by_contra h
  push_neg at h
  exact gap_theorem p hp t hn h ht

/-
## Part 6: Examples
-/

/-- For p = 2: n = 7, gap is (7, 9), first achievable above 7 is ≥ 9 -/
example : 2^2 + 2 + 1 = 7 := by norm_num

/-- For p = 3: n = 13, gap is (13, 16), first achievable above 13 is ≥ 16 -/
example : 3^2 + 3 + 1 = 13 := by norm_num

/-- For p = 4: n = 21, gap is (21, 25), first achievable above 21 is ≥ 25 -/
example : 4^2 + 4 + 1 = 21 := by norm_num

/-- For p = 5: n = 31, gap is (31, 36), first achievable above 31 is ≥ 36 -/
example : 5^2 + 5 + 1 = 31 := by norm_num

/-
## Part 7: Connection to Combinatorial Designs
-/

/-- A 2-(v, k, 1) design is a block design where every pair appears in exactly
    one block of size k -/
def Is2Design {n : ℕ} (D : BlockDesign n) (k : ℕ) : Prop :=
  ∀ A ∈ D.blocks, A.card = k

/-- Fisher's inequality for 2-designs: b ≥ v -/
axiom fisher_inequality {n : ℕ} (D : BlockDesign n) (k : ℕ)
    (hk : k ≥ 2) (h : Is2Design D k) :
  D.numBlocks ≥ n

/-- This is equivalent to de Bruijn-Erdős for uniform designs -/
theorem de_bruijn_erdos_from_fisher {n : ℕ} (hn : n ≥ 2) (D : BlockDesign n)
    (k : ℕ) (hk : k ≥ 2) (h : Is2Design D k) :
    D.numBlocks ≥ n :=
  fisher_inequality D k hk h

/-
## Part 8: Summary

**Erdős Problem #903: SOLVED (YES)**

1. de Bruijn-Erdős (1948): t ≥ n for any block design on n points
2. Projective planes: t = n is achievable for n = p² + p + 1
3. Erdős-Fowler-Sós-Wilson (1985): if t > n then t ≥ n + p
4. Gap: values in (n, n+p) are unachievable
5. Stronger: t ≥ n + 1.148p unless design is from a broken projective plane
-/

/--
**Erdős Problem #903: Summary**

Combines de Bruijn-Erdős, projective plane existence, and the gap theorem.
-/
theorem erdos_903_summary (p : ℕ) (hp : IsPrimePower p) :
    -- de Bruijn-Erdős: t ≥ n
    (∀ D : BlockDesign (p^2 + p + 1), D.numBlocks ≥ p^2 + p + 1) ∧
    -- Projective plane achieves t = n
    (∃ D : BlockDesign (p^2 + p + 1), D.numBlocks = p^2 + p + 1) ∧
    -- Erdős-Sós: if t > n then t ≥ n + p
    (∀ D : BlockDesign (p^2 + p + 1),
      D.numBlocks > p^2 + p + 1 → D.numBlocks ≥ p^2 + p + 1 + p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro D
    have hn : p^2 + p + 1 ≥ 2 := by
      obtain ⟨q, k, hq, hk, heq⟩ := hp
      subst heq
      have : q ≥ 2 := Nat.Prime.two_le hq
      calc p^2 + p + 1 = (q^k)^2 + q^k + 1 := by ring_nf
        _ ≥ (q^1)^2 + q^1 + 1 := by
            have hpow : q^k ≥ q^1 := Nat.pow_le_pow_right (Nat.Prime.one_lt hq).le hk
            omega
        _ = q^2 + q + 1 := by ring
        _ ≥ 2^2 + 2 + 1 := by omega
        _ = 7 := by norm_num
        _ ≥ 2 := by norm_num
    exact de_bruijn_erdos _ hn D
  · exact projective_plane_design p hp
  · intro D hD
    exact efsw_1985 p hp D hD

end Erdos903
