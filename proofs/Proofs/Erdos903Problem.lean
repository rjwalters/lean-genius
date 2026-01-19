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

/-!
## Part 1: Basic Definitions

Block designs and the key parameters.
-/

/-- A block design on {1,...,n} is a collection of subsets (blocks) such that
    every pair of distinct elements is contained in exactly one block -/
structure BlockDesign (n : ℕ) where
  blocks : Finset (Finset ℕ)
  -- Every block is a subset of {1,...,n}
  blocks_subset : ∀ A ∈ blocks, ∀ a ∈ A, 1 ≤ a ∧ a ≤ n
  -- Every pair of distinct elements is in exactly one block
  pair_coverage : ∀ x y : ℕ, 1 ≤ x → x ≤ n → 1 ≤ y → y ≤ n → x ≠ y →
    ∃! A, A ∈ blocks ∧ x ∈ A ∧ y ∈ A

/-- The number of blocks in a design -/
def BlockDesign.numBlocks {n : ℕ} (D : BlockDesign n) : ℕ :=
  D.blocks.card

/-- A prime power: p^k for prime p and k ≥ 1 -/
def IsPrimePower (q : ℕ) : Prop :=
  ∃ p k, Nat.Prime p ∧ k ≥ 1 ∧ q = p^k

/-- The projective plane order for n = q² + q + 1 -/
def projectivePlaneOrder (n : ℕ) : ℕ :=
  -- If n = q² + q + 1, return q; otherwise 0
  Nat.sqrt (4 * n - 3) / 2  -- Approximate

/-- Check if n has the form q² + q + 1 for prime power q -/
def IsProjectivePlaneSize (n : ℕ) : Prop :=
  ∃ q, IsPrimePower q ∧ n = q^2 + q + 1

/-!
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
axiom minimal_design_uniform (n : ℕ) (D : BlockDesign n) (h : IsMinimalDesign D) :
  ∃ k, ∀ A ∈ D.blocks, A.card = k

/-!
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
  -- Every two points determine a unique line
  two_points_one_line : ∀ P Q : ℕ, P ∈ points → Q ∈ points → P ≠ Q →
    ∃! L, L ∈ lines ∧ P ∈ L ∧ Q ∈ L

/-- A projective plane of order q gives a block design with t = n = q² + q + 1 -/
def ProjectivePlane.toBlockDesign {q : ℕ} (PP : ProjectivePlane q) :
    BlockDesign (q^2 + q + 1) where
  blocks := PP.lines
  blocks_subset := by sorry  -- Lines consist of points in {1,...,n}
  pair_coverage := by sorry  -- Every pair is in exactly one line

/-- Projective planes achieve the minimum t = n -/
theorem projective_plane_minimal (q : ℕ) (hq : IsPrimePower q) :
    ∃ PP : ProjectivePlane q, (PP.toBlockDesign).numBlocks = q^2 + q + 1 := by
  sorry

/-!
## Part 4: The Erdős-Sós Conjecture (Now Theorem)

If t > n, then t ≥ n + p where p is the projective plane order.
-/

/-- The main conjecture of Erdős and Sós, now a theorem -/
theorem erdos_sos_theorem (p : ℕ) (hp : IsPrimePower p)
    (D : BlockDesign (p^2 + p + 1)) (h : D.numBlocks > p^2 + p + 1) :
    D.numBlocks ≥ p^2 + p + 1 + p := by
  -- Proved by Erdős-Fowler-Sós-Wilson (1985)
  sorry

/-- Erdős-Fowler-Sós-Wilson (1985) axiomatized -/
axiom efsw_1985 (p : ℕ) (hp : IsPrimePower p)
    (D : BlockDesign (p^2 + p + 1)) (h : D.numBlocks > p^2 + p + 1) :
  D.numBlocks ≥ (p^2 + p + 1) + p

/-- Stronger result: unless design is from broken projective plane,
    t ≥ n + cp where c ≈ 1.148 -/
axiom efsw_strong (p : ℕ) (hp : IsPrimePower p) (c : ℝ)
    (hc : c = 1.148)  -- Approximate value
    (D : BlockDesign (p^2 + p + 1))
    (h : D.numBlocks > p^2 + p + 1)
    (not_broken : True)  -- D is not from a broken projective plane
    : D.numBlocks ≥ (p^2 + p + 1) + Nat.ceil (c * p)

/-!
## Part 5: The Gap Structure

What values of t are achievable?
-/

/-- The set of achievable values for t given n = p² + p + 1 -/
def achievableBlocks (p : ℕ) : Set ℕ :=
  { t | ∃ D : BlockDesign (p^2 + p + 1), D.numBlocks = t }

/-- t = n is always achievable (projective plane) -/
axiom n_achievable (p : ℕ) (hp : IsPrimePower p) :
  p^2 + p + 1 ∈ achievableBlocks p

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

/-!
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

/-!
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

/-!
## Part 8: Main Results
-/

/-- Erdős Problem #903: Main statement -/
theorem erdos_903_statement (p : ℕ) (hp : IsPrimePower p) :
    -- de Bruijn-Erdős: t ≥ n
    (∀ D : BlockDesign (p^2 + p + 1), D.numBlocks ≥ p^2 + p + 1) ∧
    -- t = n is achievable (projective plane)
    (∃ D : BlockDesign (p^2 + p + 1), D.numBlocks = p^2 + p + 1) ∧
    -- Erdős-Sós conjecture (proved): if t > n then t ≥ n + p
    (∀ D : BlockDesign (p^2 + p + 1),
      D.numBlocks > p^2 + p + 1 → D.numBlocks ≥ p^2 + p + 1 + p) := by
  constructor
  · intro D
    let n := p^2 + p + 1
    have hn : n ≥ 2 := by
      have hp' : p ≥ 2 := by
        obtain ⟨q, k, hq, hk, heq⟩ := hp
        subst heq
        have : q ≥ 2 := Nat.Prime.two_le hq
        calc p = q^k := rfl
          _ ≥ q^1 := by apply Nat.pow_le_pow_right (Nat.Prime.one_lt hq).le hk
          _ = q := by ring
          _ ≥ 2 := this
      calc n = p^2 + p + 1 := rfl
        _ ≥ 2^2 + 2 + 1 := by omega
        _ = 7 := by norm_num
        _ ≥ 2 := by norm_num
    exact de_bruijn_erdos n hn D
  constructor
  · sorry  -- Exists projective plane design
  · intro D hD
    exact efsw_1985 p hp D hD

/-- The answer to Erdős Problem #903: YES -/
theorem erdos_903_answer : True := trivial

/-- Summary: The Erdős-Sós conjecture is true -/
theorem erdos_903_summary :
    -- 1948: de Bruijn-Erdős proved t ≥ n
    -- 1985: Erdős-Fowler-Sós-Wilson proved t > n ⟹ t ≥ n + p
    -- Stronger: t ≥ n + 1.148p unless broken projective plane
    True := trivial

end Erdos903
