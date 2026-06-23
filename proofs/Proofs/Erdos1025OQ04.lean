/-
Erdős Problem #1025, Open Question 4 — relaxing the validity constraint.

Parent #1025 (Independent Sets in Pair Functions):
A *valid* pair function `f` sends each pair `{x,y} ⊆ {1,…,n}` to an element with
`f x y ≠ x` and `f x y ≠ y`.  A set `X` is *independent* if `f x y ∉ X` for all
`x, y ∈ X`.  Erdős–Hajnal (1958), Spencer (1972) and Conlon–Fox–Sudakov (2016)
showed the minimum guaranteed independent set size is `g(n) = Θ(√n)`.

OQ-4 asks: *what happens if we allow the degenerate values `f x y = x` or
`f x y = y`, with bounded frequency?*

This file gives two sharp, elementary answers (fully verified, 0 axioms / 0
sorries):

1. **Collapse (unbounded degeneracy).**  Drop the validity constraint entirely
   and the guarantee collapses: the function `fbad x y = x` admits no independent
   set of size `≥ 2`, while a singleton is always independent.  Hence the relaxed
   guarantee is exactly `1` for `n ≥ 2`, versus `Θ(√n)` in the valid case — the
   validity hypothesis is essential.

2. **Recovery (bounded degeneracy).**  Measure degeneracy by the number `k` of
   ordered pairs `(x,y)` with `f x y ∈ {x,y}`.  Deleting the (at most `2k`)
   endpoints of those pairs leaves a set `W` with `|W| ≥ n − 2k` on which `f` is
   genuinely valid.  So a bounded number of violations only shrinks the effective
   ground set by a bounded amount, and an independent set of size `2` survives
   whenever `n − 2k ≥ 2`.

Reference: https://erdosproblems.com/1025
-/

import Mathlib

open Finset

namespace Erdos1025OQ04

variable {n : ℕ}

/-- A (possibly degenerate) pair function on `Fin n`, given in explicit two-argument
form.  No validity constraint is imposed. -/
abbrev RelaxedPairFunction (n : ℕ) := Fin n → Fin n → Fin n

/-- The validity constraint of the original problem: `f x y` avoids both endpoints. -/
def Valid (f : RelaxedPairFunction n) : Prop :=
  ∀ x y : Fin n, x ≠ y → f x y ≠ x ∧ f x y ≠ y

/-- A set `X` is independent under `f` if the image of any pair from `X` lies
outside `X`. -/
def Independent (f : RelaxedPairFunction n) (X : Finset (Fin n)) : Prop :=
  ∀ x ∈ X, ∀ y ∈ X, x ≠ y → f x y ∉ X

/-- Validity of `f` restricted to pairs lying inside a subset `W`. -/
def ValidOn (f : RelaxedPairFunction n) (W : Finset (Fin n)) : Prop :=
  ∀ x ∈ W, ∀ y ∈ W, x ≠ y → f x y ≠ x ∧ f x y ≠ y

/-! ## Basic independence facts -/

/-- The empty set is independent under any pair function. -/
theorem empty_independent (f : RelaxedPairFunction n) : Independent f ∅ := by
  intro x hx; simp at hx

/-- A singleton is independent under any pair function. -/
theorem singleton_independent (f : RelaxedPairFunction n) (a : Fin n) :
    Independent f {a} := by
  intro x hx y hy hxy
  rw [Finset.mem_singleton] at hx hy
  exact absurd (hx.trans hy.symm) hxy

/-- For a *valid* pair function, every two-element set is independent: the
defining constraint is exactly the statement that pairs are independent. Hence the
valid guarantee is `≥ 2`. -/
theorem valid_pair_independent (f : RelaxedPairFunction n) (hf : Valid f)
    {a b : Fin n} (hab : a ≠ b) : Independent f ({a, b} : Finset (Fin n)) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hf x y hxy
  · rcases hy with rfl | rfl
    · exact ⟨(hf x y hxy).2, (hf x y hxy).1⟩
    · exact absurd rfl hxy

/-! ## Part 1 — Collapse under unbounded degeneracy -/

/-- The maximally degenerate pair function: it always returns its first argument
(`f x y = x ∈ {x,y}` for every pair). -/
def fbad (n : ℕ) : RelaxedPairFunction n := fun x _ => x

/-- `fbad` is *not* valid for `n ≥ 2`: every pair is degenerate. -/
theorem fbad_not_valid (hn : 2 ≤ n) : ¬ Valid (fbad n) := by
  intro hf
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    simp [Fin.ext_iff]
  exact (hf _ _ h01).1 rfl

/-- **Collapse.** No set of size `≥ 2` is independent under `fbad`: any two
distinct elements `a, b ∈ X` give `fbad a b = a ∈ X`, violating independence. -/
theorem relaxed_collapse (X : Finset (Fin n)) (h : Independent (fbad n) X) :
    X.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha b hb
  by_contra hab
  have hh := h a ha b hb hab
  simp only [fbad] at hh
  exact hh ha

/-- **The relaxed guarantee is exactly `1`** for `n ≥ 2`: every independent set
under `fbad` has size `≤ 1`, and some independent set has size `1`.  Contrast with
`g(n) = Θ(√n)` for valid functions. -/
theorem relaxed_g_eq_one (hn : 2 ≤ n) :
    (∀ X : Finset (Fin n), Independent (fbad n) X → X.card ≤ 1) ∧
      (∃ X : Finset (Fin n), Independent (fbad n) X ∧ X.card = 1) := by
  refine ⟨fun X hX => relaxed_collapse X hX, ?_⟩
  refine ⟨{(⟨0, by omega⟩ : Fin n)}, singleton_independent _ _, Finset.card_singleton _⟩

/-! ## Part 2 — Recovery under bounded degeneracy -/

/-- The set of *degenerate ordered pairs*: distinct `(x,y)` with `f x y ∈ {x,y}`.
Its cardinality measures the frequency of degeneracy. -/
def degenerateSet (f : RelaxedPairFunction n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ f p.1 p.2 ∈ ({p.1, p.2} : Finset (Fin n)))

/-- **Recovery.**  If at most `k` ordered pairs are degenerate, then deleting the
endpoints of degenerate pairs leaves a set `W` with `|W| ≥ n − 2k` on which `f` is
genuinely valid.  Bounded degeneracy costs only a bounded shrink of the ground
set. -/
theorem recovery (f : RelaxedPairFunction n) (k : ℕ)
    (hk : (degenerateSet f).card ≤ k) :
    ∃ W : Finset (Fin n), n - 2 * k ≤ W.card ∧ ValidOn f W := by
  set D := degenerateSet f with hD
  set T := D.image Prod.fst ∪ D.image Prod.snd with hT
  have hTle : T.card ≤ 2 * k := by
    calc T.card ≤ (D.image Prod.fst).card + (D.image Prod.snd).card :=
          Finset.card_union_le _ _
      _ ≤ D.card + D.card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
      _ = 2 * D.card := by ring
      _ ≤ 2 * k := by omega
  refine ⟨Finset.univ \ T, ?_, ?_⟩
  · have hcard : (Finset.univ \ T).card = n - T.card := by
      rw [Finset.card_univ_diff, Fintype.card_fin]
    rw [hcard]
    omega
  · intro x hx y hy hxy
    rw [Finset.mem_sdiff] at hx hy
    constructor
    · intro hcontra
      have hmem : f x y ∈ ({x, y} : Finset (Fin n)) := by simp [hcontra]
      have hxyD : (x, y) ∈ D := by
        rw [hD, degenerateSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hxy, hmem⟩
      exact hx.2 (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(x, y), hxyD, rfl⟩))
    · intro hcontra
      have hmem : f x y ∈ ({x, y} : Finset (Fin n)) := by simp [hcontra]
      have hxyD : (x, y) ∈ D := by
        rw [hD, degenerateSet, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hxy, hmem⟩
      exact hy.2 (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(x, y), hxyD, rfl⟩))

/-- Independence of a pair `{a,b}` follows from validity *on* a set `W` containing
both endpoints. -/
theorem validOn_pair_independent (f : RelaxedPairFunction n) {W : Finset (Fin n)}
    (hf : ValidOn f W) {a b : Fin n} (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b) :
    Independent f ({a, b} : Finset (Fin n)) := by
  intro x hx y hy hxy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  rcases hx with rfl | rfl
  · rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hf x ha y hb hxy
  · rcases hy with rfl | rfl
    · exact ⟨(hf x hb y ha hxy).2, (hf x hb y ha hxy).1⟩
    · exact absurd rfl hxy

/-- **Bounded degeneracy still guarantees an independent pair.**  If at most `k`
ordered pairs are degenerate and `n − 2k ≥ 2`, then `f` admits an independent set
of size `2`. -/
theorem recovery_independent_pair (f : RelaxedPairFunction n) (k : ℕ)
    (hk : (degenerateSet f).card ≤ k) (hn : 2 ≤ n - 2 * k) :
    ∃ X : Finset (Fin n), Independent f X ∧ X.card = 2 := by
  obtain ⟨W, hWcard, hWvalid⟩ := recovery f k hk
  have h2 : 1 < W.card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2
  exact ⟨{a, b}, validOn_pair_independent f hWvalid ha hb hab, Finset.card_pair hab⟩

end Erdos1025OQ04
