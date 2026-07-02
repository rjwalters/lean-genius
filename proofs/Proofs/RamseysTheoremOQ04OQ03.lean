/-
Ramsey Theory — OQ-04-OQ-03: The exact 1-uniform (pigeonhole) hypergraph Ramsey number

Source: open question of the ramseys-theorem gallery (hypergraph Ramsey, OQ-04)
Parent: Proofs/RamseysTheoremOQ04.lean  (k-uniform hypergraph Ramsey)

## Context

The parent entry formalizes the k-uniform hypergraph Ramsey theorem. The base case
k = 1 is the pigeonhole principle: a 1-uniform coloring is just an r-coloring of the
vertices, and a "monochromatic set of size n" is a color class with at least n
elements. The parent's `pigeonhole_ramsey` proves only that *some* N works. Its own
open question 2 asks for the *best known bounds* on hypergraph Ramsey numbers for
small k. This file settles the k = 1 case **exactly**:

  R₁(r, n) = r·(n-1) + 1,

with both halves proved:

  * SUFFICIENCY — if `r·(n-1) < |V|` then every r-coloring of `V` has a color class of
    size ≥ n (there is a monochromatic n-set);
  * SHARPNESS — on a set of exactly `r·(n-1)` vertices there is an r-coloring in which
    every color class has size ≤ n-1 (no monochromatic n-set), so the threshold cannot
    be lowered.

Everything is stated for an arbitrary finite vertex type `V` via `Fintype.card V`, so
the two directions compose into the exact number. Self-contained (imports only
Mathlib), axiom-free.

## Results

* `exists_large_color_class`   — sufficiency (generalized pigeonhole).
* `ramsey1_of_card_lt`         — sufficiency phrased at the threshold `r·(n-1)+1`.
* `sharp_coloring_card`        — the extremal coloring `Prod.fst` on `Fin r × Fin (n-1)`
                                 has every color class of size exactly `n-1`.
* `ramsey1_sharp`              — sharpness: `r·(n-1)` vertices are not enough.
* `ramsey1_exact` bundles the two directions at the exact threshold.
* `ramsey1_number` / `ramsey1_number_spec` — the exact Ramsey number and its
  characterization.
* `pigeonhole_two` — the classical "r+1 pigeons in r holes" as the `n = 2` case.

References:
- F. P. Ramsey, "On a problem of formal logic" (1930)
- Parent entry `ramseys-theorem-oq-04` (hypergraph Ramsey theorem)
-/

import Mathlib

open Finset

namespace HypergraphRamseyOQ04OQ03

variable {V : Type*} [Fintype V]

/-- The color class of `color` under an r-coloring `c` of the vertices `V`: the set of
vertices assigned that color. -/
def colorClass {r : ℕ} (c : V → Fin r) (color : Fin r) : Finset V :=
  Finset.univ.filter (fun v => c v = color)

-- ============================================================================
-- Sufficiency: a large vertex set forces a large color class
-- ============================================================================

/-- **Generalized pigeonhole / sufficiency.** If the number of vertices exceeds
`r·(n-1)`, then any r-coloring has a color class of size at least `n`: a monochromatic
set of size `n` exists. -/
theorem exists_large_color_class {r n : ℕ} (hn : 1 ≤ n) (c : V → Fin r)
    (h : r * (n - 1) < Fintype.card V) :
    ∃ color : Fin r, n ≤ (colorClass c color).card := by
  have hmaps : ∀ v ∈ (univ : Finset V), c v ∈ (univ : Finset (Fin r)) :=
    fun v _ => mem_univ _
  have hcard : (univ : Finset (Fin r)).card * (n - 1) < (univ : Finset V).card := by
    simpa [Finset.card_univ, Fintype.card_fin] using h
  obtain ⟨color, _, hcolor⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hcard
  exact ⟨color, by simp only [colorClass]; omega⟩

/-- **Sufficiency at the threshold.** If `V` has at least `r·(n-1)+1` vertices then every
r-coloring admits a monochromatic set of size `n`. This is the "≥ R₁" half. -/
theorem ramsey1_of_card_lt {r n : ℕ} (hn : 1 ≤ n) (c : V → Fin r)
    (h : r * (n - 1) + 1 ≤ Fintype.card V) :
    ∃ color : Fin r, n ≤ (colorClass c color).card :=
  exists_large_color_class hn c (by omega)

-- ============================================================================
-- Sharpness: r·(n-1) vertices are not enough
-- ============================================================================

/-- On the extremal vertex set `Fin r × Fin (n-1)`, the projection coloring
`Prod.fst` gives every color class size exactly `n-1`. -/
theorem sharp_coloring_card (r n : ℕ) (color : Fin r) :
    (colorClass (V := Fin r × Fin (n - 1)) Prod.fst color).card = n - 1 := by
  have hset : colorClass (V := Fin r × Fin (n - 1)) Prod.fst color
      = ({color} : Finset (Fin r)) ×ˢ (univ : Finset (Fin (n - 1))) := by
    ext p
    simp only [colorClass, Finset.mem_filter, Finset.mem_univ, true_and, and_true,
      Finset.mem_product, Finset.mem_singleton]
  rw [hset, Finset.card_product, Finset.card_singleton, one_mul, Finset.card_univ,
    Fintype.card_fin]

/-- **Sharpness.** There is a set of exactly `r·(n-1)` vertices with an r-coloring in
which every color class has size ≤ `n-1`; hence it has no monochromatic set of size `n`.
The threshold `r·(n-1)+1` therefore cannot be lowered. -/
theorem ramsey1_sharp (r n : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (c : V → Fin r),
      Fintype.card V = r * (n - 1) ∧
      ∀ color : Fin r, (colorClass c color).card ≤ n - 1 := by
  refine ⟨Fin r × Fin (n - 1), inferInstance, inferInstance, Prod.fst, ?_, ?_⟩
  · rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · intro color
    rw [sharp_coloring_card]

-- ============================================================================
-- The exact Ramsey number
-- ============================================================================

/-- The exact 1-uniform (pigeonhole) Ramsey number: the least number of vertices that
forces, under every r-coloring, a monochromatic set of size `n`. -/
def ramsey1_number (r n : ℕ) : ℕ := r * (n - 1) + 1

/-- **The two directions meet at the exact number.** With `N = ramsey1_number r n`
vertices, sufficiency holds; and there is a coloring on `N - 1 = r·(n-1)` vertices with
no monochromatic `n`-set. -/
theorem ramsey1_exact {r n : ℕ} (hn : 1 ≤ n) :
    (∀ (V : Type) [Fintype V] (c : V → Fin r),
        r * (n - 1) + 1 ≤ Fintype.card V →
        ∃ color : Fin r, n ≤ (colorClass c color).card)
    ∧ (∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (c : V → Fin r),
        Fintype.card V = r * (n - 1) ∧
        ∀ color : Fin r, (colorClass c color).card ≤ n - 1) := by
  refine ⟨?_, ramsey1_sharp r n⟩
  intro V _ c h
  exact ramsey1_of_card_lt hn c h

/-- Characterization of the Ramsey number: `ramsey1_number r n` vertices suffice to force
a monochromatic `n`-set. -/
theorem ramsey1_number_spec {r n : ℕ} (hn : 1 ≤ n) (c : V → Fin r)
    (h : ramsey1_number r n ≤ Fintype.card V) :
    ∃ color : Fin r, n ≤ (colorClass c color).card :=
  ramsey1_of_card_lt hn c h

-- ============================================================================
-- Classical corollary
-- ============================================================================

/-- **Classical pigeonhole** as the `n = 2`, `R₁(r,2) = r+1` case: any `r`-coloring of a
set with more than `r` elements has two vertices of the same color. -/
theorem pigeonhole_two {r : ℕ} (c : V → Fin r) (h : r < Fintype.card V) :
    ∃ color : Fin r, 2 ≤ (colorClass c color).card := by
  have := exists_large_color_class (V := V) (r := r) (n := 2) (by norm_num) c (by simpa using h)
  simpa using this

end HypergraphRamseyOQ04OQ03
