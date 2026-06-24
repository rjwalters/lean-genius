import Mathlib

/-
# Erdős 606 — OQ-03 / WIP-01: The de Bruijn–Erdős Lower Bound, Rigorously

## Research Problem: erdos-606-oq-03-wip-01

The parent entry `erdos-606-oq-03` (Hyperplane Determination in Higher Dimensions)
records, in prose comments only, the central lower bound for Erdős's line-counting
problem:

> "Minimum lines (non-collinear): at least n"

This work-in-progress turns that prose into a machine-checked theorem. The correct
attribution for the bound "n points, not all collinear, determine at least n lines"
is the **de Bruijn–Erdős theorem** (1948) — *not* Sylvester–Gallai, which instead
asserts the existence of an *ordinary* line. Mathlib already proves the de Bruijn–Erdős
bound in the abstract incidence-geometry setting as
`Configuration.HasLines.card_le : Fintype.card P ≤ Fintype.card L`.

We use that to establish the full **sandwich** for the number of lines determined by a
finite point configuration in which any two distinct points lie on a unique common
line and every line passes through at least two of the points:

  `n ≤ (number of lines) ≤ C(n, 2)`,  where `n` is the number of points.

* lower bound `n ≤ #L` — de Bruijn–Erdős (`HasLines.card_le`);
* upper bound `#L ≤ C(n,2)` — a counting injection: a line determined by the points
  carries a distinct unordered pair of points (uniqueness of the line through two
  points makes the assignment injective).

## Honest Scope
This is the *combinatorial* incidence content of Erdős 606. The deeper open questions of
the parent entry — Sylvester–Gallai (existence of an ordinary line), Green–Tao
(`≥ n/2` ordinary lines), and the exact set of achievable line counts — require
projective-geometry / polynomial-method machinery and remain open here. The abstract
`Configuration.HasLines` hypothesis is exactly the "any two points determine a unique
line" axiom satisfied by genuine planar point sets in general position; we do not build
a concrete geometric instance in this file.

Tags: combinatorial-geometry, de-bruijn-erdos, incidence-geometry, sylvester-gallai
-/

namespace Erdos606OQ03WIP01

open Configuration Finset

variable {P L : Type*} [Membership P L]

/-- **The de Bruijn–Erdős theorem (abstract form).**

In any nondegenerate configuration where every two distinct points lie on a (unique)
common line, the number of points is at most the number of lines. Specialised to a
finite set of points in the plane, not all collinear: `n` points determine at least
`n` distinct lines. This is the rigorous version of the parent entry's prose lower
bound, here delegated to Mathlib's `Configuration.HasLines.card_le`. -/
theorem deBruijn_erdos [HasLines P L] [Fintype P] [Fintype L] :
    Fintype.card P ≤ Fintype.card L :=
  HasLines.card_le P L

/-- **Upper bound on the number of determined lines.**

If every line is determined by the points — i.e. passes through at least two of them —
then distinct lines carry distinct unordered pairs of points (uniqueness of the line
through two points), so the number of lines is at most `C(n, 2)`. -/
theorem card_le_choose_two [HasLines P L] [Fintype P] [Fintype L]
    (htwo : ∀ l : L, ∃ p q : P, p ≠ q ∧ p ∈ l ∧ q ∈ l) :
    Fintype.card L ≤ (Fintype.card P).choose 2 := by
  classical
  choose p q hpq hp hq using htwo
  -- assign to each line the unordered pair of its two chosen points
  set f : L → Finset P := fun l => {p l, q l} with hf
  -- every member of `f l` is a point of `l`
  have hsub : ∀ l, ∀ r ∈ f l, r ∈ l := by
    intro l r hr
    simp only [hf, Finset.mem_insert, Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact hp l
    · exact hq l
  -- the assignment is injective: a shared pair forces equal lines
  have hinj : Function.Injective f := by
    intro l₁ l₂ h
    have h1 : p l₂ ∈ l₁ := hsub l₁ (p l₂) (by rw [h]; simp [hf])
    have h2 : q l₂ ∈ l₁ := hsub l₁ (q l₂) (by rw [h]; simp [hf])
    rcases Nondegenerate.eq_or_eq h1 h2 (hp l₂) (hq l₂) with hpq2 | hl
    · exact absurd hpq2 (hpq l₂)
    · exact hl
  -- each `f l` is a 2-element subset of the points
  have hcard : ∀ l, (f l).card = 2 := fun l => Finset.card_pair (hpq l)
  calc
    Fintype.card L = (Finset.univ : Finset L).card := (Finset.card_univ).symm
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ ((Finset.univ : Finset P).powersetCard 2).card := by
        refine Finset.card_le_card ?_
        intro s hs
        obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hs
        rw [Finset.mem_powersetCard]
        exact ⟨Finset.subset_univ _, hcard l⟩
    _ = (Fintype.card P).choose 2 := by
        rw [Finset.card_powersetCard, Finset.card_univ]

/-- **The Erdős 606 line-count sandwich.**

For a finite point configuration in which any two distinct points determine a unique
line and every line passes through at least two points, the number of determined lines
`m` satisfies `n ≤ m ≤ C(n, 2)`, where `n` is the number of points. The lower bound is
de Bruijn–Erdős; the upper bound is the pair-counting injection. -/
theorem line_count_sandwich [HasLines P L] [Fintype P] [Fintype L]
    (htwo : ∀ l : L, ∃ p q : P, p ≠ q ∧ p ∈ l ∧ q ∈ l) :
    Fintype.card P ≤ Fintype.card L ∧
      Fintype.card L ≤ (Fintype.card P).choose 2 :=
  ⟨HasLines.card_le P L, card_le_choose_two htwo⟩

end Erdos606OQ03WIP01

#print axioms Erdos606OQ03WIP01.line_count_sandwich
#print axioms Erdos606OQ03WIP01.card_le_choose_two
