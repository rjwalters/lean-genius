/-
# The Cantor Intersection Theorem for Complete Metric Spaces

A nested sequence of nonempty, closed, bounded sets

  s₀ ⊇ s₁ ⊇ s₂ ⊇ ⋯

in a **complete** metric space whose diameters shrink to `0` has an intersection
that is **exactly one point**:

  ⋂ₙ sₙ = {x}.

This is the metric-space form of the Cantor intersection theorem. The parent entry
(`compactness-finite-subcover-oq-01-oq-02-oq-01`) handles the special case of nested
closed *intervals* in `ℝ` shrinking to a point. Here we generalize to an arbitrary
complete metric space and, crucially, prove the **singleton characterization**:
existence *and* uniqueness of the limit point.

## What is new relative to Mathlib

Mathlib's `Metric.nonempty_iInter_of_nonempty_biInter` gives only that the
intersection is **nonempty** (and from *finite-intersection* hypotheses, not from a
nested family). It says nothing about uniqueness. This file:

1. derives the finite-intersection hypothesis from the natural *nested + nonempty*
   hypotheses (so the existence half applies), and
2. adds the **uniqueness** half — any two points of the intersection are within
   `diam (sₙ)` of each other for every `n`, and `diam (sₙ) → 0`, forcing them to
   coincide — packaging the result as `⋂ₙ sₙ = {x}` and `∃! x, x ∈ ⋂ₙ sₙ`.

The completeness hypothesis is essential: in an incomplete space (e.g. `ℚ`) such an
intersection can be empty.

This file contains no `axiom`s and no `sorry`s.

## References
- Cantor, G. (1879–1884). Über unendliche, lineare Punktmannigfaltigkeiten.
- Mathlib: `Mathlib.Topology.MetricSpace.Bounded`
  (`Metric.nonempty_iInter_of_nonempty_biInter`).
-/
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Tactic

set_option linter.unusedSectionVars false

open Metric Filter Topology Set

namespace CantorIntersection

variable {α : Type*} [MetricSpace α] [CompleteSpace α] {s : ℕ → Set α}

/-- For a **nested decreasing** family, every finite "prefix" intersection
`⋂ n ≤ N, s n` equals the last (smallest) set `s N`, hence is nonempty whenever
each `s n` is. This converts the natural nested hypothesis into the
finite-intersection hypothesis required by `nonempty_iInter_of_nonempty_biInter`. -/
theorem biInter_nonempty_of_antitone
    (hne : ∀ n, (s n).Nonempty) (hnest : ∀ n, s (n + 1) ⊆ s n) (N : ℕ) :
    (⋂ n ≤ N, s n).Nonempty := by
  have hanti : Antitone s := antitone_nat_of_succ_le hnest
  obtain ⟨x, hx⟩ := hne N
  refine ⟨x, ?_⟩
  simp only [mem_iInter]
  intro n hn
  exact hanti hn hx

/-- **Existence (Cantor intersection, complete metric space).** A nested sequence of
nonempty closed bounded sets with diameters tending to `0` has nonempty
intersection. -/
theorem nonempty_iInter
    (hne : ∀ n, (s n).Nonempty) (hclosed : ∀ n, IsClosed (s n))
    (hbdd : ∀ n, Bornology.IsBounded (s n)) (hnest : ∀ n, s (n + 1) ⊆ s n)
    (hdiam : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) :
    (⋂ n, s n).Nonempty :=
  nonempty_iInter_of_nonempty_biInter hclosed hbdd
    (biInter_nonempty_of_antitone hne hnest) hdiam

/-- **Uniqueness.** If the diameters tend to `0`, the intersection contains at most
one point: any two of its points are within `diam (s n)` for every `n`, and that
bound goes to `0`. -/
theorem subsingleton_iInter
    (hbdd : ∀ n, Bornology.IsBounded (s n))
    (hdiam : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) :
    (⋂ n, s n).Subsingleton := by
  intro x hx y hy
  simp only [mem_iInter] at hx hy
  -- `dist x y ≤ diam (s n)` for every `n`.
  have hbound : ∀ n, dist x y ≤ diam (s n) := fun n =>
    dist_le_diam_of_mem (hbdd n) (hx n) (hy n)
  -- Passing to the limit, `dist x y ≤ 0`, hence `x = y`.
  have hle : dist x y ≤ 0 := ge_of_tendsto hdiam (Eventually.of_forall hbound)
  exact dist_le_zero.mp hle

/-- **Cantor Intersection Theorem (singleton form).** A nested sequence of nonempty
closed bounded sets with diameters tending to `0` in a complete metric space
intersects in exactly one point. -/
theorem iInter_eq_singleton
    (hne : ∀ n, (s n).Nonempty) (hclosed : ∀ n, IsClosed (s n))
    (hbdd : ∀ n, Bornology.IsBounded (s n)) (hnest : ∀ n, s (n + 1) ⊆ s n)
    (hdiam : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) :
    ∃ x, (⋂ n, s n) = {x} := by
  obtain ⟨x, hx⟩ := nonempty_iInter hne hclosed hbdd hnest hdiam
  exact ⟨x, (subsingleton_iInter hbdd hdiam).eq_singleton_of_mem hx⟩

/-- **Cantor Intersection Theorem (`∃!` form).** There is a unique point common to
all the sets. -/
theorem existsUnique_mem_iInter
    (hne : ∀ n, (s n).Nonempty) (hclosed : ∀ n, IsClosed (s n))
    (hbdd : ∀ n, Bornology.IsBounded (s n)) (hnest : ∀ n, s (n + 1) ⊆ s n)
    (hdiam : Tendsto (fun n => diam (s n)) atTop (𝓝 0)) :
    ∃! x, x ∈ ⋂ n, s n := by
  obtain ⟨x, hx⟩ := iInter_eq_singleton hne hclosed hbdd hnest hdiam
  refine ⟨x, ?_, ?_⟩
  · rw [hx]; exact rfl
  · intro y hy; rw [hx] at hy; exact hy

end CantorIntersection
