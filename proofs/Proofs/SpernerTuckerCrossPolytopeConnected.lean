/-
# Connectivity of the cross-polytope facet-adjacency graph `∂◊^{n+1}`, in every dimension

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits

`SpernerTuckerCrossPolytopeBoundary` supplies the general-`n` antipodally-symmetric
substrate every prior session named: the boundary of the cross-polytope `◊^{n+1}`, whose
facet-adjacency graph `crossGraph n` is the `(n+1)`-cube `Q_{n+1}`.  That file establishes
its *local* structure (`(n+1)`-regular, free antipodal automorphism, even facet count).

The path-following / door-counting program implicitly relies on the ambient
triangulated sphere being **connected** — this is the *global* pseudomanifold-connectivity
property that lets a path from a boundary door reach an interior complementary simplex.
For the concrete models it was only ever available at fixed dimension:

* the `n = 2` hexagon (`SpernerTuckerHexagonPseudomanifold`), and
* the boundary of the simplex (`SpernerTuckerSimplexBoundaryPseudomanifold`).

This file supplies the missing **dimension-free** statement on the canonical octahedral
model: `crossGraph n` is connected, in every dimension.

## What this file proves (all `0` axioms — `propext` / `Classical.choice` / `Quot.sound`
only; **no** `decide` / `native_decide` / `ofReduceBool`, and **no** per-dimension case
split)

* `reachable_aux` — the constructive core: any two facets differing in `k` coordinates are
  joined by a walk, by induction on `k` (flip one differing coordinate at a time — the
  cube's Gray-walk).  Each flip is a `crossGraph` edge; the differing set shrinks by one.
* `crossGraph_preconnected` — every pair of facets is reachable.
* `crossGraph_connected` — `crossGraph n` is a connected graph (the octahedral sphere is
  connected), in every dimension.

This is infrastructure, not new Tucker geometry: it does not construct the labelling-broken
almost-complementary door graph (the open `bridge`).  It records the dimension-free
connectivity of the ambient antipodal substrate — the global counterpart to
`SpernerTuckerCrossPolytopeBoundary`'s local regularity.
-/
import Mathlib
import Proofs.SpernerTuckerCrossPolytopeBoundary

namespace SpernerTuckerCrossPolytopeConnected

open Finset SimpleGraph SpernerTuckerCrossPolytopeBoundary

/-- **The constructive core.**  Any two facets whose sign vectors differ in exactly `k`
coordinates are joined by a walk in the cube `crossGraph n`.  Induction on `k`: at each step
pick a differing coordinate `i`, flip it (an edge of the cube), and recurse — the differing
set loses `i` and shrinks to `k`. -/
theorem reachable_aux (n : ℕ) :
    ∀ (k : ℕ) (s t : Facet n),
      (univ.filter fun j => s j ≠ t j).card = k → (crossGraph n).Reachable s t
  | 0, s, t, h => by
      have hempty : (univ.filter fun j => s j ≠ t j) = ∅ := Finset.card_eq_zero.mp h
      have hst : s = t := by
        funext i
        by_contra hi
        have hmemi : i ∈ (univ.filter fun j => s j ≠ t j) := by
          simp only [mem_filter, mem_univ, true_and]; exact hi
        rw [hempty] at hmemi
        exact absurd hmemi (Finset.notMem_empty i)
      rw [hst]
  | k + 1, s, t, h => by
      -- there is at least one differing coordinate
      have hne : (univ.filter fun j => s j ≠ t j).Nonempty := by
        rw [← Finset.card_pos, h]; omega
      obtain ⟨i, hi⟩ := hne
      rw [mem_filter] at hi
      have hsi : s i ≠ t i := hi.2
      -- flipping coordinate `i` is a cube edge
      have hadj : (crossGraph n).Adj s (flipAt n s i) := by
        rw [← SimpleGraph.mem_neighborFinset]
        exact (mem_neighbor_iff n s (flipAt n s i)).mpr ⟨i, rfl⟩
      -- after the flip, coordinate `i` agrees with `t`
      have hti : flipAt n s i i = t i := by
        simp only [flipAt, Function.update_self]
        cases hsj : s i <;> cases htj : t i <;> simp_all
      have hmem : i ∈ (univ.filter fun j => s j ≠ t j) := by
        simp only [mem_filter, mem_univ, true_and]; exact hsi
      -- the differing set drops `i`
      have hsub : (univ.filter fun j => flipAt n s i j ≠ t j)
                = (univ.filter fun j => s j ≠ t j).erase i := by
        ext j
        simp only [mem_filter, mem_univ, true_and, Finset.mem_erase]
        by_cases hj : j = i
        · subst hj
          simp [hti]
        · have hval : flipAt n s i j = s j := by
            simp only [flipAt, Function.update_of_ne hj]
          rw [hval]
          exact ⟨fun h => ⟨hj, h⟩, fun h => h.2⟩
      have hcard' : (univ.filter fun j => flipAt n s i j ≠ t j).card = k := by
        rw [hsub, Finset.card_erase_of_mem hmem, h]; omega
      exact (hadj.reachable).trans (reachable_aux n k (flipAt n s i) t hcard')

/-- **Every pair of facets is reachable.**  The octahedral sphere's facet-adjacency graph is
preconnected, in every dimension. -/
theorem crossGraph_preconnected (n : ℕ) : (crossGraph n).Preconnected := by
  intro s t
  exact reachable_aux n _ s t rfl

/-- **The cross-polytope facet-adjacency graph is connected, in every dimension.**  The
global pseudomanifold-connectivity of the antipodal substrate `∂◊^{n+1}`, dimension-free —
the counterpart to `SpernerTuckerCrossPolytopeBoundary.facet_degree`'s local regularity. -/
theorem crossGraph_connected (n : ℕ) : (crossGraph n).Connected := by
  rw [SimpleGraph.connected_iff]
  exact ⟨crossGraph_preconnected n, ⟨fun _ => false⟩⟩

#check @reachable_aux
#check @crossGraph_preconnected
#check @crossGraph_connected

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide`.
#print axioms crossGraph_connected
#print axioms crossGraph_preconnected

end SpernerTuckerCrossPolytopeConnected
