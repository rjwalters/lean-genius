/-
# Sperner Simplicial Instance OQ-03: the full FC-oddness recursion tower

`SpernerSimplicialInstanceOQ03.lean` isolated the *single* cross-dimensional
inductive step `fc_odd_of_facet_bijection`:

  Odd #FC(Δ^{d+1})  ⟸  (top-facet door↔FC bijection)  +  Odd #FC(Δ^d).

This file closes the induction: given the base case `Odd #FC(Δ¹)` and the
facet-restriction bijection at *every* level, `Odd #FC(Δ^d)` holds for all `d ≥ 1`
simultaneously. This is the headline Sperner recursion (the engine behind
`_hLastFace` / `boundary_doors_odd`), expressed as one theorem rather than a
single step.

It reduces the entire open question to exactly **two** named geometric inputs,
both deferred to the concrete order-polytope standard triangulation:
  * `hbase` — the 1-dimensional Sperner lemma `Odd #FC(Δ¹)` (classically `= 1`);
  * `hstep` — the family of top-facet door↔FC bijections, one per dimension.
Everything else (the parity counting) is already discharged, sorry-free, by
`SpernerNDim.sperner_parity` via `fc_odd_of_facet_bijection`.

Build status: PENDING (Docker + Aristotle blackout, both re-tested live this
session). UNREGISTERED in `Proofs.lean`. The proof is a single `Nat.le_induction`
over the proven inductive step — no new geometry.
-/

import Proofs.SpernerSimplicialInstanceOQ03

namespace SpernerNDim

open Finset BigOperators

/-- **The full Sperner FC-oddness recursion.**

Let `K d` be a Sperner-colored triangulation of dimension `d` (coloring `c d`,
ambient size `N d`) for every `d`. Suppose:
  * `hbase` : the 1-dimensional triangulation has an odd number of fully-colored
    simplices (the base of the recursion);
  * `hstep` : for every `d ≥ 1`, the number of top-facet boundary doors of `K (d+1)`
    equals the number of fully-colored simplices of `K d` (the facet-restriction
    bijection, the sole geometric input).

Then `K d` has an odd number of fully-colored simplices for every `d ≥ 1`.

The proof inducts on dimension via the proven single step
`fc_odd_of_facet_bijection`; no parity counting is re-derived. -/
theorem fc_odd_tower {N : ℕ → ℕ}
    (c : ∀ d, Coloring d (N d)) (K : ∀ d, SpernerTriangulation d (N d))
    (hc : ∀ d, IsSperner (c d))
    (hbase : Odd (Finset.univ.filter (fun s : (K 1).Simplex => IsFC (c 1) (K 1) s)).card)
    (hstep : ∀ d : ℕ, 1 ≤ d →
      (Finset.univ.filter (fun p : (K (d + 1)).Simplex × Fin (d + 1 + 1) =>
        isDoorAt (c (d + 1)) (K (d + 1)) p.1 p.2 ∧
          (K (d + 1)).adj p.1 p.2 = none ∧ p.2 = Fin.last (d + 1))).card =
      (Finset.univ.filter (fun s : (K d).Simplex => IsFC (c d) (K d) s)).card) :
    ∀ d : ℕ, 1 ≤ d →
      Odd (Finset.univ.filter (fun s : (K d).Simplex => IsFC (c d) (K d) s)).card := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base => exact hbase
  | succ n hn ih =>
      exact fc_odd_of_facet_bijection (c (n + 1)) (K (n + 1)) (hc (n + 1))
        (c n) (K n) (hc n) (hstep n hn) ih

/-- **Existence form of the tower.** Under the same hypotheses, every
dimension-`d` triangulation (`d ≥ 1`) contains a fully-colored simplex — the
conclusion of Sperner's lemma, obtained from oddness (an odd count is positive).
-/
theorem exists_fc_tower {N : ℕ → ℕ}
    (c : ∀ d, Coloring d (N d)) (K : ∀ d, SpernerTriangulation d (N d))
    (hc : ∀ d, IsSperner (c d))
    (hbase : Odd (Finset.univ.filter (fun s : (K 1).Simplex => IsFC (c 1) (K 1) s)).card)
    (hstep : ∀ d : ℕ, 1 ≤ d →
      (Finset.univ.filter (fun p : (K (d + 1)).Simplex × Fin (d + 1 + 1) =>
        isDoorAt (c (d + 1)) (K (d + 1)) p.1 p.2 ∧
          (K (d + 1)).adj p.1 p.2 = none ∧ p.2 = Fin.last (d + 1))).card =
      (Finset.univ.filter (fun s : (K d).Simplex => IsFC (c d) (K d) s)).card)
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ s : (K d).Simplex, IsFC (c d) (K d) s := by
  have hodd := fc_odd_tower c K hc hbase hstep d hd
  -- an odd-cardinality finset is nonempty
  have hpos : 0 < (Finset.univ.filter (fun s : (K d).Simplex => IsFC (c d) (K d) s)).card := by
    have := Nat.odd_iff.mp hodd; omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  exact ⟨s, (Finset.mem_filter.mp hs).2⟩

end SpernerNDim
