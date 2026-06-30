/-
# The pairwise facet lemma: two distinct simplices share ≤ 1 facet (discharging `hpair`)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits

The abstract door-counting engine (`SpernerTuckerDoorGraph.lean`) derives the
path-following structure of Tucker's lemma from a finite *door-incidence relation*
`inc : V → D → Prop` satisfying three geometric hypotheses:

* `hdoor`    — each door is shared by `≤ 2` simplices (a *pseudomanifold* property);
* `hsimplex` — each almost-complementary simplex has `≤ 2` doors;
* `hpair`    — two distinct simplices share `≤ 1` door.

`hsimplex` was turned into a theorem (for the canonical Sperner colouring) in
`SpernerTuckerDoorLemma.lean`.  **This file discharges `hpair`** for the natural
*subset incidence* — the incidence that any simplicial complex actually carries: a
simplex is an `(n+1)`-element vertex set, a door/facet is one of its `n`-element
subsets, and `inc v d` means "the facet `d` is a face of the simplex `v`".

## What this file proves

For finsets over any vertex type with decidable equality:

* `card_inter_le_of_ne` — two *distinct* simplices of the same size `n+1` meet in at
  most `n` vertices (else the intersection, being a same-card subset of each, would
  equal both, forcing them equal).
* `facet_eq_inter` — an `n`-facet shared by two distinct `(n+1)`-simplices is **exactly**
  their intersection (it lies in the intersection, which already has `≤ n` elements, so
  the inclusion is an equality of cardinality `n`).
* `facets_pairwise` — **the pairwise door lemma**: two distinct simplices share at most
  one facet (both shared facets equal the intersection, hence each other).
* `subset_incidence_hpair` — `facets_pairwise` packaged in the **exact logical shape** of
  the engine's `hpair` hypothesis, for the subset incidence `inc n`.  Combined with the
  engine wiring example below, this shows `hpair` is no longer an assumption: only `hdoor`
  (the genuine pseudomanifold property) and the geometric `bridge` remain open.

The wiring example `degree_eq_shared_subset` feeds `subset_incidence_hpair` into the
engine's sharp degree formula `doorGraph_degree_eq_shared`, leaving `hdoor` as the sole
remaining incidence hypothesis there.

## Honest status

This is a genuine, dimension-free combinatorial theorem — the classical "two top-cells
of a complex share at most one codimension-1 face" fact underlying every pseudomanifold /
door-counting argument — proved from scratch (Mathlib lacks it in reusable form).  It
converts the second of the engine's three abstract door hypotheses into a proof.  It is
*not* the geometric `bridge`, and `hdoor` (the pseudomanifold property, which is genuinely
false for arbitrary complexes and so cannot be proved abstractly) remains the geometric
input, exactly as prior sessions flagged.

Self-contained.  0 sorries, 0 axioms (propext / Classical.choice / Quot.sound only).
-/
import Mathlib.Tactic
import Proofs.SpernerTuckerDoorGraph

namespace SpernerTuckerSimplexFacetPair

open Finset

variable {α : Type*} [DecidableEq α]

/-! ## The intersection bound for distinct equicardinal simplices -/

/-- **Distinct simplices of size `n+1` meet in at most `n` vertices.**  If the
intersection had `≥ n+1` elements then, being a subset of each `(n+1)`-element set with
cardinality `≥` theirs, it would equal both — forcing `v = w`. -/
theorem card_inter_le_of_ne {v w : Finset α} {n : ℕ}
    (hv : v.card = n + 1) (hw : w.card = n + 1) (hvw : v ≠ w) :
    (v ∩ w).card ≤ n := by
  by_contra h
  push_neg at h
  have e1 : v ∩ w = v := eq_of_subset_of_card_le inter_subset_left (by omega)
  have e2 : v ∩ w = w := eq_of_subset_of_card_le inter_subset_right (by omega)
  exact hvw (e1.symm.trans e2)

/-! ## A shared facet is the intersection -/

/-- **An `n`-facet shared by two distinct `(n+1)`-simplices is their intersection.**
The facet lies in `v ∩ w`, whose cardinality is already `≤ n`; an `n`-element subset of an
`(≤ n)`-element set fills it, so the inclusion is an equality. -/
theorem facet_eq_inter {v w d : Finset α} {n : ℕ}
    (hv : v.card = n + 1) (hw : w.card = n + 1) (hvw : v ≠ w)
    (hd : d.card = n) (hdv : d ⊆ v) (hdw : d ⊆ w) :
    d = v ∩ w := by
  have hsub : d ⊆ v ∩ w := subset_inter hdv hdw
  have hle : (v ∩ w).card ≤ n := card_inter_le_of_ne hv hw hvw
  exact eq_of_subset_of_card_le hsub (by omega)

/-- **The pairwise door lemma.**  Two distinct `(n+1)`-simplices share **at most one**
`n`-facet: both shared facets equal the intersection `v ∩ w`, hence each other. -/
theorem facets_pairwise {v w d d' : Finset α} {n : ℕ}
    (hv : v.card = n + 1) (hw : w.card = n + 1) (hvw : v ≠ w)
    (hd : d.card = n) (hd' : d'.card = n)
    (hdv : d ⊆ v) (hdw : d ⊆ w) (hd'v : d' ⊆ v) (hd'w : d' ⊆ w) :
    d = d' := by
  rw [facet_eq_inter hv hw hvw hd hdv hdw, facet_eq_inter hv hw hvw hd' hd'v hd'w]

/-! ## Subset incidence and the engine's `hpair` -/

/-- **Subset incidence.**  `inc n v d` holds when `v` is an `(n+1)`-simplex and `d` is one
of its `n`-element facets.  This is the incidence any simplicial complex carries. -/
def inc (n : ℕ) (v d : Finset α) : Prop := v.card = n + 1 ∧ d.card = n ∧ d ⊆ v

instance (n : ℕ) : DecidableRel (inc (α := α) n) := fun _ _ => by unfold inc; infer_instance

/-- **`hpair`, discharged.**  For the subset incidence, two distinct simplices carrying a
common pair of facets `d, d'` must have `d = d'`.  This is exactly the engine's `hpair`
hypothesis `∀ d d' v w, v ≠ w → inc v d → inc w d → inc v d' → inc w d' → d = d'`, now
proved rather than assumed. -/
theorem subset_incidence_hpair (n : ℕ) :
    ∀ d d' v w : Finset α, v ≠ w →
      inc n v d → inc n w d → inc n v d' → inc n w d' → d = d' := by
  rintro d d' v w hvw ⟨hv, hd, hdv⟩ ⟨hw, -, hdw⟩ ⟨-, hd', hd'v⟩ ⟨-, -, hd'w⟩
  exact facets_pairwise hv hw hvw hd hd' hdv hdw hd'v hd'w

/-! ## Wiring: the engine's sharp degree formula needs only `hdoor` now

`SpernerTuckerDoorGraph.doorGraph_degree_eq_shared` takes both `hdoor` and `hpair`.  With
`hpair` supplied by `subset_incidence_hpair`, the *only* remaining incidence hypothesis is
`hdoor` — the pseudomanifold "each facet borders ≤ 2 simplices" property, which is
genuinely geometric (false for arbitrary complexes) and is the open input. -/

/-- For the canonical subset incidence, the door-graph degree equals the number of shared
facets — assuming only `hdoor` (`hpair` is now the proved `subset_incidence_hpair`). -/
example [Fintype α] (n : ℕ)
    (hdoor : ∀ d : Finset α, #{v | inc n v d} ≤ 2) (v : Finset α) :
    (SpernerTuckerDoorGraph.doorGraph (inc n)).degree v
      = #{d | inc n v d ∧ ∃ w, w ≠ v ∧ inc n w d} :=
  SpernerTuckerDoorGraph.doorGraph_degree_eq_shared (inc n) hdoor
    (subset_incidence_hpair n) v

#check @facets_pairwise
#check @subset_incidence_hpair

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms facets_pairwise
#print axioms subset_incidence_hpair

end SpernerTuckerSimplexFacetPair
