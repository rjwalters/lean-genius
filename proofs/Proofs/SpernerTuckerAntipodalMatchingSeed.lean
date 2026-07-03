/-
# The self-antipodal Tucker seed, realized on a concrete matching family

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits

The door-counting program for Tucker reduces full-dimensional Tucker to a single open
geometric input — the `bridge` of `SpernerTuckerInductiveTower.TuckerTower`, which consumes
an **odd** interior-endpoint count at every level.  Two complementary halves of the parity
theory around that odd count are already machine-checked:

* `SpernerTuckerFixedPointParity` — the *abstract* characterisation.  For a
  boundary-preserving antipodal **automorphism** `σ` (an involution, *not* assumed
  fixed-point free), the interior (complementary) count is odd **iff** the number of
  **self-antipodal** interior endpoints (`σ v = v`) is odd
  (`odd_interiorEndpoints_iff_odd_selfAntipodal`), and hence a Tucker level forces the
  existence of a self-antipodal complementary simplex
  (`exists_selfAntipodal_of_tucker_level`).  This localises the odd seed onto a concrete
  geometric object: the cell the antipodal map cannot pair away.
* `SpernerTuckerDoorGraphTower` — a *concrete* growing door-graph family
  `matchingGraph (2n+1)` (a perfect matching, `2n+1` disjoint edges) on which the abstract
  engine `exists_interior_of_graph_tower` fires end-to-end
  (`matchingTower_exists_interior`).

But these two files never met: the concrete matching family was only ever run through the
*count-level* engine with the **trivial** antipodal action, and the self-antipodal
fixed-point engine had only been exercised against abstract hypotheses — **no concrete door
graph carried a genuine, non-trivial (non-free) antipodal automorphism whose fixed points
produce the odd interior seed.**

## What this file proves

This file installs a **non-trivial** antipodal automorphism on the concrete matching family
and fires the fixed-point-parity engine on it.  On `matchingGraph (2k+1)` over
`Fin (2k+1) × Bool` we take

  `antiσ k (i, a) := (Fin.rev i, a)`,

the reflection `Fin.rev` (`i ↦ 2k − i`) on the edge-index coordinate, leaving the boundary
coordinate `a` untouched.  Then:

* `antiσ_involutive` — `antiσ` is an involution (`Fin.rev_rev`);
* `antiσ_aut` — it is a graph automorphism of `matchingGraph (2k+1)`: it permutes the
  disjoint edges, sending edge `i` to edge `Fin.rev i` (`Fin.rev` is injective);
* `antiσ_boundary` — it preserves the boundary predicate `matchingB` (which depends only on
  the untouched coordinate `a`);

and `antiσ` is genuinely **non-trivial and non-free**: as a reflection with the single fixed
index `k`, it swaps the `2k` edges in `k` antipodal pairs and fixes exactly the central edge
`i = k` — the concrete analogue of the antipodal map fixing the central simplex of the ball
`B²ᵏ⁺¹`, free on all the others.

Feeding this into the fixed-point engine gives, from the odd interior count
`card_interiorEndpoints_matching (2k+1) = 2k+1`:

* `antipodalMatching_exists_selfAntipodal` — a **self-antipodal complementary simplex**
  exists: some interior (degree-1, non-boundary) vertex is fixed by `antiσ`.  This is the
  first time `exists_selfAntipodal_of_tucker_level` fires on a concrete door graph with a
  non-trivial antipodal automorphism.
* `odd_selfAntipodal_interior` — sharper: the self-antipodal complementary simplices are
  **odd** in number.  Combined with the direct count `2k+1`, this exhibits **two independent
  routes to the same oddness** — the raw interior count and the fixed-point count — agreeing
  on a concrete growing graph family, exactly the consistency the abstract
  `odd_interiorEndpoints_iff_odd_selfAntipodal` predicts.

## Honest status

**Infrastructure/validation, NOT new Tucker geometry.**  The matching family is not the
cross-polytope door graph; its "central edge" is a stand-in for the central self-antipodal
simplex, not the geometric object itself.  What is new is the *meeting* of the two prior
files: the abstract self-antipodal-seed engine is now confirmed to fire on a concrete door
graph carrying a real (non-free) antipodal automorphism, catching all four hypotheses
(`Involutive` / automorphism / boundary-preserving / odd count) at once on a genuine
`SimpleGraph` — the template the eventual asymmetric cross-polytope labelling must match.  It
does **not** build that asymmetric almost-complementary labelling on `∂◊ⁿ`, which remains the
open geometric frontier exactly as every prior session flagged.

⚠️ **PENDING MACHINE VERIFICATION.**  This file was authored during a host disk-full
environmental blocker (host `/` oscillating near 0 free; the sanctioned `docker-build.sh`
path regenerates a ~6.8 GB `.lake` and no host `.olean` cache for the dependency chain was
available), so it has **not** yet been checked by Lean.  It reuses only lemmas whose full
source was read (`matchingGraph`, `matchingB`, `card_interiorEndpoints_matching`,
`exists_selfAntipodal_of_tucker_level`, `odd_interiorEndpoints_iff_odd_selfAntipodal`) plus
standard Mathlib `Fin.rev` API (`Fin.rev_rev`, `Fin.rev_injective`).  A single
`docker-build.sh Proofs.SpernerTuckerAntipodalMatchingSeed` once disk is reclaimed should
close it; the `#print axioms` guards below are the intended 0-axiom audit.  Until then this is
a drafted artifact, not a verified gallery result.
-/
import Mathlib
import Proofs.SpernerTuckerDoorGraphTower
import Proofs.SpernerTuckerFixedPointParity

namespace SpernerTuckerAntipodalMatchingSeed

open Finset SimpleGraph
open SpernerTuckerInductiveTower SpernerTuckerDoorGraphTower SpernerTuckerFixedPointParity

/-! ## A non-trivial antipodal automorphism of the concrete matching family

On the perfect matching `matchingGraph (2k+1)` over `Fin (2k+1) × Bool`, the reflection
`Fin.rev` on the edge-index coordinate is a free-away-from-the-centre involution: it swaps the
`2k` edges in antipodal pairs and fixes only the central edge `i = k`. -/

/-- The antipodal automorphism: reflect the edge index by `Fin.rev`, keep the boundary bit. -/
def antiσ (k : ℕ) : Fin (2 * k + 1) × Bool → Fin (2 * k + 1) × Bool :=
  fun p => (Fin.rev p.1, p.2)

/-- `antiσ` is an involution (`Fin.rev` is). -/
theorem antiσ_involutive (k : ℕ) : Function.Involutive (antiσ k) := by
  intro p
  obtain ⟨i, a⟩ := p
  simp [antiσ, Fin.rev_rev]

/-- `antiσ` is a graph automorphism of `matchingGraph (2k+1)`: it sends edge `i` to edge
`Fin.rev i`, so it preserves adjacency (`Fin.rev` is injective). -/
theorem antiσ_aut (k : ℕ) (v w : Fin (2 * k + 1) × Bool) :
    (matchingGraph (2 * k + 1)).Adj (antiσ k v) (antiσ k w)
      ↔ (matchingGraph (2 * k + 1)).Adj v w := by
  obtain ⟨i, a⟩ := v
  obtain ⟨j, b⟩ := w
  -- `Adj p q` is defeq to `p.1 = q.1 ∧ p.2 ≠ q.2`; `antiσ (i,a) = (Fin.rev i, a)`.
  show (Fin.rev i = Fin.rev j ∧ a ≠ b) ↔ (i = j ∧ a ≠ b)
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨Fin.rev_injective h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨congrArg Fin.rev h1, h2⟩

/-- `antiσ` preserves the boundary predicate `matchingB` (which reads only the untouched
second coordinate). -/
theorem antiσ_boundary (k : ℕ) (v : Fin (2 * k + 1) × Bool) :
    matchingB (2 * k + 1) (antiσ k v) ↔ matchingB (2 * k + 1) v := by
  obtain ⟨i, a⟩ := v
  exact Iff.rfl

/-! ## The odd interior count and its self-antipodal localisation -/

/-- The interior (complementary) count of `matchingGraph (2k+1)` is `2k+1`, which is odd. -/
theorem odd_interior (k : ℕ) :
    Odd #(interiorEndpoints (matchingGraph (2 * k + 1)) (matchingB (2 * k + 1))) := by
  rw [card_interiorEndpoints_matching]
  exact ⟨k, by ring⟩

/-- **A self-antipodal complementary simplex exists.**  Firing
`exists_selfAntipodal_of_tucker_level` on the concrete matching family with the non-trivial
antipodal automorphism `antiσ`: some interior (degree-1, non-boundary) vertex is fixed by
`antiσ`.  Geometrically, the antipodal reflection cannot pair every complementary edge with a
distinct partner — the central edge `i = k` is its own antipode. -/
theorem antipodalMatching_exists_selfAntipodal (k : ℕ) :
    ∃ v ∈ interiorEndpoints (matchingGraph (2 * k + 1)) (matchingB (2 * k + 1)),
      antiσ k v = v :=
  exists_selfAntipodal_of_tucker_level
    (matchingGraph (2 * k + 1)) (matchingB (2 * k + 1))
    (antiσ_involutive k) (antiσ_aut k) (antiσ_boundary k) (odd_interior k)

/-- **The self-antipodal complementary simplices are odd in number.**  The sharp form: via
`odd_interiorEndpoints_iff_odd_selfAntipodal`, the odd interior count `2k+1` is carried
entirely by the interior endpoints that `antiσ` fixes.  Together with `odd_interior` this is
two independent routes to the same oddness — the raw count and the fixed-point count —
agreeing on a genuine growing graph family. -/
theorem odd_selfAntipodal_interior (k : ℕ) :
    Odd #((interiorEndpoints (matchingGraph (2 * k + 1)) (matchingB (2 * k + 1))).filter
      (fun v => antiσ k v = v)) :=
  (odd_interiorEndpoints_iff_odd_selfAntipodal
    (matchingGraph (2 * k + 1)) (matchingB (2 * k + 1))
    (antiσ_involutive k) (antiσ_aut k) (antiσ_boundary k)).mp (odd_interior k)

#check @antiσ_involutive
#check @antiσ_aut
#check @antipodalMatching_exists_selfAntipodal
#check @odd_selfAntipodal_interior

-- Axiom audit (intended): foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.  PENDING machine verification (disk-full blocker).
#print axioms antipodalMatching_exists_selfAntipodal
#print axioms odd_selfAntipodal_interior

end SpernerTuckerAntipodalMatchingSeed
