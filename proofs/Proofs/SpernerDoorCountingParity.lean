/-
# Sperner / Tucker OQ-02: The Abstract Door-Counting Parity Engine

## Context

The parent problem ("Tucker's Lemma and Borsuk–Ulam from Abstract Door-Counting")
shipped the `n = 1` milestone (`SpernerTuckerOneDim.lean`): a telescoping ℤ/2
identity producing a complementary edge on an antipodally-labelled path. The open
frontier is `n ≥ 2`, where the complementary-edge count is *no longer* a direct
parity invariant, so the 1-D telescoping argument does not lift.

This file isolates the part of the machinery that **does** lift to every
dimension: the *abstract door-counting parity engine*. In every flavour of
combinatorial fixed-point theorem (Sperner, Tucker, Scarf), one builds a "door
graph" whose vertices are cells and whose edges join cells sharing a marked facet
("door"). A cell is a *door-terminal* (a place a path can end) exactly when it has
odd door-degree, and the path-following argument is powered entirely by one fact:

  **the number of odd-degree vertices of a finite graph is even** (handshake).

Hence a *known* boundary terminal forces a *second*, distinct terminal — the
sought solution. This file states that engine cleanly over an arbitrary finite
`SimpleGraph`, specializes it to degree-≤2 "path/cycle" graphs (where door-terminal
⇔ degree 1, the literal endpoints of paths), and packages the boundary/interior
door-counting conclusion. Everything is **0 axioms, 0 sorries**.

## What lifts and what does not

- **Lifts (here):** the handshake parity engine and the "odd boundary ⇒ interior
  door" pigeonhole. Dimension-independent.
- **Does not lift (the `n ≥ 2` obstruction):** the labelling that makes the door
  graph have all degrees ≤ 2 *and* makes boundary doors odd in count. At `n ≥ 2`
  one needs Freund–Todd / Prescott–Su path-following on almost-complementary
  simplices, not a single global parity count.

## References

- Mathlib, `Mathlib.Combinatorics.SimpleGraph.DegreeSum` (handshake lemma).
- Freund & Todd, "A constructive proof of Tucker's combinatorial lemma" (1981).
- Prescott & Su, "A constructive proof of Ky Fan's combinatorial lemma" (2005).
-/
import Mathlib

namespace SpernerDoorCountingParity

open Finset SimpleGraph

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: THE ABSTRACT DOOR-COUNTING ENGINE (any degree)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- A *door-terminal* of the door graph: a cell with an odd number of doors. These
are the only cells at which a path-following argument can terminate. -/
def IsDoorTerminal (v : V) : Prop := Odd (G.degree v)

instance : DecidablePred (IsDoorTerminal G) := fun v => by
  unfold IsDoorTerminal; infer_instance

/-- **The door-counting parity engine.** The number of door-terminals is even.
This is precisely the handshake lemma, and it is the dimension-independent heart
of every Sperner/Tucker/Scarf path-following argument. -/
theorem even_card_doorTerminals :
    Even (univ.filter (IsDoorTerminal G)).card :=
  G.even_card_odd_degree_vertices

/-- **A known door forces a second door.** If one cell is a door-terminal, there is
another distinct one. In the geometric setting the first is a boundary door placed
by hand; the second is the interior solution. -/
theorem doorTerminal_forces_another {v : V} (hv : IsDoorTerminal G v) :
    ∃ w, w ≠ v ∧ IsDoorTerminal G w :=
  G.exists_ne_odd_degree_of_exists_odd_degree v hv

/-- **Boundary/interior door counting.** If the door-terminals lying on a designated
boundary set `B` are odd in number, then there is a door-terminal off `B` — the
interior solution the constructive argument seeks. -/
theorem exists_interior_doorTerminal [DecidableEq V] (B : Finset V)
    (hB : Odd ((univ.filter (IsDoorTerminal G)) ∩ B).card) :
    ∃ w, IsDoorTerminal G w ∧ w ∉ B := by
  set D := univ.filter (IsDoorTerminal G) with hD
  have hsplit : (D ∩ B).card + (D \ B).card = D.card := card_inter_add_card_sdiff D B
  have hEven : Even D.card := even_card_doorTerminals G
  -- total even, boundary part odd ⇒ interior part odd ⇒ nonempty
  have hOddSdiff : Odd (D \ B).card := by
    rcases hEven with ⟨k, hk⟩
    rcases hB with ⟨j, hj⟩
    refine ⟨k - j - 1, ?_⟩
    omega
  have hne : (D \ B).Nonempty := by
    rw [← Finset.card_pos]; rcases hOddSdiff with ⟨t, ht⟩; omega
  obtain ⟨w, hw⟩ := hne
  rw [Finset.mem_sdiff, hD, Finset.mem_filter] at hw
  exact ⟨w, hw.1.2, hw.2⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: PATH/CYCLE SPECIALIZATION (degree ≤ 2)
═══════════════════════════════════════════════════════════════════════════════ -/

/-! When the door graph has maximum degree `2` — the situation engineered by
path-following on almost-complementary simplices — door-terminals are exactly the
degree-`1` cells, i.e. the literal endpoints of the disjoint paths. -/

/-- Under degree `≤ 2`, a cell is a door-terminal iff its door-degree is exactly 1. -/
theorem doorTerminal_iff_degree_one {v : V} (hdeg : G.degree v ≤ 2) :
    IsDoorTerminal G v ↔ G.degree v = 1 := by
  unfold IsDoorTerminal
  rw [Nat.odd_iff]
  omega

/-- In a degree-`≤2` door graph the number of path endpoints (degree-1 cells) is
even — paths pair up their two ends. -/
theorem even_card_pathEnds (hG : ∀ v, G.degree v ≤ 2) :
    Even (univ.filter (fun v => G.degree v = 1)).card := by
  have h := even_card_doorTerminals G
  rwa [Finset.filter_congr (fun v _ => doorTerminal_iff_degree_one G (hG v))] at h

/-- A known path endpoint forces a second, distinct one. -/
theorem pathEnd_forces_pathEnd (hG : ∀ v, G.degree v ≤ 2) {v : V}
    (hv : G.degree v = 1) : ∃ w, w ≠ v ∧ G.degree w = 1 := by
  obtain ⟨w, hwv, hw⟩ :=
    doorTerminal_forces_another G ((doorTerminal_iff_degree_one G (hG v)).mpr hv)
  exact ⟨w, hwv, (doorTerminal_iff_degree_one G (hG w)).mp hw⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
SUMMARY
═══════════════════════════════════════════════════════════════════════════════

**Verified (0 axioms, 0 sorries):**
1. `even_card_doorTerminals` — the handshake parity engine: the number of
   door-terminals (odd-degree cells) is even.
2. `doorTerminal_forces_another` — a known door forces a distinct second door.
3. `exists_interior_doorTerminal` — odd boundary door count ⇒ an interior door.
4. Degree-`≤2` specialization: door-terminals ⇔ degree-1 endpoints, their count is
   even, and one endpoint forces another (`pathEnd_forces_pathEnd`).

This pins down the dimension-independent engine of door-counting; the `n ≥ 2`
work that remains is the construction of the degree-`≤2` door graph with an odd
boundary-door count (Freund–Todd / Prescott–Su path-following), not the parity
principle itself.
-/

#check @even_card_doorTerminals
#check @doorTerminal_forces_another
#check @exists_interior_doorTerminal
#check @pathEnd_forces_pathEnd

end SpernerDoorCountingParity
