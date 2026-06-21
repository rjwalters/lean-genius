/-
  Erdős Problem #57 — Companion: Odd Closed Walks and the Bipartite Characterization

  Source: https://erdosproblems.com/57

  The parent file `Proofs/Erdos57Problem.lean` axiomatizes the Liu–Montgomery (2020)
  theorem and leaves one open `sorry`: the hard reverse direction of the bipartite
  characterization `no odd cycle ⟹ 2-colorable`.  Mathlib itself lists this exact
  statement as future work (`Mathlib.Combinatorics.SimpleGraph.Bipartite`: "Prove that
  `G.IsBipartite` iff `G` does not contain an odd cycle").

  This companion proves the genuinely hard *construction* direction in its clean
  closed-walk form, fully and axiom-free:

      `G.IsBipartite ↔ G has no odd closed walk`   (`isBipartite_iff_no_oddClosedWalk`)

  * Forward (easy): a `Bool`-coloring forces every closed walk to have even length
    (Mathlib's `Coloring.even_length_iff_congr`).
  * Reverse (the construction): pick a base vertex in each connected component and color
    every vertex by the parity of *some* walk back to its base.  Well-definedness of this
    parity is exactly the hypothesis "no odd closed walk" (two walks with the same
    endpoints close up into a closed walk, hence have equal parity), and an edge between
    two equal-parity vertices would close up an odd walk — so the construction is a proper
    2-coloring.

  Consequences proved here (all 0-axiom):
  * `oddCycle ⟹ has odd closed walk ⟹ ¬ bipartite`  (the easy obstruction direction,
    relating back to the parent's `oddCycleLengths`), recovering
    `oddCycleLengths_empty_of_isBipartite`;
  * `has odd closed walk ⟹ 3 ≤ χ(G)`  (quantitative obstruction via Mathlib's
    `Walk.three_le_chromaticNumber_of_odd_loop`).

  The remaining gap to the parent's full *odd-cycle* characterization is now isolated to a
  single purely combinatorial lemma — "every odd closed walk contains an odd cycle" —
  which is NOT assumed anywhere below.
-/

import Mathlib
import Proofs.Erdos57Problem

open Set SimpleGraph

namespace Erdos57

variable {V : Type*} {G : SimpleGraph V}

/-! ## Odd closed walks -/

/-- `G` admits an *odd closed walk*: a walk `u → u` of odd length. -/
def HasOddClosedWalk (G : SimpleGraph V) : Prop :=
  ∃ (u : V) (p : G.Walk u u), Odd p.length

/-- If `G` has no odd closed walk, then any two walks with the same endpoints have the
same length parity: concatenating one with the reverse of the other yields a closed walk,
which (by hypothesis) must have even length. -/
theorem even_length_iff_of_noOddClosedWalk (h : ¬ HasOddClosedWalk G)
    {x y : V} (p q : G.Walk x y) : Even p.length ↔ Even q.length := by
  have hclosed : Even (p.length + q.length) := by
    have hne : ¬ Odd (p.append q.reverse).length := fun hodd => h ⟨x, _, hodd⟩
    rwa [Walk.length_append, Walk.length_reverse, Nat.not_odd_iff_even] at hne
  exact Nat.even_add.mp hclosed

/-! ## A canonical base vertex per connected component -/

/-- A chosen representative vertex of `v`'s connected component. -/
noncomputable def baseVertex (G : SimpleGraph V) (v : V) : V :=
  (G.connectedComponentMk v).out

theorem reachable_baseVertex (G : SimpleGraph V) (v : V) :
    G.Reachable (baseVertex G v) v :=
  ConnectedComponent.exact (G.connectedComponentMk v).out_eq

/-- A chosen walk from `v`'s base vertex back to `v`. -/
noncomputable def baseWalk (G : SimpleGraph V) (v : V) : G.Walk (baseVertex G v) v :=
  (reachable_baseVertex G v).some

/-! ## The parity 2-coloring -/

/-- If `G` has no odd closed walk, the "parity of a walk to the base vertex" function is a
proper `Bool`-coloring: adjacent vertices share a component, so their base vertices agree,
and an edge between them would otherwise close up an odd walk. -/
noncomputable def parityColoring (h : ¬ HasOddClosedWalk G) : G.Coloring Bool :=
  Coloring.mk (fun v => decide (Odd (baseWalk G v).length)) <| by
    intro u v hadj
    -- Adjacent vertices lie in the same component, so their base vertices coincide.
    have hcc : G.connectedComponentMk u = G.connectedComponentMk v :=
      ConnectedComponent.connectedComponentMk_eq_of_adj hadj
    have hbase : baseVertex G u = baseVertex G v := by
      unfold baseVertex; rw [hcc]
    -- Two walks `baseVertex u → v`: one through the edge `u-v`, one transported from `baseWalk v`.
    have hpar :=
      even_length_iff_of_noOddClosedWalk h
        ((baseWalk G u).append (Walk.cons hadj Walk.nil))
        ((baseWalk G v).copy hbase.symm rfl)
    have hlen1 : ((baseWalk G u).append (Walk.cons hadj Walk.nil)).length
        = (baseWalk G u).length + 1 := by simp [Walk.length_append]
    have hlen2 : ((baseWalk G v).copy hbase.symm rfl).length
        = (baseWalk G v).length := by simp [Walk.length_copy]
    rw [hlen1, hlen2, Nat.even_add_one] at hpar
    -- `hpar : ¬ Even (baseWalk u).length ↔ Even (baseWalk v).length`: opposite parities.
    simp only [ne_eq, decide_eq_decide, ← Nat.not_even_iff_odd]
    tauto

/-! ## Bipartite ⟺ no odd closed walk -/

/-- **Headline.** A simple graph is bipartite (2-colorable) iff it has no odd closed walk.

The reverse direction is the component-wise parity construction (`parityColoring`); this is
the direction Mathlib lists as future work for the odd-cycle version. -/
theorem isBipartite_iff_no_oddClosedWalk (G : SimpleGraph V) :
    G.IsBipartite ↔ ¬ HasOddClosedWalk G := by
  constructor
  · rintro ⟨c⟩ ⟨u, p, hodd⟩
    -- Recolor the `Fin 2`-coloring to a `Bool`-coloring and apply the parity lemma.
    have c' : G.Coloring Bool := G.recolorOfEquiv finTwoEquiv c
    have hEven : Even p.length := (c'.even_length_iff_congr p).mpr Iff.rfl
    exact (Nat.not_even_iff_odd.mpr hodd) hEven
  · intro h
    have hcol := (parityColoring h).colorable
    rwa [Fintype.card_bool] at hcol

/-! ## Consequences for odd cycles (the easy obstruction direction) -/

/-- An odd cycle is in particular an odd closed walk. -/
theorem hasOddClosedWalk_of_oddCycle {u : V} (c : G.Walk u u)
    (_hc : c.IsCycle) (hodd : Odd c.length) : HasOddClosedWalk G :=
  ⟨u, c, hodd⟩

/-- If the set of odd cycle lengths is nonempty, then `G` has an odd closed walk. -/
theorem hasOddClosedWalk_of_oddCycleLengths (hne : (oddCycleLengths G).Nonempty) :
    HasOddClosedWalk G := by
  obtain ⟨n, hn⟩ := hne
  simp only [oddCycleLengths, cycleLengths, Set.mem_setOf_eq] at hn
  obtain ⟨⟨u, p, _hp, hlen⟩, hodd⟩ := hn
  exact ⟨u, p, by rw [hlen]; exact hodd⟩

/-- If `G` has an odd cycle, it is not bipartite. -/
theorem not_isBipartite_of_oddCycleLengths (hne : (oddCycleLengths G).Nonempty) :
    ¬ G.IsBipartite := by
  rw [isBipartite_iff_no_oddClosedWalk, not_not]
  exact hasOddClosedWalk_of_oddCycleLengths hne

/-- Forward direction of the parent's `bipartite_iff_no_odd_cycles`, recovered through the
closed-walk framework: a bipartite graph has no odd cycles. -/
theorem oddCycleLengths_empty_of_isBipartite (h : G.IsBipartite) :
    oddCycleLengths G = ∅ := by
  by_contra hne
  exact not_isBipartite_of_oddCycleLengths (Set.nonempty_iff_ne_empty.mpr hne) h

/-! ## Quantitative chromatic obstruction -/

/-- A graph with an odd closed walk has chromatic number at least `3`. -/
theorem three_le_chromaticNumber_of_hasOddClosedWalk (h : HasOddClosedWalk G) :
    3 ≤ G.chromaticNumber := by
  obtain ⟨u, p, hodd⟩ := h
  exact p.three_le_chromaticNumber_of_odd_loop hodd

/-- A graph with an odd cycle has chromatic number at least `3`. -/
theorem three_le_chromaticNumber_of_oddCycleLengths
    (hne : (oddCycleLengths G).Nonempty) : 3 ≤ G.chromaticNumber :=
  three_le_chromaticNumber_of_hasOddClosedWalk (hasOddClosedWalk_of_oddCycleLengths hne)

end Erdos57
