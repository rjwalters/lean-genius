import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Proofs.CycleDoubleCover

/-
# Even edge-set circuit decomposition (Veblen 1912)

This file is the **foundational layer** for porting the openai/cdc-lean proof of
the Cycle Double Cover theorem (see `Proofs/CycleDoubleCover.lean` for the
statement layer; the theorem `cycleDoubleCover_of_bridgeless` itself is proved
in `Proofs/CycleDoubleCoverPort/Main.lean`). It corresponds, in the
upstream porting order, to the role of `GeneralGraph.lean` + `CycleDecomposition.lean`:
the core even-edge-set / circuit machinery on general finite multigraphs.

## Independence of expression

`openai/cdc-lean` carries **no license file** (confirmed: the license API returns
404 and no `LICENSE` exists in the repo root), so its Lean *source* is under
default copyright and is NOT copied here. The content below is an **independent
re-derivation** of classical, non-copyrightable mathematics — Veblen's 1912
theorem that every even (cycle) edge-set of a graph decomposes into edge-disjoint
circuits — written from scratch in our own Lean idiom against our Mathlib pin
(Lean v4.26.0, Mathlib 2df2f0150c27). Definitions are reused *verbatim* from our
own `Proofs/CycleDoubleCover.lean` (the equivalence target for the whole port),
so the eventual assembly discharges the real axiom, not a lookalike.

## What this file provides

Working entirely in the existing `CycleDoubleCover.FiniteGraph` namespace against
the existing `IsEvenEdgeSet` / `Cycle` definitions:

- `IsEvenEdgeSet.empty`, `IsEvenEdgeSet.sdiff` — the even edge-sets form a system
  closed under (subset) symmetric difference; this is the recursion engine.
- `exists_minimal_even_subset` — every nonempty even edge-set contains an
  inclusion-minimal nonempty even edge-set.
- `exists_cycle_subset` — every nonempty even edge-set contains a `Cycle` (a
  circuit, in the graphic-matroid sense already defined upstream).
- `evenEdgeSet_decomposes` — **Veblen's theorem**: every even edge-set is the
  disjoint union of a finite list of edge-disjoint cycles. This is the structural
  fact that the exact-double-cover argument (upstream `CubicTheorem`) ultimately
  feeds cycles into.

No new `axiom` declarations, no `sorry`, no `native_decide`.
-/

namespace CycleDoubleCover

open Finset

namespace FiniteGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

/-! ### Closure properties of even edge-sets

The even edge-sets of `G` are exactly the cycle space of the graphic matroid
over `F₂`. We only need two closure facts for the decomposition: the empty set is
even, and the difference of an even set by an even subset is even. Together these
let us peel circuits off an even set one at a time.

(`DecidableEq E` is carried by the section for the `Finset` machinery further
down, but the arithmetic lemmas here do not use it; we `omit` it to keep the
section-variable linter quiet.) -/

omit [DecidableEq E] in
/-- The empty edge set is even: every vertex meets it zero times. -/
theorem IsEvenEdgeSet.empty : G.IsEvenEdgeSet (∅ : Finset E) := by
  intro v
  simp

/-- If `F` is even and `D ⊆ F` is even, then `F \ D` is even. Over `F₂` the
incidence sum is additive across the partition `F = D ⊔ (F \ D)`, and both `F`
and `D` contribute zero, so the complement does too. -/
theorem IsEvenEdgeSet.sdiff {F D : Finset E}
    (hF : G.IsEvenEdgeSet F) (hDsub : D ⊆ F) (hD : G.IsEvenEdgeSet D) :
    G.IsEvenEdgeSet (F \ D) := by
  intro v
  have hsplit := Finset.sum_sdiff hDsub (f := fun e => G.edgeIncidence v e)
  rw [hD v, add_zero] at hsplit
  rw [hsplit, hF v]

/-! ### Extracting a minimal circuit

Among all nonempty even subsets of a nonempty even set `F`, one of minimum
cardinality is automatically *inclusion*-minimal: any proper nonempty even subset
would have strictly smaller cardinality. This minimal even set is precisely a
`Cycle` (a circuit) in the sense of `Proofs/CycleDoubleCover.lean`. -/

omit [DecidableEq E] in
/-- Every nonempty even edge-set contains an inclusion-minimal nonempty even
edge-set. -/
theorem exists_minimal_even_subset {F : Finset E} (hne : F.Nonempty)
    (hF : G.IsEvenEdgeSet F) :
    ∃ D : Finset E, D.Nonempty ∧ D ⊆ F ∧ G.IsEvenEdgeSet D ∧
      (∀ D', D'.Nonempty → D' ⊆ D → G.IsEvenEdgeSet D' → D' = D) := by
  classical
  set S := F.powerset.filter (fun D => D.Nonempty ∧ G.IsEvenEdgeSet D) with hS
  have hSne : S.Nonempty := ⟨F, by simp [hS, Finset.mem_powerset, hne, hF]⟩
  obtain ⟨D, hDS, hDmin⟩ := Finset.exists_min_image S Finset.card hSne
  simp only [hS, Finset.mem_filter, Finset.mem_powerset] at hDS
  obtain ⟨hDsub, hDne, hDe⟩ := hDS
  refine ⟨D, hDne, hDsub, hDe, ?_⟩
  intro D' hD'ne hD'sub hD'e
  have hD'S : D' ∈ S := by
    simp only [hS, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨hD'sub.trans hDsub, hD'ne, hD'e⟩
  have h1 := hDmin D' hD'S
  have h2 : D'.card ≤ D.card := Finset.card_le_card hD'sub
  exact Finset.eq_of_subset_of_card_le hD'sub (le_antisymm h2 h1 ▸ le_refl _)

omit [DecidableEq E] in
/-- Every nonempty even edge-set contains a `Cycle` (circuit) supported on it.
This packages `exists_minimal_even_subset` into the upstream `Cycle` structure:
inclusion-minimality of a nonempty even set is exactly the circuit axiom. -/
theorem exists_cycle_subset {F : Finset E} (hne : F.Nonempty)
    (hF : G.IsEvenEdgeSet F) :
    ∃ C : G.Cycle, C.edges ⊆ F := by
  obtain ⟨D, hDne, hDsub, hDe, hDmin⟩ := G.exists_minimal_even_subset hne hF
  exact ⟨⟨D, hDne, hDe, hDmin⟩, hDsub⟩

/-! ### Veblen's decomposition theorem

Every even edge-set is a disjoint union of edge-disjoint circuits. We peel one
minimal circuit `D` off `F`, recurse on the (still even, strictly smaller) set
`F \ D`, and prepend. Disjointness holds because every cycle in the recursive
decomposition lives inside `F \ D`, hence avoids `D`. -/

/-- **Veblen's circuit-decomposition theorem** for the general finite multigraph
`G`: every even edge-set `F` is the union of the edge-sets of a finite list `L`
of cycles whose edge-sets are pairwise disjoint (each edge of `F` lies in exactly
one listed cycle, and every listed cycle lies inside `F`).

This is the structural backbone the eventual exact-double-cover argument relies
on: once the flow machinery produces a family of even edge-sets covering every
edge exactly twice, this theorem turns each even set into honest cycles. -/
theorem evenEdgeSet_decomposes :
    ∀ F : Finset E, G.IsEvenEdgeSet F →
      ∃ L : List G.Cycle,
        (∀ C ∈ L, C.edges ⊆ F) ∧
        (L.Pairwise fun C D => Disjoint C.edges D.edges) ∧
        (∀ e, e ∈ F ↔ ∃ C ∈ L, e ∈ C.edges) := by
  intro F
  induction hn : F.card using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    intro hF
    rcases F.eq_empty_or_nonempty with hemp | hne
    · subst hemp
      exact ⟨[], by simp, by simp, by simp⟩
    · obtain ⟨D, hDne, hDsub, hDe, hDmin⟩ := G.exists_minimal_even_subset hne hF
      -- Package the extracted minimal even set as a Cycle.
      let C : G.Cycle := ⟨D, hDne, hDe, hDmin⟩
      -- Recurse on F \ D, which is even and strictly smaller.
      have hsub : F \ D ⊆ F := Finset.sdiff_subset
      have hcard : (F \ D).card < F.card := by
        apply Finset.card_lt_card
        refine ⟨hsub, ?_⟩
        intro hcon
        obtain ⟨x, hx⟩ := hDne
        have hxFD : x ∈ F \ D := hcon (hDsub hx)
        rw [Finset.mem_sdiff] at hxFD
        exact hxFD.2 hx
      have hFDeven : G.IsEvenEdgeSet (F \ D) := IsEvenEdgeSet.sdiff G hF hDsub hDe
      obtain ⟨L, hLsub, hLpair, hLcover⟩ := ih (F \ D).card (hn ▸ hcard) (F \ D) rfl hFDeven
      refine ⟨C :: L, ?_, ?_, ?_⟩
      · -- every listed cycle's edges ⊆ F
        intro C' hC'
        rcases List.mem_cons.mp hC' with h | h
        · subst h; exact hDsub
        · exact (hLsub C' h).trans hsub
      · -- pairwise disjoint
        rw [List.pairwise_cons]
        refine ⟨?_, hLpair⟩
        intro C' hC'
        -- C.edges = D is disjoint from C'.edges ⊆ F \ D
        have hC'sub : C'.edges ⊆ F \ D := hLsub C' hC'
        rw [Finset.disjoint_left]
        intro a haD haC'
        have haFD : a ∈ F \ D := hC'sub haC'
        rw [Finset.mem_sdiff] at haFD
        exact haFD.2 haD
      · -- coverage
        intro e
        constructor
        · intro heF
          by_cases heD : e ∈ D
          · exact ⟨C, List.mem_cons_self, heD⟩
          · have heFD : e ∈ F \ D := Finset.mem_sdiff.mpr ⟨heF, heD⟩
            obtain ⟨C', hC'mem, hC'e⟩ := (hLcover e).mp heFD
            exact ⟨C', List.mem_cons_of_mem _ hC'mem, hC'e⟩
        · rintro ⟨C', hC'mem, hC'e⟩
          rcases List.mem_cons.mp hC'mem with h | h
          · subst h; exact hDsub hC'e
          · exact hsub ((hLsub C' h) hC'e)

end FiniteGraph

end CycleDoubleCover
