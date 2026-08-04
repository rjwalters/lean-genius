import Proofs.CycleDoubleCoverPort.GeneralGraph
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.CharP.Two

/-
# Cycle Double Cover port, step 1b: even edge sets decompose into cycles

Second slice of the openai/cdc-lean port (see #37507). Corresponds to upstream
`CDCLean/CycleDecomposition.lean`.

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies and
no proof text may be vendored. This file is an *independent re-derivation*: the
upstream source was consulted only for the mathematical content — the shapes of
the definitions and the statements of the results — and every proof script here
was written from scratch against this repository's Mathlib pin. In particular
the main induction below is run on a natural-number size bound rather than on
`Finset.strongInductionOn`.

## Mathematical content

A *cycle* of a loopless multigraph is a nonempty inclusion-minimal even edge
set — the graphic-matroid notion of a circuit, which handles multigraphs
gracefully because edges rather than vertex pairs are the primitive objects.
Two facts are established:

* `decompose_even_edge_set`: every even edge set is an edge-disjoint union of
  cycles. The argument is purely finite — repeatedly split off a minimal
  nonempty even subset; characteristic two keeps the remainder even — so no
  Euler-tour construction and no external graph theory is smuggled in. The
  conclusion is stated with exact multiplicities (each edge covered exactly
  once), which is stronger than equality of unions and is what the double-cover
  bookkeeping downstream needs.
* `IndexedEvenDoubleCover.toCycleDoubleCover`: an exact even double cover
  indexed by the eight elements of `Gamma` flattens into a conventional
  `CycleDoubleCover`.

All definitions extend the namespace of `Proofs/CycleDoubleCover.lean`, so
`Cycle` and `CycleDoubleCover` here are literally the ones appearing in the
statement of the (still undischarged) `cycleDoubleCover_of_bridgeless` axiom.
-/

namespace CycleDoubleCover

namespace FiniteGraph

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : FiniteGraph V E)

/-- The ordinary natural-number degree of `v` inside an edge set. Edge ends are
counted, so parallel edges and the two ends of a single edge contribute
separately, as they should for multigraphs. -/
def degreeIn (F : Finset E) (v : V) : ℕ :=
  ((F ×ˢ (Finset.univ : Finset (Fin 2))).filter fun h => G.endAt h.1 h.2 = v).card

/-- Two edge objects are parallel when they carry the same unordered pair of
ends. -/
def AreParallel (e f : E) : Prop :=
  (G.endAt e 0 = G.endAt f 0 ∧ G.endAt e 1 = G.endAt f 1) ∨
    (G.endAt e 0 = G.endAt f 1 ∧ G.endAt e 1 = G.endAt f 0)

/-- Two distinct parallel edge objects form the length-two multigraph cycle.
This is the smallest cycle available, by `cycle_card_ge_two`. -/
def parallelPairCycle (e f : E) (hef : e ≠ f) (hpar : G.AreParallel e f) : G.Cycle where
  edges := {e, f}
  nonempty := ⟨e, Finset.mem_insert_self _ _⟩
  even := by
    intro v
    rw [Finset.sum_pair hef]
    have hEq : G.edgeIncidence v e = G.edgeIncidence v f := by
      rcases hpar with ⟨h0, h1⟩ | ⟨h0, h1⟩
      · simp only [edgeIncidence, h0, h1]
      · simp only [edgeIncidence, h0, h1]
        ring
    rw [hEq]
    exact CharTwo.add_self_eq_zero _
  minimal := by
    intro D hDne hDsub hDeven
    refine Finset.eq_of_subset_of_card_le hDsub ?_
    rw [Finset.card_pair hef]
    by_contra hlt
    push Not at hlt
    have h01 : D.card = 0 ∨ D.card = 1 := by omega
    rcases h01 with h0 | h1
    · exact hDne.ne_empty (Finset.card_eq_zero.mp h0)
    · obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      exact _root_.CycleDoubleCover.singleton_not_even G x (hx ▸ hDeven)

/-- Removing an even subset from an even edge set leaves an even edge set:
over `F₂` the incidence sums simply subtract. -/
theorem isEvenEdgeSet_sdiff {F D : Finset E} (hDF : D ⊆ F)
    (hF : G.IsEvenEdgeSet F) (hD : G.IsEvenEdgeSet D) :
    G.IsEvenEdgeSet (F \ D) := by
  intro v
  have hsplit : (∑ e ∈ F \ D, G.edgeIncidence v e) + ∑ e ∈ D, G.edgeIncidence v e
      = ∑ e ∈ F, G.edgeIncidence v e := Finset.sum_sdiff hDF
  rw [hD v, hF v, add_zero] at hsplit
  exact hsplit

/-- Size-bounded engine for `decompose_even_edge_set`. Induction is on the
natural-number bound `n`, not on the `Finset` order, so the two recursive calls
(the minimal even subset and its complement) only need a cardinality estimate. -/
private theorem decompose_aux :
    ∀ (n : ℕ) (F : Finset E), F.card ≤ n → G.IsEvenEdgeSet F →
      ∃ L : List G.Cycle,
        ∀ e : E, (L.filter fun C => e ∈ C.edges).length = if e ∈ F then 1 else 0 := by
  classical
  intro n
  induction n with
  | zero =>
    intro F hcard _
    have hF : F = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
    exact ⟨[], by simp [hF]⟩
  | succ n ih =>
    intro F hcard hF
    by_cases hne : F.Nonempty
    · by_cases hmin : ∀ D : Finset E, D.Nonempty → D ⊆ F → G.IsEvenEdgeSet D → D = F
      · refine ⟨[⟨F, hne, hF, hmin⟩], fun e => ?_⟩
        by_cases he : e ∈ F <;> simp [he]
      · push Not at hmin
        obtain ⟨D, hDne, hDsub, hDeven, hDprop⟩ := hmin
        have hDss : D ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨hDsub, hDprop⟩
        have hDcard : D.card ≤ n := by
          have := Finset.card_lt_card hDss
          omega
        have hRss : F \ D ⊂ F := by
          refine (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ?_
          obtain ⟨x, hx⟩ := hDne
          exact ⟨x, hDsub hx, by simp [Finset.mem_sdiff, hx]⟩
        have hRcard : (F \ D).card ≤ n := by
          have := Finset.card_lt_card hRss
          omega
        obtain ⟨LD, hLD⟩ := ih D hDcard hDeven
        obtain ⟨LR, hLR⟩ := ih (F \ D) hRcard (G.isEvenEdgeSet_sdiff hDsub hF hDeven)
        refine ⟨LD ++ LR, fun e => ?_⟩
        rw [List.filter_append, List.length_append, hLD e, hLR e]
        by_cases heD : e ∈ D
        · simp [heD, hDsub heD, Finset.mem_sdiff]
        · by_cases heF : e ∈ F <;> simp [heD, heF, Finset.mem_sdiff]
    · have hF0 : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      exact ⟨[], by simp [hF0]⟩

/-- Every finite even edge set is an edge-disjoint union of multigraph cycles.
The multiplicity form recorded here — each edge of `F` lies in exactly one
listed cycle, each edge outside `F` in none — is strictly stronger than
equality of unions, and is what the double-cover count downstream consumes. -/
theorem decompose_even_edge_set (F : Finset E) (hF : G.IsEvenEdgeSet F) :
    ∃ L : List G.Cycle,
      ∀ e : E, (L.filter fun C => e ∈ C.edges).length = if e ∈ F then 1 else 0 :=
  G.decompose_aux F.card F le_rfl hF

/-- In `F₂` there are only the two obvious elements. -/
private theorem f2_eq_zero_or_one (x : F₂) : x = 0 ∨ x = 1 := by
  revert x
  decide

namespace IndexedEvenDoubleCover

variable {G}

/-- The edge set selected by one of the eight members of an indexed even double
cover. -/
def support (C : G.IndexedEvenDoubleCover) (s : Gamma) : Finset E :=
  Finset.univ.filter fun e => C.member s e = 1

omit [DecidableEq E] in
theorem mem_support {C : G.IndexedEvenDoubleCover} {s : Gamma} {e : E} :
    e ∈ C.support s ↔ C.member s e = 1 := by
  simp [support]

omit [DecidableEq E] in
/-- Each of the eight selected edge sets is even, because the `F₂`-indicator of
membership agrees with the incidence contribution edge by edge. -/
theorem support_even (C : G.IndexedEvenDoubleCover) (s : Gamma) :
    G.IsEvenEdgeSet (C.support s) := by
  classical
  intro v
  have hpt : ∀ e : E, (if C.member s e = 1 then G.edgeIncidence v e else 0)
      = ((if G.endAt e 0 = v then C.member s e else 0) +
         (if G.endAt e 1 = v then C.member s e else 0)) := by
    intro e
    rcases f2_eq_zero_or_one (C.member s e) with h0 | h1
    · simp [h0]
    · simp [h1, edgeIncidence]
  rw [support, Finset.sum_filter]
  calc ∑ e : E, (if C.member s e = 1 then G.edgeIncidence v e else 0)
      = ∑ e : E, ((if G.endAt e 0 = v then C.member s e else 0) +
          (if G.endAt e 1 = v then C.member s e else 0)) :=
        Finset.sum_congr rfl fun e _ => hpt e
    _ = 0 := C.vertexEven s v

/-- An exact indexed even double cover flattens into a conventional cycle
double cover: decompose each of the eight even sets into cycles, concatenate,
and read off the multiplicity two from `coveredTwice`. -/
noncomputable def toCycleDoubleCover (C : G.IndexedEvenDoubleCover) :
    G.CycleDoubleCover := by
  classical
  choose pieces hpieces using fun s : Gamma =>
    G.decompose_even_edge_set (C.support s) (C.support_even s)
  refine ⟨(Finset.univ : Finset Gamma).toList.flatMap pieces, fun e => ?_⟩
  have hcard := C.coveredTwice e
  rw [Finset.card_filter] at hcard
  rw [List.filter_flatMap, List.length_flatMap, Finset.sum_map_toList]
  simp_rw [hpieces]
  refine Eq.trans ?_ hcard
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases h : C.member s e = 1 <;> simp [mem_support, h]

end IndexedEvenDoubleCover

/-- Statement-drift guard, machine-checked. The object produced by the ported
machinery inhabits *exactly* the type `Nonempty G.CycleDoubleCover` that forms
the conclusion of `CycleDoubleCover.cycleDoubleCover_of_bridgeless` in
`Proofs/CycleDoubleCover.lean`. Since this file extends that namespace rather
than restating it, no equivalence bridge is required: `G.CycleDoubleCover` here
and in the axiom are the same declaration.

The remaining work for the epic is therefore exactly to produce a
`G.IndexedEvenDoubleCover` from `G.Bridgeless` — that is the 8-flow route and
the novel labelling argument of upstream steps 2-7. -/
theorem nonempty_cycleDoubleCover_of_indexedEvenDoubleCover
    (C : G.IndexedEvenDoubleCover) : Nonempty G.CycleDoubleCover :=
  ⟨C.toCycleDoubleCover⟩

end FiniteGraph

end CycleDoubleCover
