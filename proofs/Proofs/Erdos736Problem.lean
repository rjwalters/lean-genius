/-
Erdős Problem #736: Chromatic Numbers and Finite Subgraph Inheritance

Source: https://erdosproblems.com/736
Status: OPEN (consistency results known)

Statement:
Let G be a graph with chromatic number ℵ₁. Is there, for every cardinal m,
some graph G_m of chromatic number m such that every finite subgraph of G_m
is a subgraph of G?

Background:
This is a conjecture of Walter Taylor. It asks whether a graph with high
chromatic number "contains" enough finite structure to support graphs of
arbitrarily high chromatic number built from those finite pieces.

More generally, Erdős asks to characterize families F_α of finite graphs
such that there exists a graph of chromatic number ℵ_α with all finite
subgraphs in F_α.

Known Results (Komjáth-Shelah, 2005):
It is consistent with ZFC that the answer is NO. There exists (in some models)
a graph G with χ(G) = ℵ₁ such that if H is any graph whose finite subgraphs
are all subgraphs of G, then χ(H) ≤ ℵ₂.

References:
- Walter Taylor (original conjecture)
- [KoSh05] Komjáth, Péter and Shelah, Saharon, "Finite subgraphs of
  uncountably chromatic graphs", J. Graph Theory (2005), 28-38.

Tags: graph-theory, chromatic-number, infinite-graphs, set-theory
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Finsubgraph
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

open Cardinal SimpleGraph

namespace Erdos736

/-
## Part I: Basic Definitions
-/

/--
**Chromatic number of a simple graph:**
The minimum number of colors needed to properly color the vertices.

We fix the vertex universe to `Type` (i.e. `Type 0`) and the color universe to
`Type`/`Cardinal.{0}`. This is no loss of generality: `Type 0` already contains
types of every cardinality relevant here (ℵ₁, ℵ₂, …), and any proper coloring can
be taken to use at most `#V` colors, so the infimum is unchanged. Pinning the
universe also keeps the cardinal-valued statements below free of universe
metavariables.
-/
noncomputable def chromaticNumber (V : Type) (G : SimpleGraph V) : Cardinal.{0} :=
  sInf { κ : Cardinal.{0} | ∃ (α : Type), #α = κ ∧ Nonempty (G.Coloring α) }

/--
**Finite subgraph:**
A subgraph supported on a finite set of vertices.
-/
def isFiniteSubgraph {V : Type*} (G : SimpleGraph V) (H : Subgraph G) : Prop :=
  H.verts.Finite

/--
**Subgraph embedding:**
H is isomorphic to a subgraph of G.
-/
def isSubgraphOf {V W : Type*} (H : SimpleGraph V) (G : SimpleGraph W) : Prop :=
  ∃ (f : V → W), Function.Injective f ∧
    ∀ v₁ v₂ : V, H.Adj v₁ v₂ → G.Adj (f v₁) (f v₂)

/--
**Finite subgraph class:**
The class of all finite subgraphs of a graph G.
-/
def finiteSubgraphClass {V : Type*} (G : SimpleGraph V) :
    Set (Σ (n : ℕ), SimpleGraph (Fin n)) :=
  { ⟨n, H⟩ | ∃ (S : Finset V) (e : S ≃ Fin n),
    ∀ i j : Fin n, H.Adj i j ↔ G.Adj (e.symm i) (e.symm j) }

/-
## Part II: The Taylor Conjecture
-/

/--
**Walter Taylor's Conjecture:**
If G has chromatic number ℵ₁, then for every cardinal m, there exists
a graph G_m with χ(G_m) = m whose finite subgraphs are all subgraphs of G.
-/
def TaylorConjecture : Prop :=
  ∀ (V : Type) (G : SimpleGraph V),
    chromaticNumber V G = aleph 1 →
    ∀ (m : Cardinal.{0}),
      ∃ (W : Type) (H : SimpleGraph W),
        chromaticNumber W H = m ∧
        ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
          isSubgraphOf F H → isSubgraphOf F G

/--
**Generalized Taylor Conjecture:**
Same as above but for any uncountable cardinal κ.
-/
def GeneralizedTaylorConjecture : Prop :=
  ∀ (κ : Cardinal.{0}), Cardinal.IsRegular κ → κ > aleph 0 →
    ∀ (V : Type) (G : SimpleGraph V),
      chromaticNumber V G = κ →
      ∀ (m : Cardinal.{0}),
        ∃ (W : Type) (H : SimpleGraph W),
          chromaticNumber W H = m ∧
          ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
            isSubgraphOf F H → isSubgraphOf F G

/-
## Part III: Erdős's General Question
-/

/--
**Family of finite graphs:**
A set of finite graphs (represented as graphs on Fin n for various n).
-/
def FiniteGraphFamily := Set (Σ (n : ℕ), SimpleGraph (Fin n))

/--
**Realizing a family at cardinal ℵ_α:**
A family F is realizable at ℵ_α if there exists a graph G with
χ(G) = ℵ_α and all finite subgraphs of G are in F.
-/
def realizableAt (F : FiniteGraphFamily) (α : Ordinal.{0}) : Prop :=
  ∃ (V : Type) (G : SimpleGraph V),
    chromaticNumber V G = aleph α ∧
    finiteSubgraphClass G ⊆ F

/--
**Erdős's General Question:**
Characterize which families F_α of finite graphs are realizable at ℵ_α.
-/
def ErdosGeneralQuestion : Prop :=
  ∃ (characterization : FiniteGraphFamily → Ordinal.{0} → Prop),
    ∀ (F : FiniteGraphFamily) (α : Ordinal.{0}),
      characterization F α ↔ realizableAt F α

/-
## Part IV: The Komjáth-Shelah Consistency Result
-/

/-
**Komjáth-Shelah (2005):**
It is consistent with ZFC that there exists a graph G with χ(G) = ℵ₁
such that any graph H whose finite subgraphs are all subgraphs of G
satisfies χ(H) ≤ ℵ₂.

**The conjecture is independent:**
Taylor's conjecture cannot be decided in ZFC alone.
-/
/-
## Part V: Related Concepts
-/

/--
**De Bruijn–Erdős theorem (coloring/compactness version):**
If every finite (induced) subgraph of `G` is `n`-colorable, then `G` itself is
`n`-colorable. This is the graph-coloring form of the compactness principle and
genuinely requires the axiom of choice (here packaged via Mathlib's inverse-limit
argument `nonempty_hom_of_forall_finite_subgraph_hom`).

This is the key piece of infrastructure underlying the "finite subgraph
inheritance" theme of Erdős #736: the chromatic number of an infinite graph is
controlled by its finite subgraphs. It is fully machine-checked; the only
foundational dependency beyond the usual `propext`/`Quot.sound` is
`Classical.choice`.
-/
theorem deBruijn_erdos_coloring {V : Type*} (G : SimpleGraph V) (n : ℕ)
    (h : ∀ G' : G.Subgraph, G'.verts.Finite → G'.coe.Colorable n) :
    G.Colorable n := by
  -- `Colorable n` unfolds to `Nonempty (G →g completeGraph (Fin n))`; apply
  -- compactness with the finite target graph `completeGraph (Fin n)`.
  apply SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom
  intro G' hfin
  exact (h G' hfin).some

/--
**De Bruijn–Erdős theorem (contrapositive form):**
If `G` is *not* `n`-colorable, then some *finite* subgraph of `G` is already not
`n`-colorable. Equivalently, the chromatic number of an infinite graph is the
supremum of the chromatic numbers of its finite subgraphs.

This is the form of the theorem most directly relevant to Erdős #736: it says the
obstruction to a small coloring always lives in a finite part of the graph, so the
"finite subgraph inheritance" behaviour of chromatic number is genuine. It is a
short, fully machine-checked consequence of `deBruijn_erdos_coloring`.
-/
theorem exists_finite_subgraph_not_colorable {V : Type*} (G : SimpleGraph V) (n : ℕ)
    (h : ¬ G.Colorable n) :
    ∃ G' : G.Subgraph, G'.verts.Finite ∧ ¬ G'.coe.Colorable n := by
  by_contra hcon
  push_neg at hcon
  exact h (deBruijn_erdos_coloring G n hcon)

/-
**Compactness in graph coloring:**
The chromatic number of a graph is determined by its finite subgraphs
in a limiting sense.

**Chromatic number and cardinal arithmetic:**
For infinite graphs, chromatic number interacts with cardinal arithmetic.
-/
/-
## Part VI: Special Cases
-/

/-
**Countable chromatic number:**
For graphs with χ(G) = ℵ₀, the Taylor question is easier.
-/
/-
## Part VII: A discrete intermediate-value theorem for chromatic number

The `finite_case` below needs: in a graph of (finite) chromatic number `k`, every
value `m ≤ k` is attained as the chromatic number of an induced subgraph.  The
underlying fact is the **discrete intermediate-value principle** for vertex
deletion: removing one vertex lowers the chromatic number by at most one, so the
value passes through every integer between `k` and `0` on the way down to the empty
graph.

We phrase everything with `Finset` of vertices and Mathlib's `ℕ`-valued
`Colorable`, which keeps every induced subgraph of the form `G.induce ↑(finset)`
over the *fixed* ambient vertex type — no subtype-of-subtype juggling — and then
bridge back to the file's custom `Cardinal`-valued `chromaticNumber`.
-/

/--
**One extra vertex costs at most one extra color.**
From a `c`-coloring of the subgraph induced on `s` we build a `(c+1)`-coloring of
the subgraph induced on `insert v s`, giving the new vertex `v` a fresh color
(`none`) and keeping the old colors (`some ·`) elsewhere.
-/
theorem colorable_insert {W : Type*} [DecidableEq W] (H : SimpleGraph W)
    (s : Finset W) (v : W) {c : ℕ}
    (hc : (H.induce (↑s : Set W)).Colorable c) :
    (H.induce (↑(insert v s) : Set W)).Colorable (c + 1) := by
  classical
  obtain ⟨C⟩ := hc
  have Cnew : (H.induce (↑(insert v s) : Set W)).Coloring (Option (Fin c)) := by
    refine Coloring.mk
      (fun x => if hx : (x : W) ∈ s then some (C ⟨(x : W), Finset.mem_coe.mpr hx⟩) else none) ?_
    intro a b hab
    have hadj : H.Adj (a : W) (b : W) := hab
    split_ifs with ha hb hb
    · simp only [ne_eq, Option.some.injEq]
      exact C.valid hadj
    · exact Option.some_ne_none _
    · exact fun h => Option.some_ne_none _ h.symm
    · exfalso
      have ea : (a : W) = v := by
        have h2 := a.2
        rw [Finset.coe_insert, Set.mem_insert_iff] at h2
        rcases h2 with h | h
        · exact h
        · exact absurd (Finset.mem_coe.mp h) ha
      have eb : (b : W) = v := by
        have h2 := b.2
        rw [Finset.coe_insert, Set.mem_insert_iff] at h2
        rcases h2 with h | h
        · exact h
        · exact absurd (Finset.mem_coe.mp h) hb
      rw [ea, eb] at hadj
      exact H.irrefl hadj
  have hcol := Cnew.colorable
  rwa [Fintype.card_option, Fintype.card_fin] at hcol

/--
**Finset form of the contrapositive de Bruijn–Erdős theorem.**
If `G` is not `n`-colorable, some *finite induced* subgraph `G.induce ↑s`
(for a `Finset s` of vertices) is already not `n`-colorable.
-/
theorem exists_finset_induce_not_colorable {V : Type*} (G : SimpleGraph V) (n : ℕ)
    (h : ¬ G.Colorable n) :
    ∃ s : Finset V, ¬ (G.induce (↑s : Set V)).Colorable n := by
  classical
  obtain ⟨G', hfin, hG'⟩ := exists_finite_subgraph_not_colorable G n h
  refine ⟨hfin.toFinset, fun hcol => hG' ?_⟩
  rw [hfin.coe_toFinset] at hcol
  refine hcol.mono_left ?_
  intro u w huw
  exact G'.coe_adj_sub u w huw

/--
**Sharp finite obstruction.**
From the Mathlib characterization of "chromatic number exactly `k`"
(`Colorable k` together with non-colorability below `k`) we extract a *finite*
induced subgraph `G.induce ↑s` with the very same chromatic number `k`.
-/
theorem exists_obstruction {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hk : G.Colorable k) (hsharp : ∀ j < k, ¬ G.Colorable j) :
    ∃ s : Finset V, (G.induce (↑s : Set V)).Colorable k ∧
      ∀ j < k, ¬ (G.induce (↑s : Set V)).Colorable j := by
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · refine ⟨∅, ?_, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    haveI : IsEmpty (↥((↑(∅ : Finset V)) : Set V)) := by
      rw [Finset.coe_empty]; infer_instance
    exact (G.induce _).colorable_of_isEmpty 0
  · obtain ⟨s, hs⟩ := exists_finset_induce_not_colorable G (k - 1) (hsharp (k - 1) (by omega))
    refine ⟨s, ?_, fun j hj hcolj => hs (hcolj.mono (by omega))⟩
    exact Colorable.of_hom (⟨Subtype.val, fun {a b} h => h⟩ : (G.induce (↑s : Set V)) →g G) hk

/--
**Discrete intermediate-value theorem.**
If the subgraph induced on a finite set `s` has chromatic number exactly `c`, then
for every `m ≤ c` there is a subset `t ⊆ s` whose induced subgraph has chromatic
number exactly `m`.  Proof: strong induction on `s.card`; if `m < c`, delete any
vertex `v ∈ s` — by `colorable_insert` this drops the chromatic number by at most
one, so the induced subgraph on `s.erase v` still has chromatic number `≥ m`, and
the induction hypothesis applies.
-/
theorem ivt_finset {W : Type} [DecidableEq W] (H : SimpleGraph W) :
    ∀ (s : Finset W) (c m : ℕ), (H.induce (↑s : Set W)).Colorable c →
      (∀ j < c, ¬ (H.induce (↑s : Set W)).Colorable j) → m ≤ c →
      ∃ t ⊆ s, (H.induce (↑t : Set W)).Colorable m ∧
        ∀ j < m, ¬ (H.induce (↑t : Set W)).Colorable j := by
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro c m hc hsharp hm
    rcases eq_or_lt_of_le hm with rfl | hlt
    · exact ⟨s, Finset.Subset.refl s, hc, hsharp⟩
    · have hcpos : 0 < c := lt_of_le_of_lt (Nat.zero_le m) hlt
      have hne : s.Nonempty := by
        rcases s.eq_empty_or_nonempty with rfl | h
        · exfalso
          apply hsharp 0 hcpos
          haveI : IsEmpty (↥((↑(∅ : Finset W)) : Set W)) := by
            rw [Finset.coe_empty]; infer_instance
          exact (H.induce _).colorable_of_isEmpty 0
        · exact h
      obtain ⟨v, hv⟩ := hne
      have hss' : s.erase v ⊂ s := Finset.erase_ssubset hv
      classical
      have hcolex : ∃ n, (H.induce (↑(s.erase v) : Set W)).Colorable n :=
        ⟨_, (H.induce _).colorable_of_fintype⟩
      obtain ⟨c', hc'spec, hc'min⟩ :
          ∃ c', (H.induce (↑(s.erase v) : Set W)).Colorable c' ∧
            ∀ j < c', ¬ (H.induce (↑(s.erase v) : Set W)).Colorable j :=
        ⟨Nat.find hcolex, Nat.find_spec hcolex, fun j hj => Nat.find_min hcolex hj⟩
      have hstep : (H.induce (↑s : Set W)).Colorable (c' + 1) := by
        have h := colorable_insert H (s.erase v) v hc'spec
        rwa [Finset.insert_erase hv] at h
      have hcle : c ≤ c' + 1 := by
        by_contra hcon
        push_neg at hcon
        exact hsharp (c' + 1) hcon hstep
      have hmc' : m ≤ c' := by omega
      obtain ⟨t, hts, htcol, htsharp⟩ := ih (s.erase v) hss' c' m hc'spec hc'min hmc'
      exact ⟨t, hts.trans (Finset.erase_subset v s), htcol, htsharp⟩

/--
**Bridge (custom ⇐ Mathlib).**
For a finite Mathlib characterization of "chromatic number exactly `m`", the file's
custom `Cardinal`-valued `chromaticNumber` equals `(m : Cardinal)`.
-/
theorem custom_chromatic_eq {W : Type} (H : SimpleGraph W) (m : ℕ)
    (hpos : H.Colorable m) (hneg : ∀ j < m, ¬ H.Colorable j) :
    chromaticNumber W H = (m : Cardinal) := by
  classical
  unfold chromaticNumber
  apply le_antisymm
  · apply csInf_le (OrderBot.bddBelow _)
    exact ⟨Fin m, Cardinal.mk_fin m, hpos⟩
  · apply le_csInf ⟨(m : Cardinal), Fin m, Cardinal.mk_fin m, hpos⟩
    rintro κ ⟨α, rfl, ⟨C⟩⟩
    by_contra hlt
    push_neg at hlt
    have hfin : Finite α :=
      Cardinal.lt_aleph0_iff_finite.mp (lt_trans hlt (Cardinal.nat_lt_aleph0 m))
    haveI : Fintype α := Fintype.ofFinite α
    rw [Cardinal.mk_fintype α] at hlt
    have hlt' : Fintype.card α < m := by exact_mod_cast hlt
    exact hneg (Fintype.card α) hlt' C.colorable

/--
**Bridge (custom ⇒ Mathlib).**
If the file's custom `Cardinal`-valued `chromaticNumber` of `H` is the natural
number `k`, then `H` is `k`-colorable but not `j`-colorable for any `j < k`.
-/
theorem colorable_of_custom {W : Type} (H : SimpleGraph W) (k : ℕ)
    (h : chromaticNumber W H = (k : Cardinal)) :
    H.Colorable k ∧ ∀ j < k, ¬ H.Colorable j := by
  classical
  unfold chromaticNumber at h
  set S : Set Cardinal.{0} :=
    { κ : Cardinal.{0} | ∃ (α : Type), #α = κ ∧ Nonempty (H.Coloring α) } with hS
  have hSne : S.Nonempty := ⟨#W, W, rfl, ⟨H.selfColoring⟩⟩
  have hmem : sInf S ∈ S := csInf_mem hSne
  refine ⟨?_, ?_⟩
  · rw [h] at hmem
    obtain ⟨α, hα, ⟨C⟩⟩ := hmem
    rw [← Cardinal.mk_fin k] at hα
    obtain ⟨e⟩ := Cardinal.eq.mp hα
    exact ⟨Coloring.mk (fun v => e (C v))
      (fun {a b} hab heq => C.valid hab (e.injective heq))⟩
  · intro j hj hcolj
    have hjmem : (j : Cardinal) ∈ S := ⟨Fin j, Cardinal.mk_fin j, hcolj⟩
    have hle : sInf S ≤ (j : Cardinal) := csInf_le (OrderBot.bddBelow _) hjmem
    rw [h] at hle
    have : k ≤ j := by exact_mod_cast hle
    omega

/--
**Finite case (now fully proved).**
For finite chromatic number `k`, every value `m ≤ k` is realized *as an induced
subgraph of `G`*, so the finite-subgraph inheritance is automatic: the witness `H`
is an induced subgraph of `G`, hence every finite subgraph of `H` is a finite
subgraph of `G` for free, and an induced subgraph of chromatic number exactly `m`
exists by the discrete intermediate-value principle (`ivt_finset`).

This discharges the side lemma that was previously `sorry`; it is a self-contained
result and **not** part of the open Taylor/Erdős conjecture itself.
-/
theorem finite_case (V : Type) (G : SimpleGraph V) (k : ℕ) :
    chromaticNumber V G = k →
    ∀ m ≤ k, ∃ (W : Type) (H : SimpleGraph W),
      chromaticNumber W H = m ∧
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
        isSubgraphOf F H → isSubgraphOf F G := by
  classical
  intro hk m hm
  obtain ⟨hGcol, hGsharp⟩ := colorable_of_custom G k hk
  obtain ⟨s, hscol, hssharp⟩ := exists_obstruction G k hGcol hGsharp
  obtain ⟨t, _hts, htcol, htsharp⟩ := ivt_finset G s k m hscol hssharp hm
  refine ⟨_, G.induce (↑t : Set V), ?_, ?_⟩
  · exact custom_chromatic_eq (G.induce (↑t : Set V)) m htcol htsharp
  · intro n F hF
    obtain ⟨f, hfinj, hfadj⟩ := hF
    refine ⟨fun i => (f i : V), ?_, ?_⟩
    · intro i j hij
      exact hfinj (Subtype.ext hij)
    · intro v₁ v₂ hadj
      exact hfadj v₁ v₂ hadj

end Erdos736
