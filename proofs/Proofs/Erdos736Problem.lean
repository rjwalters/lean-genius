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

/-!
### Discharging the finite case

The remaining ingredient for `finite_case` (below) is a *discrete intermediate value
theorem* for chromatic number: in a finite graph of chromatic number `k`, every value
`m ≤ k` is realized exactly by an induced subgraph. Adding one vertex changes the
chromatic number by at most one, so the value passes through every integer between
`0` and `k`.

We first bridge the custom `Cardinal`-valued `chromaticNumber` to Mathlib's
`SimpleGraph.Colorable` predicate (valid because the cardinals are well-ordered, so the
defining infimum is attained), then run the intermediate-value argument with a
natural-number chromatic number `chiN` for finite induced subgraphs.
-/

/-- The set defining `chromaticNumber` is always nonempty: the identity function is a
proper coloring of `G` with `#V` colors. -/
theorem chromSet_nonempty (V : Type) (G : SimpleGraph V) :
    { κ : Cardinal.{0} | ∃ (α : Type), #α = κ ∧ Nonempty (G.Coloring α) }.Nonempty :=
  ⟨#V, V, rfl, ⟨G.selfColoring⟩⟩

/-- **Bridge (⇐).** If `G` is `m`-colorable but not `j`-colorable for any `j < m`, then the
custom cardinal-valued chromatic number is exactly `m`. -/
theorem chromaticNumber_eq_of_colorable (V : Type) (G : SimpleGraph V) (m : ℕ)
    (hcol : G.Colorable m) (hmin : ∀ j < m, ¬ G.Colorable j) :
    chromaticNumber V G = (m : Cardinal.{0}) := by
  apply le_antisymm
  · apply csInf_le (OrderBot.bddBelow _)
    exact ⟨Fin m, by simp, hcol⟩
  · apply le_csInf (chromSet_nonempty V G)
    rintro κ ⟨α, rfl, ⟨C⟩⟩
    by_contra hlt
    push_neg at hlt
    have hfin : #α < ℵ₀ := lt_of_lt_of_le hlt (by exact_mod_cast (nat_lt_aleph0 m).le)
    have : Finite α := lt_aleph0_iff_finite.mp hfin
    have := Fintype.ofFinite α
    have hcolα : G.Colorable (Fintype.card α) := C.colorable
    have hcard : (Fintype.card α : Cardinal.{0}) = #α := by simp [Cardinal.mk_fintype]
    have : (Fintype.card α : Cardinal.{0}) < (m : Cardinal.{0}) := by rw [hcard]; exact hlt
    have hjm : Fintype.card α < m := by exact_mod_cast this
    exact hmin _ hjm hcolα

/-- **Bridge (⇒, colorability).** If the custom chromatic number equals the natural number
`k`, then `G` is `k`-colorable. The cardinals are well-ordered, so the defining infimum is
attained and is realized by some color type of cardinality `k`. -/
theorem colorable_of_chromaticNumber_eq (V : Type) (G : SimpleGraph V) (k : ℕ)
    (h : chromaticNumber V G = (k : Cardinal.{0})) : G.Colorable k := by
  have h' : sInf { κ : Cardinal.{0} | ∃ (α : Type), #α = κ ∧ Nonempty (G.Coloring α) } =
      (k : Cardinal.{0}) := h
  have hmem : sInf { κ : Cardinal.{0} | ∃ (α : Type), #α = κ ∧ Nonempty (G.Coloring α) } ∈
      { κ : Cardinal.{0} | ∃ (α : Type), #α = κ ∧ Nonempty (G.Coloring α) } :=
    csInf_mem (chromSet_nonempty V G)
  rw [h'] at hmem
  obtain ⟨α, hα, ⟨C⟩⟩ := hmem
  have : #α = #(Fin k) := by rw [hα]; simp
  obtain ⟨e⟩ := Cardinal.eq.mp this
  exact ⟨Coloring.mk (fun v => e (C v)) (fun {v w} hvw => by
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]; exact C.valid hvw)⟩

/-- **Bridge (⇒, minimality).** If the custom chromatic number equals `k`, then `G` is not
`j`-colorable for any `j < k`. -/
theorem not_colorable_of_chromaticNumber_eq (V : Type) (G : SimpleGraph V) (k : ℕ)
    (h : chromaticNumber V G = (k : Cardinal.{0})) :
    ∀ j < k, ¬ G.Colorable j := by
  intro j hjk hcol
  have h' : sInf { κ : Cardinal.{0} | ∃ (α : Type), #α = κ ∧ Nonempty (G.Coloring α) } =
      (k : Cardinal.{0}) := h
  have hle : sInf { κ : Cardinal.{0} | ∃ (α : Type), #α = κ ∧ Nonempty (G.Coloring α) } ≤
      (j : Cardinal.{0}) :=
    csInf_le (OrderBot.bddBelow _) ⟨Fin j, by simp, hcol⟩
  rw [h'] at hle
  have : (k : Cardinal.{0}) ≤ (j : Cardinal.{0}) := hle
  have : k ≤ j := by exact_mod_cast this
  omega

open Classical in
/-- Natural-number chromatic number, `sInf` of the colorable numbers. Well-behaved for
finite graphs (where the set is nonempty). -/
noncomputable def chiN {V : Type*} (G : SimpleGraph V) : ℕ := sInf { n : ℕ | G.Colorable n }

theorem colorable_chiN {V : Type*} [Finite V] (G : SimpleGraph V) : G.Colorable (chiN G) := by
  have : Fintype V := Fintype.ofFinite V
  have hne : { n : ℕ | G.Colorable n }.Nonempty := ⟨Fintype.card V, colorable_of_fintype G⟩
  exact Nat.sInf_mem hne

theorem chiN_le_of_colorable {V : Type*} (G : SimpleGraph V) {n : ℕ} (h : G.Colorable n) :
    chiN G ≤ n := Nat.sInf_le h

theorem not_colorable_of_lt_chiN {V : Type*} (G : SimpleGraph V) {j : ℕ} (h : j < chiN G) :
    ¬ G.Colorable j := Nat.notMem_of_lt_sInf h

/-- Colorings restrict to induced subgraphs on smaller vertex sets. -/
theorem colorable_induce_mono {V : Type*} (G : SimpleGraph V) {s s' : Set V} (h : s ⊆ s')
    {n : ℕ} (hc : (G.induce s').Colorable n) : (G.induce s).Colorable n :=
  Colorable.of_hom (SimpleGraph.induceHomOfLE G h).toHom hc

/-- `chiN` is monotone in the induced vertex set. -/
theorem chiN_induce_mono {V : Type*} (G : SimpleGraph V) {s s' : Set V} (h : s ⊆ s')
    [Finite s'] : chiN (G.induce s) ≤ chiN (G.induce s') := by
  have : Finite s := ((Set.toFinite s').subset h).to_subtype
  exact chiN_le_of_colorable _ (colorable_induce_mono G h (colorable_chiN _))

/-- **Adding one vertex raises colorability by at most one.** Extend a coloring of the
induced subgraph on `s'` by giving the new vertex `a` a fresh color. -/
theorem colorable_induce_insert {V : Type*} (G : SimpleGraph V) (s' : Set V) (a : V) {n : ℕ}
    (hc : (G.induce s').Colorable n) : (G.induce (insert a s')).Colorable (n + 1) := by
  classical
  obtain ⟨c⟩ := hc
  refine ⟨Coloring.mk
    (fun w => if h : (w : V) ∈ s' then (c ⟨w, h⟩).castSucc else Fin.last n) ?_⟩
  intro w₁ w₂ hadj
  have hG : G.Adj (w₁ : V) (w₂ : V) := hadj
  dsimp only
  by_cases h₁ : (w₁ : V) ∈ s' <;> by_cases h₂ : (w₂ : V) ∈ s'
  · rw [dif_pos h₁, dif_pos h₂, ne_eq, Fin.castSucc_inj]
    have hadj' : (G.induce s').Adj ⟨(w₁ : V), h₁⟩ ⟨(w₂ : V), h₂⟩ := hG
    exact c.valid hadj'
  · simp only [dif_pos h₁, dif_neg h₂]
    exact (Fin.castSucc_lt_last _).ne
  · simp only [dif_neg h₁, dif_pos h₂]
    exact (Fin.castSucc_lt_last _).ne'
  · exfalso
    have e1 : (w₁ : V) = a := (Set.mem_insert_iff.mp w₁.2).resolve_right h₁
    have e2 : (w₂ : V) = a := (Set.mem_insert_iff.mp w₂.2).resolve_right h₂
    rw [e1, e2] at hG
    exact G.loopless a hG

theorem chiN_induce_insert_le {V : Type*} (G : SimpleGraph V) (s' : Set V) (a : V) [Finite s'] :
    chiN (G.induce (insert a s')) ≤ chiN (G.induce s') + 1 :=
  chiN_le_of_colorable _ (colorable_induce_insert G s' a (colorable_chiN _))

/-- **Discrete intermediate value theorem for chromatic number.**
For a finite vertex set `s`, every value `m` up to `chiN (G.induce s)` is realized
*exactly* by some induced subgraph on a subset `t ⊆ s`. Proof by induction on `s`: adding
a vertex changes the chromatic number by at most one, so all intermediate values occur. -/
theorem exists_induce_chiN_eq {V : Type*} (G : SimpleGraph V) (s : Finset V) :
    ∀ m, m ≤ chiN (G.induce (↑s : Set V)) →
      ∃ t : Finset V, t ⊆ s ∧ chiN (G.induce (↑t : Set V)) = m := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro m hm
    refine ⟨∅, subset_refl _, ?_⟩
    have h0 : chiN (G.induce (↑(∅ : Finset V) : Set V)) = 0 := by
      haveI : IsEmpty ↥(↑(∅ : Finset V) : Set V) := by rw [Finset.coe_empty]; infer_instance
      exact Nat.le_zero.mp (chiN_le_of_colorable _ (colorable_of_isEmpty _ 0))
    rw [h0] at hm ⊢; omega
  | @insert a s' ha ih =>
    intro m hm
    by_cases hm' : m ≤ chiN (G.induce (↑s' : Set V))
    · obtain ⟨t, hts, hchi⟩ := ih m hm'
      exact ⟨t, hts.trans (Finset.subset_insert a s'), hchi⟩
    · push_neg at hm'
      refine ⟨insert a s', subset_refl _, ?_⟩
      have hcoe : (↑(insert a s') : Set V) = insert a (↑s' : Set V) := Finset.coe_insert a s'
      have hle : chiN (G.induce (↑(insert a s') : Set V)) ≤ chiN (G.induce (↑s' : Set V)) + 1 := by
        rw [hcoe]; exact chiN_induce_insert_le G (↑s' : Set V) a
      have hmono : chiN (G.induce (↑s' : Set V)) ≤ chiN (G.induce (↑(insert a s') : Set V)) :=
        chiN_induce_mono G (Finset.coe_subset.mpr (Finset.subset_insert a s'))
      omega

/-- If `G` is not `n`-colorable, some finite *induced* subgraph already is not
`n`-colorable (de Bruijn–Erdős, induced form). -/
theorem exists_finite_induce_not_colorable {V : Type*} (G : SimpleGraph V) (n : ℕ)
    (h : ¬ G.Colorable n) :
    ∃ s : Finset V, ¬ (G.induce (↑s : Set V)).Colorable n := by
  obtain ⟨G', hfin, hnc⟩ := exists_finite_subgraph_not_colorable G n h
  refine ⟨hfin.toFinset, ?_⟩
  intro hcol
  rw [Set.Finite.coe_toFinset] at hcol
  exact hnc (Colorable.of_hom
    (⟨id, @fun u v hh => G'.adj_sub hh⟩ : G'.coe →g G.induce G'.verts) hcol)

/-- There is a finite induced subgraph whose chromatic number is at least `k`. -/
theorem exists_finite_chiN_ge {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (hmin : ∀ j < k, ¬ G.Colorable j) :
    ∃ s : Finset V, k ≤ chiN (G.induce (↑s : Set V)) := by
  cases k with
  | zero => exact ⟨∅, Nat.zero_le _⟩
  | succ p =>
    obtain ⟨s, hnc⟩ := exists_finite_induce_not_colorable G p (hmin p (Nat.lt_succ_self p))
    refine ⟨s, ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hnc (Colorable.mono (Nat.lt_succ_iff.mp hlt) (colorable_chiN _))

/--
**Finite case (now fully proved):**
For finite chromatic number `k`, every value `m ≤ k` is realized *as an induced subgraph
of `G`*, so the finite-subgraph inheritance is automatic: the witness `H` is an induced
subgraph of `G`, hence every finite subgraph of `H` is already a subgraph of `G`.

Existence of an induced subgraph with chromatic number *exactly* `m` is the discrete
intermediate-value theorem `exists_induce_chiN_eq`: starting from a finite subgraph of
chromatic number `k` (obtained from de Bruijn–Erdős), deleting vertices one at a time
lowers the chromatic number by at most one, so it passes through every value between `k`
and `0`. The custom `Cardinal`-valued `chromaticNumber` is matched to the natural-number
chromatic number via the bridge lemmas above. This side result is fully machine-checked
(no `sorry`). -/
theorem finite_case (V : Type) (G : SimpleGraph V) (k : ℕ) :
    chromaticNumber V G = k →
    ∀ m ≤ k, ∃ (W : Type) (H : SimpleGraph W),
      chromaticNumber W H = m ∧
      ∀ (n : ℕ) (F : SimpleGraph (Fin n)),
        isSubgraphOf F H → isSubgraphOf F G := by
  intro hχ m hmk
  have hmin : ∀ j < k, ¬ G.Colorable j := not_colorable_of_chromaticNumber_eq V G k hχ
  obtain ⟨s, hs⟩ := exists_finite_chiN_ge G k hmin
  obtain ⟨t, _hts, hchi⟩ := exists_induce_chiN_eq G s m (le_trans hmk hs)
  refine ⟨↥(↑t : Set V), G.induce (↑t : Set V), ?_, ?_⟩
  · apply chromaticNumber_eq_of_colorable
    · rw [← hchi]; exact colorable_chiN _
    · intro j hj; rw [← hchi] at hj; exact not_colorable_of_lt_chiN _ hj
  · rintro n F ⟨f, hf_inj, hf_adj⟩
    refine ⟨fun x => ((f x : ↥(↑t : Set V)) : V), ?_, ?_⟩
    · intro x y hxy
      exact hf_inj (Subtype.ext hxy)
    · intro v₁ v₂ hadj
      exact hf_adj v₁ v₂ hadj

end Erdos736
