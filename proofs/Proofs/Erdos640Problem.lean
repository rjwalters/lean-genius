/-
# Erdős Problem #640: Chromatic Number of Odd Cycle Spans

**Source:** [erdosproblems.com/640](https://erdosproblems.com/640)
**Status:** OPEN (Erdős–Hajnal)

## Statement

Let k ≥ 3. Does there exist some f(k) such that if a graph G has
chromatic number χ(G) ≥ f(k), then G must contain some odd cycle
whose vertices span a subgraph of chromatic number ≥ k?

## Background

- Trivially true for k = 3: any graph with χ ≥ 3 is non-bipartite,
  so it contains an odd cycle, and all odd cycles have χ = 3.
- Raphael Steiner observed this is equivalent to replacing "odd cycle"
  with "path."
- The problem appears in [Er97d, p.84].

## Approach

We formalize the conjecture using Mathlib's `SimpleGraph` API.
The key definitions capture:
1. Chromatic number (via graph coloring)
2. Odd cycles in a graph
3. Induced subgraph on cycle vertices
4. The conjectured threshold function f(k)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Proofs.GraphCore

open GraphCore
open SimpleGraph hiding chromaticNumber

namespace Erdos640

/- ## Part II: Odd Cycles -/

/--
An odd cycle of length 2m + 1 in G is a closed walk of odd length
that visits distinct vertices. We represent it by its vertex set.
-/
def HasOddCycleWithVertices (G : SimpleGraph V) (S : Finset V) : Prop :=
  S.card ≥ 3 ∧
  Odd S.card ∧
  -- All vertices in S are pairwise reachable in G
  (∀ v ∈ S, ∀ w ∈ S, v ≠ w → G.Adj v w ∨ G.Reachable v w) ∧
  -- S forms a cycle: there exists a cyclic ordering
  ∃ (σ : Fin S.card → V),
    Function.Injective σ ∧
    (∀ i : Fin S.card, σ i ∈ S) ∧
    (∀ i : Fin S.card, G.Adj (σ i) (σ ⟨(i.val + 1) % S.card, Nat.mod_lt _ (by have := i.isLt; omega)⟩))

/- ## Part III: Induced Subgraph Chromatic Number -/

/--
The span chromatic number: the chromatic number of the subgraph
induced on the vertex set S.
We state this as a predicate: the induced subgraph on S has χ ≥ k.
-/
def InducedChromaticAtLeast (G : SimpleGraph V) (S : Finset V) (k : ℕ) : Prop :=
  ¬IsKColorable (inducedSubgraph G (↑S : Set V)) (k - 1)

/- ## Part IV: The Erdős–Hajnal Conjecture -/

/--
**Erdős Problem #640 (Erdős–Hajnal):**
For every k ≥ 3, there exists f(k) such that every graph G with
χ(G) ≥ f(k) contains an odd cycle whose vertices span a subgraph
of chromatic number ≥ k.
-/
def ErdosHajnalConjecture640 : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ fk : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        chromaticNumber G ≥ fk →
        ∃ S : Finset V,
          HasOddCycleWithVertices G S ∧
          InducedChromaticAtLeast G S k

/--
**Steiner's equivalence:**
The conjecture is equivalent when "odd cycle" is replaced by "path."
-/
def SteinerPathVariant : Prop :=
  ∀ k : ℕ, k ≥ 3 →
    ∃ fk : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        chromaticNumber G ≥ fk →
        ∃ S : Finset V,
          -- S is the vertex set of a path in G
          (∃ (σ : Fin S.card → V),
            Function.Injective σ ∧
            (∀ i : Fin S.card, σ i ∈ S) ∧
            (∀ i : Fin (S.card - 1),
              G.Adj (σ ⟨i.val, by omega⟩) (σ ⟨i.val + 1, by omega⟩))) ∧
          InducedChromaticAtLeast G S k

axiom steiner_equivalence :
  ErdosHajnalConjecture640 ↔ SteinerPathVariant

/- ## Part V: The Trivial Case k = 3 -/

/--
**Trivial case:** For k = 3, f(3) = 3 works.
Any graph with χ ≥ 3 is non-bipartite, hence contains an odd cycle.
Every odd cycle has chromatic number exactly 3.
-/
axiom trivial_case_k3 :
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    chromaticNumber G ≥ 3 →
    ∃ S : Finset V,
      HasOddCycleWithVertices G S ∧
      InducedChromaticAtLeast G S 3

/- ## Part VI: Summary -/

/--
**Summary:**
Erdős Problem #640 asks whether high chromatic number forces odd cycles
with high-chromatic spans. The k=3 case is trivial; the general case
remains open. Steiner showed the path variant is equivalent.
-/
theorem erdos_640_summary :
    (ErdosHajnalConjecture640 ↔ SteinerPathVariant) :=
  steiner_equivalence

/- ## Part VII: Structural Lemmas on Colorability -/

/-- Colorability is monotone: if G is k-colorable, it is also (k+1)-colorable. -/
theorem isKColorable_succ {G : SimpleGraph V} {k : ℕ}
    (h : IsKColorable G k) : IsKColorable G (k + 1) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨fun v => ⟨(c v).val, by omega⟩, fun v w hadj => by
    have := hc v w hadj
    simp [Fin.ext_iff] at this ⊢
    exact this⟩

/-- Colorability is monotone in general: k₁ ≤ k₂ → k₁-colorable → k₂-colorable. -/
theorem isKColorable_mono {G : SimpleGraph V} {k₁ k₂ : ℕ}
    (hle : k₁ ≤ k₂) (hk : IsKColorable G k₁) : IsKColorable G k₂ := by
  obtain ⟨c, hc⟩ := hk
  exact ⟨fun v => ⟨(c v).val, by omega⟩, fun v w hadj => by
    have := hc v w hadj
    simp [Fin.ext_iff] at this ⊢
    exact this⟩

/-- A graph with no edges is 1-colorable. -/
theorem isKColorable_one_of_no_edges {G : SimpleGraph V}
    (h : ∀ v w : V, ¬G.Adj v w) : IsKColorable G 1 :=
  ⟨fun _ => 0, fun v w hadj => absurd hadj (h v w)⟩

/-- Every graph is 0-colorable on an empty type. -/
theorem isKColorable_zero_of_isEmpty [IsEmpty V] (G : SimpleGraph V) :
    IsKColorable G 0 :=
  ⟨fun v => isEmptyElim v, fun v => isEmptyElim v⟩

/- ## Part VIII: Induced Subgraph Coloring Inheritance -/

/-- If G is k-colorable, then any induced subgraph is also k-colorable. -/
theorem inducedSubgraph_isKColorable {G : SimpleGraph V} {S : Set V} {k : ℕ}
    (hk : IsKColorable G k) : IsKColorable (inducedSubgraph G S) k := by
  obtain ⟨c, hc⟩ := hk
  exact ⟨fun v => c v.val, fun v w hadj => hc v.val w.val hadj⟩

/-- Contrapositive: if the induced subgraph on S is not (k-1)-colorable,
    then G is not (k-1)-colorable either. -/
theorem inducedChromaticAtLeast_of_not_colorable {G : SimpleGraph V}
    {S : Finset V} {k : ℕ}
    (h : InducedChromaticAtLeast G S k) : ¬IsKColorable G (k - 1) := by
  intro hcol
  exact h (inducedSubgraph_isKColorable hcol)

/- ## Part IX: Odd Cycle Chromatic Number -/

/-- An odd cycle with ≥ 3 vertices is not 1-colorable.
    Any adjacent pair forces two colors. -/
theorem oddCycle_not_one_colorable {G : SimpleGraph V}
    {S : Finset V} (hcyc : HasOddCycleWithVertices G S) :
    ¬IsKColorable (inducedSubgraph G (↑S : Set V)) 1 := by
  intro ⟨c, hc⟩
  obtain ⟨hcard, _, _, σ, _, hσ_mem, hσ_adj⟩ := hcyc
  have h0 : (0 : ℕ) < S.card := by omega
  let idx0 : Fin S.card := ⟨0, h0⟩
  let idx1 : Fin S.card := ⟨(0 + 1) % S.card, Nat.mod_lt _ h0⟩
  have hadj := hσ_adj idx0
  have hv0 : σ idx0 ∈ S := hσ_mem idx0
  have hv1 : σ idx1 ∈ S := hσ_mem idx1
  have := hc ⟨σ idx0, hv0⟩ ⟨σ idx1, hv1⟩ hadj
  exact this (Subsingleton.elim _ _)

/- ## Part X: Every Graph is Colorable -/

/-- Every graph on a finite type is colorable (using card V colors). -/
theorem exists_colorable [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ∃ k, IsKColorable G k := by
  use Fintype.card V
  by_cases h : IsEmpty V
  · exact ⟨fun v => isEmptyElim v, fun v => isEmptyElim v⟩
  · rw [not_isEmpty_iff] at h
    let e := Fintype.equivFin V
    exact ⟨fun v => e v, fun v w hadj heq => by
      have := G.ne_of_adj hadj
      exact this (e.injective (Fin.ext (Fin.mk.inj heq)))⟩

/- ## Part XI: Bipartite and 2-Colorability -/

/-- A 2-colorable graph is one where vertices can be properly 2-colored. -/
def IsBipartiteColoring (G : SimpleGraph V) : Prop := IsKColorable G 2

/-- An odd cycle has InducedChromaticAtLeast with k = 3:
    the induced subgraph on cycle vertices is not 2-colorable (not bipartite).
    This is because walking around an odd cycle with 2 colors leads to a parity
    contradiction. -/
theorem oddCycle_chromatic_at_least_3 {G : SimpleGraph V}
    {S : Finset V} (hcyc : HasOddCycleWithVertices G S) :
    InducedChromaticAtLeast G S 3 := by
  -- InducedChromaticAtLeast G S 3 means ¬IsKColorable (inducedSubgraph G S) 2
  unfold InducedChromaticAtLeast
  simp only [show 3 - 1 = 2 from rfl]
  intro ⟨c, hc⟩
  obtain ⟨hcard, hodd, _, σ, hσ_inj, hσ_mem, hσ_adj⟩ := hcyc
  -- Map colors to Bool
  let b : Fin S.card → Fin 2 := fun i => c ⟨σ i, hσ_mem i⟩
  -- Adjacent vertices must have different colors
  have hdiff : ∀ i : Fin S.card,
      b i ≠ b ⟨(i.val + 1) % S.card, Nat.mod_lt _ (by omega)⟩ := by
    intro i
    exact hc ⟨σ i, hσ_mem i⟩
      ⟨σ ⟨(i.val + 1) % S.card, _⟩, hσ_mem _⟩ (hσ_adj i)
  -- With 2 colors, adjacent ≠ means the value flips at each step.
  -- After S.card steps around the odd cycle, parity contradicts.
  -- Key: for Fin 2, a ≠ b means b.val = 1 - a.val
  have hflip : ∀ i : Fin S.card,
      (b ⟨(i.val + 1) % S.card, Nat.mod_lt _ (by omega)⟩).val = 1 - (b i).val := by
    intro i
    have hneq : (b i).val ≠ (b ⟨(i.val + 1) % S.card, _⟩).val :=
      fun h => hdiff i (Fin.ext h)
    omega
  -- By induction: b(i).val = (b(0).val + i) % 2 for i < S.card
  have hparity : ∀ i : ℕ, (hi : i < S.card) →
      (b ⟨i, hi⟩).val = ((b ⟨0, by omega⟩).val + i) % 2 := by
    intro i hi
    induction i with
    | zero => simp
    | succ n ih =>
      have hn : n < S.card := by omega
      have hmod : (n + 1) % S.card = n + 1 := Nat.mod_eq_of_lt hi
      have hf := hflip ⟨n, hn⟩
      -- hf : b(⟨(n+1) % S.card, _⟩).val = 1 - b(⟨n, hn⟩).val
      -- Since (n+1) % S.card = n+1, rewrite
      have : (b ⟨(n + 1) % S.card, Nat.mod_lt _ (by omega)⟩).val =
             (b ⟨n + 1, hi⟩).val := by congr 1; exact Fin.ext (by omega)
      rw [this] at hf
      rw [hf, ih hn]
      omega
  -- Apply at S.card - 1 and use cycle closure to get contradiction
  have hlast := hparity (S.card - 1) (by omega)
  -- Cycle closure: b(S.card - 1) ≠ b(0)
  have hclose := hdiff ⟨S.card - 1, by omega⟩
  -- (S.card - 1 + 1) % S.card = 0
  have hmod0 : (S.card - 1 + 1) % S.card = 0 := by omega
  have hval_neq : (b ⟨S.card - 1, by omega⟩).val ≠ (b ⟨0, by omega⟩).val := by
    intro heq; apply hclose; exact Fin.ext heq
  -- From hlast: b(S.card-1).val = (b(0).val + S.card - 1) % 2
  -- From hval_neq: b(S.card-1).val ≠ b(0).val
  -- Since b(0).val < 2: these two facts force S.card to be even
  -- But hodd says S.card is odd: contradiction
  omega

/- ## Part XII: Structural Summary -/

/-- The k=3 structural fact: any graph containing an odd cycle has an odd
    cycle whose vertices span a subgraph of chromatic number ≥ 3. This is
    because every odd cycle requires exactly 3 colors. -/
theorem k3_odd_cycle_span {G : SimpleGraph V}
    {S : Finset V} (hcyc : HasOddCycleWithVertices G S) :
    HasOddCycleWithVertices G S ∧ InducedChromaticAtLeast G S 3 :=
  ⟨hcyc, oddCycle_chromatic_at_least_3 hcyc⟩

end Erdos640
