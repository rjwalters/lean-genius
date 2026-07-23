/-
Erdős Problem #751: Cycle Lengths in 4-Chromatic Graphs

Source: https://erdosproblems.com/751
Status: SOLVED

Statement:
Let G be a graph with chromatic number χ(G) = 4. If m₁ < m₂ < ⋯ are the lengths
of the cycles in G, can min(mᵢ₊₁ - mᵢ) be arbitrarily large? Can this happen
if the girth of G is large?

Answer: NO

Bondy and Vince (1998) proved that every graph with minimum degree at least 3
has two cycles whose lengths differ by at most 2. Since every graph with
chromatic number 4 contains a subgraph of minimum degree at least 3, the
answer follows (the two close cycles in that subgraph are also cycles in G).

Key Insight:
The chromatic number controls degeneracy: χ(G) ≤ Δ(G) + 1, and more relevantly,
a graph with χ(G) ≥ k contains a subgraph of minimum degree ≥ k − 1. (The bound
is on a subgraph, not the global minimum degree of G, which an isolated vertex
can force to 0.)

References:
- Bondy, Vince (1998): "Cycles in a graph whose lengths differ by one or two"
  J. Graph Theory 27, 11-15
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Lattice.Nat

open SimpleGraph

namespace Erdos751

/-
## Part I: Graph Theory Foundations

Basic definitions for graphs, cycles, and chromatic number.
-/

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/--
**Minimum Degree:**
The minimum degree δ(G) is the smallest vertex degree in G.
-/
noncomputable def minDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.min' (Finset.univ.image (fun v => G.degree v)) (by simp)

/--
**Maximum Degree:**
The maximum degree Δ(G) is the largest vertex degree in G.
-/
noncomputable def maxDegree (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.max' (Finset.univ.image (fun v => G.degree v)) (by simp)

/--
**Chromatic Number:**
The chromatic number χ(G) is the minimum number of colors needed to properly
color the vertices of G (no two adjacent vertices have the same color).

Defined from Mathlib's `SimpleGraph.chromaticNumber : ℕ∞` via `.toNat`.
(Formerly an axiom.) -/
noncomputable def chromaticNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (SimpleGraph.chromaticNumber G).toNat

/--
**Girth:**
The girth of G is the length of the shortest cycle in G.
If G is acyclic (a forest), the girth is 0 (Mathlib's `girth = egirth.toNat`,
and `egirth` of an acyclic graph is `⊤`, whose `toNat` is `0`).

Defined from Mathlib's `SimpleGraph.girth`. (Formerly an axiom.) -/
noncomputable def girth (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  SimpleGraph.girth G

/--
**Cycle Lengths:**
The set of all cycle lengths present in G: lengths of closed cycle walks.

Defined directly from Mathlib's `Walk`/`IsCycle`. (Formerly an axiom.) -/
def cycleLengths (G : SimpleGraph V) [DecidableRel G.Adj] : Set ℕ :=
  {n | ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = n}

/--
**Cycle Length Gap:**
Given the cycle lengths, the minimum gap between consecutive lengths.
-/
noncomputable def minCycleLengthGap (lengths : Set ℕ) : ℕ :=
  sInf {d : ℕ | ∃ a ∈ lengths, ∃ b ∈ lengths, a < b ∧ d = b - a}

/--
**Minimum gap upper bound.**
Any pair of distinct lengths in the set witnesses an upper bound on the minimum
gap: the closest pair of elements is always a consecutive pair, so the minimum
difference over all distinct pairs equals the minimum consecutive gap. -/
theorem minCycleLengthGap_le {S : Set ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S)
    (hab : a < b) : minCycleLengthGap S ≤ b - a :=
  Nat.sInf_le ⟨a, ha, b, hb, hab, rfl⟩

/-
## Part II: Key Relationships
-/

/--
**Cycle lengths are monotone under subgraphs.**
If `H ≤ G`, every cycle of `H` is a cycle of `G` (via `Walk.mapLe`), so the set
of cycle lengths of `H` is contained in that of `G`. -/
theorem cycleLengths_mono {G H : SimpleGraph V} [DecidableRel G.Adj]
    [DecidableRel H.Adj] (h : H ≤ G) : cycleLengths H ⊆ cycleLengths G := by
  rintro n ⟨v, c, hcyc, hlen⟩
  refine ⟨v, c.mapLe h, (Walk.mapLe_isCycle h).mpr hcyc, ?_⟩
  have hlm : (c.mapLe h).length = c.length := c.length_map (Hom.ofLE h)
  rw [hlm]; exact hlen

/-
**Chromatic Number and Minimum Degree:**
For any graph G with at least one vertex:
  χ(G) ≤ Δ(G) + 1 (greedy coloring bound)

More importantly for us:
  If χ(G) ≥ k, then G has a subgraph with minimum degree ≥ k - 1.
-/
/-- A graph on an empty vertex type is `n`-colorable for every `n`. -/
theorem colorable_of_isEmpty {W : Type*} [IsEmpty W] (H : SimpleGraph W) (n : ℕ) :
    H.Colorable n :=
  ⟨Coloring.mk (fun v => isEmptyElim v) (fun {v} _ _ => isEmptyElim v)⟩

/-- A graph whose (file) chromatic number is `4` is not 3-colorable. -/
theorem not_colorable_three_of_chromaticNumber_four (G : SimpleGraph V)
    [DecidableRel G.Adj] (hchi : chromaticNumber G = 4) : ¬ G.Colorable 3 := by
  intro hcol
  have hle : SimpleGraph.chromaticNumber G ≤ (3 : ℕ) := hcol.chromaticNumber_le
  have h3 : ((3 : ℕ) : ℕ∞) ≠ ⊤ := by simp
  have hton := ENat.toNat_le_toNat hle h3
  unfold chromaticNumber at hchi
  simp at hton
  omega

/-- **Greedy extension step**: if `v ∈ t` has fewer than `3` neighbours inside
`t` and the graph induced on `t.erase v` is 3-colorable, then so is the graph
induced on `t` — colour `v` with a colour unused by its (at most two)
neighbours. -/
theorem colorable_of_erase_colorable (G : SimpleGraph V) [DecidableRel G.Adj]
    {t : Finset V} {v : V} (hv : v ∈ t)
    (hdeg : (t.filter (fun u => G.Adj v u)).card < 3)
    (hcol : (G.induce (↑(t.erase v) : Set V)).Colorable 3) :
    (G.induce (↑t : Set V)).Colorable 3 := by
  obtain ⟨C⟩ := hcol
  -- the colours used by neighbours of `v` inside `t.erase v`
  set N : Finset V := (t.erase v).filter (fun u => G.Adj v u) with hN
  have hNsub : ∀ u ∈ N, u ∈ t.erase v := fun u hu => (Finset.mem_filter.mp hu).1
  set used : Finset (Fin 3) :=
    N.attach.image (fun u => C ⟨u.1, Finset.mem_coe.mpr (hNsub u.1 u.2)⟩) with hused
  have husedcard : used.card < 3 := by
    have h1 : used.card ≤ N.attach.card := Finset.card_image_le
    have h1' : N.attach.card = N.card := Finset.card_attach
    have h2 : N.card ≤ (t.filter (fun u => G.Adj v u)).card := by
      apply Finset.card_le_card
      intro u hu
      rw [hN, Finset.mem_filter] at hu
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_of_mem_erase hu.1, hu.2⟩
    omega
  -- a free colour exists
  obtain ⟨c, hc⟩ : ∃ c : Fin 3, c ∉ used := by
    by_contra hcon
    have hall : used = Finset.univ := by
      apply Finset.eq_univ_iff_forall.mpr
      intro c
      by_contra hcc
      exact hcon ⟨c, hcc⟩
    rw [hall, Finset.card_univ] at husedcard
    simp at husedcard
  -- extend the colouring by giving `v` the free colour
  refine ⟨Coloring.mk (fun x => if hx : x.1 = v then c else
    C ⟨x.1, Finset.mem_coe.mpr
      (Finset.mem_erase.mpr ⟨hx, Finset.mem_coe.mp x.2⟩)⟩) ?_⟩
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hadj
  have hadj' : G.Adj a b := hadj
  by_cases hav : a = v <;> by_cases hbv : b = v
  · subst hav
    subst hbv
    exact absurd hadj' G.irrefl
  · simp only [dif_pos hav, dif_neg hbv]
    have hbN : b ∈ N := by
      rw [hN, Finset.mem_filter]
      exact ⟨Finset.mem_erase.mpr ⟨hbv, Finset.mem_coe.mp hb⟩, hav ▸ hadj'⟩
    intro heq
    apply hc
    rw [heq]
    exact Finset.mem_image.mpr ⟨⟨b, hbN⟩, Finset.mem_attach _ _, rfl⟩
  · simp only [dif_pos hbv, dif_neg hav]
    have haN : a ∈ N := by
      rw [hN, Finset.mem_filter]
      exact ⟨Finset.mem_erase.mpr ⟨hav, Finset.mem_coe.mp ha⟩,
        (show G.Adj a v from hbv ▸ hadj').symm⟩
    intro heq
    apply hc
    rw [← heq]
    exact Finset.mem_image.mpr ⟨⟨a, haN⟩, Finset.mem_attach _ _, rfl⟩
  · simp only [dif_neg hav, dif_neg hbv]
    exact C.valid hadj'

/-- **Critical-subgraph extraction**: any vertex set whose induced subgraph is
not 3-colorable contains a nonempty subset in which every vertex has at least
`3` neighbours *inside the subset*. Strong induction on the vertex set: a
vertex with fewer than 3 internal neighbours can be removed without making the
induced graph 3-colorable (`colorable_of_erase_colorable`). -/
theorem exists_min_subset_of_not_colorable (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∀ t : Finset V, ¬ (G.induce (↑t : Set V)).Colorable 3 →
    ∃ s : Finset V, s.Nonempty ∧
      ∀ v ∈ s, 3 ≤ (s.filter (fun u => G.Adj v u)).card := by
  intro t
  induction t using Finset.strongInduction with
  | _ t ih =>
    intro hncol
    by_cases hall : ∀ v ∈ t, 3 ≤ (t.filter (fun u => G.Adj v u)).card
    · refine ⟨t, ?_, hall⟩
      rcases Finset.eq_empty_or_nonempty t with rfl | hne
      · exfalso
        apply hncol
        haveI : IsEmpty ↥((↑(∅ : Finset V)) : Set V) := by
          constructor
          rintro ⟨x, hx⟩
          simp at hx
        exact colorable_of_isEmpty _ 3
      · exact hne
    · simp only [not_forall, not_le] at hall
      obtain ⟨v, hvt, hdeg⟩ := hall
      exact ih (t.erase v) (Finset.erase_ssubset hvt)
        (fun hcol => hncol (colorable_of_erase_colorable G hvt hdeg hcol))

/--
**Chromatic–degeneracy lemma (PROVED, sound induced-subgraph form):**
Every graph with chromatic number 4 contains a nonempty vertex set `s` in which
every vertex has at least `3` neighbours *inside `s`* — i.e. the subgraph
induced on `s` has minimum degree at least 3.

The bound is on the *induced subgraph*: a previous formalization asserted
`∃ H ≤ G, minDegree H ≥ 3` with `minDegree` ranging over **all** of `V`, which
is false (for `K₄` plus an isolated vertex every subgraph `H ≤ G` on the same
vertex type keeps the isolated vertex at degree 0). This statement quantifies
the degree only over the extracted vertex set, which is the correct classical
fact — and it is proved here (formerly an axiom): take a vertex-minimal subset
whose induced subgraph is not 3-colorable; each of its vertices must have `≥ 3`
internal neighbours, else greedy extension of a 3-colouring of the smaller set
would 3-colour it. -/
theorem four_chromatic_subgraph_minDeg (G : SimpleGraph V) [DecidableRel G.Adj]
    (hchi : chromaticNumber G = 4) :
    ∃ s : Finset V, s.Nonempty ∧
      ∀ v ∈ s, 3 ≤ (s.filter (fun u => G.Adj v u)).card := by
  apply exists_min_subset_of_not_colorable G Finset.univ
  intro hcol
  apply not_colorable_three_of_chromaticNumber_four G hchi
  obtain ⟨C⟩ := hcol
  exact ⟨C.comp ⟨fun v => ⟨v, by simp⟩, fun {a b} h => h⟩⟩

/-- The degree of a vertex in the graph induced on `↑s` equals the number of
its neighbours inside `s`. -/
theorem degree_induce_eq_filter_card (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) [DecidableRel (G.induce (↑s : Set V)).Adj]
    (x : ↥(↑s : Set V)) :
    (G.induce (↑s : Set V)).degree x = (s.filter (fun u => G.Adj x.1 u)).card := by
  show ((G.induce (↑s : Set V)).neighborFinset x).card = _
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_coe.mp y.2, hy⟩
  · intro y1 h1 y2 h2 heq
    exact Subtype.ext heq
  · intro u hu
    rw [Finset.mem_filter] at hu
    exact ⟨⟨u, Finset.mem_coe.mpr hu.1⟩,
      by rw [SimpleGraph.mem_neighborFinset]; exact hu.2, rfl⟩

/-- If every vertex of `s` has at least 3 neighbours inside `s`, the graph
induced on `s` has minimum degree at least 3. -/
theorem minDegree_induce_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) [Nonempty ↥(↑s : Set V)]
    [DecidableRel (G.induce (↑s : Set V)).Adj]
    (h : ∀ v ∈ s, 3 ≤ (s.filter (fun u => G.Adj v u)).card) :
    minDegree (G.induce (↑s : Set V)) ≥ 3 := by
  unfold minDegree
  apply Finset.le_min'
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨x, _, rfl⟩ := hy
  rw [degree_induce_eq_filter_card]
  exact h x.1 (Finset.mem_coe.mp x.2)

/-- Every cycle of the graph induced on `s` is a cycle of `G`: the induced
graph embeds into `G`, and cycles map to cycles along injective
homomorphisms. -/
theorem cycleLengths_induce_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [DecidableRel (G.induce s).Adj] :
    cycleLengths (G.induce s) ⊆ cycleLengths G := by
  rintro n ⟨v, c, hcyc, hlen⟩
  let f : G.induce s ↪g G :=
    (induceUnivIso G).toEmbedding.comp (G.induceHomOfLE (Set.subset_univ s))
  have hinj : Function.Injective (f.toHom : ↥s → V) := f.injective
  refine ⟨f.toHom v, c.map f.toHom, ?_, ?_⟩
  · exact (Walk.map_isCycle_iff_of_injective hinj).mpr hcyc
  · rw [Walk.length_map]
    exact hlen

/-
## Part III: Bondy-Vince Theorem

The key result: graphs with minimum degree ≥ 3 have close cycle lengths.
-/

/--
**Bondy-Vince Theorem (1998):**
Every graph with minimum degree at least 3 has two cycles whose lengths
differ by at most 2.

More precisely: if G has δ(G) ≥ 3, then there exist cycle lengths
m, m' in G with |m - m'| ≤ 2.
-/
axiom bondy_vince_theorem (G : SimpleGraph V) [DecidableRel G.Adj] :
    minDegree G ≥ 3 →
    ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
      (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2

/- 
**Immediate Corollary:**
The minimum gap between consecutive cycle lengths is at most 2.
-/
/-
## Part IV: Main Results

Answer to Erdős's question.
-/

/--
**Erdős Problem #751: Part 1**
For graphs with chromatic number 4, the minimum gap between consecutive
cycle lengths cannot be arbitrarily large.

In fact, the gap is always at most 2.
-/
theorem erdos_751_chromatic_4 (G : SimpleGraph V) [DecidableRel G.Adj] :
    chromaticNumber G = 4 →
    ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
      (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2 := by
  intro hchi
  obtain ⟨s, hne, hdeg⟩ := four_chromatic_subgraph_minDeg G hchi
  haveI : Nonempty ↥((↑s : Set V)) :=
    ⟨⟨hne.choose, Finset.mem_coe.mpr hne.choose_spec⟩⟩
  letI : DecidableRel (G.induce (↑s : Set V)).Adj :=
    fun a b => decidable_of_iff (G.Adj a.1 b.1) induce_adj.symm
  have hmin : minDegree (G.induce (↑s : Set V)) ≥ 3 := minDegree_induce_ge G s hdeg
  obtain ⟨m, m', hm, hm', hnem, hg1, hg2⟩ :=
    bondy_vince_theorem (G.induce (↑s : Set V)) hmin
  exact ⟨m, m', cycleLengths_induce_subset G _ hm,
    cycleLengths_induce_subset G _ hm', hnem, hg1, hg2⟩

/--
**Erdős Problem #751: Part 2**
The answer is NO even if we require large girth.
Having large girth doesn't help because minimum degree ≥ 3 is the key.
-/
theorem erdos_751_with_girth (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    chromaticNumber G = 4 → girth G ≥ k →
    ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
      (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2 := by
  intro hchi _hgirth
  -- The girth condition doesn't help - the result follows from χ(G) = 4 alone
  exact erdos_751_chromatic_4 G hchi

/--
**Erdős Problem #751: Full Answer**
Can min(mᵢ₊₁ - mᵢ) be arbitrarily large for χ(G) = 4?
Answer: NO, the gap is always ≤ 2.
-/
theorem erdos_751 (G : SimpleGraph V) [DecidableRel G.Adj] :
    chromaticNumber G = 4 →
    ¬(∀ n : ℕ, minCycleLengthGap (cycleLengths G) > n) := by
  intro hchi hcontra
  -- The gap is at most 2, so it can't be > 2
  have h := erdos_751_chromatic_4 G hchi
  obtain ⟨m, m', hm, hm', hne, hgap1, hgap2⟩ := h
  -- The minimum gap is at most |m - m'| ≤ 2
  have hgap_bound : minCycleLengthGap (cycleLengths G) ≤ 2 := by
    rcases lt_or_gt_of_ne hne with h | h
    · calc minCycleLengthGap (cycleLengths G) ≤ m' - m := minCycleLengthGap_le hm hm' h
        _ ≤ 2 := by omega
    · calc minCycleLengthGap (cycleLengths G) ≤ m - m' := minCycleLengthGap_le hm' hm h
        _ ≤ 2 := by omega
  -- But hcontra says gap > 3, contradiction
  have := hcontra 3
  omega

/-
## Part V: Strengthening - Minimum Degree 3 Suffices
-/

/--
**Generalization:**
The result holds for any graph with minimum degree ≥ 3, not just χ(G) = 4.
-/
theorem min_degree_3_cycle_gap (G : SimpleGraph V) [DecidableRel G.Adj] :
    minDegree G ≥ 3 →
    ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
      (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2 :=
  bondy_vince_theorem G

/--
**Why Chromatic Number 4 Implies a Dense Subgraph:**
A graph with χ(G) = 4 must contain a nonempty vertex set on which the induced
subgraph has minimum degree ≥ 3 (the chromatic–degeneracy lemma, proved above).
The bound holds inside the extracted vertex set, not on the global minimum
degree of `G` (an isolated vertex forces the latter to 0).
-/
theorem chromatic_4_implies_subgraph_min_deg_3 (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    chromaticNumber G = 4 →
    ∃ s : Finset V, s.Nonempty ∧
      ∀ v ∈ s, 3 ≤ (s.filter (fun u => G.Adj v u)).card :=
  four_chromatic_subgraph_minDeg G

/-
## Part VI: Summary
-/

/--
**Erdős Problem #751: SOLVED**

Summary of results:
1. Bondy-Vince: δ(G) ≥ 3 ⟹ two cycles differ by at most 2
2. χ(G) = 4 ⟹ G has a subgraph H ≤ G with δ(H) ≥ 3
3. Therefore: χ(G) = 4 ⟹ gap ≤ 2 (the close cycles in H are cycles in G)

The answer is NO - the gap cannot be arbitrarily large, and large
girth doesn't help either.
-/
theorem erdos_751_summary (G : SimpleGraph V) [DecidableRel G.Adj] :
    -- Main result: 4-chromatic implies close cycles
    (chromaticNumber G = 4 →
      ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
        (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2) ∧
    -- Generalization: min degree 3 suffices
    (minDegree G ≥ 3 →
      ∃ m m' : ℕ, m ∈ cycleLengths G ∧ m' ∈ cycleLengths G ∧ m ≠ m' ∧
        (m : ℤ) - m' ≤ 2 ∧ (m' : ℤ) - m ≤ 2) ∧
    -- Connection: χ = 4 implies an induced subgraph of min degree ≥ 3
    (chromaticNumber G = 4 →
      ∃ s : Finset V, s.Nonempty ∧
        ∀ v ∈ s, 3 ≤ (s.filter (fun u => G.Adj v u)).card) :=
  ⟨erdos_751_chromatic_4 G, min_degree_3_cycle_gap G,
    chromatic_4_implies_subgraph_min_deg_3 G⟩

/-
## Part VII: Cycle Existence (axiom-free)

The Bondy–Vince axiom asserts *two* cycles with close lengths. This section
proves, without any axiom, that the cycle spectrum is at least *nonempty*:
a finite nonempty graph in which every vertex has degree at least 2 contains
a cycle (each connected component of an acyclic graph is a tree, and a
nontrivial finite tree has a vertex of degree 1). Chained through the proved
chromatic–degeneracy lemma this yields `erdos_751_cycle_exists`: a 4-chromatic
graph contains a cycle — previously even this weak form of the answer was only
derivable through the Bondy–Vince axiom.
-/

/-- Every member of `cycleLengths` is at least 3: cycles in a simple graph
have length at least 3. -/
theorem three_le_of_mem_cycleLengths {G : SimpleGraph V} [DecidableRel G.Adj]
    {n : ℕ} (hn : n ∈ cycleLengths G) : 3 ≤ n := by
  obtain ⟨v, c, hc, rfl⟩ := hn
  exact hc.three_le_length

/-- The degree of a vertex inside its connected-component graph equals its
degree in `G`: every `G`-neighbour of a vertex lies in the vertex's
component. -/
theorem degree_toSimpleGraph_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : G.ConnectedComponent) [Fintype C] [DecidableRel C.toSimpleGraph.Adj]
    (x : C) : C.toSimpleGraph.degree x = G.degree x.1 := by
  show (C.toSimpleGraph.neighborFinset x).card = (G.neighborFinset x.1).card
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    rw [SimpleGraph.mem_neighborFinset] at hy
    rw [SimpleGraph.mem_neighborFinset]
    exact hy
  · intro y1 h1 y2 h2 heq
    exact Subtype.ext heq
  · intro u hu
    rw [SimpleGraph.mem_neighborFinset] at hu
    have hus : u ∈ C.supp := C.mem_supp_of_adj_mem_supp x.2 hu
    exact ⟨⟨u, hus⟩, by rw [SimpleGraph.mem_neighborFinset]; exact hu, rfl⟩

/-- **Minimum degree ≥ 2 forces a cycle** (contrapositive form): a finite
nonempty graph in which every vertex has at least two neighbours is not
acyclic. If it were, each connected component would be a tree
(`IsAcyclic.isTree_connectedComponent`); the component of any vertex is
nontrivial (the vertex has a neighbour, which lies in the same component), so
the tree has a vertex of degree 1 (`IsTree.exists_vert_degree_one_of_nontrivial`),
whose degree in `G` is the same — contradicting the degree bound. -/
theorem not_isAcyclic_of_two_le_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ v, 2 ≤ G.degree v) : ¬ G.IsAcyclic := by
  intro hac
  obtain ⟨v⟩ := ‹Nonempty V›
  have hvdeg : 0 < G.degree v := lt_of_lt_of_le (by norm_num) (h v)
  obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj v).mp hvdeg
  let C : G.ConnectedComponent := G.connectedComponentMk v
  have hvC : v ∈ C.supp := rfl
  have hwC : w ∈ C.supp := C.mem_supp_of_adj_mem_supp hvC hw
  haveI : Fintype C := Fintype.ofFinite C
  haveI : DecidableRel C.toSimpleGraph.Adj := Classical.decRel _
  haveI : Nontrivial C :=
    ⟨⟨v, hvC⟩, ⟨w, hwC⟩, fun heq => hw.ne (congrArg Subtype.val heq)⟩
  have htree : C.toSimpleGraph.IsTree := hac.isTree_connectedComponent C
  obtain ⟨x, hx⟩ := htree.exists_vert_degree_one_of_nontrivial
  have hxdeg : C.toSimpleGraph.degree x = G.degree x.1 :=
    degree_toSimpleGraph_eq G C x
  have h2 := h x.1
  omega

/-- A finite nonempty graph in which every vertex has degree at least 2 has a
nonempty cycle spectrum. -/
theorem cycleLengths_nonempty_of_two_le_degree (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : ∀ v, 2 ≤ G.degree v) :
    (cycleLengths G).Nonempty := by
  by_contra hempty
  apply not_isAcyclic_of_two_le_degree G h
  intro v c hc
  exact hempty ⟨c.length, v, c, hc, rfl⟩

/-- The file's `minDegree` is a lower bound for every vertex degree. -/
theorem minDegree_le_degree' (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    minDegree G ≤ G.degree v :=
  Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ v))

/-- **Nonvacuity of the Bondy–Vince hypothesis** (axiom-free): minimum degree
at least 2 — in particular the `minDegree G ≥ 3` hypothesis of
`bondy_vince_theorem` — already forces the cycle spectrum to be nonempty. -/
theorem cycleLengths_nonempty_of_two_le_minDegree (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : 2 ≤ minDegree G) : (cycleLengths G).Nonempty :=
  cycleLengths_nonempty_of_two_le_degree G
    (fun v => le_trans h (minDegree_le_degree' G v))

/-- **Erdős #751, axiom-free component: a 4-chromatic graph contains a
cycle.** The chromatic–degeneracy lemma extracts a vertex set on which the
induced subgraph has all degrees ≥ 3 ≥ 2, the cycle-existence engine produces
a cycle there, and cycles of induced subgraphs are cycles of `G`.
`#print axioms erdos_751_cycle_exists` reports foundational axioms only — no
`bondy_vince_theorem`. -/
theorem erdos_751_cycle_exists (G : SimpleGraph V) [DecidableRel G.Adj]
    (hchi : chromaticNumber G = 4) : (cycleLengths G).Nonempty := by
  obtain ⟨s, hne, hdeg⟩ := four_chromatic_subgraph_minDeg G hchi
  haveI : Nonempty ↥((↑s : Set V)) :=
    ⟨⟨hne.choose, Finset.mem_coe.mpr hne.choose_spec⟩⟩
  letI : DecidableRel (G.induce (↑s : Set V)).Adj :=
    fun a b => decidable_of_iff (G.Adj a.1 b.1) induce_adj.symm
  have h2 : ∀ x : ↥((↑s : Set V)), 2 ≤ (G.induce (↑s : Set V)).degree x := by
    intro x
    rw [degree_induce_eq_filter_card G s x]
    have := hdeg x.1 (Finset.mem_coe.mp x.2)
    omega
  obtain ⟨n, hn⟩ := cycleLengths_nonempty_of_two_le_degree
    (G.induce (↑s : Set V)) h2
  exact ⟨n, cycleLengths_induce_subset G _ hn⟩

/-- A 4-chromatic graph is not acyclic (axiom-free corollary of
`erdos_751_cycle_exists`). -/
theorem not_isAcyclic_of_four_chromatic (G : SimpleGraph V)
    [DecidableRel G.Adj] (hchi : chromaticNumber G = 4) : ¬ G.IsAcyclic := by
  obtain ⟨n, v, c, hc, _⟩ := erdos_751_cycle_exists G hchi
  exact fun hac => hac c hc

/-- A 4-chromatic graph has girth at least 3 (axiom-free): its cycle spectrum
is nonempty, so Mathlib's `three_le_girth` applies. -/
theorem three_le_girth_of_four_chromatic (G : SimpleGraph V)
    [DecidableRel G.Adj] (hchi : chromaticNumber G = 4) : 3 ≤ girth G :=
  SimpleGraph.three_le_girth (not_isAcyclic_of_four_chromatic G hchi)

end Erdos751
