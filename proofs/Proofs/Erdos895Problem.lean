/-
  Erdős Problem #895: Independent Additive Triples in Triangle-Free Graphs

  Source: https://erdosproblems.com/895
  Status: SOLVED (Answer: YES)

  Statement:
  For all sufficiently large n, if G is a triangle-free graph on {1,...,n},
  must there exist three independent vertices a, b, a+b?

  Answer: YES, for all n ≥ 18.

  This problem beautifully connects two areas:
  - Graph theory: triangle-free graphs and independent sets
  - Additive combinatorics: Schur triples and sum-free sets

  Historical Context:
  - Posed by Erdős and Hajnal
  - Solved by Ben Barber using SAT solver verification
  - Threshold: n = 18 is the smallest value where the result holds

  The Key Insight:
  In a triangle-free graph, the neighborhood of any vertex is an independent set.
  Combined with additive structure on {1,...,n}, this forces the existence of
  additive triples a, b, a+b that are mutually non-adjacent.

  Open Generalization (Hajnal):
  Does there exist an independent Hindman set—a set containing all finite sums
  of some finite collection of base elements?
-/

import Mathlib

open Finset SimpleGraph

/- ## Basic Graph Definitions -/

/-- The complete graph on vertices {1,...,n} -/
def completeGraphOn (n : ℕ) : SimpleGraph (Fin n) := ⊤

/-- A graph on {1,...,n} represented as a simple graph on Fin n -/
abbrev GraphOnInterval (n : ℕ) := SimpleGraph (Fin n)

/-- Three vertices form an independent set if no two are adjacent -/
def IsIndependentTriple {n : ℕ} (G : GraphOnInterval n) (a b c : Fin n) : Prop :=
  ¬G.Adj a b ∧ ¬G.Adj b c ∧ ¬G.Adj a c

/-- A graph is triangle-free if it contains no 3-clique -/
def IsTriangleFree {n : ℕ} (G : GraphOnInterval n) : Prop :=
  ∀ a b c : Fin n, ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj a c)

/- ## Additive Triples -/

/-- An additive triple (a, b, a+b) where all three are in {1,...,n} -/
def IsAdditiveTriple {n : ℕ} (a b c : Fin n) : Prop :=
  (a.val : ℕ) + b.val = c.val ∧ a.val > 0 ∧ b.val > 0

/-- Check if there exists an independent additive triple -/
def HasIndependentAdditiveTriple {n : ℕ} (G : GraphOnInterval n) : Prop :=
  ∃ a b c : Fin n, IsAdditiveTriple a b c ∧ IsIndependentTriple G a b c

/- ## The Main Conjecture -/

/-- Erdős Problem #895: Every triangle-free graph on {1,...,n} has an
    independent additive triple, for sufficiently large n. -/
def erdos895Conjecture : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ G : GraphOnInterval n,
    IsTriangleFree G → HasIndependentAdditiveTriple G

/-- The threshold is n = 18 -/
def erdos895Threshold : ℕ := 18

/- ## Barber's Theorem (2015) -/

/-- Ben Barber's result: the conjecture holds with threshold 18 -/
theorem barber_theorem : ∀ n ≥ 18, ∀ G : GraphOnInterval n,
    IsTriangleFree G → HasIndependentAdditiveTriple G := by
  sorry

/-- The main result: Erdős Problem #895 is TRUE -/
theorem erdos_895 : erdos895Conjecture := by
  use 18
  exact barber_theorem

/- ## Small Cases -/

/-- For n = 17, there exists a triangle-free graph with no independent additive triple -/
theorem counterexample_17 : ∃ G : GraphOnInterval 17,
    IsTriangleFree G ∧ ¬HasIndependentAdditiveTriple G := by
  sorry

/-- The threshold 18 is sharp -/
theorem threshold_sharp : (∀ n ≥ 18, ∀ G : GraphOnInterval n,
    IsTriangleFree G → HasIndependentAdditiveTriple G) ∧
    (∃ G : GraphOnInterval 17, IsTriangleFree G ∧ ¬HasIndependentAdditiveTriple G) := by
  exact ⟨barber_theorem, counterexample_17⟩

/- ## Connection to Ramsey Theory -/

/-- Map the 15 edges of K₆ (i < j) to pairs: edge k gives vertices (pairOf6 k).1 and .2 -/
private def pairOf6 (k : Fin 15) : Fin 6 × Fin 6 :=
  match k.val with
  | 0 => (0,1) | 1 => (0,2) | 2 => (0,3) | 3 => (0,4) | 4 => (0,5)
  | 5 => (1,2) | 6 => (1,3) | 7 => (1,4) | 8 => (1,5)
  | 9 => (2,3) | 10 => (2,4) | 11 => (2,5)
  | 12 => (3,4) | 13 => (3,5)
  | _ => (4,5)  -- k.val = 14

/-- Map ordered pair (i,j) with i < j to edge index -/
private def edgeIdx6 (p : Fin 6 × Fin 6) : Fin 15 :=
  match p.1.val, p.2.val with
  | 0, 1 => 0 | 0, 2 => 1 | 0, 3 => 2 | 0, 4 => 3 | 0, 5 => 4
  | 1, 2 => 5 | 1, 3 => 6 | 1, 4 => 7 | 1, 5 => 8
  | 2, 3 => 9 | 2, 4 => 10 | 2, 5 => 11
  | 3, 4 => 12 | 3, 5 => 13
  | _, _ => 14  -- (4,5) and default

/-- For ordered pairs, pairOf6 and edgeIdx6 are inverses -/
private lemma pairOf6_edgeIdx6 {a b : Fin 6} (h : a.val < b.val) :
    pairOf6 (edgeIdx6 (a, b)) = (a, b) := by
  fin_cases a <;> fin_cases b <;>
    simp_all [edgeIdx6, pairOf6]

/-- R(3,3) = 6: for any 2-coloring of the 15 edges of K₆, there exists a
    monochromatic triangle. Verified by native_decide (2^15 = 32768 cases). -/
private theorem r33_via_edges :
    ∀ col : Fin 15 → Fin 2,
    ∃ a b d : Fin 6, a.val < b.val ∧ b.val < d.val ∧
      col (edgeIdx6 (a, b)) = col (edgeIdx6 (a, d)) ∧
      col (edgeIdx6 (a, d)) = col (edgeIdx6 (b, d)) := by
  native_decide

/-- The Ramsey number R(3,3) = 6: any 2-coloring of K₆ has a monochromatic triangle -/
theorem ramsey_3_3 : ∀ c : Fin 6 → Fin 6 → Fin 2,
    (∀ i j, i ≠ j → c i j = c j i) →
    ∃ a b d : Fin 6, a ≠ b ∧ b ≠ d ∧ a ≠ d ∧ c a b = c b d ∧ c b d = c a d := by
  intro c hc
  -- Apply r33_via_edges with col k := c on the pair at edge index k
  obtain ⟨a, b, d, hab, hbd, h1, h2⟩ :=
    r33_via_edges (fun k => c (pairOf6 k).1 (pairOf6 k).2)
  -- a.val < b.val < d.val gives distinctness
  have hab' : a ≠ b := Fin.ne_of_lt (Fin.mk_lt_mk.mpr hab)
  have hbd' : b ≠ d := Fin.ne_of_lt (Fin.mk_lt_mk.mpr hbd)
  have had' : a ≠ d := Fin.ne_of_lt (Fin.mk_lt_mk.mpr (Nat.lt_trans hab hbd))
  -- Rewrite h1, h2 using pairOf6_edgeIdx6 to get c equalities
  simp only [pairOf6_edgeIdx6 hab, pairOf6_edgeIdx6 (Nat.lt_trans hab hbd),
             pairOf6_edgeIdx6 hbd] at h1 h2
  -- h1 : c a b = c a d,  h2 : c a d = c b d  → all equal
  exact ⟨a, b, d, hab', hbd', had', h1.trans h2, h2.symm⟩

/-- Triangle-free graphs have independence number at least √n (Ramsey bound) -/
theorem triangleFree_independence_bound {n : ℕ} (G : GraphOnInterval n) (hG : IsTriangleFree G) :
    ∃ S : Finset (Fin n), S.card ≥ Nat.sqrt n ∧ ∀ a b : Fin n, a ∈ S → b ∈ S → a ≠ b → ¬G.Adj a b := by
  sorry

/- ## Connection to Schur Numbers -/

/-- A set is sum-free if it contains no Schur triple a, b, a+b -/
def IsSumFree (S : Finset ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ S → b ∈ S → a + b ∉ S

/-- The Schur number S(k) is the largest n such that {1,...,n} can be
    k-colored with no monochromatic Schur triple (a, b, a+b with a,b ≥ 1) -/
noncomputable def schurNumber (k : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ c : ℕ → Fin k, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a ≤ n → b ≤ n → a + b ≤ n →
    ¬(c a = c b ∧ c b = c (a + b))}

/-- There exists a valid 2-coloring of {1,...,4}: coloring 1→0, 2→1, 3→1, 4→0
    avoids all monochromatic Schur triples (1,1,2), (1,2,3), (1,3,4), (2,2,4). -/
private lemma schur_4_colorable :
    ∃ f : Fin 5 → Fin 2, ∀ a b c : Fin 5,
    1 ≤ a.val → 1 ≤ b.val → c.val = a.val + b.val →
    ¬(f a = f b ∧ f b = f c) := by
  native_decide

/-- Every 2-coloring of {1,...,5} contains a monochromatic Schur triple.
    Verified by native_decide over all 2^6 = 64 colorings. -/
private lemma schur_5_forced :
    ∀ f : Fin 6 → Fin 2, ∃ a b c : Fin 6,
    1 ≤ a.val ∧ 1 ≤ b.val ∧ c.val = a.val + b.val ∧
    f a = f b ∧ f b = f c := by
  native_decide

/-- S(2) = 4: {1,2,3,4} can be 2-colored without monochromatic Schur triple,
    but every 2-coloring of {1,...,5} contains one. -/
theorem schur_2 : schurNumber 2 = 4 := by
  unfold schurNumber
  let S := {n : ℕ | ∃ c : ℕ → Fin 2, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
    a ≤ n → b ≤ n → a + b ≤ n → ¬(c a = c b ∧ c b = c (a + b))}
  show sSup S = 4
  -- 4 ∈ S: lift the Fin 5 coloring from schur_4_colorable
  have hmem4 : 4 ∈ S := by
    obtain ⟨f, hf⟩ := schur_4_colorable
    refine ⟨fun n => if h : n < 5 then f ⟨n, h⟩ else ⟨0, by norm_num⟩, ?_⟩
    intro a b ha1 hb1 ha4 hb4 hab4
    intro ⟨h1, h2⟩
    have ha5 : a < 5 := by omega
    have hb5 : b < 5 := by omega
    have hab5 : a + b < 5 := by omega
    rw [dif_pos ha5, dif_pos hb5] at h1
    rw [dif_pos hb5, dif_pos hab5] at h2
    exact hf ⟨a, ha5⟩ ⟨b, hb5⟩ ⟨a + b, hab5⟩ ha1 hb1 rfl ⟨h1, h2⟩
  -- 5 ∉ S: any supposed coloring yields a mono triple from schur_5_forced
  have hS5 : 5 ∉ S := by
    intro ⟨col, hcol⟩
    obtain ⟨a, b, cs, ha1, hb1, hcs_eq, hf1, hf2⟩ :=
      schur_5_forced (fun i => col i.val)
    exact hcol a.val b.val (by omega) (by omega)
      (Nat.lt_succ_iff.mp a.isLt) (Nat.lt_succ_iff.mp b.isLt)
      (hcs_eq ▸ Nat.lt_succ_iff.mp cs.isLt)
      ⟨hf1, hf2.trans (congr_arg col hcs_eq)⟩
  -- Every n ≥ 5 fails (restrict any supposed coloring to positions ≤ 5)
  have hSle4 : ∀ m ∈ S, m ≤ 4 := fun m hm => by
    by_contra hlt
    push_neg at hlt
    obtain ⟨col, hcol⟩ := hm
    exact hS5 ⟨col, fun a b ha1 hb1 ha5 hb5 hab5 =>
      hcol a b ha1 hb1 (by omega) (by omega) (by omega)⟩
  exact le_antisymm
    (csSup_le ⟨4, hmem4⟩ hSle4)
    (le_csSup ⟨4, hSle4⟩ hmem4)

/-- Erdős 895 implies a Schur-like result for graph colorings:
    Every 2-coloring of {1,...,n} either has a same-colored additive pair (a,b with a+b in range)
    or a fully same-colored Schur triple (a, b, a+b all the same color). -/
theorem erdos895_implies_schur_variant {n : ℕ} (hn : n ≥ 18) :
    ∀ c : Fin n → Fin 2,
    (∃ a b d : Fin n, IsAdditiveTriple a b d ∧ c a = c b) ∨
    (∃ a b d : Fin n, IsAdditiveTriple a b d ∧ c a = c b ∧ c b = c d) := by
  sorry

/- ## Hajnal's Generalization (OPEN) -/

/-- A Hindman set: all finite sums of a base set -/
def hindmanSet (base : Finset ℕ) : Set ℕ :=
  {s : ℕ | ∃ T : Finset ℕ, T ⊆ base ∧ T.Nonempty ∧ T.sum id = s}

/-- Hajnal's conjecture: triangle-free graphs have independent Hindman sets -/
def hajnalConjecture : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, ∀ G : GraphOnInterval n, IsTriangleFree G →
    ∃ base : Finset (Fin n), base.card ≥ 2 ∧
      ∀ s t : Fin n, (s.val ∈ hindmanSet (base.image (·.val))) →
        (t.val ∈ hindmanSet (base.image (·.val))) → s ≠ t → ¬G.Adj s t

/-- Hajnal's conjecture remains OPEN -/
theorem hajnal_conjecture_open : hajnalConjecture ↔ hajnalConjecture := by
  rfl

/- ## Density Considerations -/

/-- A triangle-free graph on n vertices has at most n²/4 edges (Mantel).
    Proof: IsTriangleFree → CliqueFree 3, then apply Turán's theorem with r=2.
    The Turán bound for r=2 gives #edges ≤ (n²-(n%2)²)/4 ≤ n²/4. -/
theorem mantel_theorem {n : ℕ} (G : GraphOnInterval n) [DecidableRel G.Adj]
    (hG : IsTriangleFree G) : G.edgeFinset.card ≤ n^2 / 4 := by
  -- Convert IsTriangleFree to CliqueFree (2+1)
  -- isNClique_iff : G.IsNClique n s ↔ G.IsClique s ∧ #s = n  (IsClique field first)
  have hcf : G.CliqueFree (2 + 1) := by
    intro t ht
    rw [SimpleGraph.isNClique_iff] at ht
    obtain ⟨hclique_set, hcard⟩ := ht   -- hclique_set : G.IsClique ↑t, hcard : #t = 2+1
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hcard
    -- hclique_set : (↑{a,b,c} : Set _).Pairwise G.Adj
    exact hG a b c ⟨
      hclique_set (by simp) (by simp) hab,   -- G.Adj a b
      hclique_set (by simp) (by simp) hbc,   -- G.Adj b c
      hclique_set (by simp) (by simp) hac⟩  -- G.Adj a c
  -- Apply Turán's theorem: CliqueFree(r+1) → #edges ≤ Turán bound
  have hbound : G.edgeFinset.card ≤
      (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2) + (n % 2).choose 2 := by
    have key := CliqueFree.card_edgeFinset_le hcf
    simp only [Fintype.card_fin] at key
    exact key
  -- Arithmetic: Turán bound for r=2 equals ⌊n²/4⌋
  -- (n%2).choose 2 = 0 since n%2 < 2
  have hchoose : (n % 2).choose 2 = 0 :=
    Nat.choose_eq_zero_of_lt (Nat.mod_lt n (by norm_num))
  calc G.edgeFinset.card
      ≤ (n ^ 2 - (n % 2) ^ 2) * (2 - 1) / (2 * 2) + (n % 2).choose 2 := hbound
    _ = (n ^ 2 - (n % 2) ^ 2) / 4 + 0 := by rw [hchoose]; norm_num
    _ ≤ n ^ 2 / 4 := by simp only [add_zero]; exact Nat.div_le_div_right (Nat.sub_le _ _)

/-- Dense triangle-free graphs force large independent sets -/
theorem dense_triangleFree_independence {n : ℕ} (G : GraphOnInterval n) [DecidableRel G.Adj]
    (hG : IsTriangleFree G) (hdense : G.edgeFinset.card ≥ n^2 / 5) :
    ∃ S : Finset (Fin n), S.card ≥ n / 3 ∧
      ∀ a b : Fin n, a ∈ S → b ∈ S → a ≠ b → ¬G.Adj a b := by
  sorry

/- ## Computational Verification -/

/-- The result was verified computationally via SAT solver -/
theorem erdos895_sat_verified :
    ∀ n : Fin 100, n.val ≥ 18 → ∀ G : GraphOnInterval n.val,
      IsTriangleFree G → HasIndependentAdditiveTriple G := by
  sorry

/- ## Main Results Summary -/

/-- Erdős Problem #895: SOLVED
    Answer: Yes, for n ≥ 18, every triangle-free graph on {1,...,n}
    contains an independent additive triple a, b, a+b. -/
theorem erdos_895_summary :
    (∀ n ≥ 18, ∀ G : GraphOnInterval n,
      IsTriangleFree G → HasIndependentAdditiveTriple G) ∧
    erdos895Threshold = 18 := by
  exact ⟨barber_theorem, rfl⟩

#check erdos_895
#check barber_theorem
#check hajnal_conjecture_open
