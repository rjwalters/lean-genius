/-
# Erdős Problem 159: Ramsey Numbers for C₄ and Complete Graphs

Determine whether there exists a constant `c > 0` such that
`R(C₄, Kₙ) ≪ n^{2-c}`.

Known bounds:
- Upper: `R(C₄, Kₙ) ≪ n² / (log n)²` (Szemerédi)
- Lower: `R(C₄, Kₙ) ≫ n^{3/2} / (log n)^{3/2}` (Spencer)

The Ramsey function R(C₄, Kₙ) is defined (not axiomatized) via `Nat.find`,
using the finite Ramsey theorem to establish existence. The only axioms are
the known upper and lower bounds (deep results not in Mathlib).

*Reference:* [erdosproblems.com/159](https://www.erdosproblems.com/159)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Proofs.RamseysTheorem

open SimpleGraph

/- ## Graph predicates -/

/-- A simple graph contains a 4-cycle `C₄` if there exist four distinct
vertices forming a cycle `a-b-c-d-a`. -/
def HasC4 {V : Type*} (G : SimpleGraph V) : Prop :=
    ∃ (a b c d : V),
      a ≠ b ∧ b ≠ c ∧ c ≠ d ∧ a ≠ c ∧ a ≠ d ∧ b ≠ d ∧
      G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a

/-- A simple graph contains a complete subgraph on `n` vertices if there
exist `n` distinct vertices that are pairwise adjacent. -/
def HasClique {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
    ∃ (S : Finset V), S.card = n ∧
      ∀ u ∈ S, ∀ v ∈ S, u ≠ v → G.Adj u v

/- ## Clique auxiliary lemmas -/

/-- Clique size is monotone: a graph with a clique of size `n` also has
one of size `m ≤ n`, by extracting a subset. -/
lemma HasClique_mono {V : Type*} {G : SimpleGraph V} {m n : ℕ}
    (hmn : m ≤ n) (hc : HasClique G n) : HasClique G m := by
  obtain ⟨S, hcard, hadj⟩ := hc
  obtain ⟨T, hTS, hTcard⟩ := Finset.exists_subset_card_eq (by omega : m ≤ S.card)
  exact ⟨T, hTcard, fun u hu v hv huv => hadj u (hTS hu) v (hTS hv) huv⟩

/-- A clique of size `n` in a graph on a finite type requires at least
`n` vertices. -/
lemma HasClique_card_le {V : Type*} [Fintype V] {G : SimpleGraph V} {n : ℕ}
    (hc : HasClique G n) : n ≤ Fintype.card V := by
  obtain ⟨S, hcard, _⟩ := hc
  calc n = S.card := hcard.symm
    _ ≤ Fintype.card V := S.card_le_univ

/-- The empty graph has no 4-cycle (no edges means no cycle). -/
lemma bot_not_HasC4 {V : Type*} : ¬HasC4 (⊥ : SimpleGraph V) := by
  rintro ⟨_, _, _, _, -, -, -, -, -, -, hab, -, -, -⟩
  exact hab

/- ## Ramsey number R(C₄, Kₙ) — defined from Ramsey's theorem

We eliminate the axioms for the Ramsey function and its specification by:
1. Proving K₄ ⊇ C₄ (a 4-clique contains a 4-cycle)
2. Using the finite Ramsey theorem to show R(C₄, Kₙ) ≤ R(4, n)
3. Defining ramseyC4Kn via Nat.find on the existence proof
4. Deriving the threshold specification from Nat.find properties
-/

section RamseyC4Kn

open Classical

/-- A 4-clique contains a 4-cycle: given four pairwise adjacent vertices,
they form the cycle a-b-c-d-a (since K₄ ⊇ C₄). -/
lemma HasClique_four_hasC4 {V : Type*} {G : SimpleGraph V}
    (h : HasClique G 4) : HasC4 G := by
  obtain ⟨S, hcard, hadj⟩ := h
  -- Decompose the 4-element Finset into its constituents
  have h4 : S.card = 3 + 1 := by omega
  obtain ⟨a, S₃, ha, rfl, h3⟩ := Finset.card_eq_succ.mp h4
  have h3' : S₃.card = 2 + 1 := by omega
  obtain ⟨b, S₂, hb, rfl, h2⟩ := Finset.card_eq_succ.mp h3'
  have h2' : S₂.card = 1 + 1 := by omega
  obtain ⟨c, S₁, hc, rfl, h1⟩ := Finset.card_eq_succ.mp h2'
  obtain ⟨d, rfl⟩ := Finset.card_eq_one.mp h1
  -- Extract distinctness from non-membership
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb hc
  push_neg at ha hb hc
  -- Build the 4-cycle from pairwise adjacency
  exact ⟨a, b, c, d, ha.1, hb.1, hc, ha.2.1, ha.2.2, hb.2,
    hadj a (Finset.mem_insert_self _ _) b (by simp) ha.1,
    hadj b (by simp) c (by simp) hb.1,
    hadj c (by simp) d (by simp) hc,
    hadj d (by simp) a (Finset.mem_insert_self _ _) (Ne.symm ha.2.2)⟩

/-- For every n ≥ 1, there exists N such that every graph on N vertices
contains C₄ or has independence number ≥ n (i.e., Gᶜ contains Kₙ).
This follows from Ramsey's theorem: R(4, n) witnesses the property,
since every red K₄ contains a C₄. -/
theorem ramsey_C4_Kn_exists (n : ℕ) (hn : 1 ≤ n) :
    ∃ N, ∀ (G : SimpleGraph (Fin N)), HasC4 G ∨ HasClique Gᶜ n := by
  -- Ramsey's theorem provides R(4, n)
  obtain ⟨N, _, hRamsey⟩ := RamseysTheorem.ramsey_theorem 4 n (by omega) hn
  use N
  intro G
  -- Construct edge coloring: red = G's edges, blue = complement edges
  let c : RamseysTheorem.EdgeColoring (Fin N) :=
    { color := fun x y => if G.Adj x y then true else false
      symm := fun x y => by
        simp only [show G.Adj x y ↔ G.Adj y x from G.adj_comm]
      irrefl := fun x => if_neg (G.loopless x) }
  rcases hRamsey c with ⟨red, hred_card, hred_clique⟩ | ⟨blue, hblue_card, hblue_clique⟩
  · -- Red 4-clique in the coloring → 4-clique in G → C₄ in G
    left
    apply HasClique_four_hasC4
    exact ⟨red, hred_card, fun u hu v hv huv => by
      have h := hred_clique (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
      -- h : c.redGraph.Adj u v, definitionally (if G.Adj u v then true else false) = true ∧ u ≠ v
      change (if G.Adj u v then true else false) = true ∧ u ≠ v at h
      by_contra hn
      rw [if_neg hn] at h
      exact absurd h.1 (by decide)⟩
  · -- Blue n-clique in the coloring → n-clique in Gᶜ
    right
    exact ⟨blue, hblue_card, fun u hu v hv huv => by
      have h := hblue_clique (Finset.mem_coe.mpr hu) (Finset.mem_coe.mpr hv) huv
      -- h : c.blueGraph.Adj u v, definitionally (if G.Adj u v then true else false) = false ∧ u ≠ v
      change (if G.Adj u v then true else false) = false ∧ u ≠ v at h
      rw [compl_adj]
      exact ⟨huv, fun hadj => by rw [if_pos hadj] at h; exact absurd h.1 (by decide)⟩⟩

/-- `R(C₄, Kₙ)` is the smallest `N` such that every 2-colouring of `K_N`
contains either a red `C₄` or a blue `Kₙ`. Equivalently, every graph on
`N` vertices either contains `C₄` or has independence number `≥ n`.

Defined via `Nat.find` from the existence proof, not axiomatized. -/
noncomputable def ramseyC4Kn (n : ℕ) : ℕ :=
  if h : 1 ≤ n then Nat.find (ramsey_C4_Kn_exists n h) else 0

/-- The Ramsey number is the threshold: the Ramsey property holds at
`ramseyC4Kn n`, and for every smaller N a counterexample exists.
Proved from the `Nat.find` definition. -/
theorem ramseyC4Kn_spec (n : ℕ) (hn : 1 ≤ n) :
    (∀ (G : SimpleGraph (Fin (ramseyC4Kn n))),
      HasC4 G ∨ HasClique Gᶜ n) ∧
    (∀ N : ℕ, N < ramseyC4Kn n →
      ∃ (G : SimpleGraph (Fin N)),
        ¬HasC4 G ∧ ¬HasClique Gᶜ n) := by
  have hdef : ramseyC4Kn n = Nat.find (ramsey_C4_Kn_exists n hn) := dif_pos hn
  constructor
  · -- The Ramsey property holds at the minimum
    rw [hdef]
    exact Nat.find_spec (ramsey_C4_Kn_exists n hn)
  · -- Below the minimum, counterexamples exist
    intro N hN
    rw [hdef] at hN
    have hmin := Nat.find_min (ramsey_C4_Kn_exists n hn) hN
    push_neg at hmin
    exact hmin

end RamseyC4Kn

/- ## Known bounds -/

/-- Szemerédi's upper bound: `R(C₄, Kₙ) ≤ C · n² / (log n)²` for some
constant `C > 0` and sufficiently large `n`. -/
axiom szemeredi_upper :
    ∃ C : ℝ, 0 < C ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        (ramseyC4Kn n : ℝ) ≤ C * (n : ℝ) ^ 2 / (Real.log n) ^ 2

/-- Spencer's lower bound: `R(C₄, Kₙ) ≥ c · n^{3/2} / (log n)^{3/2}`
for some constant `c > 0` and sufficiently large `n`. -/
axiom spencer_lower :
    ∃ c : ℝ, 0 < c ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        c * (n : ℝ) ^ (3/2 : ℝ) / (Real.log n) ^ (3/2 : ℝ) ≤ (ramseyC4Kn n : ℝ)

/- ## Main conjecture -/

/-- Erdős Problem 159: Does there exist `c > 0` such that
`R(C₄, Kₙ) ≤ C · n^{2-c}` for some constant `C` and all large `n`?

This asks whether the upper bound can be improved from `n²/(log n)²`
to a genuine power saving `n^{2-c}`. -/
noncomputable def ErdosProblem159 : Prop :=
    ∃ (c : ℝ), 0 < c ∧
      ∃ (C : ℝ), 0 < C ∧
        ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
          (ramseyC4Kn n : ℝ) ≤ C * (n : ℝ) ^ (2 - c)

/- ## Proved properties -/

/-- `R(C₄, Kₙ)` is monotone: for `1 ≤ m ≤ n`, `R(C₄, Kₘ) ≤ R(C₄, Kₙ)`.
Proved from the specification: if the Ramsey property holds at level `n`,
it also holds at level `m` since any independent set of size `≥ n`
contains one of size `m`. -/
theorem ramseyC4Kn_mono (m n : ℕ) (hm : 1 ≤ m) (h : m ≤ n) :
    ramseyC4Kn m ≤ ramseyC4Kn n := by
  by_contra hlt
  push_neg at hlt
  have hn : 1 ≤ n := le_trans hm h
  obtain ⟨G, hnoC4, hnoClique⟩ := (ramseyC4Kn_spec m hm).2 (ramseyC4Kn n) hlt
  rcases (ramseyC4Kn_spec n hn).1 G with hC4 | hClique
  · exact hnoC4 hC4
  · exact hnoClique (HasClique_mono h hClique)

/-- Trivial lower bound: `R(C₄, Kₙ) ≥ n` for `n ≥ 1`. The empty graph
on fewer than `n` vertices has no `C₄` and its complement cannot contain
a clique of size `n` (not enough vertices). -/
theorem ramseyC4Kn_ge (n : ℕ) (hn : 1 ≤ n) : n ≤ ramseyC4Kn n := by
  by_contra hlt
  push_neg at hlt
  rcases (ramseyC4Kn_spec n hn).1 (⊥ : SimpleGraph (Fin (ramseyC4Kn n)))
    with hC4 | hClique
  · exact bot_not_HasC4 hC4
  · have hle := HasClique_card_le hClique
    have hfin : Fintype.card (Fin (ramseyC4Kn n)) = ramseyC4Kn n :=
      Fintype.card_fin _
    omega
