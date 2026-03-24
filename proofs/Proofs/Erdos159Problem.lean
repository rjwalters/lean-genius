/-
# Erdős Problem 159: Ramsey Numbers for C₄ and Complete Graphs

Determine whether there exists a constant `c > 0` such that
`R(C₄, Kₙ) ≪ n^{2-c}`.

Known bounds:
- Upper: `R(C₄, Kₙ) ≪ n² / (log n)²` (Szemerédi)
- Lower: `R(C₄, Kₙ) ≫ n^{3/2} / (log n)^{3/2}` (Spencer)

*Reference:* [erdosproblems.com/159](https://www.erdosproblems.com/159)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

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

/- ## Ramsey number R(C₄, Kₙ) -/

/-- `R(C₄, Kₙ)` is the smallest `N` such that every 2-colouring of `K_N`
contains either a red `C₄` or a blue `Kₙ`. Equivalently, every graph on
`N` vertices either contains `C₄` or has independence number `≥ n`. -/
axiom ramseyC4Kn : ℕ → ℕ

/-- The Ramsey number is the threshold: below it, a counterexample
exists. -/
axiom ramseyC4Kn_spec (n : ℕ) (hn : 1 ≤ n) :
    (∀ (G : SimpleGraph (Fin (ramseyC4Kn n))),
      HasC4 G ∨ HasClique Gᶜ n) ∧
    (∀ N : ℕ, N < ramseyC4Kn n →
      ∃ (G : SimpleGraph (Fin N)),
        ¬HasC4 G ∧ ¬HasClique Gᶜ n)

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
def ErdosProblem159 : Prop :=
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
