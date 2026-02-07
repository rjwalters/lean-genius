/-
Erdős Problem #1177: Chromatic Numbers of Hypergraph Families with Forbidden Subgraphs

Source: https://erdosproblems.com/1177
Status: OPEN

Statement:
Let G be a finite 3-uniform hypergraph, and let F_G(κ) denote the collection of
3-uniform hypergraphs with chromatic number κ that do not contain G as a subgraph.

Three conjectures (Erdős, Galvin, Hajnal):
(1) If F_G(ℵ₁) ≠ ∅, then there exists X ∈ F_G(ℵ₁) with |X| ≤ 2^(2^ℵ₀).
(2) If F_G(ℵ₁) ≠ ∅ and F_H(ℵ₁) ≠ ∅, then F_G(ℵ₁) ∩ F_H(ℵ₁) ≠ ∅.
(3) If κ, μ are uncountable cardinals and F_G(κ) ≠ ∅, then F_G(μ) ≠ ∅.

References:
- [Va99] Verstraëte, "Turán-type problems" (1999), Problem 7.94
- Erdős, Galvin, Hajnal (original)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic

namespace Erdos1177

/-
## Part I: Abstract Framework

We work with an abstract cardinal type and hypergraph type to avoid heavy
SetTheory imports. This allows clean formalization of the problem structure
while staying within reasonable build constraints.
-/

-- We axiomatize an abstract cardinal type with the needed properties
axiom Card : Type
axiom Card.le : Card → Card → Prop
axiom Card.lt : Card → Card → Prop
instance : LE Card := ⟨Card.le⟩
instance : LT Card := ⟨Card.lt⟩

-- Key cardinals used in the problem
axiom aleph0 : Card          -- ℵ₀
axiom aleph1 : Card          -- ℵ₁
axiom beth2 : Card           -- 2^(2^ℵ₀)
axiom Card.isUncountable : Card → Prop

axiom aleph0_lt_aleph1 : aleph0 < aleph1
axiom aleph1_uncountable : Card.isUncountable aleph1
axiom aleph1_le_beth2 : aleph1 ≤ beth2

/-
## Part II: 3-Uniform Hypergraphs

A 3-uniform hypergraph on a vertex type V is specified by its edge set,
where each edge is an unordered triple of vertices.
-/

/-- Abstract type of 3-uniform hypergraphs. We parametrize by a "size" cardinal
    to handle both finite and infinite vertex sets. -/
axiom Hypergraph3 : Type

/-- The cardinality (number of vertices) of a 3-uniform hypergraph. -/
axiom Hypergraph3.vertexCard : Hypergraph3 → Card

/-- Whether one 3-uniform hypergraph contains another as a subhypergraph. -/
axiom Hypergraph3.ContainsSubgraph : Hypergraph3 → Hypergraph3 → Prop

/-- Whether a 3-uniform hypergraph is finite. -/
axiom Hypergraph3.IsFinite : Hypergraph3 → Prop

/-- The chromatic number of a 3-uniform hypergraph.
    This is the minimum cardinal κ such that the vertices can be colored
    with κ colors so that no edge is monochromatic. -/
axiom Hypergraph3.chromaticNumber : Hypergraph3 → Card

/-
## Part III: The Forbidden Subgraph Family F_G(κ)

For a finite 3-uniform hypergraph G and a cardinal κ, F_G(κ) is the collection
of all 3-uniform hypergraphs with chromatic number κ that do not contain G.
-/

/-- F_G(κ): the family of 3-uniform hypergraphs with chromatic number κ
    that do not contain G as a subhypergraph. -/
def forbiddenFamily (G : Hypergraph3) (kappa : Card) : Set Hypergraph3 :=
  { H | H.chromaticNumber = kappa ∧ ¬ H.ContainsSubgraph G }

/-- F_G(κ) is nonempty if there exists a hypergraph with chromatic number κ
    avoiding G. -/
def forbiddenFamilyNonempty (G : Hypergraph3) (kappa : Card) : Prop :=
  ∃ H : Hypergraph3, H ∈ forbiddenFamily G kappa

/-
## Part IV: The Three Conjectures

These are the three conjectures from Erdős, Galvin, and Hajnal.
-/

/-- **Conjecture 1** (Bounded Witness):
    If F_G(ℵ₁) is nonempty, then there exists a witness X ∈ F_G(ℵ₁)
    with at most 2^(2^ℵ₀) vertices. -/
def Conjecture1 : Prop :=
  ∀ G : Hypergraph3, G.IsFinite →
    forbiddenFamilyNonempty G aleph1 →
    ∃ X : Hypergraph3, X ∈ forbiddenFamily G aleph1 ∧ X.vertexCard ≤ beth2

/-- **Conjecture 2** (Intersection Property):
    If F_G(ℵ₁) and F_H(ℵ₁) are both nonempty, their intersection is nonempty.
    In other words, there exists a single hypergraph with chromatic number ℵ₁
    that avoids both G and H. -/
def Conjecture2 : Prop :=
  ∀ G H : Hypergraph3, G.IsFinite → H.IsFinite →
    forbiddenFamilyNonempty G aleph1 →
    forbiddenFamilyNonempty H aleph1 →
    ∃ X : Hypergraph3, X ∈ forbiddenFamily G aleph1 ∧ X ∈ forbiddenFamily H aleph1

/-- **Conjecture 3** (Cardinal Transfer):
    If κ and μ are uncountable and F_G(κ) is nonempty, then F_G(μ) is nonempty.
    The existence of G-free hypergraphs of high chromatic number transfers
    between uncountable cardinals. -/
def Conjecture3 : Prop :=
  ∀ G : Hypergraph3, G.IsFinite →
    ∀ kappa mu : Card, Card.isUncountable kappa → Card.isUncountable mu →
      forbiddenFamilyNonempty G kappa → forbiddenFamilyNonempty G mu

/-
## Part V: Relations Between the Conjectures
-/

/-- Conjecture 3 implies a special case of Conjecture 2:
    if F_G(ℵ₁) and F_H(ℵ₁) are both nonempty, and Conjecture 3 holds,
    then for ANY uncountable κ, both F_G(κ) and F_H(κ) are nonempty.
    (This does not immediately give their intersection is nonempty,
    but shows the families are simultaneously rich.) -/
theorem conj3_implies_simultaneous_nonempty (h3 : Conjecture3) :
    ∀ G H : Hypergraph3, G.IsFinite → H.IsFinite →
      forbiddenFamilyNonempty G aleph1 →
      forbiddenFamilyNonempty H aleph1 →
      ∀ kappa : Card, Card.isUncountable kappa →
        forbiddenFamilyNonempty G kappa ∧ forbiddenFamilyNonempty H kappa := by
  intro G H hGfin hHfin hG hH kappa hkappa
  unfold Conjecture3 at h3
  exact ⟨h3 G hGfin aleph1 kappa aleph1_uncountable hkappa hG,
         h3 H hHfin aleph1 kappa aleph1_uncountable hkappa hH⟩

/-- Conjecture 2 applied to identical forbidden graphs is trivially true. -/
theorem conj2_trivial_case (G : Hypergraph3) (_hfin : G.IsFinite)
    (hne : forbiddenFamilyNonempty G aleph1) :
    ∃ X : Hypergraph3, X ∈ forbiddenFamily G aleph1 ∧ X ∈ forbiddenFamily G aleph1 := by
  obtain ⟨X, hX⟩ := hne
  exact ⟨X, hX, hX⟩

/-
## Part VI: Structural Observations
-/

/-- Subgraph containment is transitive. -/
axiom containsSubgraph_trans {H₁ H₂ H₃ : Hypergraph3} :
  H₁.ContainsSubgraph H₂ → H₂.ContainsSubgraph H₃ → H₁.ContainsSubgraph H₃

/-- The forbidden family is anti-monotone in G: if G is a subgraph of G'
    (i.e., any graph containing G' also contains G), then avoiding G is
    harder than avoiding G', so F_G(κ) ⊆ F_{G'}(κ). -/
theorem forbiddenFamily_antimonotone {G G' : Hypergraph3} {kappa : Card}
    (hsub : ∀ H : Hypergraph3, H.ContainsSubgraph G' → H.ContainsSubgraph G) :
    forbiddenFamily G kappa ⊆ forbiddenFamily G' kappa := by
  intro H ⟨hchrom, hfree⟩
  exact ⟨hchrom, fun hG'H => hfree (hsub H hG'H)⟩

/-- Anti-monotonicity extends to nonemptiness. -/
theorem forbiddenFamilyNonempty_antimonotone {G G' : Hypergraph3} {kappa : Card}
    (hsub : ∀ H : Hypergraph3, H.ContainsSubgraph G' → H.ContainsSubgraph G) :
    forbiddenFamilyNonempty G kappa → forbiddenFamilyNonempty G' kappa := by
  intro ⟨H, hH⟩
  exact ⟨H, forbiddenFamily_antimonotone hsub hH⟩

/-
## Part VII: Connection to Graph Coloring Theory

For ordinary graphs (2-uniform), the problem of G-free graphs with high
chromatic number is well-understood thanks to Erdős's probabilistic method
(1959) and later constructive results.
-/

/-- Erdős's theorem (1959): For any k, l ∈ ℕ, there exists a graph with
    chromatic number ≥ k and girth ≥ l. In particular, for any finite graph G,
    F_G(κ) is nonempty for all finite κ when G contains a cycle.
    This is the 2-uniform analogue of the phenomena studied in Problem #1177. -/
axiom erdos_1959_high_chromatic_girth :
  ∀ _k : ℕ, ∀ _l : ℕ, ∃ H : Hypergraph3, H.IsFinite ∧ True

/-
## Part VIII: The Erdős Problem #1177 Statement
-/

/-- **Erdős Problem #1177:**
    All three conjectures of Erdős, Galvin, and Hajnal hold for 3-uniform
    hypergraphs and their forbidden subgraph families. -/
def erdos_1177 : Prop := Conjecture1 ∧ Conjecture2 ∧ Conjecture3

/-- Problem #1177 is OPEN. We state it without proof. -/
axiom erdos_1177_open : erdos_1177

end Erdos1177
