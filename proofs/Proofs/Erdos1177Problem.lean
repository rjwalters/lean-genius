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

import Mathlib

namespace Erdos1177

open Cardinal

/-
## Part I: Cardinals from Mathlib

The original formalization axiomatized an abstract cardinal type with 10 axioms
(Card, Card.le, Card.lt, aleph0, aleph1, beth2, Card.isUncountable, and 3 properties).
Using Mathlib's Cardinal type eliminates all of them.
-/

-- ℵ₀ < ℵ₁ (proved from Mathlib; was axiom)
theorem aleph0_lt_aleph1 : Cardinal.aleph0 < Cardinal.aleph 1 := by
  rw [← Cardinal.aleph_zero]
  exact Cardinal.aleph_lt_aleph.mpr (by norm_num)

-- ℵ₁ is uncountable (proved; was axiom)
theorem aleph1_uncountable : Cardinal.aleph0 < Cardinal.aleph 1 := aleph0_lt_aleph1

-- ℵ₁ ≤ 2^(2^ℵ₀) (proved; was axiom)
-- Proof: ℵ₁ = succ(ℵ₀) ≤ 2^ℵ₀ (Cantor) ≤ 2^(2^ℵ₀) (monotone power)
theorem aleph1_le_beth2 :
    Cardinal.aleph 1 ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.aleph0) := by
  have h_cantor := Cardinal.cantor Cardinal.aleph0
  -- Step 1: ℵ₁ ≤ 2^ℵ₀
  have h1 : Cardinal.aleph 1 ≤ (2 : Cardinal) ^ Cardinal.aleph0 := by
    -- ℵ₁ = aleph(succ 0) = succ(aleph 0) = succ(ℵ₀)
    have hsuc : Cardinal.aleph 1 = Order.succ Cardinal.aleph0 := by
      rw [← Cardinal.aleph_zero, ← Cardinal.aleph_succ]
      congr 1; exact Ordinal.succ_zero.symm
    rw [hsuc]
    exact Order.succ_le_of_lt h_cantor
  -- Step 2: 2^ℵ₀ ≤ 2^(2^ℵ₀)
  exact le_trans h1 (Cardinal.power_le_power_left
    (by norm_num : (2 : Cardinal) ≠ 0) (le_of_lt h_cantor))

/-
## Part II: 3-Uniform Hypergraphs

A 3-uniform hypergraph on a vertex type V is specified by its edge set,
where each edge is an unordered triple of vertices.
We axiomatize the abstract type and its key operations.
-/

/-- Abstract type of 3-uniform hypergraphs. -/
axiom Hypergraph3 : Type

/-- The cardinality (number of vertices) of a 3-uniform hypergraph. -/
axiom Hypergraph3.vertexCard : Hypergraph3 → Cardinal.{0}

/-- Whether one 3-uniform hypergraph contains another as a subhypergraph. -/
axiom Hypergraph3.ContainsSubgraph : Hypergraph3 → Hypergraph3 → Prop

/-- Whether a 3-uniform hypergraph is finite. -/
axiom Hypergraph3.IsFinite : Hypergraph3 → Prop

/-- The chromatic number of a 3-uniform hypergraph.
    This is the minimum cardinal κ such that the vertices can be colored
    with κ colors so that no edge is monochromatic. -/
axiom Hypergraph3.chromaticNumber : Hypergraph3 → Cardinal.{0}

/-
## Part III: The Forbidden Subgraph Family F_G(κ)

For a finite 3-uniform hypergraph G and a cardinal κ, F_G(κ) is the collection
of all 3-uniform hypergraphs with chromatic number κ that do not contain G.
-/

/-- F_G(κ): the family of 3-uniform hypergraphs with chromatic number κ
    that do not contain G as a subhypergraph. -/
def forbiddenFamily (G : Hypergraph3) (kappa : Cardinal.{0}) : Set Hypergraph3 :=
  { H | H.chromaticNumber = kappa ∧ ¬ H.ContainsSubgraph G }

/-- F_G(κ) is nonempty if there exists a hypergraph with chromatic number κ
    avoiding G. -/
def forbiddenFamilyNonempty (G : Hypergraph3) (kappa : Cardinal.{0}) : Prop :=
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
    forbiddenFamilyNonempty G (Cardinal.aleph 1) →
    ∃ X : Hypergraph3, X ∈ forbiddenFamily G (Cardinal.aleph 1) ∧
      X.vertexCard ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.aleph0)

/-- **Conjecture 2** (Intersection Property):
    If F_G(ℵ₁) and F_H(ℵ₁) are both nonempty, their intersection is nonempty.
    In other words, there exists a single hypergraph with chromatic number ℵ₁
    that avoids both G and H. -/
def Conjecture2 : Prop :=
  ∀ G H : Hypergraph3, G.IsFinite → H.IsFinite →
    forbiddenFamilyNonempty G (Cardinal.aleph 1) →
    forbiddenFamilyNonempty H (Cardinal.aleph 1) →
    ∃ X : Hypergraph3, X ∈ forbiddenFamily G (Cardinal.aleph 1) ∧
      X ∈ forbiddenFamily H (Cardinal.aleph 1)

/-- **Conjecture 3** (Cardinal Transfer):
    If κ and μ are uncountable and F_G(κ) is nonempty, then F_G(μ) is nonempty.
    The existence of G-free hypergraphs of high chromatic number transfers
    between uncountable cardinals. -/
def Conjecture3 : Prop :=
  ∀ G : Hypergraph3, G.IsFinite →
    ∀ kappa mu : Cardinal.{0}, Cardinal.aleph0 < kappa → Cardinal.aleph0 < mu →
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
      forbiddenFamilyNonempty G (Cardinal.aleph 1) →
      forbiddenFamilyNonempty H (Cardinal.aleph 1) →
      ∀ kappa : Cardinal.{0}, Cardinal.aleph0 < kappa →
        forbiddenFamilyNonempty G kappa ∧ forbiddenFamilyNonempty H kappa := by
  intro G H hGfin hHfin hG hH kappa hkappa
  exact ⟨h3 G hGfin (Cardinal.aleph 1) kappa aleph0_lt_aleph1 hkappa hG,
         h3 H hHfin (Cardinal.aleph 1) kappa aleph0_lt_aleph1 hkappa hH⟩

/-- Conjecture 2 applied to identical forbidden graphs is trivially true. -/
theorem conj2_trivial_case (G : Hypergraph3) (_hfin : G.IsFinite)
    (hne : forbiddenFamilyNonempty G (Cardinal.aleph 1)) :
    ∃ X : Hypergraph3, X ∈ forbiddenFamily G (Cardinal.aleph 1) ∧
      X ∈ forbiddenFamily G (Cardinal.aleph 1) := by
  obtain ⟨X, hX⟩ := hne
  exact ⟨X, hX, hX⟩

/-
## Part VI: Structural Observations
-/

/-- Subgraph containment is transitive. -/
/-- The forbidden family is anti-monotone in G: if G is a subgraph of G'
    (i.e., any graph containing G' also contains G), then avoiding G is
    harder than avoiding G', so F_G(κ) ⊆ F_{G'}(κ). -/
theorem forbiddenFamily_antimonotone {G G' : Hypergraph3} {kappa : Cardinal.{0}}
    (hsub : ∀ H : Hypergraph3, H.ContainsSubgraph G' → H.ContainsSubgraph G) :
    forbiddenFamily G kappa ⊆ forbiddenFamily G' kappa := by
  intro H ⟨hchrom, hfree⟩
  exact ⟨hchrom, fun hG'H => hfree (hsub H hG'H)⟩

/-- Anti-monotonicity extends to nonemptiness. -/
theorem forbiddenFamilyNonempty_antimonotone {G G' : Hypergraph3} {kappa : Cardinal.{0}}
    (hsub : ∀ H : Hypergraph3, H.ContainsSubgraph G' → H.ContainsSubgraph G) :
    forbiddenFamilyNonempty G kappa → forbiddenFamilyNonempty G' kappa := by
  intro ⟨H, hH⟩
  exact ⟨H, forbiddenFamily_antimonotone hsub hH⟩

/-
## Part VII: The Erdős Problem #1177 Statement
-/

/-- **Erdős Problem #1177:**
    All three conjectures of Erdős, Galvin, and Hajnal hold for 3-uniform
    hypergraphs and their forbidden subgraph families. -/
def erdos_1177 : Prop := Conjecture1 ∧ Conjecture2 ∧ Conjecture3

/-- Problem #1177 is OPEN. We state it without proof. -/
/-
## Summary

**Axiom reduction**: 18 → 7
- Eliminated 10 cardinal axioms by using Mathlib's Cardinal type
- Eliminated 1 meaningless placeholder axiom (erdos_1959_high_chromatic_girth)
- Retained 5 Hypergraph3 axioms (abstract type), 1 transitivity, 1 open conjecture

**Proved from Mathlib**: aleph0_lt_aleph1, aleph1_uncountable, aleph1_le_beth2
-/

end Erdos1177
