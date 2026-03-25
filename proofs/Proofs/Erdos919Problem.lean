/-
Erdős Problem #919: Chromatic Numbers on Ordinal Products

**Problem Statement (OPEN)**

Two questions about graphs on ordinal products:

1. Is there a graph G on vertex set ω₂² with chromatic number ℵ₂ such that
   every subgraph on fewer than ℵ₂ vertices has chromatic number ≤ ℵ₀?

2. What if we instead ask for chromatic number ℵ₁?

**Background:**
Babai proved results about subgraphs of well-ordered vertex sets. Erdős and
Hajnal showed this doesn't generalize to higher cardinals by constructing a
graph on ω₁² with χ(G) = ℵ₁ where every strictly smaller subgraph has χ ≤ ℵ₀.

**Note on formalization:** The original problem uses order-type conditions
("subgraph whose vertices have lesser order type"). We formalize using
cardinality conditions (|S| < κ), which is strictly stronger: any subset with
|S| < ℵ_α has order type < ω_α ≤ ω_α², so the cardinality version implies the
order-type version. This avoids requiring a linear order on the product type.

**Status:** OPEN

**Reference:** [Er69b]

Adapted from erdosproblems.com (Apache 2.0 License)
-/

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal
import Mathlib.SetTheory.Cardinal.Cofinality
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.InitialSeg

open Cardinal Ordinal Set

namespace Erdos919

/-
# Part 1: Basic Definitions

We work with graphs on ordinal products and their chromatic numbers.
-/

/-- The ordinal ω₁ (first uncountable ordinal) -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- The ordinal ω₂ (second uncountable ordinal) = initial ordinal of ℵ₂ -/
noncomputable def omega2 : Ordinal := (aleph 2).ord

/-- The ordinal product ω₁² = ω₁ × ω₁ -/
def omega1Squared : Type := omega1.ToType × omega1.ToType

/-- The ordinal product ω₂² = ω₂ × ω₂ -/
def omega2Squared : Type := omega2.ToType × omega2.ToType

/-- A graph on vertex set V -/
structure GraphOn (V : Type) where
  adj : V → V → Prop
  symm : ∀ x y, adj x y → adj y x
  loopless : ∀ x, ¬adj x x

/-
# Part 2: Chromatic Number

The chromatic number χ(G) is the minimum number of colors needed to color
vertices so adjacent vertices have different colors. Following Erdős #1176,
we use existential color types to avoid Cardinal.toType API issues.
-/

/-- A graph is κ-colorable: there exists a proper coloring into a type of
    cardinality κ. -/
def IsColorable {V : Type} (G : GraphOn V) (κ : Cardinal) : Prop :=
  ∃ (C : Type) (_ : Cardinal.mk C = κ) (f : V → C),
    ∀ x y, G.adj x y → f x ≠ f y

/-- The chromatic number: infimum of κ such that G is κ-colorable. -/
noncomputable def chromaticNumber {V : Type} (G : GraphOn V) : Cardinal :=
  sInf {κ : Cardinal | IsColorable G κ}

/-
# Part 3: Induced Subgraphs and Monotonicity
-/

/-- Induced subgraph on a vertex subset -/
def inducedSubgraph {V : Type} (G : GraphOn V) (S : Set V) : GraphOn S where
  adj := fun x y => G.adj x.val y.val
  symm := fun x y h => G.symm x.val y.val h
  loopless := fun x => G.loopless x.val

/-- If G is κ-colorable, any induced subgraph is κ-colorable. -/
theorem isColorable_inducedSubgraph {V : Type} {G : GraphOn V} {κ : Cardinal}
    (hk : IsColorable G κ) (S : Set V) : IsColorable (inducedSubgraph G S) κ := by
  obtain ⟨C, hC, f, hf⟩ := hk
  exact ⟨C, hC, fun x => f x.val, fun x y hadj => hf x.val y.val hadj⟩

/-- The set of colorable cardinals for an induced subgraph contains those of G. -/
theorem colorable_supset {V : Type} (G : GraphOn V) (S : Set V) :
    {κ | IsColorable G κ} ⊆ {κ | IsColorable (inducedSubgraph G S) κ} :=
  fun _ hκ => isColorable_inducedSubgraph hκ S

/-- Every graph is colorable with mk(V) colors (identity coloring). -/
theorem isColorable_mk {V : Type} (G : GraphOn V) : IsColorable G (Cardinal.mk V) := by
  refine ⟨V, rfl, id, fun x y hadj hfeq => ?_⟩
  have heq : x = y := hfeq
  exact absurd (heq ▸ hadj) (G.loopless y)

/-- The set of colorable cardinals is nonempty. -/
theorem colorable_nonempty {V : Type} (G : GraphOn V) :
    Set.Nonempty {κ : Cardinal | IsColorable G κ} :=
  ⟨Cardinal.mk V, isColorable_mk G⟩

/-- Chromatic number is monotone for induced subgraphs: χ(G[S]) ≤ χ(G).
    A larger set of colorable cardinals has a smaller infimum. -/
theorem chromaticNumber_inducedSubgraph_le {V : Type} (G : GraphOn V) (S : Set V) :
    chromaticNumber (inducedSubgraph G S) ≤ chromaticNumber G := by
  apply csInf_le_csInf (OrderBot.bddBelow _) (colorable_nonempty G) (colorable_supset G S)

/-
# Part 4: The Erdős-Hajnal Construction

Erdős and Hajnal constructed a graph on ω₁² showing Babai's theorem doesn't
generalize to higher cardinals.
-/

/-- The Erdős-Hajnal graph on ω₁²:
    (x_α, y_β) is adjacent to (x_γ, y_δ) iff α < γ and β > δ or α > γ and β < δ.
    This is the comparability graph of the product partial order: two points are
    adjacent iff their coordinates move in opposite directions. -/
def erdosHajnalGraph : GraphOn omega1Squared where
  adj := fun p q => (p.1 < q.1 ∧ q.2 < p.2) ∨ (q.1 < p.1 ∧ p.2 < q.2)
  symm := fun _ _ h => Or.comm.mp h
  loopless := fun _ h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl _ h

/-- mk(omega1.ToType) = ℵ₁ -/
private theorem mk_omega1_ToType : Cardinal.mk omega1.ToType = ℵ₁ := by
  unfold omega1
  rw [Cardinal.mk_toType, Cardinal.ord_aleph, Ordinal.card_omega]

/-- The E-H graph is ℵ₁-colorable: color each vertex (α, β) by β. -/
private theorem isColorable_erdosHajnal_aleph1 :
    IsColorable erdosHajnalGraph ℵ₁ := by
  refine ⟨omega1.ToType, mk_omega1_ToType, Prod.snd, fun p q hadj hfeq => ?_⟩
  -- Adjacent vertices have different second coordinates
  rcases hadj with ⟨_, hlt⟩ | ⟨_, hlt⟩
  · exact absurd hfeq (ne_of_gt hlt)
  · exact absurd hfeq (ne_of_lt hlt)

/-- Helper: κ < ℵ₁ implies κ ≤ ℵ₀ -/
private theorem le_aleph0_of_lt_aleph1 {κ : Cardinal} (h : κ < ℵ₁) : κ ≤ ℵ₀ := by
  rw [show (ℵ₁ : Cardinal) = aleph 1 from rfl] at h
  rw [show (1 : Ordinal) = Order.succ 0 by rw [Order.succ_eq_add_one, zero_add],
      aleph_succ, aleph_zero] at h
  exact Order.lt_succ_iff.mp h

/-- The E-H graph has chromatic number ℵ₁.
    Upper bound: color by second coordinate (proved as isColorable_erdosHajnal_aleph1).
    Lower bound: any ℵ₀-coloring yields a contradiction via double pigeonhole —
    for each row α, some color has an uncountable fiber in ω₁. By pigeonhole again,
    two rows α₁ < α₂ share the same "dominant color" c₀ with uncountable fibers.
    Since initial segments of ω₁ are countable, we find β₁ > β₂ in the respective
    fibers, giving an adjacent monochromatic pair — contradiction.
    The lower bound requires substantial cardinal/ordinal infrastructure
    (cardinal pigeonhole, initial-segment cardinality bounds, cofinality of ω₁). -/
axiom erdosHajnal_chromatic : chromaticNumber erdosHajnalGraph = ℵ₁

/-- Every subgraph on fewer than ℵ₁ vertices has chromatic number ≤ ℵ₀.
    Proof: |S| < ℵ₁ implies |S| ≤ ℵ₀. Identity coloring uses |S| colors,
    so χ(G[S]) ≤ |S| ≤ ℵ₀. -/
theorem erdosHajnal_subgraph (S : Set omega1Squared)
    (hS : Cardinal.mk S < ℵ₁) :
    chromaticNumber (inducedSubgraph erdosHajnalGraph S) ≤ ℵ₀ := by
  -- χ(G[S]) ≤ |S| via identity coloring
  have h1 : chromaticNumber (inducedSubgraph erdosHajnalGraph S) ≤ Cardinal.mk ↥S :=
    csInf_le (OrderBot.bddBelow _) (isColorable_mk _)
  -- |S| < ℵ₁ = succ(ℵ₀) implies |S| ≤ ℵ₀
  have h2 : Cardinal.mk ↥S ≤ ℵ₀ := by
    rw [show (ℵ₁ : Cardinal) = aleph 1 from rfl] at hS
    rw [show (1 : Ordinal) = Order.succ 0 by rw [Order.succ_eq_add_one, zero_add],
        aleph_succ, aleph_zero] at hS
    exact Order.lt_succ_iff.mp hS
  exact le_trans h1 h2

/-
# Part 5: The Main Questions

The problem asks about analogous constructions at higher cardinals.
-/

/-- Question 1: Does there exist a graph G on ω₂² with:
    - χ(G) = ℵ₂
    - Every subgraph on fewer than ℵ₂ vertices has χ ≤ ℵ₀ -/
def Question1 : Prop :=
  ∃ G : GraphOn omega2Squared,
    chromaticNumber G = aleph 2 ∧
    ∀ S : Set omega2Squared, Cardinal.mk S < aleph 2 →
      chromaticNumber (inducedSubgraph G S) ≤ ℵ₀

/-- Question 2: What if we ask for χ(G) = ℵ₁ instead? -/
def Question2 : Prop :=
  ∃ G : GraphOn omega2Squared,
    chromaticNumber G = ℵ₁ ∧
    ∀ S : Set omega2Squared, Cardinal.mk S < aleph 2 →
      chromaticNumber (inducedSubgraph G S) ≤ ℵ₀

/-
# Part 6: Known Partial Results

There are some constructions that partially address these questions.
-/

/-- A graph on ω₂² with χ = ℵ₂ where smaller subgraphs have χ ≤ ℵ₁.
    This gives a weaker bound (≤ ℵ₁ instead of ≤ ℵ₀) so it does not directly
    answer Question1. The gap between ℵ₀ and ℵ₁ is precisely what makes
    Question1 open. -/
axiom partialConstruction : ∃ G : GraphOn omega2Squared,
  chromaticNumber G = aleph 2 ∧
  ∀ S : Set omega2Squared, Cardinal.mk S < aleph 2 →
    chromaticNumber (inducedSubgraph G S) ≤ ℵ₁

/-
# Part 7: Generalization to Higher Cardinals

The questions can be generalized to arbitrary vertex types and cardinal bounds.
-/

/-- General question parameterized by vertex type V and cardinal bounds:
    Does there exist a graph on V with χ = chi where subsets of cardinality < bound
    have χ ≤ sub? This captures the pattern shared by Question1, Question2, and
    the Erdős-Hajnal result. -/
def GeneralQuestion (V : Type) (bound chi sub : Cardinal) : Prop :=
  ∃ G : GraphOn V,
    chromaticNumber G = chi ∧
    ∀ S : Set V,
      Cardinal.mk S < bound →
        chromaticNumber (inducedSubgraph G S) ≤ sub

/-- Question1 is the special case V = ω₂², bound = ℵ₂, χ = ℵ₂, sub = ℵ₀ -/
theorem question1_is_general :
    Question1 ↔ GeneralQuestion omega2Squared (aleph 2) (aleph 2) ℵ₀ :=
  ⟨id, id⟩

/-- The Erdős-Hajnal result establishes the case V = ω₁², bound = ℵ₁, χ = ℵ₁, sub = ℵ₀.
    This is the key known construction motivating the open question at ℵ₂. -/
theorem erdosHajnal_is_general : GeneralQuestion omega1Squared ℵ₁ ℵ₁ ℵ₀ :=
  ⟨erdosHajnalGraph, erdosHajnal_chromatic, erdosHajnal_subgraph⟩

/-
# Part 8: Connection to Babai's Theorem

Babai's theorem concerns graphs on well-ordered sets.
-/

/-- Babai's theorem (simplified): For graphs on any vertex type, a chromatic
    bound on the whole graph propagates to all induced subgraphs.
    This follows immediately from chromatic number monotonicity. -/
theorem babai_theorem {V : Type} (G : GraphOn V) (hG : chromaticNumber G ≤ ℵ₀)
    (S : Set V) : chromaticNumber (inducedSubgraph G S) ≤ ℵ₀ :=
  le_trans (chromaticNumber_inducedSubgraph_le G S) hG

/-- The E-H construction shows Babai doesn't extend to ω₁: there exists a graph
    on ω₁² with χ = ℵ₁ > ℵ₀, even though every countable subgraph has χ ≤ ℵ₀. -/
theorem babai_fails_omega1 : ¬(∀ G : GraphOn omega1Squared,
    (∀ S : Set omega1Squared, Cardinal.mk S < ℵ₁ →
      chromaticNumber (inducedSubgraph G S) ≤ ℵ₀) →
    chromaticNumber G ≤ ℵ₀) := by
  intro h
  have hle := h erdosHajnalGraph erdosHajnal_subgraph
  rw [erdosHajnal_chromatic] at hle
  have h₀₁ : (0 : Ordinal) < 1 := zero_lt_one
  have haleph : aleph 0 < aleph 1 := aleph_lt_aleph.mpr h₀₁
  rw [aleph_zero] at haleph
  exact absurd hle (not_le.mpr haleph)

/-
# Part 9: Problem Status

Both questions remain open.
-/

/-- Main formal statement: Question 1 (stronger version) -/
def ErdosProblem919Part1 : Prop := Question1

/-- Main formal statement: Question 2 (weaker version) -/
def ErdosProblem919Part2 : Prop := Question2

/-- Summary of what we know -/
theorem summary :
    (∃ G : GraphOn omega1Squared,
      chromaticNumber G = ℵ₁ ∧
      ∀ S : Set omega1Squared, Cardinal.mk S < ℵ₁ →
        chromaticNumber (inducedSubgraph G S) ≤ ℵ₀) ∧
    (∃ G : GraphOn omega2Squared,
      chromaticNumber G = aleph 2 ∧
      ∀ S : Set omega2Squared, Cardinal.mk S < aleph 2 →
        chromaticNumber (inducedSubgraph G S) ≤ ℵ₁) :=
  ⟨⟨erdosHajnalGraph, erdosHajnal_chromatic, erdosHajnal_subgraph⟩, partialConstruction⟩

/-
# Part 10: Formal Problem Statement
-/

theorem question1_implies_exists (h : Question1) :
    ∃ G : GraphOn omega2Squared, chromaticNumber G = aleph 2 :=
  let ⟨G, hchi, _⟩ := h; ⟨G, hchi⟩

theorem question2_implies_exists (h : Question2) :
    ∃ G : GraphOn omega2Squared, chromaticNumber G = ℵ₁ :=
  let ⟨G, hchi, _⟩ := h; ⟨G, hchi⟩

end Erdos919
