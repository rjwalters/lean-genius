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
import Mathlib.SetTheory.Cardinal.Order
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

/-
# Part 4a: Infrastructure for Chromatic Number Lower Bound

We prove χ(E-H graph) = ℵ₁ via a double pigeonhole argument. The key steps:
1. Cardinal pigeonhole: uncountable domain + countable codomain → uncountable fiber
2. Initial segments of ω₁ are countable (so uncountable sets are cofinal)
3. Double pigeonhole on rows then colors gives a monochromatic edge
-/

/-- ℵ₀ < ℵ₁: used throughout the lower bound proof -/
private theorem aleph0_lt_aleph1 : (ℵ₀ : Cardinal) < ℵ₁ := by
  have : aleph 0 < aleph 1 := aleph_lt_aleph.mpr (by norm_num)
  rwa [aleph_zero] at this

/-- ℵ₁ = Order.succ ℵ₀ -/
private theorem aleph1_eq_succ_aleph0 : (ℵ₁ : Cardinal) = Order.succ ℵ₀ := by
  show aleph 1 = Order.succ (aleph 0)
  rw [show (1 : Ordinal) = Order.succ 0 by rw [Order.succ_eq_add_one, zero_add],
      aleph_succ]

/-- ω₁.ToType is uncountable: ℵ₀ < #(ω₁.ToType) -/
private theorem mk_omega1_ToType_gt_aleph0 : ℵ₀ < Cardinal.mk omega1.ToType := by
  rw [mk_omega1_ToType]; exact aleph0_lt_aleph1

/-- Cardinal pigeonhole for uncountable → countable maps:
    If f : A → B with #A > ℵ₀ and #B ≤ ℵ₀, then some fiber has cardinality > ℵ₀. -/
private theorem exists_uncountable_fiber {A B : Type} (f : A → B)
    (hA : ℵ₀ < Cardinal.mk A) (hB : Cardinal.mk B ≤ ℵ₀) :
    ∃ b : B, ℵ₀ < Cardinal.mk (f ⁻¹' {b}) := by
  by_contra hall
  push_neg at hall
  -- All fibers have cardinality ≤ ℵ₀
  have hle : Cardinal.mk A ≤ Cardinal.mk B * ℵ₀ :=
    mk_le_mk_mul_of_mk_preimage_le f hall
  -- #B * ℵ₀ ≤ ℵ₀ * ℵ₀ = ℵ₀
  have hmul : Cardinal.mk B * ℵ₀ ≤ ℵ₀ := by
    calc Cardinal.mk B * ℵ₀ ≤ ℵ₀ * ℵ₀ := mul_le_mul_right' hB ℵ₀
      _ = ℵ₀ := mul_eq_self le_rfl
  exact absurd (lt_of_lt_of_le hA (le_trans hle hmul)) (lt_irrefl _)

/-- Initial segments of omega1.ToType below any element are countable.
    Uses: typein gives ordinal of element, which is < omega1, so its card < ℵ₁. -/
private theorem mk_Iio_omega1_le_aleph0 (a : omega1.ToType) :
    Cardinal.mk {x : omega1.ToType | x < a} ≤ ℵ₀ := by
  -- The ordinal of a in omega1.ToType is < omega1
  have hlt : Ordinal.typein (· < · : omega1.ToType → omega1.ToType → Prop) a < omega1 :=
    Ordinal.typein_lt_type _ a
  -- card(typein a) = #{x | x < a}  (by definition of typein + card_type)
  have hcard : (Ordinal.typein (· < · : omega1.ToType → omega1.ToType → Prop) a).card =
      Cardinal.mk {x : omega1.ToType | x < a} :=
    Ordinal.card_type (Subrel (· < ·) {x : omega1.ToType | x < a})
  -- typein a < omega1 = (aleph 1).ord, so card(typein a) < aleph 1 = ℵ₁
  have hcard_lt : (Ordinal.typein (· < · : omega1.ToType → omega1.ToType → Prop) a).card < ℵ₁ := by
    rw [show (ℵ₁ : Cardinal) = aleph 1 from rfl]
    exact Cardinal.lt_ord.mp (by rwa [Cardinal.ord_aleph] at hlt)
  rw [← hcard]
  exact le_aleph0_of_lt_aleph1 hcard_lt

/-- Uncountable subsets of omega1.ToType are cofinal: for any a, there exists s > a in S. -/
private theorem uncountable_cofinal (S : Set omega1.ToType)
    (hS : ℵ₀ < Cardinal.mk S) (a : omega1.ToType) :
    ∃ s, s ∈ S ∧ a < s := by
  -- If S ⊆ {x | x ≤ a} = {x | ¬(a < x)}, then #S ≤ #{x | x ≤ a}
  by_contra hall
  push_neg at hall
  -- hall : ∀ s, s ∈ S → ¬(a < s), i.e., ∀ s ∈ S, s ≤ a
  -- So S ⊆ {x | x ≤ a} = {x | x < a} ∪ {a}
  have hle : Cardinal.mk S ≤ Cardinal.mk {x : omega1.ToType | x ≤ a} := by
    apply Cardinal.mk_subtype_mono
    intro x hx
    exact le_of_not_lt (hall x hx)
  -- #{x | x ≤ a} ≤ #{x | x < a} + 1 ≤ ℵ₀ + 1 = ℵ₀
  have hiio : Cardinal.mk {x : omega1.ToType | x < a} ≤ ℵ₀ := mk_Iio_omega1_le_aleph0 a
  have hiic : Cardinal.mk {x : omega1.ToType | x ≤ a} ≤ ℵ₀ := by
    -- {x | x ≤ a} = {x | x < a} ∪ {a}, and {a} has card 1
    have : {x : omega1.ToType | x ≤ a} ⊆ {x | x < a} ∪ {a} := by
      intro x hx
      rcases lt_or_eq_of_le hx with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc Cardinal.mk {x : omega1.ToType | x ≤ a}
        ≤ Cardinal.mk ({x : omega1.ToType | x < a} ∪ {a} : Set _) :=
          Cardinal.mk_subtype_mono this
      _ ≤ Cardinal.mk {x : omega1.ToType | x < a} + Cardinal.mk ({a} : Set _) :=
          Cardinal.mk_union_le _ _
      _ ≤ ℵ₀ + 1 := by
          apply add_le_add hiio
          rw [Cardinal.mk_singleton]
      _ = ℵ₀ := Cardinal.add_one_of_aleph0_le le_rfl
  exact absurd (lt_of_lt_of_le hS (le_trans hle hiic)) (lt_irrefl _)

/-- Nonempty from uncountable: #S > ℵ₀ implies S is nonempty -/
private theorem nonempty_of_uncountable {α : Type} {S : Set α}
    (h : ℵ₀ < Cardinal.mk S) : S.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro he
  rw [he, Cardinal.mk_emptyCollection] at h
  exact absurd h (not_lt.mpr (Cardinal.zero_le _))

/-- Two distinct elements exist in an uncountable set -/
private theorem exists_two_distinct {α : Type} [LinearOrder α] {S : Set α}
    (h : ℵ₀ < Cardinal.mk S) :
    ∃ a₁ a₂, a₁ ∈ S ∧ a₂ ∈ S ∧ a₁ < a₂ := by
  -- #S > ℵ₀ ≥ 2, so S has at least 2 elements
  have hne := nonempty_of_uncountable h
  obtain ⟨x, hx⟩ := hne
  -- S \ {x} is still uncountable (removing one element from an uncountable set)
  have hS' : S.Nonempty := ⟨x, hx⟩
  -- #(S \ {x}) = #S - 1, but for uncountable sets, #S - 1 = #S > ℵ₀
  -- Simpler: #S > 1 since #S > ℵ₀ ≥ 1
  have h1 : (1 : Cardinal) < Cardinal.mk S := lt_trans one_lt_aleph0 h
  rw [Cardinal.one_lt_iff_nontrivial] at h1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := h1.exists_pair_ne
  simp only [Subtype.mk.injEq] at hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, ha, hb, h⟩
  · exact ⟨b, a, hb, ha, h⟩

/-- The E-H graph cannot be properly colored with countably many colors.
    Proof by double pigeonhole:
    1. Each row has a "dominant" color with uncountable fiber
    2. Some color is dominant for uncountably many rows
    3. Two such rows give a monochromatic adjacent pair via cofinality -/
private theorem erdosHajnal_not_countably_colorable
    (C : Type) (hC : Cardinal.mk C ≤ ℵ₀)
    (f : omega1Squared → C)
    (hf : ∀ x y, erdosHajnalGraph.adj x y → f x ≠ f y) :
    False := by
  -- Abbreviation for the vertex type
  set T := omega1.ToType
  have hTunc : ℵ₀ < Cardinal.mk T := mk_omega1_ToType_gt_aleph0
  -- Step 1: For each row α, some color has an uncountable fiber
  have hrow : ∀ α : T, ∃ c : C, ℵ₀ < Cardinal.mk (Set.preimage (fun β : T => f (α, β)) {c}) :=
    fun α => exists_uncountable_fiber (fun β => f (α, β)) hTunc hC
  -- Step 2: Define dominant color for each row via Choice
  let domColor : T → C := fun α => (hrow α).choose
  have hdom_spec : ∀ α : T,
      ℵ₀ < Cardinal.mk (Set.preimage (fun β : T => f (α, β)) {domColor α}) :=
    fun α => (hrow α).choose_spec
  -- Step 3: Pigeonhole on dominant colors — some color c₀ is dominant for uncountably many rows
  obtain ⟨c₀, hc₀⟩ := exists_uncountable_fiber domColor hTunc hC
  -- The set of rows where domColor = c₀
  set Rows := domColor ⁻¹' {c₀} with hRows_def
  -- Rows is a subset of T, and its subtype has cardinality > ℵ₀
  -- Convert to Set for easier manipulation
  have hRowsSet : ℵ₀ < Cardinal.mk {α : T | domColor α = c₀} := by
    convert hc₀ using 1
  -- Step 4: Pick two rows α₁ < α₂ with dominant color c₀
  obtain ⟨α₁, α₂, hα₁, hα₂, hlt_α⟩ := exists_two_distinct hRowsSet
  -- Both rows have uncountable c₀-fibers
  have hα₁_dom : domColor α₁ = c₀ := hα₁
  have hα₂_dom : domColor α₂ = c₀ := hα₂
  -- The c₀-fiber in row α₁: {β | f(α₁, β) = c₀} is uncountable
  have hfiber₁ : ℵ₀ < Cardinal.mk {β : T | f (α₁, β) = c₀} := by
    have := hdom_spec α₁; rw [hα₁_dom] at this
    convert this using 1
  -- The c₀-fiber in row α₂ is nonempty (since uncountable)
  have hfiber₂ : ℵ₀ < Cardinal.mk {β : T | f (α₂, β) = c₀} := by
    have := hdom_spec α₂; rw [hα₂_dom] at this
    convert this using 1
  -- Pick any β₂ from the c₀-fiber of row α₂
  obtain ⟨β₂, hβ₂⟩ := nonempty_of_uncountable hfiber₂
  -- Step 5: By cofinality, find β₁ > β₂ in the c₀-fiber of row α₁
  obtain ⟨β₁, hβ₁, hlt_β⟩ := uncountable_cofinal {β : T | f (α₁, β) = c₀} hfiber₁ β₂
  -- Step 6: (α₁, β₁) and (α₂, β₂) are adjacent: α₁ < α₂ and β₂ < β₁
  have hadj : erdosHajnalGraph.adj (α₁, β₁) (α₂, β₂) := by
    left; exact ⟨hlt_α, hlt_β⟩
  -- But both have color c₀ — contradiction with proper coloring
  have hcolor₁ : f (α₁, β₁) = c₀ := hβ₁
  have hcolor₂ : f (α₂, β₂) = c₀ := hβ₂
  exact hf _ _ hadj (by rw [hcolor₁, hcolor₂])

/-- The E-H graph has chromatic number ℵ₁.
    Upper bound: color by second coordinate (proved as isColorable_erdosHajnal_aleph1).
    Lower bound: any ℵ₀-coloring yields a contradiction via double pigeonhole —
    for each row α, some color has an uncountable fiber in ω₁. By pigeonhole again,
    two rows α₁ < α₂ share the same "dominant color" c₀ with uncountable fibers.
    Since initial segments of ω₁ are countable, we find β₁ > β₂ in the respective
    fibers, giving an adjacent monochromatic pair — contradiction. -/
theorem erdosHajnal_chromatic : chromaticNumber erdosHajnalGraph = ℵ₁ := by
  apply le_antisymm
  · -- Upper bound: χ ≤ ℵ₁ via second-coordinate coloring
    exact csInf_le (OrderBot.bddBelow _) isColorable_erdosHajnal_aleph1
  · -- Lower bound: ℵ₁ ≤ χ, i.e., for any κ-coloring, ℵ₁ ≤ κ
    apply le_csInf (colorable_nonempty erdosHajnalGraph)
    intro κ ⟨C, hCk, f, hf⟩
    -- If κ < ℵ₁, then κ ≤ ℵ₀, so the coloring is countable → contradiction
    by_contra hlt
    push_neg at hlt
    have hle : κ ≤ ℵ₀ := le_aleph0_of_lt_aleph1 hlt
    rw [← hCk] at hle
    exact erdosHajnal_not_countably_colorable C hle f hf

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

/-- The Erdős-Hajnal graph on ω₂²: two pairs (α₁,β₁) and (α₂,β₂)
    are adjacent iff one coordinate increases while the other decreases.
    This is the natural generalization of `erdosHajnalGraph` from ω₁² to ω₂². -/
def erdosHajnalGraph2 : GraphOn omega2Squared where
  adj := fun p q => (p.1 < q.1 ∧ q.2 < p.2) ∨ (q.1 < p.1 ∧ p.2 < q.2)
  symm := fun _ _ h => Or.comm.mp h
  loopless := fun _ h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ <;> exact lt_irrefl _ h

/-- mk(omega2.ToType) = ℵ₂ -/
private theorem mk_omega2_ToType : Cardinal.mk omega2.ToType = aleph 2 := by
  unfold omega2
  rw [Cardinal.mk_toType, Cardinal.ord_aleph, Ordinal.card_omega]

/-- The ω₂² E-H graph is ℵ₂-colorable: color each vertex (α, β) by β. -/
private theorem isColorable_erdosHajnal2_aleph2 :
    IsColorable erdosHajnalGraph2 (aleph 2) := by
  refine ⟨omega2.ToType, mk_omega2_ToType, Prod.snd, fun p q hadj hfeq => ?_⟩
  rcases hadj with ⟨_, hlt⟩ | ⟨_, hlt⟩
  · exact absurd hfeq (ne_of_gt hlt)
  · exact absurd hfeq (ne_of_lt hlt)

/-- Helper: κ < ℵ₂ implies κ ≤ ℵ₁ -/
private theorem le_aleph1_of_lt_aleph2 {κ : Cardinal} (h : κ < aleph 2) : κ ≤ ℵ₁ := by
  rw [show (2 : Ordinal) = Order.succ 1 by rw [Order.succ_eq_add_one]; norm_num,
      aleph_succ] at h
  exact Order.lt_succ_iff.mp h

/-- Subsets of ω₂² with fewer than ℵ₂ elements have chromatic number ≤ ℵ₁
    in the E-H graph. Proof: χ(G[S]) ≤ |S| ≤ ℵ₁ since |S| < ℵ₂ = succ(ℵ₁). -/
theorem erdosHajnal2_subgraph (S : Set omega2Squared)
    (hS : Cardinal.mk S < aleph 2) :
    chromaticNumber (inducedSubgraph erdosHajnalGraph2 S) ≤ ℵ₁ := by
  have h1 : chromaticNumber (inducedSubgraph erdosHajnalGraph2 S) ≤ Cardinal.mk ↥S :=
    csInf_le (OrderBot.bddBelow _) (isColorable_mk _)
  exact le_trans h1 (le_aleph1_of_lt_aleph2 hS)

/-
# Part 6a: Infrastructure for ω₂² Chromatic Number Lower Bound

We prove χ(E-H graph on ω₂²) = ℵ₂ via double pigeonhole at the ℵ₂ level.
The argument is structurally identical to the ω₁² case but one cardinal level higher.
-/

/-- ℵ₁ < ℵ₂ -/
private theorem aleph1_lt_aleph2 : (ℵ₁ : Cardinal) < aleph 2 := by
  have : aleph 1 < aleph 2 := aleph_lt_aleph.mpr (by norm_num)
  exact this

/-- ω₂.ToType has cardinality > ℵ₁ -/
private theorem mk_omega2_ToType_gt_aleph1 : ℵ₁ < Cardinal.mk omega2.ToType := by
  rw [mk_omega2_ToType]; exact aleph1_lt_aleph2

/-- Cardinal pigeonhole for > ℵ₁ → ≤ ℵ₁ maps:
    If f : A → B with #A > ℵ₁ and #B ≤ ℵ₁, then some fiber has cardinality > ℵ₁. -/
private theorem exists_large_fiber {A B : Type} (f : A → B)
    (hA : ℵ₁ < Cardinal.mk A) (hB : Cardinal.mk B ≤ ℵ₁) :
    ∃ b : B, ℵ₁ < Cardinal.mk (f ⁻¹' {b}) := by
  by_contra hall
  push_neg at hall
  have hle : Cardinal.mk A ≤ Cardinal.mk B * ℵ₁ :=
    mk_le_mk_mul_of_mk_preimage_le f hall
  have hmul : Cardinal.mk B * ℵ₁ ≤ ℵ₁ := by
    calc Cardinal.mk B * ℵ₁ ≤ ℵ₁ * ℵ₁ := mul_le_mul_right' hB ℵ₁
      _ = ℵ₁ := mul_eq_self aleph0_lt_aleph1.le
  exact absurd (lt_of_lt_of_le hA (le_trans hle hmul)) (lt_irrefl _)

/-- Initial segments of omega2.ToType below any element have cardinality ≤ ℵ₁.
    Uses: typein gives ordinal of element, which is < omega2, so its card < ℵ₂. -/
private theorem mk_Iio_omega2_le_aleph1 (a : omega2.ToType) :
    Cardinal.mk {x : omega2.ToType | x < a} ≤ ℵ₁ := by
  have hlt : Ordinal.typein (· < · : omega2.ToType → omega2.ToType → Prop) a < omega2 :=
    Ordinal.typein_lt_type _ a
  have hcard : (Ordinal.typein (· < · : omega2.ToType → omega2.ToType → Prop) a).card =
      Cardinal.mk {x : omega2.ToType | x < a} :=
    Ordinal.card_type (Subrel (· < ·) {x : omega2.ToType | x < a})
  have hcard_lt : (Ordinal.typein (· < · : omega2.ToType → omega2.ToType → Prop) a).card < aleph 2 := by
    exact Cardinal.lt_ord.mp (by rwa [Cardinal.ord_aleph] at hlt)
  rw [← hcard]
  exact le_aleph1_of_lt_aleph2 hcard_lt

/-- Sets of cardinality > ℵ₁ in omega2.ToType are cofinal. -/
private theorem large_cofinal (S : Set omega2.ToType)
    (hS : ℵ₁ < Cardinal.mk S) (a : omega2.ToType) :
    ∃ s, s ∈ S ∧ a < s := by
  by_contra hall
  push_neg at hall
  have hle : Cardinal.mk S ≤ Cardinal.mk {x : omega2.ToType | x ≤ a} := by
    apply Cardinal.mk_subtype_mono
    intro x hx
    exact le_of_not_lt (hall x hx)
  have hiio : Cardinal.mk {x : omega2.ToType | x < a} ≤ ℵ₁ := mk_Iio_omega2_le_aleph1 a
  have hiic : Cardinal.mk {x : omega2.ToType | x ≤ a} ≤ ℵ₁ := by
    have : {x : omega2.ToType | x ≤ a} ⊆ {x | x < a} ∪ {a} := by
      intro x hx
      rcases lt_or_eq_of_le hx with h | h
      · exact Or.inl h
      · exact Or.inr h
    calc Cardinal.mk {x : omega2.ToType | x ≤ a}
        ≤ Cardinal.mk ({x : omega2.ToType | x < a} ∪ {a} : Set _) :=
          Cardinal.mk_subtype_mono this
      _ ≤ Cardinal.mk {x : omega2.ToType | x < a} + Cardinal.mk ({a} : Set _) :=
          Cardinal.mk_union_le _ _
      _ ≤ ℵ₁ + 1 := by
          apply add_le_add hiio
          rw [Cardinal.mk_singleton]
      _ = ℵ₁ := Cardinal.add_one_of_aleph0_le aleph0_lt_aleph1.le
  exact absurd (lt_of_lt_of_le hS (le_trans hle hiic)) (lt_irrefl _)

/-- Two distinct elements exist in a set of cardinality > ℵ₁ -/
private theorem exists_two_distinct_large {α : Type} [LinearOrder α] {S : Set α}
    (h : ℵ₁ < Cardinal.mk S) :
    ∃ a₁ a₂, a₁ ∈ S ∧ a₂ ∈ S ∧ a₁ < a₂ := by
  have h1 : (1 : Cardinal) < Cardinal.mk S := lt_trans one_lt_aleph0 (lt_trans aleph0_lt_aleph1 h)
  rw [Cardinal.one_lt_iff_nontrivial] at h1
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := h1.exists_pair_ne
  simp only [Subtype.mk.injEq] at hab
  rcases lt_or_gt_of_ne hab with h | h
  · exact ⟨a, b, ha, hb, h⟩
  · exact ⟨b, a, hb, ha, h⟩

/-- Nonempty from large: #S > ℵ₁ implies S is nonempty -/
private theorem nonempty_of_large {α : Type} {S : Set α}
    (h : ℵ₁ < Cardinal.mk S) : S.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro he
  rw [he, Cardinal.mk_emptyCollection] at h
  exact absurd h (not_lt.mpr (Cardinal.zero_le _))

/-- The ω₂² E-H graph cannot be properly colored with ≤ ℵ₁ colors.
    Proof by double pigeonhole at the ℵ₂ level:
    1. Each row has a "dominant" color with fiber of size > ℵ₁
    2. Some color is dominant for > ℵ₁ rows
    3. Two such rows give a monochromatic adjacent pair via cofinality -/
private theorem erdosHajnal2_not_aleph1_colorable
    (C : Type) (hC : Cardinal.mk C ≤ ℵ₁)
    (f : omega2Squared → C)
    (hf : ∀ x y, erdosHajnalGraph2.adj x y → f x ≠ f y) :
    False := by
  set T := omega2.ToType
  have hTunc : ℵ₁ < Cardinal.mk T := mk_omega2_ToType_gt_aleph1
  -- Step 1: For each row α, some color has a fiber of size > ℵ₁
  have hrow : ∀ α : T, ∃ c : C, ℵ₁ < Cardinal.mk (Set.preimage (fun β : T => f (α, β)) {c}) :=
    fun α => exists_large_fiber (fun β => f (α, β)) hTunc hC
  -- Step 2: Define dominant color for each row via Choice
  let domColor : T → C := fun α => (hrow α).choose
  have hdom_spec : ∀ α : T,
      ℵ₁ < Cardinal.mk (Set.preimage (fun β : T => f (α, β)) {domColor α}) :=
    fun α => (hrow α).choose_spec
  -- Step 3: Pigeonhole on dominant colors — some color c₀ is dominant for > ℵ₁ rows
  obtain ⟨c₀, hc₀⟩ := exists_large_fiber domColor hTunc hC
  set Rows := domColor ⁻¹' {c₀} with hRows_def
  have hRowsSet : ℵ₁ < Cardinal.mk {α : T | domColor α = c₀} := by
    convert hc₀ using 1
  -- Step 4: Pick two rows α₁ < α₂ with dominant color c₀
  obtain ⟨α₁, α₂, hα₁, hα₂, hlt_α⟩ := exists_two_distinct_large hRowsSet
  have hα₁_dom : domColor α₁ = c₀ := hα₁
  have hα₂_dom : domColor α₂ = c₀ := hα₂
  -- The c₀-fiber in row α₁ has size > ℵ₁
  have hfiber₁ : ℵ₁ < Cardinal.mk {β : T | f (α₁, β) = c₀} := by
    have := hdom_spec α₁; rw [hα₁_dom] at this
    convert this using 1
  -- The c₀-fiber in row α₂ has size > ℵ₁
  have hfiber₂ : ℵ₁ < Cardinal.mk {β : T | f (α₂, β) = c₀} := by
    have := hdom_spec α₂; rw [hα₂_dom] at this
    convert this using 1
  -- Pick any β₂ from the c₀-fiber of row α₂
  obtain ⟨β₂, hβ₂⟩ := nonempty_of_large hfiber₂
  -- Step 5: By cofinality, find β₁ > β₂ in the c₀-fiber of row α₁
  obtain ⟨β₁, hβ₁, hlt_β⟩ := large_cofinal {β : T | f (α₁, β) = c₀} hfiber₁ β₂
  -- Step 6: (α₁, β₁) and (α₂, β₂) are adjacent: α₁ < α₂ and β₂ < β₁
  have hadj : erdosHajnalGraph2.adj (α₁, β₁) (α₂, β₂) := by
    left; exact ⟨hlt_α, hlt_β⟩
  -- But both have color c₀ — contradiction with proper coloring
  have hcolor₁ : f (α₁, β₁) = c₀ := hβ₁
  have hcolor₂ : f (α₂, β₂) = c₀ := hβ₂
  exact hf _ _ hadj (by rw [hcolor₁, hcolor₂])

/-- The ω₂² E-H graph has chromatic number exactly ℵ₂. The upper bound
    follows from ℵ₂-colorability. The lower bound uses double pigeonhole
    at the ℵ₂ level: any ≤ ℵ₁ coloring forces a monochromatic edge. -/
theorem erdosHajnalGraph2_chromatic :
    chromaticNumber erdosHajnalGraph2 = aleph 2 := by
  apply le_antisymm
  · exact csInf_le (OrderBot.bddBelow _) isColorable_erdosHajnal2_aleph2
  · -- Lower bound: aleph 2 ≤ χ, i.e., for any κ-coloring, aleph 2 ≤ κ
    apply le_csInf (colorable_nonempty erdosHajnalGraph2)
    intro κ ⟨C, hCk, f, hf⟩
    by_contra hlt
    push_neg at hlt
    have hle : κ ≤ ℵ₁ := le_aleph1_of_lt_aleph2 hlt
    rw [← hCk] at hle
    exact erdosHajnal2_not_aleph1_colorable C hle f hf

/-- A graph on ω₂² with χ = ℵ₂ where smaller subgraphs have χ ≤ ℵ₁.
    This gives a weaker bound (≤ ℵ₁ instead of ≤ ℵ₀) so it does not directly
    answer Question1. The gap between ℵ₀ and ℵ₁ is precisely what makes
    Question1 open. -/
theorem partialConstruction : ∃ G : GraphOn omega2Squared,
  chromaticNumber G = aleph 2 ∧
  ∀ S : Set omega2Squared, Cardinal.mk S < aleph 2 →
    chromaticNumber (inducedSubgraph G S) ≤ ℵ₁ :=
  ⟨erdosHajnalGraph2, erdosHajnalGraph2_chromatic, erdosHajnal2_subgraph⟩

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
