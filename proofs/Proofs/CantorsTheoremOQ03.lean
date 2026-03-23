import Mathlib

/-
# OQ-03: The Diagonal Argument in Cardinal Arithmetic and Beyond

Source: König (1905), Cantor (1891), Lawvere (1969)

## The Open Question

OQ-03 asks: Can we generalize the diagonal argument to structures beyond sets?

## Answer

YES. OQ-02 showed Lawvere's Fixed-Point Theorem unifies Cantor, Russell, and
Gödel via: surjection + fixed-point-free map → contradiction.

OQ-03 reveals a HIERARCHY of diagonal arguments of increasing generality:

**Level 1 — Lawvere**: One map g with no fixed point, applied uniformly.
**Level 2 — Coordinate**: Different dodge values at each index, same target type.
**Level 3 — König**: Different TYPES and dodges at each index (heterogeneous).

Each level subsumes the previous. König captures cardinal arithmetic
(Σ κᵢ < Π λᵢ when κᵢ < λᵢ), the coordinate diagonal captures
non-enumerability results, and Lawvere captures the fixed-point-theoretic
essence. We show the diagonal argument works on ℕ, ℤ, Bool, Prop, and
arbitrary types — not just on sets.

## Results

Part I:   König's heterogeneous diagonal principle (3 theorems)
Part II:  The coordinate diagonal — intermediate level (2 theorems)
Part III: Cantor and Lawvere as special cases (5 theorems)
Part IV:  Fixed-point-free endomorphisms on various structures (4 theorems)
Part V:   Applications: non-enumerability beyond sets (3 theorems)

Axioms: 0
Sorries: 0
-/

set_option linter.unusedVariables false

namespace CantorsTheoremOQ03

open Function

-- ============================================================
-- PART I: König's Heterogeneous Diagonal Principle
-- ============================================================

/-
## Part I: König's Diagonal Principle

König's theorem (1905) generalizes Cantor's diagonal argument from a single
function space to INDEXED FAMILIES of different types.

The setting:
- ι is an index type
- α, β : ι → Type are families of types (potentially DIFFERENT at each index)
- f : (Σ i, α i) → (Π i, β i) maps the disjoint union to the product

The dodge: at each index i, find an element of β i not hit by any (i, a) pair.
The diagonal element d, where d(i) = dodged element, is not in the range of f.

This is STRICTLY more general than Lawvere:
- Lawvere: one type β, one fixed-point-free map g, same at every coordinate
- König: different types β i, different dodges at each coordinate
-/

/-- **König's Diagonal Principle**: No function from a dependent sum to a
    dependent product is surjective when each coordinate allows dodging.

    At each index i, the "column" {f ⟨i, a⟩ i | a : α i} misses some element
    of β i. Collecting these missed elements gives the diagonal witness. -/
theorem konig_principle {ι : Type*} {α : ι → Type*} {β : ι → Type*}
    (f : (Σ i, α i) → (Π i, β i))
    (h : ∀ i, ∃ b : β i, ∀ a : α i, f ⟨i, a⟩ i ≠ b) :
    ¬Surjective f := by
  intro hf
  choose dodge hdodge using h
  obtain ⟨⟨j, a⟩, hja⟩ := hf dodge
  exact hdodge j a (congr_fun hja j)

/-- **König's explicit witness**: The diagonal element dodge differs from
    f s at coordinate s.1 for every s in the domain. -/
theorem konig_witness_ne {ι : Type*} {α : ι → Type*} {β : ι → Type*}
    (f : (Σ i, α i) → (Π i, β i))
    (dodge : Π i, β i)
    (hdodge : ∀ i (a : α i), f ⟨i, a⟩ i ≠ dodge i) :
    ∀ s : Σ i, α i, f s ≠ dodge := by
  intro ⟨j, a⟩ heq
  exact hdodge j a (congr_fun heq j)

/-- **König for non-surjective columns**: If no column projection
    col_i(a) = f(⟨i, a⟩)(i) is surjective, then f is not surjective.

    This formulation makes the connection to cardinality explicit: when
    |α i| < |β i|, the column at i cannot be surjective. -/
theorem konig_of_column_not_surj {ι : Type*} {α : ι → Type*} {β : ι → Type*}
    (f : (Σ i, α i) → (Π i, β i))
    (h : ∀ i, ¬Surjective (fun a : α i => f ⟨i, a⟩ i)) :
    ¬Surjective f := by
  apply konig_principle
  intro i
  -- Non-surjectivity means some element is missed
  by_contra hall
  push_neg at hall
  exact h i fun b => hall b

-- ============================================================
-- PART II: The Coordinate Diagonal
-- ============================================================

/-
## Part II: The Coordinate Diagonal

An intermediate generalization between Lawvere and König: the target type β
is the SAME at each index, but the dodge value can be DIFFERENT at each index.

This captures enumerability results: given any listing f(0), f(1), f(2), ...
of sequences ι → β, the diagonal d(i) ≠ f(i)(i) is a missed sequence.

- Lawvere: d(i) = g(f(i)(i)) for a FIXED g (uniform strategy)
- Coordinate: d(i) just needs to differ from f(i)(i) (pointwise strategy)
-/

/-- **Coordinate Diagonal**: If dodge(i) ≠ f(i)(i) for all i, then the
    sequence dodge is not in the range of f. The dodge need not come from
    a single fixed-point-free map — any coordinate-wise deviation suffices. -/
theorem coordinate_diagonal {ι : Type*} {β : Type*}
    (f : ι → ι → β) (dodge : ι → β) (h : ∀ i, dodge i ≠ f i i) :
    ¬Surjective f := by
  intro hf
  obtain ⟨n, hn⟩ := hf dodge
  exact h n ((congr_fun hn n).symm)

/-- **Coordinate diagonal witness**: The diagonal element differs from every
    listed sequence at the diagonal position. -/
theorem coordinate_diagonal_ne {ι : Type*} {β : Type*}
    (f : ι → ι → β) (dodge : ι → β) (h : ∀ i, dodge i ≠ f i i) :
    ∀ n : ι, dodge ≠ f n := by
  intro n hn
  exact h n (congr_fun hn n)

-- ============================================================
-- PART III: Cantor and Lawvere as Special Cases
-- ============================================================

/-
## Part III: Deriving Classical Results

Both Lawvere's Fixed-Point Theorem and Cantor's Theorem follow as special
cases of the coordinate diagonal. A fixed-point-free endomorphism g : β → β
provides the uniform dodge strategy: d(i) = g(f(i)(i)).
-/

/-- **Lawvere from coordinate diagonal**: If g : β → β has no fixed point,
    then d(i) = g(f(i)(i)) satisfies the coordinate diagonal condition.
    One line: a fixed-point-free map provides the uniform dodge strategy. -/
theorem lawvere_from_diagonal {α : Type*} {β : Type*}
    (g : β → β) (hg : ∀ b, g b ≠ b)
    (f : α → α → β) : ¬Surjective f :=
  coordinate_diagonal f (fun a => g (f a a)) (fun i => hg (f i i))

/-- **Negation on Prop has no fixed point**: There is no p : Prop with ¬p = p.
    This is the engine of Cantor's theorem and Russell's paradox. -/
theorem not_no_fixed_point : ∀ p : Prop, (¬p) ≠ p := by
  intro p hp
  have h1 : ¬p → p := Eq.mp hp
  have h2 : p → ¬p := Eq.mp hp.symm
  have hnp : ¬p := fun h => h2 h h
  exact hnp (h1 hnp)

/-- **Cantor for Bool via Lawvere**: No function α → (α → Bool) is surjective.
    Bool negation (!b ≠ b) is the fixed-point-free endomorphism. -/
theorem cantor_bool {α : Type*} (f : α → α → Bool) : ¬Surjective f :=
  lawvere_from_diagonal (fun b => !b) (fun b => by cases b <;> decide) f

/-- **Cantor for Prop via Lawvere**: No function α → (α → Prop) is surjective.
    Propositional negation (¬p ≠ p) is the fixed-point-free endomorphism. -/
theorem cantor_prop {α : Type*} (f : α → α → Prop) : ¬Surjective f :=
  lawvere_from_diagonal Not not_no_fixed_point f

/-- **Cantor for Set via Prop**: No function α → Set α is surjective.
    Since Set α = α → Prop, this is the Prop version of Cantor's theorem. -/
theorem cantor_set {α : Type*} (f : α → Set α) : ¬Surjective f :=
  cantor_prop f

-- ============================================================
-- PART IV: Fixed-Point-Free Endomorphisms
-- ============================================================

/-
## Part IV: Fixed-Point-Free Maps on Various Structures

The diagonal argument works on ANY type that admits a fixed-point-free
endomorphism. Different structures yield different diagonal constructions:

- Bool: negation (!b ≠ b)
- ℕ: successor (n+1 ≠ n)
- ℤ: successor (n+1 ≠ n)
- Prop: logical negation (¬p ≠ p)

Each provides a non-enumerability result via Lawvere's theorem.
-/

/-- Bool negation is fixed-point-free. -/
theorem bool_neg_fpf : ∀ b : Bool, !b ≠ b := by decide

/-- Successor on ℕ is fixed-point-free. -/
theorem nat_succ_fpf : ∀ n : ℕ, n + 1 ≠ n := by omega

/-- Successor on ℤ is fixed-point-free. -/
theorem int_succ_fpf : ∀ n : ℤ, n + 1 ≠ n := by omega

/-- **Master theorem**: Any type β with a fixed-point-free endomorphism g
    satisfies: for all α, no f : α → (α → β) is surjective.

    This characterizes the connection between fixed-point-free maps and
    the diagonal argument. The diagonal operates on β precisely when β
    admits an endomorphism without fixed points. -/
theorem fpf_implies_non_enumerable {β : Type*}
    (g : β → β) (hg : ∀ b, g b ≠ b) :
    ∀ {α : Type*} (f : α → α → β), ¬Surjective f :=
  fun f => lawvere_from_diagonal g hg f

-- ============================================================
-- PART V: Non-Enumerability Applications
-- ============================================================

/-
## Part V: Applications Beyond Sets

The diagonal argument proves non-enumerability for function spaces into
ANY type with a fixed-point-free endomorphism. This goes beyond Cantor's
original set-theoretic formulation to algebraic and combinatorial structures.
-/

/-- **ℕ → ℕ is not countable**: No surjection ℕ → (ℕ → ℕ).
    The diagonal element d(n) = f(n)(n) + 1 differs from every listed
    sequence at position n. This uses SUCCESSOR, not complementation. -/
theorem nat_seq_uncountable (f : ℕ → ℕ → ℕ) : ¬Surjective f :=
  fpf_implies_non_enumerable (· + 1) nat_succ_fpf f

/-- **ℕ → ℤ is not countable**: No surjection ℕ → (ℕ → ℤ).
    The integer successor diagonal. -/
theorem int_seq_uncountable (f : ℕ → ℕ → ℤ) : ¬Surjective f :=
  fpf_implies_non_enumerable (· + 1) int_succ_fpf f

/-- **König subsumes Lawvere**: The heterogeneous König principle
    (Level 3) implies the uniform Lawvere principle (Level 1), completing
    the hierarchy: König ⟹ Coordinate ⟹ Lawvere.

    Proof: View f : α → (α → β) as a König map with constant fibers
    α i = PUnit, β i = β. The column at i has |PUnit| = 1 element,
    while g : β → β being fixed-point-free means β has ≥ 2 elements,
    so each column can dodge. -/
theorem konig_implies_lawvere {α : Type*} {β : Type*}
    (g : β → β) (hg : ∀ b, g b ≠ b)
    (f : α → α → β) : ¬Surjective f := by
  -- Encode in König's framework: fibers are Unit (singleton at each index)
  let f' : (Σ _ : α, Unit) → (α → β) := fun ⟨a, _⟩ => f a
  -- Each column can dodge using g
  have hdodge : ∀ a : α, ∃ b : β, ∀ _ : Unit, f' ⟨a, ()⟩ a ≠ b := by
    intro a
    exact ⟨g (f a a), fun _ => Ne.symm (hg (f a a))⟩
  -- König says f' is not surjective
  have hns := konig_principle f' hdodge
  -- Transfer: if f were surjective, f' would be too
  intro hf
  apply hns
  intro h
  obtain ⟨a, ha⟩ := hf h
  exact ⟨⟨a, ()⟩, ha⟩

-- ============================================================
-- SUMMARY
-- ============================================================

/-
## The Diagonal Hierarchy

The diagonal argument is not one technique but a FAMILY of techniques,
organized by generality:

**Level 1 — Lawvere** (1969): Fixed-point-free g : β → β, applied uniformly
  "If g has no fixed point, no f : α → (α → β) is surjective."
  Engine: d(i) = g(f(i)(i)), so d(i) ≠ f(i)(i) by fixed-point-freeness.

**Level 2 — Coordinate Diagonal**: Pointwise dodge, same target type
  "If dodge(i) ≠ f(i)(i) for all i, f is not surjective."
  Engine: d(i) = dodge(i), each coordinate dodges independently.

**Level 3 — König** (1905): Heterogeneous, different types at each index
  "If each column col_i : α i → β i misses an element, f is not surjective."
  Engine: d(i) = missed element of β i, types may differ at each coordinate.

**Implications**: König ⟹ Coordinate ⟹ Lawvere (by specialization).

**Universality**: The diagonal works on ANY structure with a fixed-point-free
endomorphism: Bool (negation), ℕ (successor), ℤ (successor), Prop (¬),
and any type with ≥ 2 distinguishable elements.

**Cardinal Arithmetic**: König's theorem Σ κᵢ < Π λᵢ (when κᵢ < λᵢ for all i)
is precisely this heterogeneous diagonal: the column at i maps a set of size κᵢ
into a set of size λᵢ > κᵢ, so it misses an element. Cantor's κ < 2^κ is the
special case κᵢ = 1, λᵢ = 2.
-/

end CantorsTheoremOQ03
