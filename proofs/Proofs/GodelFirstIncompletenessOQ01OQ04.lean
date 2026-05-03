import Mathlib.Logic.Basic
import Mathlib.Tactic

/-!
# Gödel's Diagonal Lemma: A Principled Formalization (OQ-04)

## What This File Proves

This file formalizes the **Diagonal Lemma** (also called the Fixed-Point Lemma)
and derives Gödel's First Incompleteness Theorem from it. It is a companion to
`GodelFirstIncompletenessOQ01.lean`, providing an alternative axiomatization
that makes the logical structure more transparent.

## The Diagonal Lemma

  ∀ ψ : ℕ → Formula, ∃ σ : Formula, (⊢ σ) ↔ (⊢ ψ(⌈σ⌉))

For any "formula-with-free-variable" ψ, there is a self-referential sentence σ
that is provable if and only if ψ(⌈σ⌉) is provable.

## Comparison with OQ-01

| Property          | OQ-01 approach               | OQ-04 (this file)              |
|-------------------|------------------------------|--------------------------------|
| G_self_reference  | **Axiom** (G = ⟨42⟩)         | **Derived** from diagonal_lem  |
| Diagonal Lemma    | Not stated                   | General **Axiom**              |
| G definition      | Fixed formula code 42        | Constructed from diagonal_lem  |
| neg_G_prov        | Axiom                        | Axiom (needs object-level F)   |
| ω-consistency     | Axiom                        | Axiom (same)                   |
| Total axioms      | 5                            | **5** (same count, better structure) |

The improvement: `G_self_reference` (a hand-crafted axiom for a specific formula)
is now **derived** from the general Diagonal Lemma. The key theorem `G_not_provable`
follows more cleanly, exposing the three distinct mathematical ingredients.

## The Three Components

1. **D1 Representability** (`d1`): Provability is internally representable.
2. **Diagonal Lemma** (`diagonal_lem`): Self-reference is constructible for ANY ψ.
3. **ω-Consistency** (`neg_G_prov` + `omega_cons`): Rules out ¬G.

## Key Insight: G is DERIVED, not ASSUMED

In OQ-01, `G : Formula := ⟨42⟩` is fixed and `G_self_reference` is an axiom.
Here, G is **constructed** as the fixed point of ψ(x) = ¬Prov(x) from the
Diagonal Lemma. The self-reference property `G_spec` is a **theorem**.

This mirrors the actual mathematical proof where G is explicitly constructed
via the diagonal construction: G = φ(⌈φ(sub(x,x))⌉) for the substitution function.
-/

namespace GodelDiagonal

-- ============================================================
-- PART 1: Basic Infrastructure
-- ============================================================

/-- Formulas identified by their Gödel number (code). -/
structure Formula where
  code : Nat
  deriving DecidableEq

/-- Negation of a formula (simplified encoding). -/
def neg (φ : Formula) : Formula := ⟨φ.code + 1⟩
prefix:75 "¬ᶠ" => neg

/-- The Gödel number of a formula is its code. -/
def godelNum (φ : Formula) : Nat := φ.code

/-- The provability formula: Prov(n) expresses "the formula coded by n is provable". -/
def Prov : Nat → Formula := fun n => ⟨n * 2⟩

-- ============================================================
-- PART 2: The First Three Axioms
-- ============================================================

/-- The provability predicate (opaque, non-trivial). -/
axiom Provable : Formula → Prop

notation:50 "⊢ " φ => Provable φ

/-- **Axiom 1 — D1 (Representability)**:
    If F proves φ, then F proves Prov(⌈φ⌉). (Same as OQ-01.) -/
axiom d1 : ∀ φ : Formula, (⊢ φ) → (⊢ Prov (godelNum φ))

/-- **Axiom 2 — Diagonal Lemma** (General Fixed-Point Theorem):
    For ANY unary predicate ψ : ℕ → Formula, there exists a self-referential
    sentence σ such that σ is provable iff ψ(⌈σ⌉) is provable.

    Mathematical content: This is the meta-level Diagonal Lemma. In a full
    formalization, it follows from a computable Gödel numbering with a
    substitution function `sub : ℕ → ℕ → ℕ` and primitive recursion in F.
    Specifically, the construction σ = ψ(sub(⌈ψ∘sub_diag⌉, ⌈ψ∘sub_diag⌉)) works.

    This is the meta-level form: (⊢ σ) ↔ (⊢ ψ(⌈σ⌉)) as a Lean biconditional.
    The object-level form — F ⊢ σ ↔ ψ(⌈σ⌉) as a formula inside F — is stronger
    and would be needed to derive `neg_G_prov` (Axiom 3 below).

    **This axiom replaces OQ-01's `G_self_reference`** — see `G_spec` below. -/
axiom diagonal_lem : ∀ ψ : Nat → Formula, ∃ σ : Formula, (⊢ σ) ↔ (⊢ ψ (godelNum σ))

-- ============================================================
-- PART 3: Define the Gödel Sentence via the Diagonal Lemma
-- ============================================================

/-- The Gödel sentence G is the fixed point of ψ(x) = ¬Prov(x).
    Unlike OQ-01 where `G : Formula := ⟨42⟩` (arbitrary code),
    here G is CONSTRUCTED from the Diagonal Lemma. -/
noncomputable def G : Formula := (diagonal_lem (fun n => ¬ᶠ Prov n)).choose

/-- **G_spec** — Key THEOREM (not an axiom):
    G is provable if and only if ¬Prov(⌈G⌉) is provable.

    In OQ-01, the analogous statement was AXIOM `G_self_reference`. Here it is
    a one-line theorem from `diagonal_lem`. This is the central improvement
    of the OQ-04 formalization. -/
theorem G_spec : (⊢ G) ↔ (⊢ ¬ᶠ Prov (godelNum G)) :=
  (diagonal_lem (fun n => ¬ᶠ Prov n)).choose_spec

-- ============================================================
-- PART 4: Remaining Two Axioms (about the derived G)
-- ============================================================

/-- **Axiom 3 — Object-Level Consequence**:
    If F proves ¬G, then F proves Prov(⌈G⌉).

    In a full formalization, this follows from the OBJECT-LEVEL Diagonal Lemma:
      (a) F ⊢ G ↔ ¬Prov(⌈G⌉) [object-level, as a formula inside F]
      (b) F ⊢ ¬G               [hypothesis]
      (c) ∴ F ⊢ Prov(⌈G⌉)      [modus tollens + dne inside F]
    The meta-level `diagonal_lem` alone is insufficient (would need completeness).
    (Same mathematical role as `neg_G_prov_G` in OQ-01.) -/
axiom neg_G_prov : (⊢ ¬ᶠ G) → (⊢ Prov (godelNum G))

/-- **Axiom 4 — ω-Consistency** (restricted to G):
    If G is not provable, then Prov(⌈G⌉) is not provable.
    (Same as `omega_consistency_G` in OQ-01.) -/
axiom omega_cons : ¬(⊢ G) → ¬(⊢ Prov (godelNum G))

-- ============================================================
-- PART 5: Consistency and Completeness
-- ============================================================

/-- A system is consistent if no formula and its negation are both provable. -/
def Consistent : Prop := ∀ φ : Formula, ¬((⊢ φ) ∧ (⊢ ¬ᶠ φ))

/-- A system is complete if every formula or its negation is provable. -/
def Complete : Prop := ∀ φ : Formula, (⊢ φ) ∨ (⊢ ¬ᶠ φ)

-- ============================================================
-- PART 6: Main Theorems (derived from 5 axioms + G_spec)
-- ============================================================

/-- **G is not provable** (assuming consistency).

    The proof uses `G_spec` (derived from the Diagonal Lemma) rather than
    the ad hoc `G_self_reference` axiom from OQ-01. The logical structure
    is identical, but the source of G's self-reference property is now clear.

    Proof:
    1. Suppose ⊢ G
    2. By d1 (D1 Representability): ⊢ Prov(⌈G⌉)
    3. By G_spec (forward): ⊢ ¬Prov(⌈G⌉)         [from Diagonal Lemma!]
    4. Both ⊢ Prov(⌈G⌉) and ⊢ ¬Prov(⌈G⌉) — Consistent gives contradiction. -/
theorem G_not_provable (h : Consistent) : ¬(⊢ G) := by
  intro hG
  have hProvG : ⊢ Prov (godelNum G) := d1 G hG
  have hNegProvG : ⊢ ¬ᶠ Prov (godelNum G) := G_spec.mp hG
  exact h (Prov (godelNum G)) ⟨hProvG, hNegProvG⟩

/-- **¬G is not provable** (assuming consistency and ω-consistency).

    Proof:
    1. Suppose ⊢ ¬G
    2. By neg_G_prov (Axiom 3): ⊢ Prov(⌈G⌉)
    3. By G_not_provable: ¬(⊢ G)
    4. By omega_cons (Axiom 4): ¬(⊢ Prov(⌈G⌉))
    5. Contradiction with (2). -/
theorem neg_G_not_provable (h : Consistent) : ¬(⊢ ¬ᶠ G) := by
  intro hnG
  have hProvG : ⊢ Prov (godelNum G) := neg_G_prov hnG
  have hNotG : ¬(⊢ G) := G_not_provable h
  exact omega_cons hNotG hProvG

/-- **Gödel's First Incompleteness Theorem** (via Diagonal Lemma):
    Any consistent system satisfying D1 and the Diagonal Lemma is incomplete.

    G witnesses incompleteness: neither G nor ¬G is provable. -/
theorem first_incompleteness (h : Consistent) : ¬ Complete := by
  intro hComp
  rcases hComp G with hG | hnG
  · exact G_not_provable h hG
  · exact neg_G_not_provable h hnG

/-- **Corollary**: G is undecidable. -/
theorem G_undecidable (h : Consistent) : ¬(⊢ G) ∧ ¬(⊢ ¬ᶠ G) :=
  ⟨G_not_provable h, neg_G_not_provable h⟩

-- ============================================================
-- PART 7: Generality of the Diagonal Lemma
-- ============================================================

/-- The Diagonal Lemma provides fixed points for ANY predicate — not just ¬Prov.
    Here: a "trivially true" fixed point (σ is provable iff Prov(⌈σ⌉) is). -/
theorem prov_fixed_point_exists :
    ∃ σ : Formula, (⊢ σ) ↔ (⊢ Prov (godelNum σ)) :=
  diagonal_lem (fun n => Prov n)

/-- The Gödel sentence is one instance; other fixed points exist for other predicates. -/
theorem arb_fixed_point_exists (ψ : Nat → Formula) :
    ∃ σ : Formula, (⊢ σ) ↔ (⊢ ψ (godelNum σ)) :=
  diagonal_lem ψ

/-- The consistency sentence: "I am not provably consistent" — another Diagonal Lemma instance. -/
theorem consistency_sentence_exists :
    ∃ σ : Formula, (⊢ σ) ↔ (⊢ ¬ᶠ Prov (godelNum σ)) :=
  diagonal_lem (fun n => ¬ᶠ Prov n)

-- ============================================================
-- PART 8: The Forward Direction of G_self_reference (OQ-01 Comparison)
-- ============================================================

/-- OQ-01 took as an AXIOM: (⊢ G) ↔ ¬(⊢ Prov(⌈G⌉)).
    Here we derive the FORWARD direction (the only part needed for incompleteness):
    (⊢ G) → ¬(⊢ Prov(⌈G⌉))

    The backward direction ¬(⊢ Prov(⌈G⌉)) → (⊢ G) would require completeness
    of the formal system and is not derivable. OQ-01 was slightly stronger than
    necessary by taking the full biconditional as an axiom. -/
theorem G_self_reference_fwd (h : Consistent) : (⊢ G) → ¬(⊢ Prov (godelNum G)) := by
  intro hG hProvG
  have hNegProvG : ⊢ ¬ᶠ Prov (godelNum G) := G_spec.mp hG
  exact h (Prov (godelNum G)) ⟨hProvG, hNegProvG⟩

end GodelDiagonal

-- Verify main theorems are accessible
#check GodelDiagonal.first_incompleteness
#check GodelDiagonal.G_spec
#check GodelDiagonal.G_undecidable
#check GodelDiagonal.diagonal_lem
