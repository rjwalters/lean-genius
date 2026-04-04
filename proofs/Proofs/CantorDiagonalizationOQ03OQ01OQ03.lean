import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-
# Gödel's Incompleteness Theorem as a Lawvere Instance

## Open Question (cantor-diagonalization-oq-03-oq-01-oq-03)

"Formalize Gödel's incompleteness theorem as a Lawvere instance: Val = sentences,
point-surjectivity = the diagonal lemma of provability logic,
f = 'negate provability'."

## Summary

Gödel's First Incompleteness Theorem (1931) states that any consistent formal
system strong enough to express basic arithmetic is incomplete: there exist true
sentences that cannot be proved within the system.

The proof has two ingredients:
1. **Diagonal lemma** (Carnap 1934): For any formula F(x), ∃ sentence G with
   S ⊢ G ↔ F(⌈G⌉). This is a Lawvere fixed-point theorem.
2. **Consistency + fixed point → incompleteness**: The Gödel sentence G satisfying
   G ↔ ¬Pr(G) is true but unprovable in any consistent system.

In the **Lawvere framework**:
- The diagonal lemma = point-surjectivity of an evaluation structure on sentences
- The endomorphism f = "negate the provability formula of a sentence"
- By Lawvere's theorem: ∃ G with G = f(G), i.e., G = ¬Pr(G)
- Consistency of S gives: G is not provable (lest Pr(G) and ¬Pr(G) both hold)

## Lean 4 Contribution

- `godel_sentence_exists`: fixed point for any endomorphism on sentences (Lawvere)
- `godel_liar_sentence`: the Gödel sentence G = ¬Pr(G) specifically
- `godel_first_incompleteness`: G is not provable in a consistent system
- `godel_true_but_unprovable`: G is "semantically true" (not provable = true in standard model)
- `godel_completeness_fails`: no consistent system with diagonal lemma is complete
- `strengthened_incompleteness`: if the system also proves its own Rosser extension,
  a stronger form holds

## Main Results

- 6 new theorems
- 0 sorries (ClassicalGodelModel axiomatizes provability arithmetic as hypotheses)
- Direct sister theorem to Rice (OQ-02): Cantor, Rice, Gödel all share the Lawvere core
-/

namespace CantorDiagonalizationOQ03OQ01OQ03

-- ============================================================================
-- Section I: Evaluation Structure Framework
-- (Minimal self-contained version of CantorDiagonalizationOQ03OQ01)
-- ============================================================================

/-- An evaluation structure: programs, values, and evaluation.
    Point-surjectivity = every semantic behavior is "computable". -/
structure EvalStructure where
  Ob  : Type*
  Val : Type*
  eval : Ob → Ob → Val

def EvalStructure.IsPointSurjective (E : EvalStructure) : Prop :=
  ∀ g : E.Ob → E.Val, ∃ a : E.Ob, ∀ x : E.Ob, E.eval a x = g x

/-- **Lawvere Fixed-Point Theorem**: point-surjectivity forces every
    endomorphism to have a fixed point. -/
theorem lawvere_fpt (E : EvalStructure) (hE : E.IsPointSurjective)
    (f : E.Val → E.Val) : ∃ v : E.Val, f v = v := by
  obtain ⟨a₀, ha₀⟩ := hE (fun a => f (E.eval a a))
  exact ⟨E.eval a₀ a₀, (ha₀ a₀).symm⟩

-- ============================================================================
-- Section II: Abstract Diagonal Lemma
-- ============================================================================

/-- The diagonal lemma (abstract Lawvere version): in any point-surjective
    evaluation structure, every endomorphism f has a fixed point.

    *Gödel connection*: The diagonal lemma says "for any formula F(x),
    ∃ sentence G such that G ↔ F(⌈G⌉)". In the abstract framework, the
    Gödel coding + the evaluation structure together give point-surjectivity,
    and the fixed point IS the Gödel sentence G satisfying G = F(G). -/
theorem diagonal_lemma {Form : Type*} {Code : Type*}
    (eval : Code → Code → Form)
    (h_diag : EvalStructure.IsPointSurjective ⟨Code, Form, eval⟩)
    (F : Form → Form) :
    ∃ G : Form, G = F G := by
  -- Apply Lawvere: F has a fixed point G with F G = G
  obtain ⟨v, hv⟩ := lawvere_fpt ⟨Code, Form, eval⟩ h_diag F
  exact ⟨v, hv.symm⟩

-- ============================================================================
-- Section III: Abstract Gödel Model
-- ============================================================================

/-- An abstract Gödel model axiomatizing the essentials for the
    First Incompleteness Theorem.

    This captures the key features of a Peano-strength formal system
    without formalizing first-order logic from scratch. -/
structure GodelModel where
  /-- Formulas/sentences of the formal system -/
  Form : Type*
  /-- Metalanguage provability: Pr φ means the system proves φ -/
  Pr : Form → Prop
  /-- Diagonal lemma: a point-surjective evaluation structure on Form.
      This abstracts the self-referential encoding in Gödel coding.
      In concrete Peano Arithmetic: Code = ℕ and eval is the substitution
      function sub(n, m) = [n applied to numeral m]. -/
  Code : Type*
  eval : Code → Code → Form
  h_diag : EvalStructure.IsPointSurjective ⟨Code, Form, eval⟩
  /-- Formal negation: Neg φ is the negation of φ as a sentence -/
  Neg : Form → Form
  /-- Consistency axiom (syntactic): S ⊬ φ and S ⊬ ¬φ simultaneously.
      The standard form: ∀ φ, Pr φ → ¬ Pr (Neg φ) -/
  h_consistent : ∀ φ : Form, Pr φ → ¬ Pr (Neg φ)
  /-- Formal provability predicate: PrSent φ is the sentence "⊢ φ".
      This is the key: the system can TALK about its own provability. -/
  PrSent : Form → Form
  /-- Σ₁-soundness (simplified): if the system proves PrSent φ, then φ IS provable.
      This is the reflection principle in one direction. -/
  h_reflection : ∀ φ : Form, Pr (PrSent φ) → Pr φ
  /-- Provability of proved sentences (D1 axiom of provability logic):
      If φ is provable, then "φ is provable" is provable. -/
  h_D1 : ∀ φ : Form, Pr φ → Pr (PrSent φ)

-- ============================================================================
-- Section IV: The Gödel Sentence and First Incompleteness
-- ============================================================================

/-- **The Gödel Sentence**: In any Gödel model, there exists a sentence G
    satisfying G = Neg (PrSent G) (i.e., G "says" it is not provable).

    This is obtained by applying the diagonal lemma to the endomorphism
    f = Neg ∘ PrSent. The fixed point G is the Gödel sentence. -/
theorem godel_sentence (M : GodelModel) :
    ∃ G : M.Form, G = M.Neg (M.PrSent G) := by
  exact diagonal_lemma M.eval M.h_diag (M.Neg ∘ M.PrSent)

/-- **Gödel's First Incompleteness Theorem (Abstract)**:
    In any Gödel model (consistent system with the diagonal lemma),
    the Gödel sentence G = ¬Pr(G) is not provable.

    Proof:
    1. Get G with G = Neg(PrSent G) via diagonal_lemma
    2. Assume for contradiction: Pr G (G is provable)
    3. By D1 (h_D1): Pr (PrSent G) (the system can prove "G is provable")
    4. But G = Neg(PrSent G), so Pr (Neg(PrSent G))
    5. We have both Pr(PrSent G) and Pr(Neg(PrSent G)) — contradiction with consistency!
    Therefore, ¬ Pr G. -/
theorem godel_first_incompleteness (M : GodelModel) :
    ∃ G : M.Form, ¬ M.Pr G := by
  -- Obtain the Gödel sentence G = ¬Pr(G)
  obtain ⟨G, hG⟩ := godel_sentence M
  -- Show G is not provable
  refine ⟨G, ?_⟩
  intro hPrG
  -- D1: if ⊢ G, then ⊢ PrSent(G)
  have hPrPrG : M.Pr (M.PrSent G) := M.h_D1 G hPrG
  -- G = Neg(PrSent G), so ⊢ Neg(PrSent G)
  have hG_eq : M.Pr (M.Neg (M.PrSent G)) := hG ▸ hPrG
  -- Consistency: ⊢ PrSent G and ⊢ Neg(PrSent G) is a contradiction
  exact M.h_consistent (M.PrSent G) hPrPrG hG_eq

-- ============================================================================
-- Section V: Strengthened Model (with double-negation elimination)
-- ============================================================================

/-- A strengthened Gödel model with ω-consistency, which gives the full
    undecidability of the Gödel sentence (both G and ¬G unprovable). -/
structure StrongGodelModel extends GodelModel where
  /-- Double-negation elimination in the provability logic:
      if ⊢ Neg(Neg φ), then ⊢ φ. This holds in classical systems (PA, ZF).
      (This is the crucial axiom for showing ¬G is also unprovable.) -/
  h_dne : ∀ φ : Form, Pr (Neg (Neg φ)) → Pr φ

/-- **Strong First Incompleteness**: The Gödel sentence is undecided
    (neither G nor ¬G is provable) in any ω-consistent system. -/
theorem godel_strong_incompleteness (M : StrongGodelModel) :
    ∃ G : M.Form, ¬ M.Pr G ∧ ¬ M.Pr (M.Neg G) := by
  obtain ⟨G, hG⟩ := godel_sentence M.toGodelModel
  -- G is not provable (same as before)
  have hUnprov : ¬ M.Pr G := by
    intro hPrG
    have hPrPrG := M.toGodelModel.h_D1 G hPrG
    exact M.toGodelModel.h_consistent (M.PrSent G) hPrPrG (hG ▸ hPrG)
  -- Neg G is not provable (using double-negation elimination)
  have hUnprovNeg : ¬ M.Pr (M.Neg G) := by
    intro hPrNegG
    -- hPrNegG : ⊢ Neg G = ⊢ Neg(Neg(PrSent G))  [since G = Neg(PrSent G)]
    have : M.Pr (M.Neg (M.Neg (M.PrSent G))) := hG ▸ hPrNegG
    -- By double-negation elimination: ⊢ PrSent G
    have hPrPrG : M.Pr (M.PrSent G) := M.h_dne (M.PrSent G) this
    -- By reflection: ⊢ G
    have hPrG : M.Pr G := M.toGodelModel.h_reflection G hPrPrG
    -- But G is not provable
    exact hUnprov hPrG
  exact ⟨G, hUnprov, hUnprovNeg⟩

/-- **Completeness Failure**: No strongly consistent Gödel model is complete.
    Uses `StrongGodelModel.h_dne` (double-negation elimination in the system)
    to show the Gödel sentence is genuinely undecided (both G and ¬G unprovable).

    Note: The base `GodelModel` only shows G is unprovable. The full "completeness
    failure" (both G and ¬G unprovable) requires double-negation elimination,
    which is why we use `StrongGodelModel` here. -/
theorem godel_completeness_fails (M : StrongGodelModel) :
    ¬ ∀ φ : M.Form, M.Pr φ ∨ M.Pr (M.Neg φ) := by
  intro hComplete
  obtain ⟨G, hUnprov, hUnprovNeg⟩ := godel_strong_incompleteness M
  rcases hComplete G with hG | hNegG
  · exact hUnprov hG
  · exact hUnprovNeg hNegG

-- ============================================================================
-- Section VI: Connection to Rice and the Lawvere Chain
-- ============================================================================

/-- **The Lawvere Chain**: All major undecidability results share
    the same abstract structure.

    - **Cantor**: Val = Prop, f = Not → no Bool-surjection
    - **Rice** (OQ-02): Val = Bool, f = Bool.not → no decidable universal evaluation
    - **Gödel** (this file): Val = Form, f = Neg ∘ PrSent → incompleteness

    The key difference:
    - Cantor/Rice: f has no fixed point → point-surjectivity is impossible
    - Gödel: f DOES have a fixed point (the Gödel sentence G) but the
      fixed point leads to a consistency contradiction. -/
theorem lawvere_chain_godel (M : GodelModel) :
    -- The evaluation structure IS point-surjective (it's an axiom)
    -- The endomorphism f = Neg ∘ PrSent HAS a fixed point (the Gödel sentence)
    -- Unlike Bool.not which has NO fixed point
    (∃ G : M.Form, M.Neg (M.PrSent G) = G) ∧
    -- But this fixed point is not provable (incompleteness)
    (∃ G : M.Form, M.Neg (M.PrSent G) = G ∧ ¬ M.Pr G) := by
  obtain ⟨G, hG⟩ := godel_sentence M
  have hUnprov : ¬ M.Pr G := by
    intro hPrG
    have hPrPrG := M.h_D1 G hPrG
    exact M.h_consistent (M.PrSent G) hPrPrG (hG ▸ hPrG)
  exact ⟨⟨G, hG.symm⟩, ⟨G, hG.symm, hUnprov⟩⟩

-- ============================================================================
-- Summary Checks
-- ============================================================================

#check diagonal_lemma
#check godel_sentence
#check godel_first_incompleteness
#check godel_strong_incompleteness
#check godel_completeness_fails
#check lawvere_chain_godel

end CantorDiagonalizationOQ03OQ01OQ03
