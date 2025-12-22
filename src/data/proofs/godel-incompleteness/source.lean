/-
  Gödel's First Incompleteness Theorem

  Any consistent formal system F capable of expressing basic arithmetic
  contains statements that are true but unprovable within F.

  This formalization presents the key conceptual components of the proof:
  1. Gödel numbering - encoding formulas as natural numbers
  2. Representability - expressing arithmetic within the formal system
  3. The Diagonal Lemma - achieving self-reference
  4. The Gödel sentence - "This statement is unprovable"
  5. The incompleteness argument

  This is an illustrative proof sketch capturing the essential structure.
  A complete formalization would require thousands of lines defining
  formal syntax, proof systems, and computability theory.

  Historical note: Proved by Kurt Gödel in 1931, this theorem shattered
  Hilbert's program to establish a complete, consistent foundation for
  all of mathematics.
-/

namespace Godel

-- ============================================================
-- PART 1: The Formal System
-- ============================================================

-- We axiomatize the minimal requirements for a formal system F
-- capable of expressing arithmetic

-- Formulas in the system (abstract type)
axiom Formula : Type

-- Provability predicate: F ⊢ φ means φ is provable in F
axiom Provable : Formula → Prop

notation:50 "⊢ " φ => Provable φ

-- Negation of formulas
axiom neg : Formula → Formula
prefix:75 "¬ᶠ" => neg

-- The system can express basic arithmetic
-- (We assume natural numbers are definable)
axiom numeral : Nat → Formula

-- ============================================================
-- PART 2: Consistency Assumption
-- ============================================================

-- Consistency: there is no formula φ such that both φ and ¬φ are provable
def Consistent : Prop :=
  ∀ φ : Formula, ¬(⊢ φ ∧ ⊢ ¬ᶠφ)

-- ω-consistency: a stronger condition Gödel originally used
-- The system is ω-consistent if: whenever ⊢ ¬P(0), ⊢ ¬P(1), ⊢ ¬P(2), ...
-- for all numerals, we don't also have ⊢ ∃x.P(x)
-- This prevents the system from being "wrong" about the natural numbers

-- ω-consistency implies simple consistency
-- (Rosser later showed simple consistency suffices with a modified sentence)

-- ============================================================
-- PART 3: Gödel Numbering
-- ============================================================

-- Every formula can be encoded as a natural number
axiom godelNum : Formula → Nat

-- This encoding is injective (different formulas get different numbers)
axiom godelNum_injective : ∀ φ ψ : Formula, godelNum φ = godelNum ψ → φ = ψ

-- We can recover formulas from their Gödel numbers (partial)
axiom decode : Nat → Option Formula

-- Encoding and decoding are inverse operations
axiom decode_godelNum : ∀ φ : Formula, decode (godelNum φ) = some φ

-- ============================================================
-- PART 4: Representability
-- ============================================================

-- Key property: provability itself is representable in the system
-- There exists a formula Prov(x) such that:
--   F ⊢ Prov(⌜φ⌝) ↔ F ⊢ φ
-- where ⌜φ⌝ is the numeral for the Gödel number of φ

-- The provability predicate expressed as a formula
axiom ProvFormula : Nat → Formula

-- Notation: Prov(n) represents "the formula with Gödel number n is provable"
notation:50 "Prov(" n ")" => ProvFormula n

-- Representability: if φ is provable, then Prov(⌜φ⌝) is provable
axiom prov_complete : ∀ φ : Formula, ⊢ φ → ⊢ Prov(godelNum φ)

-- ============================================================
-- PART 5: The Diagonal Lemma (Fixed Point Theorem)
-- ============================================================

-- This is the heart of Gödel's construction
-- For any property P(x) expressible in F, there exists a sentence γ
-- such that F ⊢ γ ↔ P(⌜γ⌝)
-- In other words: γ says "I have property P"

-- Equivalence of formulas (both directions provable)
axiom Equiv : Formula → Formula → Prop
notation:50 φ " ⟺ " ψ => Equiv φ ψ

-- The substitution function for building self-reference
-- sub(φ, n) substitutes numeral n into φ
axiom sub : Formula → Nat → Formula

-- The diagonal lemma (Gödel's fixed point theorem)
axiom diagonal_lemma :
  ∀ P : Nat → Formula,
  ∃ γ : Formula, γ ⟺ P (godelNum γ)

-- This lemma allows formulas to "talk about themselves"
-- It's the formal version of the Liar's Paradox construction

-- ============================================================
-- PART 6: The Gödel Sentence
-- ============================================================

-- Apply the diagonal lemma to the negation of provability
-- We want: G ⟺ ¬Prov(⌜G⌝)
-- In English: "G says 'I am not provable'"

-- Negation of the provability formula
def NotProv (n : Nat) : Formula := ¬ᶠ(Prov(n))

-- The Gödel sentence exists by the diagonal lemma
theorem godel_sentence_exists :
  ∃ G : Formula, G ⟺ NotProv (godelNum G) :=
  diagonal_lemma NotProv

-- Get the Gödel sentence
noncomputable def G : Formula :=
  Classical.choose godel_sentence_exists

-- G is equivalent to "G is not provable"
theorem G_self_reference : G ⟺ NotProv (godelNum G) :=
  Classical.choose_spec godel_sentence_exists

-- ============================================================
-- PART 7: The Incompleteness Argument
-- ============================================================

-- We need equivalence to imply co-provability
axiom equiv_implies_coprovable :
  ∀ φ ψ : Formula, φ ⟺ ψ → (⊢ φ ↔ ⊢ ψ)

-- If the system is consistent, G is not provable
theorem G_not_provable (h_consistent : Consistent) : ¬(⊢ G) := by
  intro hG  -- Assume G is provable
  -- By self-reference, G ⟺ ¬Prov(⌜G⌝)
  have h_self := G_self_reference
  -- Since G is provable, Prov(⌜G⌝) is provable
  have h_prov : ⊢ Prov(godelNum G) := prov_complete G hG
  -- By equivalence, ¬Prov(⌜G⌝) is provable (since G is)
  have h_not_prov : ⊢ NotProv (godelNum G) :=
    (equiv_implies_coprovable G (NotProv (godelNum G)) h_self).mp hG
  -- But NotProv(n) = ¬Prov(n), so we have ⊢ ¬Prov(⌜G⌝)
  -- This contradicts consistency: we proved both Prov(⌜G⌝) and ¬Prov(⌜G⌝)
  unfold NotProv at h_not_prov
  exact h_consistent (Prov(godelNum G)) ⟨h_prov, h_not_prov⟩

-- The Gödel sentence is true (in the standard model)
-- If G were false, then "G is not provable" would be false
-- meaning G would be provable, contradicting the above
-- Therefore G is true but unprovable

-- ============================================================
-- PART 8: The First Incompleteness Theorem
-- ============================================================

-- Completeness would mean every true sentence is provable
-- We define a weaker notion: syntactic completeness
def Complete : Prop :=
  ∀ φ : Formula, ⊢ φ ∨ ⊢ ¬ᶠφ

-- Key lemma: ¬G implies Prov(⌜G⌝) (¬G says "G is provable")
-- This follows from the self-reference: G ⟺ ¬Prov(⌜G⌝), so ¬G ⟺ Prov(⌜G⌝)
axiom notG_implies_prov : ⊢ ¬ᶠG → ⊢ Prov(godelNum G)

-- Σ₁-completeness: Provability claims that are true are provable
-- If φ is actually provable (i.e., there exists a proof), then ⊢ Prov(⌜φ⌝)
-- Conversely (and crucially): if ⊢ Prov(⌜φ⌝), the system correctly reflects provability
-- This is the key technical condition that Gödel originally captured via ω-consistency
axiom sigma1_soundness : ⊢ Prov(godelNum G) → ⊢ G

-- ¬G is also not provable (under consistency)
-- If ⊢ ¬G, then ⊢ Prov(⌜G⌝) (since ¬G says "G is provable")
-- By Σ₁-soundness, this would mean ⊢ G
-- But then both ⊢ G and ⊢ ¬G, contradicting consistency
theorem notG_not_provable (h_consistent : Consistent) : ¬(⊢ ¬ᶠG) := by
  intro hNotG
  -- ¬G says "G is provable", so ⊢ ¬G implies ⊢ Prov(⌜G⌝)
  have h_prov : ⊢ Prov(godelNum G) := notG_implies_prov hNotG
  -- By Σ₁-soundness, if the system proves Prov(⌜G⌝), then G is provable
  have hG : ⊢ G := sigma1_soundness h_prov
  -- Now we have both ⊢ G and ⊢ ¬G, contradicting consistency
  exact h_consistent G ⟨hG, hNotG⟩

-- First Incompleteness Theorem:
-- G is undecidable: neither G nor ¬G is provable
theorem G_undecidable (h_consistent : Consistent) : ¬(⊢ G) ∧ ¬(⊢ ¬ᶠG) :=
  ⟨G_not_provable h_consistent, notG_not_provable h_consistent⟩

-- The Incompleteness Theorem: No consistent system is complete
theorem first_incompleteness (h_consistent : Consistent) : ¬Complete := by
  intro h_complete
  -- By completeness, either ⊢ G or ⊢ ¬G
  cases h_complete G with
  | inl hG =>
    -- Case 1: G is provable - contradicts G_not_provable
    exact G_not_provable h_consistent hG
  | inr hNotG =>
    -- Case 2: ¬G is provable - contradicts notG_not_provable
    exact notG_not_provable h_consistent hNotG

-- ============================================================
-- PART 9: Philosophical Implications
-- ============================================================

/-
  Gödel's theorem has profound implications:

  1. INCOMPLETENESS OF ARITHMETIC
     Peano Arithmetic, ZFC, and any sufficiently strong consistent
     system contains true but unprovable statements.

  2. DEATH OF HILBERT'S PROGRAM
     Hilbert hoped to prove the consistency of mathematics using
     finitary methods. Gödel's second incompleteness theorem shows
     this is impossible: no consistent system can prove its own
     consistency (unless it's inconsistent).

  3. LIMITS OF FORMALIZATION
     There will always be mathematical truths that escape any
     fixed formal system. Mathematics is inexhaustible.

  4. MECHANISM VS MIND
     Some argue this shows human mathematical reasoning transcends
     any algorithmic process. This interpretation is controversial.

  5. THE LIAR'S PARADOX REDEEMED
     Gödel transformed the ancient paradox "This sentence is false"
     into rigorous mathematics by replacing "false" with "unprovable."
-/

-- ============================================================
-- PART 10: The Construction Summarized
-- ============================================================

/-
  The Proof in a Nutshell:

  1. ENCODING: Assign each formula φ a unique natural number ⌜φ⌝
     (the Gödel number). This lets the system "talk about" formulas.

  2. REPRESENTABILITY: The provability relation is expressible
     within the system via a formula Prov(x).

  3. SELF-REFERENCE: By the diagonal lemma, construct G such that
     G ⟺ ¬Prov(⌜G⌝), i.e., G says "I am not provable."

  4. TRUTH OF G: If the system is consistent:
     - If ⊢ G, then ⊢ Prov(⌜G⌝) (by representability)
     - But G says ⊢ ¬Prov(⌜G⌝)
     - Contradiction! So G is not provable.

  5. CONCLUSION: G is true (it correctly asserts its unprovability)
     but not provable. The system is incomplete.

  The genius of Gödel was to arithmetize metamathematics:
  proofs become numbers, derivations become calculations,
  and the system can reflect on itself.
-/

end Godel

-- Final type check of the main theorem
#check @Godel.first_incompleteness
#check @Godel.G_not_provable
#check @Godel.diagonal_lemma
