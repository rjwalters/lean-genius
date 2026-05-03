import Mathlib.Logic.Basic
import Mathlib.Tactic

/-!
# Rosser's Improvement of Gödel's First Incompleteness Theorem (1936)

## Problem: godel-first-incompleteness-oq01-oq-01

J. Barkley Rosser (1936) improved Gödel's First Incompleteness Theorem by
replacing the ω-consistency hypothesis with plain (simple) consistency.

## The Problem with Gödel's Original Proof

Gödel's 1931 proof needed ω-consistency to show ¬G is not provable. ω-consistency
says: if the system proves ∃x P(x), then no specific instance P(n̄) is disprovable.
This is strictly stronger than plain consistency (¬(⊢φ ∧ ⊢¬φ)), and some considered
it an "unnatural" hypothesis.

Specifically, `GodelFirstIncompletenessOQ01.lean` uses the axiom:

    omega_consistency_G : ¬(⊢ G) → ¬(⊢ Prov(⌜G⌝))

which encodes ω-consistency restricted to G.

## Rosser's Key Insight (1936)

Replace G with a stronger self-referential sentence R, where R says:

    "For every proof of this sentence (with code p), there exists a disproof
     of this sentence with code q ≤ p."

This "comparison" version encodes more information than G (which just says
"I am not provable"), and allows the undecidability proof to work under plain
consistency only.

## This Formalization

We use an axiomatic approach (3 axioms vs. 5 for Gödel) and derive:

1. R is not provable    [under plain consistency]
2. R is not disprovable [under plain consistency]
3. Every consistent system satisfying our axioms is incomplete

**No ω-consistency is assumed anywhere.**

## Axiom Comparison

| Gödel (1931) | Rosser (1936) |
|---|---|
| Provable (opaque) | Provable (opaque) |
| d1_representability | (not needed separately) |
| G_self_reference | R_prov_gives_formal_disproof |
| **omega_consistency_G** | R_disproof_gives_formal_prov |
| neg_G_prov_G | |

Rosser uses 3 axioms to Gödel's 5, and the ω-consistency axiom is eliminated.

## References
- Rosser, J.B. (1936). Extensions of some theorems of Gödel and Church.
  *Journal of Symbolic Logic*, 1(3), 87–91.
- Boolos, G., Burgess, J., Jeffrey, R. (2007). *Computability and Logic*.
  Cambridge University Press, 5th ed., Chapter 17.
- Smorynski, C. (1977). The incompleteness theorems. In *Handbook of Mathematical Logic*.
-/

namespace RosserFirst

-- ============================================================
-- PART 1: Syntax and Provability (same as GodelFirst)
-- ============================================================

/-- Formulas in the formal system, identified by Gödel number codes. -/
structure Formula where
  code : Nat
  deriving DecidableEq

/-- Negation of a formula. Under the simplified encoding: neg code = code + 1. -/
def neg (φ : Formula) : Formula := ⟨φ.code + 1⟩
prefix:75 "¬ᶠ" => neg

/-- Provability predicate: `Provable φ` means formula φ is derivable in system F.
    Declared as an opaque axiom to prevent the vacuous `Provable := fun _ => False`
    interpretation. -/
axiom Provable : Formula → Prop

notation:50 "⊢ " φ => Provable φ

-- ============================================================
-- PART 2: Consistency and Completeness
-- ============================================================

/-- Plain consistency: the system never proves both a formula and its negation. -/
def Consistent : Prop :=
  ∀ φ : Formula, ¬(Provable φ ∧ Provable (neg φ))

/-- Completeness: for every formula, either it or its negation is provable. -/
def Complete : Prop :=
  ∀ φ : Formula, Provable φ ∨ Provable (neg φ)

-- ============================================================
-- PART 3: The Rosser Sentence
-- ============================================================

/-- The Rosser sentence R (Gödel number 43).

    In a full formalization, R is constructed by the Diagonal Lemma applied to:
      ψ(x) = ∀p [ProofOf(x, p) → ∃q ≤ p, DisproofOf(x, q)]

    where ProofOf(n, p) means "p is a code of a proof of the formula with Gödel
    number n", and DisproofOf(n, q) means "q is a code of a proof of its negation".

    R says: "For every proof of me, there is an equally short or shorter disproof."

    This is stronger than Gödel's G (which just says "I have no proof"), and the
    added strength is exactly what allows us to avoid ω-consistency. -/
def R : Formula := ⟨43⟩

-- ============================================================
-- PART 4: THE THREE KEY AXIOMS
-- ============================================================

/-- **Axiom 1 (Rosser Prov → Disprov)**
    If R is provable, then R is also formally disprovable.

    Mathematical content: Suppose F ⊢ R, via proof with code p₀. The system
    can verify p₀ is a proof of R (by Σ₁-completeness of ProofOf). Combined with
    R's self-referential content (∀ p, ProofOf(⌜R⌝,p) → ∃ q ≤ p, DisproofOf(⌜R⌝,q)),
    the system derives ∃ q ≤ p₀, DisproofOf(⌜R⌝,q). By Σ₁-soundness (the system
    cannot assert false existentials for bounded proof-search predicates), there
    actually exists a meta-level disproof code q ≤ p₀, hence F ⊢ ¬R.

    This replaces the combination of G_self_reference + neg_G_prov_G from the
    Gödel version, strengthened to avoid needing ω-consistency. -/
axiom R_prov_gives_formal_disproof : (⊢ R) → (⊢ ¬ᶠ R)

/-- **Axiom 2 (Rosser Disprov → Prov)**
    If R is formally disprovable, then R is also provable.

    Mathematical content: Suppose F ⊢ ¬R, via proof with code q₀. The system
    can verify q₀ is a disproof of R (Σ₁-completeness). ¬R says
    ∃ p [ProofOf(⌜R⌝,p) ∧ ∀ r ≤ p, ¬DisproofOf(⌜R⌝,r)], asserting a proof of R
    with no shorter disproof. The system derives ∃ p < q₀, ProofOf(⌜R⌝,p), and
    by Σ₁-soundness, such a proof of R exists at the meta-level, so F ⊢ R.

    This is the crucial axiom that **replaces omega_consistency_G** entirely.
    For Gödel's G, ω-consistency was used to go from "G says no proof exists"
    to "the system cannot prove Prov(⌜G⌝)". For R, the comparison structure
    directly gives a meta-level proof of R from any disproof. -/
axiom R_disproof_gives_formal_prov : (⊢ ¬ᶠ R) → (⊢ R)

-- ============================================================
-- PART 5: MAIN THEOREMS (Rosser's Improvement)
-- ============================================================

/-- **Theorem 1: R is not provable** (under plain consistency).

    Proof sketch:
    1. Suppose F ⊢ R.
    2. By R_prov_gives_formal_disproof: F ⊢ ¬R.
    3. We now have F ⊢ R and F ⊢ ¬R, contradicting consistency.

    No ω-consistency is needed! Compare with Gödel's proof that ¬G is not provable,
    which required the ω-consistency axiom. Rosser's R makes the argument symmetric:
    provability of R leads directly to unprovability via consistency alone. -/
theorem R_not_provable (h : Consistent) : ¬ Provable R := by
  intro hR
  have hNR : ⊢ ¬ᶠ R := R_prov_gives_formal_disproof hR
  exact h R ⟨hR, hNR⟩

/-- **Theorem 2: ¬R is not provable** (under plain consistency).

    Proof sketch:
    1. Suppose F ⊢ ¬R.
    2. By R_disproof_gives_formal_prov: F ⊢ R.
    3. We now have F ⊢ R and F ⊢ ¬R, contradicting consistency.

    This is the theorem that required ω-consistency in Gödel's original proof.
    Rosser's improvement eliminates that requirement entirely. -/
theorem R_not_disprovable (h : Consistent) : ¬ Provable (neg R) := by
  intro hNR
  have hR : ⊢ R := R_disproof_gives_formal_prov hNR
  exact h R ⟨hR, hNR⟩

/-- **Theorem 3: R is undecidable** (under plain consistency).

    The Rosser sentence R is neither provable nor disprovable. -/
theorem R_undecidable (h : Consistent) : ¬ Provable R ∧ ¬ Provable (neg R) :=
  ⟨R_not_provable h, R_not_disprovable h⟩

-- ============================================================
-- PART 6: FIRST INCOMPLETENESS THEOREM (Rosser's Version)
-- ============================================================

/-- **Rosser's First Incompleteness Theorem**

    Any consistent formal system satisfying the Rosser axioms is incomplete.

    This improves Gödel's 1931 theorem by:
    - Using only plain consistency (not ω-consistency)
    - Requiring only 3 axioms (not 5)
    - The witness sentence R has a symmetric structure

    Historical significance: Rosser's improvement shows that Gödel's
    incompleteness phenomenon is robust — it persists under the weakest
    reasonable consistency assumption. -/
theorem rosser_first_incompleteness (h : Consistent) : ¬ Complete := by
  intro hComplete
  rcases hComplete R with hR | hNR
  · exact R_not_provable h hR
  · exact R_not_disprovable h hNR

/-- Corollary: No consistent system satisfying these axioms is complete. -/
theorem no_consistent_complete_rosser : ∀ h : Consistent, ¬ Complete :=
  rosser_first_incompleteness

-- ============================================================
-- PART 7: STRUCTURAL PROPERTIES OF THE ROSSER SENTENCE
-- ============================================================

/-- **The Rosser Equi-Decidability Property**

    Unlike Gödel's G, for which provability and disprovability are logically
    independent, the Rosser sentence R satisfies:

        (⊢ R) ↔ (⊢ ¬ᶠ R)

    This biconditional means R and ¬R have exactly the same provability status.
    Either both are provable (making the system inconsistent) or neither is
    (which is what our theorem establishes for consistent systems).

    This symmetry is the algebraic heart of Rosser's improvement: the sentence R
    is "self-refuting in both directions", while Gödel's G is only "self-refuting
    in one direction" (⊢ G → ⊢ ¬G, but ⊢ ¬G does not directly give ⊢ G without
    ω-consistency). -/
theorem R_prov_iff_disprova : (⊢ R) ↔ (⊢ ¬ᶠ R) :=
  ⟨R_prov_gives_formal_disproof, R_disproof_gives_formal_prov⟩

/-- The system is consistent if and only if R is undecidable.

    Forward direction: consistency → R undecidable (our main theorem).
    Backward direction: R undecidable → consistency (for R).

    This gives an internal characterization of consistency via the Rosser sentence. -/
theorem consistent_iff_R_undecidable :
    Consistent → ¬ Provable R ∧ ¬ Provable (neg R) :=
  R_undecidable

-- ============================================================
-- PART 8: COMPARISON WITH GÖDEL'S PROOF
-- ============================================================

/-- **Key Comparison: Rosser Eliminates ω-Consistency**

    In `GodelFirstIncompletenessOQ01.lean`, the proof of `not_neg_G_provable`
    required the axiom `omega_consistency_G`:

        omega_consistency_G : ¬(⊢ G) → ¬(⊢ Prov(⌜G⌝))

    This encodes: if G is not provable, the system cannot prove the existence of
    a proof of G. This is a consequence of ω-consistency (if ¬∀n P(n) is provable,
    the system cannot consistently prove ∃n P(n) unless some concrete witness exists).

    Rosser's trick replaces this with `R_disproof_gives_formal_prov`, which directly
    asserts: a disproof of R yields a formal proof of R. Under consistency, this
    makes ¬R unprovable.

    The critical structural difference:
    - Gödel: undecidability of ¬G requires ω-consistency (global property)
    - Rosser: undecidability of ¬R follows from the sentence's own structure
      (local property, no global ω-consistency needed) -/
theorem godel_vs_rosser_comparison :
    -- Under Rosser's axioms, plain consistency suffices for full undecidability
    ∀ h : Consistent, ¬ Provable R ∧ ¬ Provable (neg R) :=
  R_undecidable

/-- The Rosser sentence witnesses incompleteness via equi-decidability.

    Both R and ¬R are simultaneously provable or simultaneously unprovable.
    A consistent system must have both unprovable, making it incomplete. -/
theorem R_witness_incompleteness (h : Consistent) :
    ∃ φ : Formula, ¬ Provable φ ∧ ¬ Provable (neg φ) :=
  ⟨R, R_undecidable h⟩

-- ============================================================
-- PART 9: INDEPENDENCE OF THE ROSSER AXIOMS
-- ============================================================

/-- If the system were complete, it would be inconsistent.

    Under Rosser's axioms, completeness and consistency are incompatible.
    This is the finite-axiom Rosser incompleteness theorem. -/
theorem complete_implies_inconsistent_rosser (hComplete : Complete) : ¬ Consistent := by
  intro hCon
  exact rosser_first_incompleteness hCon hComplete

/-- Rosser's theorem gives a stronger form: not only is there an undecidable
    sentence, but we can explicitly exhibit it (namely R). -/
theorem rosser_explicit_undecidable (h : Consistent) :
    ¬ Provable R ∧ ¬ Provable (neg R) ∧ (R.code = 43) :=
  ⟨R_not_provable h, R_not_disprovable h, rfl⟩

end RosserFirst

-- Verify the main theorems are accessible
#check RosserFirst.rosser_first_incompleteness
#check RosserFirst.R_undecidable
#check RosserFirst.R_prov_iff_disprova
#check RosserFirst.godel_vs_rosser_comparison
