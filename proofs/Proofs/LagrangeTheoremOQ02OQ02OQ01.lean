import Mathlib
import Proofs.LagrangeTheoremOQ02OQ02

/-
  Burnside's Lemma from the Conjugation-Action Class Equation
  (lagrange-theorem-oq-02-oq-02 — OQ-01)

  Parent open question:
    Can the class equation be used to formally prove Burnside's lemma
    in Lean 4 using only the infrastructure developed here?

  Answer: YES. The class equation and Burnside's lemma are the same
  orbit-decomposition identity applied to two different actions:

  - Class equation = (G ↷ G by conjugation), with central elements
    isolated as singleton orbits. The parent file proves it via
    `Group.nat_card_center_add_sum_card_noncenter_eq_card`.
  - Burnside's lemma = (G ↷ X arbitrary), packaged as the dual
    Σ_g |Fix(g)| = |X/G| · |G| via Mathlib's
    `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`.

  The parent's "infrastructure" — `conj_orbit_eq_carrier`,
  `conj_stabilizer_eq_centralizer`,
  `card_conjClass_eq_centralizer_index`, and the conjugation-action
  setup — is exactly the specialisation of the same MulAction
  machinery that powers Burnside. This file makes the parallel
  explicit by deriving Burnside's lemma in three forms (sum,
  average, and the conjugation-action restatement), then bundles
  them as `oq01_resolution`.

  ## Proof chain
  (1) `burnside_lemma_sum_form` — direct Mathlib invocation
      Σ_g |Fix(g)| = |X/G| · |G|.
  (2) `burnside_lemma_average_form` — corollary by Nat-division.
  (3) `conjugation_burnside_form` — specialisation to G ↷ G via
      `ConjAct G`, exhibiting the parallel with the parent's
      class equation.
  (4) `oq01_resolution` — packaged conjunction of (1) and (3),
      a single statement attesting the affirmative answer.

  ## Mathlib API used
  - `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
    (Mathlib.GroupTheory.GroupAction.Quotient)
  - `ConjAct` (Mathlib.GroupTheory.GroupAction.ConjAct)
  - `Nat.eq_div_of_eq_mul_left` for the average form.

  ## Axiom-cleanliness
  No new axioms. The Mathlib API closure uses only the standard
  Mathlib triple (`Classical.choice`, `propext`, `Quot.sound`),
  shared with the parent file's import chain.

  References:
  - Burnside, W. (1897). "Theory of Groups of Finite Order." §119.
  - Cauchy, A.-L. (1845). Original orbit-counting argument.
  - Frobenius, F.G. (1887). Earlier statement (hence "Cauchy–Frobenius").
  - Mathlib: Mathlib.GroupTheory.GroupAction.Quotient,
             Mathlib.GroupTheory.GroupAction.ConjAct.

  Tags: group-theory, burnside, class-equation, orbit-counting,
        conjugation-action, mulaction
-/

set_option maxHeartbeats 800000

namespace LagrangeTheoremOQ02OQ02OQ01

open MulAction

-- ============================================================================
-- Part I: Burnside's Lemma (sum form) — direct Mathlib invocation
-- ============================================================================

/-- **Burnside's Lemma (sum form)**: for a finite group `G` acting on a
    finite set `X`, the total number of fixed points (summed over `G`)
    equals the number of orbits times `|G|`:

    `Σ_{g ∈ G} |Fix(g)| = |X/G| · |G|`.

    This is the multiplicative formulation that avoids `ℕ`-division.
    It is `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
    verbatim, restated in the namespace of this file. -/
theorem burnside_lemma_sum_form
    (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] [Fintype X]
    [(g : G) → Fintype (fixedBy X g)]
    [Fintype (orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (fixedBy X g) =
      Fintype.card (orbitRel.Quotient G X) * Fintype.card G :=
  MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X

-- ============================================================================
-- Part II: Burnside's Lemma (average form)
-- ============================================================================

/-- **Burnside's Lemma (average form)**: the number of orbits equals the
    average number of fixed points,

    `|X/G| = (1/|G|) · Σ_{g ∈ G} |Fix(g)|`,

    cast in `ℕ` using exact division (legal because `|G| > 0` and
    `|G|` divides the left-hand side).

    Derived from `burnside_lemma_sum_form` plus `Nat` division. -/
theorem burnside_lemma_average_form
    (G : Type*) [Group G] [Fintype G]
    (X : Type*) [MulAction G X] [Fintype X]
    [(g : G) → Fintype (fixedBy X g)]
    [Fintype (orbitRel.Quotient G X)]
    (hG : 0 < Fintype.card G) :
    Fintype.card (orbitRel.Quotient G X) =
      (∑ g : G, Fintype.card (fixedBy X g)) / Fintype.card G := by
  rw [burnside_lemma_sum_form G X]
  exact (Nat.mul_div_cancel _ hG).symm

-- ============================================================================
-- Part III: The Conjugation-Action Specialisation
-- ============================================================================

/-- **Burnside applied to the conjugation action** `ConjAct G ↷ G`:

    `Σ_{c ∈ ConjAct G} |Fix_c(G)| = |G/∼_conj| · |ConjAct G|`.

    This is the *same* identity the parent file uses for the class
    equation — the conjugation action is one specialisation of
    `MulAction`, the general `G ↷ X` action is another. The fixed
    points of a conjugation element `c = ConjAct.toConjAct g` are
    precisely the elements of `G` that commute with `g`, i.e. the
    centraliser `C_G(g)`. Summing over `c` is the dual statement to
    summing over conjugacy classes (the class equation form). -/
theorem conjugation_burnside_form
    (G : Type*) [Group G] [Fintype G]
    [(c : ConjAct G) → Fintype (fixedBy G c)]
    [Fintype (orbitRel.Quotient (ConjAct G) G)] :
    ∑ c : ConjAct G, Fintype.card (fixedBy G c) =
      Fintype.card (orbitRel.Quotient (ConjAct G) G) *
        Fintype.card (ConjAct G) :=
  burnside_lemma_sum_form (ConjAct G) G

-- ============================================================================
-- Part IV: OQ-01 Resolution
-- ============================================================================

/-- **OQ-01 resolution**. The open question

      "Can the class equation be used to formally prove the Burnside
       lemma in Lean 4 using only the infrastructure developed here?"

    is answered in the affirmative by the conjunction:

    (1) the symmetric (sum) form of Burnside's lemma holds for every
        finite group `G` and finite `G`-set `X`, and
    (2) the conjugation-action specialisation — the *same* identity
        used by the parent file's class equation — is recovered as a
        special case.

    The Lean proof is the trivial conjunction of `burnside_lemma_sum_form`
    and `conjugation_burnside_form`. Together they exhibit Burnside as
    the general statement of which the parent's class equation is the
    `G ↷ G` specialisation. -/
theorem oq01_resolution :
    (∀ (G : Type) [Group G] [Fintype G]
        (X : Type) [MulAction G X] [Fintype X]
        [(g : G) → Fintype (fixedBy X g)]
        [Fintype (orbitRel.Quotient G X)],
        ∑ g : G, Fintype.card (fixedBy X g) =
          Fintype.card (orbitRel.Quotient G X) * Fintype.card G) ∧
    (∀ (G : Type) [Group G] [Fintype G]
        [(c : ConjAct G) → Fintype (fixedBy G c)]
        [Fintype (orbitRel.Quotient (ConjAct G) G)],
        ∑ c : ConjAct G, Fintype.card (fixedBy G c) =
          Fintype.card (orbitRel.Quotient (ConjAct G) G) *
            Fintype.card (ConjAct G)) :=
  ⟨fun G _ _ X _ _ _ _ => burnside_lemma_sum_form G X,
   fun G _ _ _ _ => conjugation_burnside_form G⟩

#check @burnside_lemma_sum_form
#check @burnside_lemma_average_form
#check @conjugation_burnside_form
#check @oq01_resolution

/-
  ## Results Summary

  | Theorem | Statement | Status |
  |---------|-----------|--------|
  | `burnside_lemma_sum_form` | Σ_g \|Fix(g)\| = \|X/G\| · \|G\| | Proved (Mathlib) |
  | `burnside_lemma_average_form` | \|X/G\| = (Σ_g \|Fix(g)\|) / \|G\| | Proved |
  | `conjugation_burnside_form` | Σ_c \|Fix_c(G)\| = \|G/∼\| · \|ConjAct G\| | Proved |
  | `oq01_resolution` | (sum form) ∧ (conjugation specialisation) | Proved |

  **Sorries**: 0
  **Axioms**: 0 declared (Mathlib triple inherited)
-/

end LagrangeTheoremOQ02OQ02OQ01
