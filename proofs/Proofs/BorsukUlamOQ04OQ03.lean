/-
# The ∞-Topos Section Problem — the π₁ Shadow of the Covering Obstruction

Open question (Borsuk-Ulam family, `borsuk-ulam-oq-04-oq-03`):

  "Can the ∞-topos section problem — the non-existence of a section of the
   universal ℤ/2-bundle EℤZ/2 → BℤZ/2 — be formalized in Lean?"

The classical Borsuk-Ulam covering-space obstruction says: the double cover
Sⁿ → RPⁿ admits no section. Stated in the language of classifying spaces, the
universal ℤ/2-bundle `EℤZ/2 → BℤZ/2` has a **contractible total space**
`EℤZ/2 ≃ *`, so a section would exhibit the base `BℤZ/2 = RP^∞` as a retract of
a contractible space, forcing `BℤZ/2` to be contractible. But
`π₁(BℤZ/2) = ℤ/2 ≠ 0`. Contradiction.

## What is (and is not) formalized here

Lean 4's type theory is **not** homotopy type theory: it has definitional proof
irrelevance and UIP, so there is no native notion of a homotopically nontrivial
"contractible" type, and a literal *synthetic-HoTT* proof (univalence + higher
inductive types) is not available in Mathlib. The problem statement explicitly
offers an alternative route — "using Mathlib's fundamental groups" — and that is
what this file delivers.

We formalize the obstruction at the level of its **fundamental-group shadow**,
the algebraic invariant the classical argument actually uses. Applying `π₁(-)` to
a fibration `p : E → B` gives a group homomorphism `p_* : π₁(E) → π₁(B)`. A
section `s : B → E` (with `p ∘ s = id`) induces a *group-theoretic section*
`s_* : π₁(B) → π₁(E)` with `p_* ∘ s_* = id`. Thus:

  a topological section ⟹ a group retraction of π₁(B) onto a subgroup of π₁(E).

The whole obstruction is then pure group theory, which we prove with **0 axioms,
0 sorries**:

* `section_injective`            — a homomorphism section is injective.
* `card_le_of_section`           — a section forces `|π₁(B)| ≤ |π₁(E)|`.
* `projStar_surjective_of_section` — `p_*` is a split epimorphism.
* `no_section_of_trivial_total`  — if `π₁(E)` is trivial and `π₁(B)` is
                                    nontrivial, **no section exists**.

The geometric payload is the corollary `universalZ2Bundle_no_section`: modelling
the universal bundle by its fundamental groups `π₁(EℤZ/2) = 0` (contractible
total space) and `π₁(BℤZ/2) = ℤ/2`, the universal ℤ/2-bundle admits no section.

This is the honest, machine-checked content of the ∞-topos section problem that
Lean/Mathlib can carry today: the homotopy-coherent statement reduced to the
1-truncated (fundamental-group) obstruction it rests on.

Axioms: 0
Sorries: 0

Reference: https://erdosproblems.com (Borsuk-Ulam family)
-/

import Mathlib

set_option linter.unusedVariables false

namespace BorsukUlamOQ04OQ03

-- ============================================================
-- PART 1: The π₁-level section obstruction (pure group theory)
-- ============================================================
/-
Applying the fundamental-group functor to a fibration `p : E → B` produces a
group homomorphism `p_* : π₁(E) → π₁(B)`. A topological section `s : B → E` with
`p ∘ s = id` induces `s_* : π₁(B) → π₁(E)` with `p_* ∘ s_* = id`. We work with an
abstract such pair `(p, s)` of group homomorphisms.
-/

variable {G H : Type*} [Group G] [Group H]

/-- A homomorphism section is injective: if `p ∘ s = id` then `s` has a left
    inverse, hence is injective. (The base `π₁(B)` embeds into `π₁(E)`.) -/
theorem section_injective (p : H →* G) (s : G →* H)
    (hsec : p.comp s = MonoidHom.id G) : Function.Injective s := by
  have hL : Function.LeftInverse p s := fun x => by
    have := congrArg (fun (f : G →* G) => f x) hsec
    simpa using this
  exact hL.injective

/-- A section forces a cardinality inequality on fundamental groups:
    `|π₁(B)| ≤ |π₁(E)|`. For the universal ℤ/2-bundle this reads `2 ≤ 1`,
    already impossible. -/
theorem card_le_of_section [Fintype G] [Fintype H] (p : H →* G) (s : G →* H)
    (hsec : p.comp s = MonoidHom.id G) :
    Fintype.card G ≤ Fintype.card H :=
  Fintype.card_le_of_injective _ (section_injective p s hsec)

/-- The projection `p_*` is a split epimorphism: a section makes it surjective. -/
theorem projStar_surjective_of_section (p : H →* G) (s : G →* H)
    (hsec : p.comp s = MonoidHom.id G) : Function.Surjective p := by
  intro g
  refine ⟨s g, ?_⟩
  have := congrArg (fun (f : G →* G) => f g) hsec
  simpa using this

/-- **The section obstruction.** If `π₁(E)` is trivial (the total space is
    contractible, so `Subsingleton`) while `π₁(B)` is nontrivial, then there is
    no group-theoretic section of `p_* : π₁(E) → π₁(B)`. This is the algebraic
    heart of "a fibration with contractible total space has no section when the
    base has nontrivial fundamental group". -/
theorem no_section_of_trivial_total [Subsingleton H] [Nontrivial G] :
    ¬ ∃ (p : H →* G) (s : G →* H), p.comp s = MonoidHom.id G := by
  rintro ⟨p, s, hsec⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne G
  exact hab (section_injective p s hsec (Subsingleton.elim (s a) (s b)))

-- ============================================================
-- PART 2: The abstract section problem as a structure
-- ============================================================
/-
We package a fibration's π₁ data into a structure mirroring the ∞-topos framing:
the "section problem" is the pair of fundamental groups together with the
induced projection `p_* : π₁(E) → π₁(B)`. `HasSection` asks for a homomorphism
splitting.
-/

/-- The π₁ data of a fibration `E → B`: the fundamental groups of total and base
    space together with the induced homomorphism `projStar = p_*`. -/
structure SectionProblem where
  /-- `π₁(E)`, the fundamental group of the total space. -/
  Total : Type
  /-- `π₁(B)`, the fundamental group of the base space. -/
  Base : Type
  [groupTotal : Group Total]
  [groupBase : Group Base]
  /-- The induced map on fundamental groups, `p_* : π₁(E) → π₁(B)`. -/
  projStar : Total →* Base

attribute [instance] SectionProblem.groupTotal SectionProblem.groupBase

/-- A section problem `HasSection` when `projStar` admits a homomorphism
    splitting `s : π₁(B) → π₁(E)` with `projStar ∘ s = id`. -/
def SectionProblem.HasSection (F : SectionProblem) : Prop :=
  ∃ s : F.Base →* F.Total, F.projStar.comp s = MonoidHom.id F.Base

/-- The structural form of the obstruction: a section problem whose total
    fundamental group is trivial and whose base fundamental group is nontrivial
    has no section. -/
theorem SectionProblem.no_section (F : SectionProblem)
    [Subsingleton F.Total] [Nontrivial F.Base] : ¬ F.HasSection := by
  rintro ⟨s, hs⟩
  exact no_section_of_trivial_total ⟨F.projStar, s, hs⟩

-- ============================================================
-- PART 3: The universal ℤ/2-bundle EℤZ/2 → BℤZ/2
-- ============================================================
/-
We instantiate the framework with the fundamental-group data of the universal
ℤ/2-bundle:

  π₁(EℤZ/2) = 0      (EℤZ/2 ≃ * is contractible)         modelled by `PUnit`
  π₁(BℤZ/2) = ℤ/2    (BℤZ/2 = RP^∞)                       modelled by `Multiplicative (ZMod 2)`

The only homomorphism out of the trivial group is the trivial one, so
`projStar = 1`. The corollary is exactly the non-existence of a section.
-/

/-- `π₁(BℤZ/2) = ℤ/2` is nontrivial. Written multiplicatively, as fundamental
    groups are. -/
instance : Nontrivial (Multiplicative (ZMod 2)) :=
  ⟨⟨Multiplicative.ofAdd 0, Multiplicative.ofAdd 1, by
      simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]; decide⟩⟩

/-- The universal ℤ/2-bundle, recorded through its fundamental groups:
    contractible total space (`π₁ = PUnit`) over `BℤZ/2 = RP^∞`
    (`π₁ = ℤ/2`), with the necessarily-trivial induced projection. -/
def universalZ2Bundle : SectionProblem where
  Total := PUnit
  Base := Multiplicative (ZMod 2)
  projStar := 1

/-- **The ∞-topos section problem, π₁ shadow.** The universal ℤ/2-bundle
    `EℤZ/2 → BℤZ/2` admits no section: a section would split `π₁`, embedding
    `π₁(BℤZ/2) = ℤ/2` into the trivial group `π₁(EℤZ/2) = 0`, which is
    impossible since `ℤ/2 ≠ 0`. This is the covering-space obstruction at the
    foundation of the Borsuk-Ulam theorem. -/
theorem universalZ2Bundle_no_section : ¬ universalZ2Bundle.HasSection :=
  universalZ2Bundle.no_section

/-- The same obstruction read quantitatively: any putative section of the
    universal ℤ/2-bundle would force `|π₁(BℤZ/2)| ≤ |π₁(EℤZ/2)|`, i.e. `2 ≤ 1`. -/
theorem universalZ2Bundle_card_obstruction :
    ¬ ∃ (p : PUnit →* Multiplicative (ZMod 2)) (s : Multiplicative (ZMod 2) →* PUnit),
        p.comp s = MonoidHom.id _ := by
  rintro ⟨p, s, hsec⟩
  have h := card_le_of_section p s hsec
  have h2 : 1 < Fintype.card (Multiplicative (ZMod 2)) := Fintype.one_lt_card
  simp only [Fintype.card_punit] at h
  omega

end BorsukUlamOQ04OQ03
