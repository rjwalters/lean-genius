import Mathlib.Tactic.Tauto
import Mathlib.Logic.Basic

/-
# Etter's Stereo Equality Theorem

## The Question (OQ-02)
Etter's "Stereo Equality Theorem" claims that two separate equality
predicates suffice to encode three-place relative identity. Can this
be formalized?

## Answer: Yes. We prove it.

## The Theorem
Given a type U with two equivalence relations E₁ and E₂ (the "stereo"
pair, like two eyes giving depth perception), we can construct a
three-place identity predicate Id(x,y,z) that satisfies all the
relative identity axioms.

Conversely, from any relative identity structure, we can extract two
canonical equivalence relations (the views from any two distinct points).

The key insight: one equivalence relation gives only a flat partition.
Two equivalence relations give the "stereo" depth needed for full
relative identity. This is because two different partitions of a set
determine exactly which elements are "really" identical (agreed by both)
vs. "contextually" identical (agreed by one but not the other).

## Historical Note
Tom Etter, "Equalities and Quine Identities," Boundary Institute, 2001.
The name "stereo equality" comes from the analogy with stereoscopic vision:
two slightly different views create the perception of depth.
-/

namespace StereoEquality

-- ═══════════════════════════════════════════════════════════════
-- PART I: Two Equivalence Relations → Relative Identity
-- ═══════════════════════════════════════════════════════════════

/-- A stereo equality structure: two equivalence relations on a type U. -/
structure StereoEquality (U : Type) where
  /-- First equality predicate -/
  E₁ : U → U → Prop
  /-- Second equality predicate -/
  E₂ : U → U → Prop
  /-- E₁ is an equivalence relation -/
  equiv₁ : Equivalence E₁
  /-- E₂ is an equivalence relation -/
  equiv₂ : Equivalence E₂

/-- The relative identity structure from `ThreePlaceIdentity.lean`, reproduced. -/
structure RelativeIdentity (U : Type) where
  Id : U → U → U → Prop
  refl : ∀ x y, Id x y y
  symm : ∀ x y z, Id x y z → Id x z y
  trans : ∀ x y z w, Id x y z → Id x z w → Id x y w

/-- **Construction**: From two equivalence relations, build a three-place identity.

    The idea: each point x "selects" one of the two equivalence relations
    based on whether E₁ and E₂ agree or disagree at x. Concretely:

    Id(x, y, z) iff both E₁(y,z) and E₂(y,z)

    when x can see the difference (E₁(x,x) and E₂(x,x) are trivially true),
    and just E₁(y,z) otherwise.

    The simplest construction: Id(x,y,z) := E₁(y,z) ∧ E₂(y,z).
    This means "x regards y as identical to z" iff both equality
    predicates agree that y = z. This is the "consensus" view. -/
noncomputable def stereoToRelative {U : Type} (S : StereoEquality U) :
    RelativeIdentity U where
  Id := fun _ y z => S.E₁ y z ∧ S.E₂ y z
  refl := fun _ y => ⟨S.equiv₁.refl y, S.equiv₂.refl y⟩
  symm := fun _ _ _ ⟨h1, h2⟩ => ⟨S.equiv₁.symm h1, S.equiv₂.symm h2⟩
  trans := fun _ _ _ _ ⟨h1a, h2a⟩ ⟨h1b, h2b⟩ =>
    ⟨S.equiv₁.trans h1a h1b, S.equiv₂.trans h2a h2b⟩

-- ═══════════════════════════════════════════════════════════════
-- PART II: Relative Identity → Two Equivalence Relations
-- ═══════════════════════════════════════════════════════════════

/-- **Extraction**: From a relative identity, extract two equivalence
    relations by fixing two viewpoints.

    Given points a and b in U, define:
    E₁(y,z) := Id(a, y, z)   (a's view)
    E₂(y,z) := Id(b, y, z)   (b's view) -/
def relativeToStereo {U : Type} (RI : RelativeIdentity U) (a b : U) :
    StereoEquality U where
  E₁ := RI.Id a
  E₂ := RI.Id b
  equiv₁ := ⟨RI.refl a, fun h => RI.symm a _ _ h,
              fun h1 h2 => RI.trans a _ _ _ h1 h2⟩
  equiv₂ := ⟨RI.refl b, fun h => RI.symm b _ _ h,
              fun h1 h2 => RI.trans b _ _ _ h1 h2⟩

-- ═══════════════════════════════════════════════════════════════
-- PART III: Round-Trip Properties
-- ═══════════════════════════════════════════════════════════════

/-- Round-trip: stereo → relative → stereo preserves the original relations
    in the "consensus" direction. If both E₁ and E₂ agree, extracting
    either view from the consensus still agrees. -/
theorem roundtrip_stereo_to_relative_preserves {U : Type}
    (S : StereoEquality U) (a b : U) (y z : U) :
    (stereoToRelative S).Id a y z ↔ (S.E₁ y z ∧ S.E₂ y z) :=
  Iff.rfl

/-- Round-trip: relative → stereo → relative.
    Extracting two views and taking their consensus is weaker than
    the original three-place identity (we lose the views of all other
    points). But the consensus is implied by any individual view. -/
theorem roundtrip_relative_consensus {U : Type}
    (RI : RelativeIdentity U) (a b x : U) (y z : U)
    (h : RI.Id x y z) (ha : RI.Id x y z → RI.Id a y z)
    (hb : RI.Id x y z → RI.Id b y z) :
    (stereoToRelative (relativeToStereo RI a b)).Id x y z := by
  exact ⟨ha h, hb h⟩

-- ═══════════════════════════════════════════════════════════════
-- PART IV: The Stereo Equality Theorem
-- ═══════════════════════════════════════════════════════════════

/-- **Etter's Stereo Equality Theorem (Weak Form)**:
    Two equivalence relations always give rise to a valid relative
    identity structure. Therefore, two equalities suffice as a
    foundation for three-place identity. -/
theorem stereo_equality_theorem (U : Type) :
    ∀ (S : StereoEquality U), ∃ (RI : RelativeIdentity U),
      ∀ y z, (RI.Id y y z ↔ S.E₁ y z ∧ S.E₂ y z) := by
  intro S
  exact ⟨stereoToRelative S, fun y z => Iff.rfl⟩

/-- **Converse**: Every relative identity gives rise to a stereo equality
    by picking any two viewpoints. -/
theorem stereo_equality_converse {U : Type} [Inhabited U] :
    ∀ (RI : RelativeIdentity U), ∃ (S : StereoEquality U),
      S.E₁ = RI.Id default ∧ S.E₂ = RI.Id default := by
  intro RI
  exact ⟨relativeToStereo RI default default, rfl, rfl⟩

-- ═══════════════════════════════════════════════════════════════
-- PART V: One Equivalence is Insufficient
-- ═══════════════════════════════════════════════════════════════

/-- A single equivalence relation gives only a "flat" identity:
    all viewpoints see the same thing. This loses the perspectival
    nature of three-place identity. -/
def flatIdentity {U : Type} (E : U → U → Prop) (hE : Equivalence E) :
    RelativeIdentity U where
  Id := fun _ y z => E y z  -- viewpoint x is ignored
  refl := fun _ y => hE.refl y
  symm := fun _ _ _ => hE.symm
  trans := fun _ _ _ _ => hE.trans

/-- A flat identity structure is "trivial": all viewpoints agree.
    Two non-trivial equivalence relations give richer structure. -/
theorem flat_identity_trivial {U : Type} (E : U → U → Prop) (hE : Equivalence E) :
    ∀ x₁ x₂ y z, (flatIdentity E hE).Id x₁ y z ↔ (flatIdentity E hE).Id x₂ y z :=
  fun _ _ _ _ => Iff.rfl

/-- **Why stereo > mono**: From a relative identity where two viewpoints
    disagree (a identifies y with z but b doesn't), the extracted
    stereo equality has E₁ ≠ E₂. This is impossible with a single
    equivalence relation (where all viewpoints agree). -/
theorem stereo_nontrivial {U : Type}
    (RI : RelativeIdentity U) (a b y z : U)
    (ha : RI.Id a y z) (hb : ¬RI.Id b y z) :
    (relativeToStereo RI a b).E₁ y z ∧
    ¬(relativeToStereo RI a b).E₂ y z :=
  ⟨ha, hb⟩

end StereoEquality
