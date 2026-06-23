import Mathlib.Logic.Function.Basic
import Mathlib.Tactic

/-
# Lawvere Fixed-Point Theorem: Retraction Version

## What This Proves
The retraction formulation of Lawvere's fixed-point theorem: if a type Y can
"code" all its own endomorphisms — meaning there exist encode : (Y → Y) → Y
and decode : Y → (Y → Y) with decode ∘ encode = id — then every endomorphism
f : Y → Y has a fixed point. In categorical terms: in a cartesian closed
category, if the exponential Y^Y retracts onto Y, every endomorphism has a
fixed point.

This complements CantorDiagonalizationOQ03 (surjection version) by making
the retraction/section structure explicit, connecting to the categorical notion
of a retract in a CCC.

## Approach
- **Foundation**: Section-retraction pairs (encode, decode) with decode ∘ encode = id
- **Key construction**: g(y) = f(decode(y)(y)) — the diagonal via retraction
- **Applications**: ℕ, Bool, Prop cannot code their own endomorphisms;
  Cantor's theorem follows; the Y combinator is extracted constructively

## Proof Techniques
- Diagonal construction with retractions
- Fixed-point extraction via self-application
- Impossibility by exhibiting fixed-point-free endomorphisms

Historical Note: F. William Lawvere (1969) proved this in the setting of
cartesian closed categories. The retraction formulation captures the
categorical content: "Y^Y retracts onto Y" means every endomorphism of Y
can be named by an element of Y and faithfully recovered. This is the
property that makes fixed-point theorems (and their impossibility duals)
work across set theory, logic, and computation.
-/

namespace CantorDiagonalizationOQ04

-- ================================================================
-- Part I: The Retraction Framework
-- ================================================================

/-
  A type Y "codes its own endomorphisms" if the function space Y → Y
  is a retract of Y. This means there is an encoding that assigns each
  endomorphism a "name" in Y, and a decoding that faithfully recovers
  the endomorphism from its name.

  In categorical language: there exist morphisms
    encode : Y^Y → Y  and  decode : Y → Y^Y
  with decode ∘ encode = id_{Y^Y}.

  This is stronger than mere surjectivity of decode: it provides a
  canonical section (right inverse).
-/

/-- A type codes its own endomorphisms when Y → Y retracts into Y
    via an encode/decode pair with decode ∘ encode = id. -/
structure CodesEndomorphisms (Y : Type*) where
  /-- Assign a name in Y to each endomorphism -/
  encode : (Y → Y) → Y
  /-- Recover the endomorphism from its name -/
  decode : Y → (Y → Y)
  /-- Round-trip property: decoding an encoded endomorphism recovers it -/
  retract : ∀ f : Y → Y, decode (encode f) = f

-- ================================================================
-- Part II: Lawvere's Fixed-Point Theorem (Retraction Version)
-- ================================================================

/-
  The core theorem: if Y codes its own endomorphisms, then every
  endomorphism f : Y → Y has a fixed point.

  Proof: Define g(y) = f(decode(y)(y)) — the "diagonal" endomorphism.
  Since g is an endomorphism of Y, it has a name y₀ = encode(g).
  Then decode(y₀) = g by the retract property, so:

    g(y₀) = f(decode(y₀)(y₀)) = f(g(y₀))

  Setting b = g(y₀), we have f(b) = b. ∎
-/

/-- **Lawvere Fixed-Point Theorem (Retraction Version)**: If Y codes
    its own endomorphisms, every f : Y → Y has a fixed point. -/
theorem lawvere_fixpoint {Y : Type*} (c : CodesEndomorphisms Y)
    (f : Y → Y) : ∃ y : Y, f y = y := by
  -- The diagonal endomorphism: g(y) = f(decode(y)(y))
  let g : Y → Y := fun y => f (c.decode y y)
  -- Encode g to get its "name"
  let y₀ := c.encode g
  -- g(y₀) is the fixed point
  refine ⟨g y₀, ?_⟩
  -- By the retract property: decode(encode(g)) = g
  -- So decode(y₀)(y₀) = g(y₀), hence g(y₀) = f(g(y₀))
  have key : c.decode y₀ y₀ = g y₀ := congr_fun (c.retract g) y₀
  -- Goal: f(g(y₀)) = g(y₀), which follows since g(y₀) = f(decode(y₀)(y₀)) = f(g(y₀))
  exact (congr_arg f key).symm

-- ================================================================
-- Part III: Contrapositive — Fixed-Point-Free Implies No Coding
-- ================================================================

/-- If f : Y → Y has no fixed point, then Y cannot code its
    own endomorphisms. This is the impossibility direction. -/
theorem no_coding_if_fixpoint_free {Y : Type*} (f : Y → Y)
    (hf : ∀ y, f y ≠ y) : CodesEndomorphisms Y → False := by
  intro c
  obtain ⟨y, hy⟩ := lawvere_fixpoint c f
  exact hf y hy

-- ================================================================
-- Part IV: Surjections Induce Retractions
-- ================================================================

/-
  If decode : Y → (Y → Y) is surjective, the axiom of choice gives
  a right inverse encode, yielding a CodesEndomorphisms instance.
  This connects the retraction version to the surjection version
  proved in CantorDiagonalizationOQ03.
-/

/-- A surjection Y → (Y → Y) induces an endomorphism coding
    (using choice for the right inverse). -/
noncomputable def codesOfSurjection {Y : Type*} (e : Y → Y → Y)
    (he : Function.Surjective e) : CodesEndomorphisms Y where
  encode := fun f => (he f).choose
  decode := e
  retract := fun f => (he f).choose_spec

/-- The surjection version of Lawvere follows from the retraction version:
    if e : Y → (Y → Y) is surjective, every f : Y → Y has a fixed point. -/
theorem lawvere_fixpoint_of_surjection {Y : Type*} (e : Y → Y → Y)
    (he : Function.Surjective e) (f : Y → Y) :
    ∃ y : Y, f y = y :=
  lawvere_fixpoint (codesOfSurjection e he) f

-- ================================================================
-- Part V: Impossibility Results
-- ================================================================

/-
  Several familiar types cannot code their own endomorphisms because
  they admit fixed-point-free endomorphisms.
-/

/-- ℕ cannot code its own endomorphisms: successor has no fixed point. -/
theorem nat_cannot_code : CodesEndomorphisms ℕ → False :=
  no_coding_if_fixpoint_free Nat.succ Nat.succ_ne_self

/-- Bool cannot code its own endomorphisms: negation has no fixed point. -/
theorem bool_cannot_code : CodesEndomorphisms Bool → False := by
  apply no_coding_if_fixpoint_free (fun b => !b)
  intro b; cases b <;> decide

/-- Negation has no fixed point in Prop. -/
theorem not_no_fixpoint : ∀ p : Prop, (¬p) ≠ p := by
  intro p h
  have to_np : p → ¬p := cast h.symm
  have to_p : ¬p → p := cast h
  have np : ¬p := fun hp => to_np hp hp
  exact np (to_p np)

/-- Prop cannot code its own endomorphisms: negation has no fixed point. -/
theorem prop_cannot_code : CodesEndomorphisms Prop → False :=
  no_coding_if_fixpoint_free Not not_no_fixpoint

-- ================================================================
-- Part VI: Cantor's Theorem via Retractions
-- ================================================================

/-
  Cantor's theorem in retraction form: there is no surjection from any
  type A to its function space A → B when B admits a fixed-point-free
  endomorphism. The retraction version gives us: A → B cannot be a
  retract of A.
-/

/-- No surjection A → (A → B) exists when B has a fixed-point-free
    endomorphism (Cantor's theorem via Lawvere). -/
theorem cantor_no_surjection {A B : Type*} (f : B → B)
    (hf : ∀ b, f b ≠ b) :
    ¬∃ e : A → A → B, Function.Surjective e := by
  rintro ⟨e, he⟩
  obtain ⟨b, hb⟩ := lawvere_fixpoint_of_surjection e he f
  exact hf b hb

/-- No surjection A → (A → Prop). -/
theorem cantor_prop (A : Type*) :
    ¬∃ e : A → A → Prop, Function.Surjective e :=
  cantor_no_surjection Not not_no_fixpoint

/-- No surjection A → (A → Bool). -/
theorem cantor_bool (A : Type*) :
    ¬∃ e : A → A → Bool, Function.Surjective e := by
  apply cantor_no_surjection (fun b => !b)
  intro b; cases b <;> decide

/-- No surjection A → (A → ℕ). -/
theorem cantor_nat (A : Type*) :
    ¬∃ e : A → A → ℕ, Function.Surjective e :=
  cantor_no_surjection Nat.succ Nat.succ_ne_self

-- ================================================================
-- Part VII: The Y Combinator
-- ================================================================

/-
  The proof of Lawvere's theorem constructively builds a fixed-point
  operator. In settings where every type codes its endomorphisms
  (like the untyped lambda calculus, where Y ≅ Y → Y), this gives
  the Y combinator: Y(f) = g(y₀) where g(y) = f(decode(y)(y)).
-/

/-- The fixed-point combinator extracted from an endomorphism coding. -/
def yCombinator {Y : Type*} (c : CodesEndomorphisms Y) (f : Y → Y) : Y :=
  let g : Y → Y := fun y => f (c.decode y y)
  g (c.encode g)

/-- The Y combinator produces genuine fixed points. -/
theorem yCombinator_is_fixpoint {Y : Type*} (c : CodesEndomorphisms Y)
    (f : Y → Y) : f (yCombinator c f) = yCombinator c f := by
  unfold yCombinator
  -- After unfolding, the goal involves c.decode (c.encode g) (c.encode g)
  -- which equals g (c.encode g) by the retract property
  exact (congr_arg f (congr_fun (c.retract _) _)).symm

-- ================================================================
-- Part VIII: The Diagonal Map
-- ================================================================

/-
  The diagonal map d(y) = decode(y)(y) is the key construction.
  It satisfies a universal tracking property: for every endomorphism
  g : Y → Y, there exists y₀ with d(y₀) = g(y₀). This is why the
  diagonal "defeats" any attempted enumeration.
-/

/-- The diagonal map: apply the decoded endomorphism to its own name. -/
def diag {Y : Type*} (c : CodesEndomorphisms Y) : Y → Y :=
  fun y => c.decode y y

/-- The diagonal tracks every endomorphism at some point:
    for every g : Y → Y, there exists y₀ with diag(y₀) = g(y₀). -/
theorem diag_tracks {Y : Type*} (c : CodesEndomorphisms Y)
    (g : Y → Y) : ∃ y₀, diag c y₀ = g y₀ :=
  ⟨c.encode g, congr_fun (c.retract g) (c.encode g)⟩

-- ================================================================
-- Part IX: Categorical Interpretation
-- ================================================================

/-
  In a cartesian closed category C, every object Y has an exponential
  object Y^Y (the internal hom [Y, Y]). "Y^Y retracts onto Y" means
  Y is a retract of Y^Y: there exist morphisms

    encode : Y^Y → Y   and   decode : Y → Y^Y

  with decode ∘ encode = id_{Y^Y}.

  The type-theoretic version proved above is this theorem instantiated
  in the category Type, where:
  - Objects are types
  - Morphisms are functions
  - The exponential Y^Y is the function type Y → Y
  - Terminal object 1 is Unit (PUnit)
  - Global elements (1 → Y) correspond to terms of type Y
  - "Fixed point" means f(y) = y for some y : Y

  The proof carries over to any CCC because it uses only:
  1. Composition of morphisms
  2. The evaluation map ev : Y^Y × Y → Y
  3. The diagonal Δ : Y → Y × Y
  4. Currying (to form the diagonal endomorphism)

  All of which are available in any cartesian closed category.
-/

-- For completeness, we show that CodesEndomorphisms is equivalent
-- to Function.HasRightInverse for the decode map.

/-- Having a right inverse for decode is equivalent to coding endomorphisms. -/
theorem codes_iff_right_inverse {Y : Type*} :
    Nonempty (CodesEndomorphisms Y) ↔
    ∃ d : Y → Y → Y, Function.HasRightInverse d := by
  constructor
  · rintro ⟨c⟩
    exact ⟨c.decode, c.encode, c.retract⟩
  · rintro ⟨d, e, he⟩
    exact ⟨⟨e, d, he⟩⟩

end CantorDiagonalizationOQ04

-- Verification
#check CantorDiagonalizationOQ04.lawvere_fixpoint
#check CantorDiagonalizationOQ04.nat_cannot_code
#check CantorDiagonalizationOQ04.bool_cannot_code
#check CantorDiagonalizationOQ04.prop_cannot_code
#check CantorDiagonalizationOQ04.cantor_no_surjection
#check CantorDiagonalizationOQ04.yCombinator_is_fixpoint
#check CantorDiagonalizationOQ04.diag_tracks
#check CantorDiagonalizationOQ04.codes_iff_right_inverse
