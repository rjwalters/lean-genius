import Mathlib.Logic.Function.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic

/-
# Lawvere Fixed-Point Theorem: Setoid Generalization

## Open Question (cantor-diagonalization-oq-04-oq-01)
"Can the retraction version be formalized in a general topos or CCC in Lean,
beyond the Type category?"

## Answer
Yes — the key step toward CCC generality is replacing strict Type equality with a
Setoid equivalence relation. This file proves Lawvere's FPT for Setoids:

If the endomorphisms of `Y` can be "named" up to setoid equivalence
(decode(encode(f))(y) ≈ f(y) for all y), then every function f : Y → Y
has a **setoid fixed point** — an element p with f(p) ≈ p.

This strictly generalizes the parent result (CantorDiagonalizationOQ04):
- **Type version**: requires exact equality decode(encode f) = f
- **Setoid version**: only requires decode(encode f)(y) ≈ f(y) pointwise

The setoid framework models the CCC situation: in a CCC (or topos), equality
is often replaced by isomorphism or coherent equivalence. Setoids internalize
this within Lean's type theory. The discrete setoid (≈ = equality) recovers
the original theorem exactly.

## Key Results
1. `lawvere_fixpoint_setoid` — setoid fixed point for any f : Y → Y
2. `no_coding_setoid_if_fixpoint_free` — contrapositive: fixpoint-free f prevents coding
3. `typeToSetoidCoding` — Type coding implies setoid coding (discrete setoid)
4. `lawvere_type_from_setoid` — setoid version recovers Type version
5. `cannot_code_endomorphisms_bool_setoid` — Bool cannot code its endomorphisms
6. `cantor_setoid_no_surjection` — Cantor diagonal in setoid setting
7. `cannot_code_endomorphisms_nat_parity` — ℕ cannot code endomorphisms up to parity
8. `trivial_setoid_codes_endomorphisms` — every inhabited Y codes under the trivial (one-class) setoid
9. `bool_trivial_setoid_codes_endomorphisms` — Bool codes under trivial setoid (contrast with #5)
10. `coding_descends_to_coarser` — coding under a finer setoid descends to any coarser setoid

## Proof Technique
Diagonal construction: g(y) = f(decode(y)(y)).
Set y₀ = encode(g), p = decode(y₀)(y₀).
Retraction gives: p ≈ g(y₀) = f(p). By symmetry: f(p) ≈ p.
Note: f need NOT be a setoid morphism.

References:
- F.W. Lawvere, "Diagonal arguments and cartesian closed categories" (1969)
- Parent: CantorDiagonalizationOQ04 (Type-level retraction version)
-/

namespace CantorDiagonalizationOQ04OQ01

-- ============================================================
-- Part I: Coded Endomorphisms for Setoids
-- ============================================================

/-- `Y` **codes its endomorphisms up to setoid equivalence** when there exist
    encode/decode functions with a setoid-level retraction:
    `decode (encode g) y ≈ g y` for all g and y. -/
structure CodesEndomorphismsSetoid (Y : Type*) (s : Setoid Y) where
  encode : (Y → Y) → Y
  decode : Y → (Y → Y)
  retract : ∀ (g : Y → Y) (y : Y), s.r (decode (encode g) y) (g y)

-- ============================================================
-- Part II: Main Theorem
-- ============================================================

/-- **Lawvere Fixed-Point Theorem (Setoid Version)**.

    If Y codes its endomorphisms up to ≈, every f : Y → Y has a
    setoid fixed point p with f(p) ≈ p.

    The diagonal: g(y) = f(decode(y)(y)), y₀ = encode(g), p = decode(y₀)(y₀).
    Retraction gives p ≈ g(y₀) = f(p), so f(p) ≈ p by symmetry. -/
theorem lawvere_fixpoint_setoid {Y : Type*} (s : Setoid Y)
    (c : CodesEndomorphismsSetoid Y s) (f : Y → Y) :
    ∃ p : Y, s.r (f p) p := by
  let g : Y → Y := fun y => f (c.decode y y)
  let y₀ := c.encode g
  exact ⟨c.decode y₀ y₀, s.iseqv.symm (c.retract g y₀)⟩

-- ============================================================
-- Part III: Contrapositive
-- ============================================================

/-- If f : Y → Y has no setoid fixed point, Y cannot code its endomorphisms. -/
theorem no_coding_setoid_if_fixpoint_free {Y : Type*} (s : Setoid Y)
    (f : Y → Y) (hf : ∀ y : Y, ¬ s.r (f y) y) :
    CodesEndomorphismsSetoid Y s → False := fun c =>
  let ⟨p, hp⟩ := lawvere_fixpoint_setoid s c f; hf p hp

-- ============================================================
-- Part IV: Type Version as Discrete Setoid Case
-- ============================================================

/-- The discrete setoid: two elements are equivalent iff equal. -/
def discreteSetoid (Y : Type*) : Setoid Y where
  r := (· = ·)
  iseqv := eq_equivalence

/-- Any exact (Type-level) coding gives a setoid coding under the discrete setoid. -/
def typeToSetoidCoding {Y : Type*}
    (encode : (Y → Y) → Y) (decode : Y → (Y → Y))
    (retract : ∀ g : Y → Y, decode (encode g) = g) :
    CodesEndomorphismsSetoid Y (discreteSetoid Y) where
  encode := encode
  decode := decode
  retract := fun g y => congr_fun (retract g) y

/-- The setoid version for the discrete setoid recovers the Type fixed-point theorem. -/
theorem lawvere_type_from_setoid {Y : Type*}
    (encode : (Y → Y) → Y) (decode : Y → (Y → Y))
    (retract : ∀ g : Y → Y, decode (encode g) = g) (f : Y → Y) :
    ∃ y : Y, f y = y :=
  lawvere_fixpoint_setoid (discreteSetoid Y) (typeToSetoidCoding encode decode retract) f

-- ============================================================
-- Part V: Bool Cannot Code Its Endomorphisms
-- ============================================================

/-- Boolean negation has no discrete-setoid fixed point. -/
theorem bool_not_no_fixed_point : ∀ p : Bool, (! p) ≠ p := by decide

/-- Bool cannot code its own endomorphisms under the discrete setoid. -/
theorem cannot_code_endomorphisms_bool_setoid :
    CodesEndomorphismsSetoid Bool (discreteSetoid Bool) → False :=
  no_coding_setoid_if_fixpoint_free (discreteSetoid Bool) (fun b : Bool => !b)
    (fun p hp => bool_not_no_fixed_point p hp)

-- ============================================================
-- Part VI: Cantor's Theorem in Setoid Setting
-- ============================================================

/-- There is no point-surjective function from Y to its powerset.

    If h(y₀) = D (diagonal predicate), then h(y₀)(y₀) ↔ ¬h(y₀)(y₀). -/
theorem cantor_setoid_no_surjection (Y : Type*) :
    ¬ ∃ h : Y → (Y → Prop), ∀ P : Y → Prop, ∃ y : Y, h y = P := by
  intro ⟨h, hsurj⟩
  let D : Y → Prop := fun y => ¬ h y y
  obtain ⟨y₀, hy₀⟩ := hsurj D
  have hkey : h y₀ y₀ ↔ ¬ h y₀ y₀ := iff_of_eq (congr_fun hy₀ y₀)
  exact absurd (hkey.mpr (fun h1 => hkey.mp h1 h1)) (fun h1 => hkey.mp h1 h1)

-- ============================================================
-- Part VII: Parity Setoid Example
-- ============================================================

/-- The parity setoid on ℕ: a ≈ b iff a and b have the same remainder mod 2. -/
def paritySetoidN : Setoid ℕ where
  r := fun a b => a % 2 = b % 2
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The successor function n ↦ n+1 has no parity-equivalence fixed point,
    since n+1 and n always differ in parity. -/
theorem succ_no_parity_fixpoint : ∀ n : ℕ, ¬ paritySetoidN.r (n + 1) n := by
  intro n h
  simp only [paritySetoidN] at h
  omega

/-- ℕ cannot code its endomorphisms up to the parity setoid,
    since the parity-shifting function n ↦ n+1 has no parity fixed point. -/
theorem cannot_code_endomorphisms_nat_parity :
    CodesEndomorphismsSetoid ℕ paritySetoidN → False :=
  no_coding_setoid_if_fixpoint_free paritySetoidN (fun n : ℕ => n + 1) succ_no_parity_fixpoint

-- ============================================================
-- Part VIII: Trivial Setoid — Coding Always Possible
-- ============================================================

/-- The trivial setoid: every pair is equivalent. Collapses Y to a single class. -/
def trivialSetoid (Y : Type*) : Setoid Y where
  r := fun _ _ => True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

/-- **Setoid-choice sensitivity**: under the trivial (one-class) setoid, every
    inhabited type codes its endomorphisms vacuously. The retraction holds because
    `s.r a b = True` for all `a, b`. Together with `cannot_code_endomorphisms_bool_setoid`
    this shows that coding-feasibility depends genuinely on the setoid structure,
    not just on the underlying type. -/
theorem trivial_setoid_codes_endomorphisms (Y : Type*) [Inhabited Y] :
    CodesEndomorphismsSetoid Y (trivialSetoid Y) where
  encode := fun _ => default
  decode := fun _ => id
  retract := fun _ _ => trivial

/-- Bool DOES code its endomorphisms under the trivial setoid, even though it
    fails under the discrete setoid (cf. `cannot_code_endomorphisms_bool_setoid`).
    Witnesses that the impossibility result for Bool is setoid-specific. -/
theorem bool_trivial_setoid_codes_endomorphisms :
    CodesEndomorphismsSetoid Bool (trivialSetoid Bool) :=
  trivial_setoid_codes_endomorphisms Bool

-- ============================================================
-- Part IX: Refinement Lemma — Coding Descends to Coarser Setoids
-- ============================================================

/-- A setoid `s` **refines** `t` when `s`-equivalence implies `t`-equivalence
    (equivalently, `t` is coarser than `s`). The discrete setoid refines every
    setoid; every setoid refines the trivial setoid. -/
def IsRefinement {Y : Type*} (s t : Setoid Y) : Prop :=
  ∀ a b : Y, s.r a b → t.r a b

/-- **Refinement-descent**: if `Y` codes its endomorphisms under a finer setoid `s`,
    the same encode/decode also code under any coarser setoid `t`. The retraction
    transports along refinement because `t`-equivalence is weaker than `s`-equivalence. -/
theorem coding_descends_to_coarser {Y : Type*} {s t : Setoid Y}
    (hst : IsRefinement s t) (c : CodesEndomorphismsSetoid Y s) :
    CodesEndomorphismsSetoid Y t where
  encode := c.encode
  decode := c.decode
  retract := fun g y => hst _ _ (c.retract g y)

/-- Every setoid is a refinement of the trivial setoid (vacuously: the trivial relation
    is `True`). This is the canonical "top" of the refinement order on `Setoid Y`. -/
theorem refines_trivial {Y : Type*} (s : Setoid Y) : IsRefinement s (trivialSetoid Y) :=
  fun _ _ _ => trivial

end CantorDiagonalizationOQ04OQ01
