import Mathlib.Logic.Function.Basic
import Mathlib.Data.Setoid.Basic
import Mathlib.Tactic

/-
# Lawvere Fixed-Point Theorem: Relational Generalization

## Open Question (cantor-diagonalization-oq-04-oq-01-oq-03)
"The setoid generalization (parent oq-04-oq-01) replaces strict Type equality
with an equivalence relation, motivated as the step toward a CCC/topos version
where equality becomes coherence. Exactly *which* properties of that relation
does Lawvere's diagonal argument actually use?"

## Answer
**None.** Inspecting the setoid proof shows the diagonal argument uses only the
retraction equation — it never invokes reflexivity, symmetry, or transitivity of
the coherence relation. Lawvere's fixed-point theorem therefore holds for an
**arbitrary binary relation** `r`, with the fixed point delivered in the
retraction orientation `r p (f p)`:

  If `Y` codes its endomorphisms up to `r` (i.e. `decode (encode g) y  r  g y`),
  then every `f : Y → Y` has a point `p` with `r p (f p)`.

Symmetry of `r` is needed *only* to flip the conclusion to the setoid-style
orientation `r (f p) p`; reflexivity and transitivity are never used at all.

This strictly generalizes the parent results:
- **Type version** (oq-04): exact equality `decode (encode g) = g`.
- **Setoid version** (oq-04-oq-01): an equivalence relation `≈`.
- **Relational version** (this file): *any* relation — recovers the setoid
  version as the symmetric special case, and additionally applies to
  **tolerance relations** (reflexive + symmetric, non-transitive) and to
  **strict orders** (irreflexive, non-symmetric), neither of which is a setoid.

Isolating "arbitrary relation" as the true hypothesis clarifies the obstruction
to the genuine CCC version: the categorical content is a coherence *relation* on
global points, with no equivalence structure required of it.

## Key Results
1. `lawvere_fixpoint_rel`       — fixed point `r p (f p)` for ANY relation `r`
2. `lawvere_fixpoint_rel_symm`  — symmetric `r` gives `r (f p) p`
3. `no_coding_rel_of_no_prefixpoint` — contrapositive for arbitrary `r`
4. `lawvere_fixpoint_setoid`    — recovers the setoid theorem (symmetric case)
5. `nat_cannot_code_endos_tol`  — tolerance example (non-transitive, not a setoid)
6. `nat_cannot_code_endos_lt`   — strict-order example (non-symmetric, not a setoid)

## Proof Technique
Identical diagonal to the parent: `g y = f (decode y y)`, `y₀ = encode g`,
`p = decode y₀ y₀`. The retraction equation evaluated at `(g, y₀)` is *exactly*
`r p (f p)`; no relation axioms are consumed.

References:
- F.W. Lawvere, "Diagonal arguments and cartesian closed categories" (1969)
- Parent: CantorDiagonalizationOQ04OQ01 (Setoid generalization)
-/

namespace CantorDiagonalizationOQ04OQ01OQ03

-- ============================================================
-- Part I: Coded Endomorphisms up to an Arbitrary Relation
-- ============================================================

/-- `Y` **codes its endomorphisms up to the relation `r`** when there exist
    encode/decode functions whose retraction holds only up to `r`:
    `r (decode (encode g) y) (g y)` for all `g` and `y`.

    No properties (reflexivity/symmetry/transitivity) are assumed of `r`. -/
structure CodesEndomorphismsRel (Y : Type*) (r : Y → Y → Prop) where
  encode : (Y → Y) → Y
  decode : Y → (Y → Y)
  retract : ∀ (g : Y → Y) (y : Y), r (decode (encode g) y) (g y)

-- ============================================================
-- Part II: Main Theorem — No Hypotheses on `r`
-- ============================================================

/-- **Lawvere Fixed-Point Theorem (Relational Version)**.

    If `Y` codes its endomorphisms up to *any* relation `r`, then every
    `f : Y → Y` has a point `p` with `r p (f p)`.

    The diagonal `g y = f (decode y y)`, `y₀ = encode g`, `p = decode y₀ y₀`
    makes the retraction equation `r (decode (encode g) y₀) (g y₀)` literally
    `r p (f p)`. No relation axioms are used. -/
theorem lawvere_fixpoint_rel {Y : Type*} {r : Y → Y → Prop}
    (c : CodesEndomorphismsRel Y r) (f : Y → Y) :
    ∃ p : Y, r p (f p) := by
  let g : Y → Y := fun y => f (c.decode y y)
  let y₀ := c.encode g
  exact ⟨c.decode y₀ y₀, c.retract g y₀⟩

/-- With symmetric `r`, the fixed point can be stated in the parent's
    orientation `r (f p) p`. Symmetry is the *only* property ever needed,
    and only to flip the conclusion. -/
theorem lawvere_fixpoint_rel_symm {Y : Type*} {r : Y → Y → Prop}
    (hsymm : Symmetric r) (c : CodesEndomorphismsRel Y r) (f : Y → Y) :
    ∃ p : Y, r (f p) p := by
  obtain ⟨p, hp⟩ := lawvere_fixpoint_rel c f
  exact ⟨p, hsymm hp⟩

-- ============================================================
-- Part III: Contrapositive
-- ============================================================

/-- If `f` has no point `p` with `r p (f p)` (no "`r`-prefixed point"), then `Y`
    cannot code its endomorphisms up to `r`. Holds for arbitrary `r`. -/
theorem no_coding_rel_of_no_prefixpoint {Y : Type*} {r : Y → Y → Prop}
    (f : Y → Y) (hf : ∀ y : Y, ¬ r y (f y)) :
    CodesEndomorphismsRel Y r → False := fun c =>
  let ⟨p, hp⟩ := lawvere_fixpoint_rel c f; hf p hp

-- ============================================================
-- Part IV: Recovering the Setoid Version
-- ============================================================

/-- The setoid generalization (parent oq-04-oq-01) is the symmetric special
    case: an equivalence relation is in particular symmetric, so coding up to a
    setoid relation `s.r` yields a setoid fixed point `s.r (f p) p`. Reflexivity
    and transitivity of the setoid play no role. -/
theorem lawvere_fixpoint_setoid {Y : Type*} (s : Setoid Y)
    (c : CodesEndomorphismsRel Y s.r) (f : Y → Y) :
    ∃ p : Y, s.r (f p) p := by
  have hsymm : Symmetric s.r := by intro a b h; exact s.iseqv.symm h
  exact lawvere_fixpoint_rel_symm hsymm c f

-- ============================================================
-- Part V: Tolerance Relation — Reflexive + Symmetric, NOT Transitive
-- ============================================================

/-- The tolerance "differ by at most one" on `ℕ`: `tol a b ↔ |a - b| ≤ 1`,
    written without subtraction as `a ≤ b + 1 ∧ b ≤ a + 1`.

    This is reflexive and symmetric but **not transitive** (`tol 0 1`, `tol 1 2`,
    yet `¬ tol 0 2`), so it is genuinely **not a setoid** — outside the reach of
    the parent's framework, but squarely inside this relational one. -/
def tol (a b : ℕ) : Prop := a ≤ b + 1 ∧ b ≤ a + 1

theorem tol_refl (a : ℕ) : tol a a := ⟨by omega, by omega⟩

theorem tol_symm : Symmetric tol := by
  intro a b h; obtain ⟨h1, h2⟩ := h; exact ⟨h2, h1⟩

/-- `tol` is not transitive: `tol 0 1` and `tol 1 2` hold but `tol 0 2` fails. -/
theorem tol_not_transitive : ¬ Transitive tol := by
  intro htrans
  have h01 : tol 0 1 := ⟨by omega, by omega⟩
  have h12 : tol 1 2 := ⟨by omega, by omega⟩
  obtain ⟨-, h2⟩ := htrans h01 h12
  omega

/-- The shift `n ↦ n + 2` has no tolerance prefixed point: `tol n (n+2)` would
    force `n + 2 ≤ n + 1`. -/
theorem add_two_no_tol_prefixpoint : ∀ n : ℕ, ¬ tol n (n + 2) := by
  intro n h; obtain ⟨-, h2⟩ := h; omega

/-- **ℕ cannot code its endomorphisms up to the (non-transitive) tolerance
    `tol`.** A genuinely new instance: `tol` is not an equivalence relation, so
    this is not reachable from the parent setoid theorem. -/
theorem nat_cannot_code_endos_tol : CodesEndomorphismsRel ℕ tol → False :=
  no_coding_rel_of_no_prefixpoint (fun n => n + 2) add_two_no_tol_prefixpoint

-- ============================================================
-- Part VI: Strict Order — Irreflexive + Non-Symmetric
-- ============================================================

/-- **ℕ cannot code its endomorphisms up to strict order `<`.** The identity has
    no point with `p < id p`, since `<` is irreflexive. This relation is neither
    reflexive nor symmetric, illustrating that the *orientation* `r p (f p)` is
    the only thing that matters — no relation axioms whatsoever. -/
theorem nat_cannot_code_endos_lt : CodesEndomorphismsRel ℕ (· < ·) → False :=
  no_coding_rel_of_no_prefixpoint id (fun n => lt_irrefl n)

end CantorDiagonalizationOQ04OQ01OQ03
