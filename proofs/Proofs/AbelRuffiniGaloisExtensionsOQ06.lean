/-
  Primitive Solvable Permutation Groups of Prime Degree (OQ-06)

  Galois (1832): for prime degree `p`, the primitive solvable permutation
  groups of degree `p` are precisely the affine groups
  `AGL(1, p) = ℤ/pℤ ⋊ (ℤ/pℤ)ˣ` of order `p(p-1)`.

  This file (S2) carves out the *forward direction* infrastructure:

  1. `AGL1Z p` — the concrete affine group as a structure on
     `(ZMod p) × (ZMod p)ˣ` with the semidirect product law
     `(a, u) * (b, v) = (a + u·b, u·v)`.
  2. `Group (AGL1Z p)` — manual group instance (associativity, identity,
     inverses).
  3. `AGL1Z.card_eq` — the order calculation `Nat.card (AGL1Z p) = p * (p - 1)`
     via a bijection with the cartesian product and the well-known
     `Fintype.card (ZMod p)ˣ = p - 1` for prime `p`.

  ## Deferred (S3+)

  - `IsSolvable (AGL1Z p)` (the abelian-by-abelian extension is solvable
    of derived length ≤ 2).
  - The natural permutation action `AGL1Z p →* Equiv.Perm (ZMod p)`
    given by `(a, u) · x = a + u · x` and its faithfulness.
  - Primitivity of the action (S4).
  - Galois direction: every primitive solvable subgroup of `S_p` embeds
    into `AGL(1, p)` (S5+).

  ## Mathlib dependencies (verified at v4.26.0)

  - `ZMod.card` : `Fintype.card (ZMod n) = n` for `n > 0`.
  - `ZMod.card_units_eq_totient` + `Nat.totient_prime` : the units of
    `ZMod p` for prime `p` form a group of order `p - 1`.

  ## Honest contribution

  Galois proved this in 1832; the result is classical. The Lean contribution
  is a concrete, gallery-ready formalization of the affine group structure
  that future formalization work on degree-`p` Galois groups and Frobenius
  groups can reuse.
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.Algebra.Group.Action.End
import Proofs.AbelRuffiniGaloisExtensions

namespace AbelRuffiniGaloisExtensionsOQ06

/--
  `AGL1Z p` — the affine group `AGL(1, ℤ/pℤ)` packaged as a structure with a
  translation part `trans : ZMod p` and a (multiplicative) scale part
  `scale : (ZMod p)ˣ`. The group law is the semidirect product
  `(a, u) * (b, v) = (a + u·b, u·v)`.
-/
@[ext]
structure AGL1Z (p : ℕ) [Fact p.Prime] where
  trans : ZMod p
  scale : (ZMod p)ˣ

namespace AGL1Z

variable {p : ℕ} [hp : Fact p.Prime]

/-- The semidirect product multiplication. -/
instance : Mul (AGL1Z p) where
  mul g h := ⟨g.trans + (g.scale : ZMod p) * h.trans, g.scale * h.scale⟩

/-- The identity element is `(0, 1)`. -/
instance : One (AGL1Z p) where
  one := ⟨0, 1⟩

/--
  The inverse of `(a, u)` is `(-u⁻¹ · a, u⁻¹)`. Verification of the group
  axioms below uses the standard identities `(u⁻¹)·u = 1` and `u·(u⁻¹) = 1`
  in `(ZMod p)ˣ`.
-/
instance : Inv (AGL1Z p) where
  inv g := ⟨- ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * g.trans, g.scale⁻¹⟩

lemma mul_trans (g h : AGL1Z p) :
    (g * h).trans = g.trans + (g.scale : ZMod p) * h.trans := rfl

lemma mul_scale (g h : AGL1Z p) :
    (g * h).scale = g.scale * h.scale := rfl

lemma one_trans : (1 : AGL1Z p).trans = 0 := rfl

lemma one_scale : (1 : AGL1Z p).scale = 1 := rfl

lemma inv_trans (g : AGL1Z p) :
    g⁻¹.trans = - ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * g.trans := rfl

lemma inv_scale (g : AGL1Z p) : g⁻¹.scale = g.scale⁻¹ := rfl

instance : Group (AGL1Z p) where
  mul_assoc g h k := by
    apply AGL1Z.ext
    · -- trans: ((g*h)*k).trans = (g*(h*k)).trans
      show (g.trans + (g.scale : ZMod p) * h.trans)
          + (((g.scale * h.scale : (ZMod p)ˣ) : ZMod p)) * k.trans
        = g.trans + (g.scale : ZMod p) * (h.trans + (h.scale : ZMod p) * k.trans)
      push_cast
      ring
    · -- scale: ((g*h)*k).scale = (g*(h*k)).scale
      show g.scale * h.scale * k.scale = g.scale * (h.scale * k.scale)
      exact mul_assoc _ _ _
  one_mul g := by
    apply AGL1Z.ext
    · show (0 : ZMod p) + ((1 : (ZMod p)ˣ) : ZMod p) * g.trans = g.trans
      push_cast; ring
    · show (1 : (ZMod p)ˣ) * g.scale = g.scale
      exact one_mul _
  mul_one g := by
    apply AGL1Z.ext
    · show g.trans + (g.scale : ZMod p) * (0 : ZMod p) = g.trans
      ring
    · show g.scale * 1 = g.scale
      exact mul_one _
  inv_mul_cancel g := by
    apply AGL1Z.ext
    · -- (-u⁻¹·a) + u⁻¹·a = 0, where u = g.scale, a = g.trans
      show - ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * g.trans
          + ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * g.trans = 0
      ring
    · -- u⁻¹ * u = 1 in (ZMod p)ˣ
      show g.scale⁻¹ * g.scale = 1
      exact inv_mul_cancel _

/-- The natural bijection `AGL1Z p ≃ ZMod p × (ZMod p)ˣ` (as sets). -/
def equivProd : AGL1Z p ≃ ZMod p × (ZMod p)ˣ where
  toFun g := (g.trans, g.scale)
  invFun ab := ⟨ab.1, ab.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance : Fintype (AGL1Z p) := Fintype.ofEquiv _ equivProd.symm

/--
  **Order of `AGL(1, p)`.** For every prime `p`, the affine group
  `AGL(1, ℤ/pℤ)` has order `p · (p - 1)`.

  Proof: bijection to `ZMod p × (ZMod p)ˣ`, then `ZMod.card` and
  `ZMod.card_units_eq_totient` combined with `Nat.totient_prime`.
-/
theorem card_eq : Fintype.card (AGL1Z p) = p * (p - 1) := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, ZMod.card,
    ZMod.card_units_eq_totient, Nat.totient_prime hp.out]

/--
  **Order via `Nat.card`.** A `Nat.card` restatement of `card_eq` for
  uniform downstream use.
-/
theorem nat_card_eq : Nat.card (AGL1Z p) = p * (p - 1) := by
  rw [Nat.card_eq_fintype_card, card_eq]

end AGL1Z

/-!
  ## S3 — Solvability via short exact sequence

  Both ends `(Multiplicative (ZMod p), +)` and `(ZMod p)ˣ` are abelian and
  hence solvable (`CommGroup.isSolvable`); the middle term `AGL1Z p` is then
  solvable via `solvable_of_ker_le_range` applied to the translation
  inclusion and the scaling projection.
-/

namespace AGL1Z

variable {p : ℕ} [hp : Fact p.Prime]

/--
  The "scale" projection `AGL1Z p →* (ZMod p)ˣ`. The translation kernel of
  this map is the abelian normal subgroup of pure translations.
-/
def scaleHom (p : ℕ) [Fact p.Prime] : AGL1Z p →* (ZMod p)ˣ where
  toFun g := g.scale
  map_one' := AGL1Z.one_scale
  map_mul' g h := AGL1Z.mul_scale g h

/--
  The "translation" inclusion `Multiplicative (ZMod p) →* AGL1Z p`.
  Sends the `Multiplicative`-encoded `a` to the pure translation `(a, 1)`.
  `Multiplicative` is the standard way to view the additive group `ZMod p`
  as a multiplicative group so that we can build a `MonoidHom` into the
  multiplicative `AGL1Z p`.
-/
def transHom (p : ℕ) [Fact p.Prime] :
    Multiplicative (ZMod p) →* AGL1Z p where
  toFun a := ⟨Multiplicative.toAdd a, 1⟩
  map_one' := by
    apply AGL1Z.ext
    · rfl
    · rfl
  map_mul' a b := by
    apply AGL1Z.ext
    · -- `(a * b).toAdd = a.toAdd + b.toAdd` via `Multiplicative.toAdd_mul`
      show (Multiplicative.toAdd (a * b) : ZMod p)
          = Multiplicative.toAdd a + ((1 : (ZMod p)ˣ) : ZMod p)
              * Multiplicative.toAdd b
      rw [toAdd_mul]
      push_cast
      ring
    · -- 1 = 1 * 1 in `(ZMod p)ˣ`
      show (1 : (ZMod p)ˣ) = 1 * 1
      simp

/--
  The kernel of the scale projection is contained in the range of the
  translation inclusion: every `(a, u)` with `u = 1` is the image of
  `Multiplicative.ofAdd a` under `transHom`.
-/
theorem ker_scaleHom_le_range_transHom (p : ℕ) [Fact p.Prime] :
    (scaleHom p).ker ≤ (transHom p).range := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  -- `hg : g.scale = 1`. Witness: `Multiplicative.ofAdd g.trans`.
  refine ⟨Multiplicative.ofAdd g.trans, ?_⟩
  apply AGL1Z.ext
  · rfl
  · -- Goal becomes `1 = g.scale`; close with `hg.symm`.
    exact hg.symm

end AGL1Z

variable (p : ℕ) [Fact p.Prime]

/--
  **Solvability of `AGL(1, p)`.** The short exact sequence
  `1 → Multiplicative (ZMod p) → AGL1Z p → (ZMod p)ˣ → 1` exhibits
  `AGL1Z p` as an abelian-by-abelian extension. Both ends are solvable
  (via `CommGroup.isSolvable`), so `solvable_of_ker_le_range` gives
  solvability of `AGL1Z p` with derived length at most 2.
-/
theorem AGL1Z_isSolvable : IsSolvable (AGL1Z p) :=
  solvable_of_ker_le_range (AGL1Z.transHom p) (AGL1Z.scaleHom p)
    (AGL1Z.ker_scaleHom_le_range_transHom p)

/-!
  ## S3 — Faithful permutation action

  The natural affine action `(a, u) · x = a + u · x` packages as a
  monoid homomorphism `AGL1Z p →* Equiv.Perm (ZMod p)`. We verify
  injectivity by evaluating at `x = 0` (forces `g.trans = 0`) and `x = 1`
  (forces `g.scale = 1`).
-/

namespace AGL1Z

variable {p : ℕ} [hp : Fact p.Prime]

/--
  The action of `g = ⟨a, u⟩` on `ZMod p` packaged as an `Equiv.Perm`.
  Forward direction `x ↦ a + u·x`; inverse `y ↦ u⁻¹·(y - a)`.
-/
def toPermEquiv (g : AGL1Z p) : Equiv.Perm (ZMod p) where
  toFun x := g.trans + (g.scale : ZMod p) * x
  invFun y := ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * (y - g.trans)
  left_inv := by
    intro x
    show ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p)
        * ((g.trans + (g.scale : ZMod p) * x) - g.trans) = x
    have hu : ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p)
        * ((g.scale : ZMod p)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel]
      rfl
    -- Distribute and cancel using `hu`.
    have : ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p)
        * ((g.trans + (g.scale : ZMod p) * x) - g.trans)
        = ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * (g.scale : ZMod p) * x := by
      ring
    rw [this, hu, one_mul]
  right_inv := by
    intro y
    show g.trans + (g.scale : ZMod p)
          * (((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * (y - g.trans)) = y
    have hu : ((g.scale : ZMod p))
        * ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel]
      rfl
    have : g.trans + (g.scale : ZMod p)
            * (((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * (y - g.trans))
        = g.trans + (g.scale : ZMod p)
            * ((g.scale⁻¹ : (ZMod p)ˣ) : ZMod p) * (y - g.trans) := by
      ring
    rw [this, hu, one_mul]
    ring

/--
  The action packaged as a `MonoidHom AGL1Z p →* Equiv.Perm (ZMod p)`.
  Multiplicativity follows from the semidirect product law
  `(g * h).trans = g.trans + g.scale · h.trans` and
  `(g * h).scale = g.scale · h.scale`.
-/
def toPerm (p : ℕ) [Fact p.Prime] :
    AGL1Z p →* Equiv.Perm (ZMod p) where
  toFun := toPermEquiv
  map_one' := by
    apply Equiv.ext
    intro x
    show (1 : AGL1Z p).trans + ((1 : AGL1Z p).scale : ZMod p) * x = x
    rw [AGL1Z.one_trans, AGL1Z.one_scale]
    push_cast
    ring
  map_mul' g h := by
    apply Equiv.ext
    intro x
    show (g * h).trans + ((g * h).scale : ZMod p) * x
        = g.trans + (g.scale : ZMod p)
            * (h.trans + (h.scale : ZMod p) * x)
    rw [AGL1Z.mul_trans, AGL1Z.mul_scale]
    push_cast
    ring

/-- The action is faithful: only the identity element acts trivially. -/
theorem toPerm_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (toPerm p) := by
  intro g₁ g₂ hg
  apply AGL1Z.ext
  · -- Evaluate both sides at `x = 0`.
    have h0 := Equiv.ext_iff.mp hg 0
    -- `toPermEquiv gᵢ 0 = gᵢ.trans + gᵢ.scale * 0 = gᵢ.trans`.
    have : g₁.trans + (g₁.scale : ZMod p) * 0
        = g₂.trans + (g₂.scale : ZMod p) * 0 := h0
    simpa using this
  · -- From `x = 0` get `g₁.trans = g₂.trans`; from `x = 1` get scale-equality.
    have h0 := Equiv.ext_iff.mp hg 0
    have h1 := Equiv.ext_iff.mp hg 1
    have htrans : g₁.trans = g₂.trans := by
      have : g₁.trans + (g₁.scale : ZMod p) * 0
          = g₂.trans + (g₂.scale : ZMod p) * 0 := h0
      simpa using this
    have heq1 : g₁.trans + (g₁.scale : ZMod p) * 1
        = g₂.trans + (g₂.scale : ZMod p) * 1 := h1
    have hscale_val : (g₁.scale : ZMod p) = (g₂.scale : ZMod p) := by
      have : g₁.trans + (g₁.scale : ZMod p)
          = g₂.trans + (g₂.scale : ZMod p) := by simpa using heq1
      rw [htrans] at this
      exact add_left_cancel this
    -- Lift `(g₁.scale : ZMod p) = (g₂.scale : ZMod p)` to `g₁.scale = g₂.scale`.
    exact Units.ext hscale_val

end AGL1Z

/--
  **Faithful action of `AGL(1, p)` on `ZMod p`.** The map
  `toPerm : AGL1Z p →* Equiv.Perm (ZMod p)` sending `(a, u)` to the
  affine permutation `x ↦ a + u·x` is an injective group homomorphism.
-/
theorem AGL1Z_faithful_action :
    ∃ φ : AGL1Z p →* Equiv.Perm (ZMod p), Function.Injective φ :=
  ⟨AGL1Z.toPerm p, AGL1Z.toPerm_injective p⟩

/-! ### Primitivity (S4)

  The action `AGL1Z p ↷ ZMod p` is *primitive*: pretransitive (the
  translation `(x, 1)` sends `0 ↦ x`) with no non-trivial blocks. The
  block-triviality is automatic: `Nat.card (ZMod p) = p` is prime, so
  any pretransitive action on it is preprimitive
  (`MulAction.IsPreprimitive.of_prime_card`).

  Recipe verified line-by-line against Mathlib v4.26.0 in the S4-α PREP
  (`sessions/2026-05-13-s04-alpha-prep-action-wiring-bearer-audit-and-errata.md`).
-/

section Primitivity

variable {p : ℕ} [hp : Fact p.Prime]

/-- Wire the action `AGL1Z p ↷ ZMod p` via `MulAction.compHom` along the
    permutation hom `AGL1Z.toPerm`. -/
instance AGL1Z.mulAction : MulAction (AGL1Z p) (ZMod p) :=
  MulAction.compHom (ZMod p) (AGL1Z.toPerm p)

/-- Pretransitivity: the translation `(x, 1) ∈ AGL1Z p` sends `0 ↦ x`.

    The chain `(g : AGL1Z p) • (x : ZMod p) = (toPerm g) • x = (toPerm g) x`
    is two `rfl` steps (`MulAction.compHom_smul_def` then
    `Equiv.Perm.smul_def`), so the goal reduces to the affine identity
    `x + (1 : (ZMod p)ˣ) * 0 = x`, closed by `simp`. -/
theorem AGL1Z_isPretransitive :
    MulAction.IsPretransitive (AGL1Z p) (ZMod p) := by
  rw [MulAction.isPretransitive_iff_base (0 : ZMod p)]
  intro x
  refine ⟨⟨x, 1⟩, ?_⟩
  show x + ((1 : (ZMod p)ˣ) : ZMod p) * 0 = x
  simp

/-- Primitivity: `Nat.card (ZMod p) = p` is prime by hypothesis, so any
    pretransitive action on `ZMod p` is preprimitive
    (`MulAction.IsPreprimitive.of_prime_card`). -/
instance AGL1Z.isPreprimitive :
    MulAction.IsPreprimitive (AGL1Z p) (ZMod p) := by
  haveI : MulAction.IsPretransitive (AGL1Z p) (ZMod p) :=
    AGL1Z_isPretransitive
  apply MulAction.IsPreprimitive.of_prime_card
  rw [Nat.card_eq_fintype_card, ZMod.card]
  exact hp.out

end Primitivity

/-! ### S5 Lite — Forward-direction conjunctive packaging

  Bundles the three forward-direction facts on `AGL1Z p`:
  solvability (S3), faithfulness of the permutation action (S3),
  and primitivity of that action (S4). This is the Lite layer of
  the S5 PREP packaging (PR #18456); the Full layer (existential
  subgroup of `Equiv.Perm (ZMod p)` form) is deferred.

  Note: `AGL1Z_isSolvable` is declared as a `theorem`, not an
  `instance`, so `inferInstance` does not find it — we name it
  explicitly. The `AGL1Z.isPreprimitive` instance (S4) is found
  by `inferInstance`.
-/

section ForwardPackaging

variable (p : ℕ) [Fact p.Prime]

/-- **Forward direction (Lite layer).** `AGL(1, p)` is solvable, acts
    faithfully on `ZMod p`, and that action is preprimitive. Bundles
    `AGL1Z_isSolvable`, `AGL1Z.toPerm_injective`, and the
    `AGL1Z.isPreprimitive` instance into a single statement.

    This is the conjunctive ("Lite") form of the S5 PREP forward
    packaging; the subgroup-existential ("Full") form
    `AGL1Z_forward_witness` is in the next section. -/
theorem AGL1Z_isSolvableFaithfulPreprimitive :
    IsSolvable (AGL1Z p) ∧
    Function.Injective (AGL1Z.toPerm p) ∧
    MulAction.IsPreprimitive (AGL1Z p) (ZMod p) :=
  ⟨AGL1Z_isSolvable p, AGL1Z.toPerm_injective p, inferInstance⟩

end ForwardPackaging

/-! ### S5b Full — Forward-direction subgroup-of-S_p packaging

  Promotes the Lite layer (the conjunctive statement
  `IsSolvable ∧ Injective toPerm ∧ IsPreprimitive`) to the
  mathematically-faithful subgroup form: there exists a subgroup `H`
  of `Equiv.Perm (ZMod p)` (namely the image of `AGL1Z p` under its
  faithful permutation action) that is solvable, acts preprimitively
  on `ZMod p`, and has order `p · (p - 1)`.

  Mathlib bearers (verified at v4.26.0):

  - `solvable_of_surjective` (`Mathlib.GroupTheory.Solvable:147`)
    transfers solvability across a surjective `MonoidHom`.
  - `MonoidHom.rangeRestrict_surjective`
    (`Mathlib.Algebra.Group.Subgroup.Ker:114`) supplies the
    surjection `(toPerm p).rangeRestrict`.
  - `MonoidHom.ofInjective` (`Mathlib.Algebra.Group.Subgroup.Ker:188`)
    supplies the multiplicative isomorphism
    `AGL1Z p ≃* (AGL1Z.toPerm p).range` used in cardinality transfer.
  - `MulAction.IsPreprimitive.of_prime_card`
    (`Mathlib.GroupTheory.GroupAction.Primitive:320`) closes
    preprimitivity once `Nat.card (ZMod p) = p` is shown prime.
  - `MulAction.isPretransitive_iff_base`
    (`Mathlib.GroupTheory.GroupAction.Transitive:43`) reduces
    pretransitivity to "every `x` is reached from `0`".

  Design note: the range's pretransitivity is established directly
  (with the translation `(x, 1)` lifted via `rangeRestrict` as
  witness), rather than transferring along an equivariant map from
  the parent `AGL1Z p` action. This keeps the proof in the same
  definitional shape as the S4 ACT pretransitivity proof above and
  avoids the `MulActionHom` plumbing that the S5b PREP recipe used.
-/

section ForwardSubgroupPackaging

variable (p : ℕ) [hp : Fact p.Prime]

/-- Pretransitivity of the range action `(AGL1Z.toPerm p).range ↷ ZMod p`.

    Witness: `(x, 1) ∈ AGL1Z p` lifts via `(AGL1Z.toPerm p).rangeRestrict`
    to an element of the range whose underlying permutation
    `AGL1Z.toPerm p ⟨x, 1⟩ = toPermEquiv ⟨x, 1⟩` sends `0 ↦ x + 1 · 0 = x`. -/
theorem AGL1Z.range_isPretransitive :
    MulAction.IsPretransitive ((AGL1Z.toPerm p).range) (ZMod p) := by
  rw [MulAction.isPretransitive_iff_base (0 : ZMod p)]
  intro x
  refine ⟨(AGL1Z.toPerm p).rangeRestrict ⟨x, 1⟩, ?_⟩
  show x + ((1 : (ZMod p)ˣ) : ZMod p) * 0 = x
  simp

/-- Preprimitivity of the range action via `of_prime_card`, since
    `Nat.card (ZMod p) = p` is prime by hypothesis. -/
instance AGL1Z.range_isPreprimitive :
    MulAction.IsPreprimitive ((AGL1Z.toPerm p).range) (ZMod p) := by
  haveI : MulAction.IsPretransitive ((AGL1Z.toPerm p).range) (ZMod p) :=
    AGL1Z.range_isPretransitive p
  apply MulAction.IsPreprimitive.of_prime_card
  rw [Nat.card_eq_fintype_card, ZMod.card]
  exact hp.out

/-- **Forward direction (Full layer).** There exists a subgroup `H`
    of `Equiv.Perm (ZMod p)` that is solvable, acts preprimitively on
    `ZMod p`, and has order `p · (p - 1)`. The witness is
    `H := (AGL1Z.toPerm p).range`, the image of `AGL1Z p` under its
    faithful permutation action.

    This is the subgroup-of-S_p form of Galois's forward classification,
    complementing the conjunctive Lite layer
    `AGL1Z_isSolvableFaithfulPreprimitive`. -/
theorem AGL1Z_forward_witness :
    ∃ H : Subgroup (Equiv.Perm (ZMod p)),
      IsSolvable H ∧
      MulAction.IsPreprimitive H (ZMod p) ∧
      Nat.card H = p * (p - 1) := by
  refine ⟨(AGL1Z.toPerm p).range, ?_, ?_, ?_⟩
  · -- Solvability of the range: transfer from `IsSolvable (AGL1Z p)` via
    -- the surjective `rangeRestrict`.
    haveI : IsSolvable (AGL1Z p) := AGL1Z_isSolvable p
    exact solvable_of_surjective (AGL1Z.toPerm p).rangeRestrict_surjective
  · -- Preprimitivity: the instance proved above.
    exact AGL1Z.range_isPreprimitive p
  · -- Cardinality: transfer along `MonoidHom.ofInjective (toPerm_injective)`,
    -- then apply `AGL1Z.card_eq`.
    rw [Nat.card_eq_fintype_card,
      Fintype.card_congr
        (MonoidHom.ofInjective (AGL1Z.toPerm_injective p)).toEquiv.symm]
    exact AGL1Z.card_eq

end ForwardSubgroupPackaging

end AbelRuffiniGaloisExtensionsOQ06
