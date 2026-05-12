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
  ## Deferred (S3+ stubs)

  The following are placeholders for the next iteration. Each is replaced
  by a sorry-free proof in S3 (solvability + faithfulness) or S4 (primitivity).
-/

variable (p : ℕ) [Fact p.Prime]

/--
  **S3 stub.** The affine group is solvable: the short exact sequence
  `1 → ZMod p → AGL1Z p → (ZMod p)ˣ → 1` exhibits `AGL1Z p` as an
  abelian-by-abelian extension, so the derived length is at most 2.
-/
theorem AGL1Z_isSolvable : IsSolvable (AGL1Z p) := by
  sorry

/--
  **S3 stub.** The natural action `AGL1Z p → Equiv.Perm (ZMod p)`
  given by `(a, u) · x = a + u · x` is faithful (an injective group
  homomorphism). The proof requires defining the action map and verifying
  injectivity via `(a, u) ∈ ker ↔ a = 0 ∧ u = 1`.
-/
theorem AGL1Z_faithful_action :
    ∃ φ : AGL1Z p →* Equiv.Perm (ZMod p), Function.Injective φ := by
  sorry

end AbelRuffiniGaloisExtensionsOQ06
