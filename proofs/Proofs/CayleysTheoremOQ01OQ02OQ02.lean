/-
Proof: The inner automorphism group is normal in the automorphism group, and the
outer automorphism group as the quotient — the short exact sequence

        1 ⟶ Inn(G) ⟶ Aut(G) ⟶ Out(G) ⟶ 1.

Research: cayleys-theorem-oq-01-oq-02-oq-02

Open question (from the parent `cayleys-theorem-oq-01-oq-02`, second open
question): "Prove the outer automorphism exact sequence at the formalized level:
1 → Inn(G) → Aut(G) → Out(G) → 1, building on G/Z(G) ≅ Inn(G) established there to
define Out(G) = Aut(G)/Inn(G)."

The parent established the conjugation representation `C : G →* Equiv.Perm G`, its
kernel `Z(G)`, and `G/Z(G) ≃* (conjRep G).range`.  That image lived inside the
symmetric group `Sym(G)`.  Here we move into the *automorphism* group `MulAut G`,
where the same image is the classical **inner automorphism group** `Inn(G)`, and
we complete the structural picture:

  1.  **Covariance of conjugation.**  For any automorphism `φ` and any `g`,
        `φ · conj g · φ⁻¹ = conj (φ g)`     (in `MulAut G`).
      Conjugating an inner automorphism by *any* automorphism is again inner.

  2.  **`Inn(G) ◁ Aut(G)`.**  Consequently the inner automorphism group
      `Inn G := (MulAut.conj).range` is a *normal* subgroup of `MulAut G`.

  3.  **`Out(G) := Aut(G) / Inn(G)`** is therefore a well-defined group, the
      **outer automorphism group**.

  4.  **Exactness of `1 → Inn(G) → Aut(G) → Out(G) → 1`.**  The inclusion
      `Inn(G).subtype` is injective, the quotient map `Aut(G) → Out(G)` is
      surjective, and the image of the inclusion equals the kernel of the
      quotient map:
        `(Inn G).subtype.range = (QuotientGroup.mk' (Inn G)).ker`.

  5.  **`G/Z(G) ≃* Inn(G)`** realised inside `MulAut G` (the parent's isomorphism
      transported from `Sym(G)` to `MulAut G`), via `ker (MulAut.conj) = Z(G)`.

  6.  **Order formula** for finite `G`:
        `|Aut(G)| = |Out(G)| · |Inn(G)| = |Out(G)| · |G/Z(G)|`.

Mathlib supplies the primitives (`MulAut.conj`, `QuotientGroup`,
`Subgroup.center`); the content here is proving the covariance lemma, hence the
normality that turns `Out(G)` into a group, and assembling the exact sequence.
-/

import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Tactic

namespace CayleyOuter

variable {G : Type*} [Group G]

/-! ### The inner automorphism group -/

/-- The **inner automorphism group** `Inn(G) ≤ Aut(G)`, defined as the range of
the inner-automorphism homomorphism `MulAut.conj : G →* MulAut G`.  Its elements
are exactly the automorphisms `x ↦ g * x * g⁻¹`. -/
def Inn (G : Type*) [Group G] : Subgroup (MulAut G) := (MulAut.conj (G := G)).range

@[simp] theorem mem_Inn_iff {φ : MulAut G} :
    φ ∈ Inn G ↔ ∃ g : G, MulAut.conj g = φ := Iff.rfl

/-- **Covariance of conjugation.**  Conjugating the inner automorphism `conj g`
by an arbitrary automorphism `φ` yields the inner automorphism `conj (φ g)`.
This is the engine behind the normality of `Inn(G)`: the inner automorphisms are
permuted among themselves by every automorphism. -/
theorem conj_mulAut_conj (φ : MulAut G) (g : G) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  simp only [MulAut.mul_apply, MulAut.inv_apply, MulAut.conj_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

/-- **`Inn(G)` is normal in `Aut(G)`.**  Immediate from covariance: any conjugate
of an inner automorphism is again inner. -/
instance : (Inn G).Normal where
  conj_mem := by
    rintro _ ⟨g, rfl⟩ φ
    exact ⟨φ g, (conj_mulAut_conj φ g).symm⟩

/-! ### The outer automorphism group -/

/-- The **outer automorphism group** `Out(G) := Aut(G) / Inn(G)`.  Well-defined as
a group precisely because `Inn(G)` is normal (the instance above). -/
def Out (G : Type*) [Group G] : Type _ := MulAut G ⧸ Inn G

noncomputable instance : Group (Out G) := QuotientGroup.Quotient.group (Inn G)

/-- The canonical surjection `Aut(G) → Out(G)`. -/
def outMk (G : Type*) [Group G] : MulAut G →* Out G := QuotientGroup.mk' (Inn G)

/-! ### Exactness of `1 → Inn(G) → Aut(G) → Out(G) → 1` -/

/-- **Injectivity at `Inn(G)`.**  The inclusion `Inn(G) ↪ Aut(G)` is injective —
the left end of the exact sequence. -/
theorem inn_subtype_injective : Function.Injective (Inn G).subtype :=
  (Inn G).subtype_injective

/-- **Surjectivity at `Out(G)`.**  The quotient map `Aut(G) → Out(G)` is
surjective — the right end of the exact sequence. -/
theorem outMk_surjective : Function.Surjective (outMk G) :=
  QuotientGroup.mk'_surjective (Inn G)

/-- **Exactness in the middle.**  The image of the inclusion `Inn(G) ↪ Aut(G)`
equals the kernel of the quotient map `Aut(G) → Out(G)`:
  `range (Inn(G).subtype) = ker (Aut(G) → Out(G))`.
Together with injectivity and surjectivity this is the short exact sequence
`1 → Inn(G) → Aut(G) → Out(G) → 1`. -/
theorem range_inn_subtype_eq_ker_outMk :
    (Inn G).subtype.range = (outMk G).ker := by
  rw [Subgroup.range_subtype, outMk, QuotientGroup.ker_mk']

/-! ### Identification of `Inn(G)` with `G / Z(G)` -/

/-- **The kernel of the inner-automorphism homomorphism is the centre.**  An
element `g` induces the identity inner automorphism exactly when it commutes with
everything.  (This is the `MulAut`-level twin of the parent's `ker_conjRep`.) -/
theorem ker_mulAutConj : (MulAut.conj (G := G)).ker = Subgroup.center G := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff, MulEquiv.ext_iff]
  constructor
  · intro h x
    have hx := h x
    rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul] at hx
    exact hx.symm
  · intro h x
    rw [MulAut.conj_apply, MulAut.one_apply, mul_inv_eq_iff_eq_mul]
    exact (h x).symm

/-- **First isomorphism theorem for the inner automorphism group:**
`G ⧸ Z(G) ≃* Inn(G)`.  Realises the parent's `G/Z(G) ≅ Inn(G)` directly as an
isomorphism onto the automorphism subgroup `Inn(G) ≤ Aut(G)`. -/
noncomputable def quotientCenterEquivInn :
    G ⧸ Subgroup.center G ≃* Inn G :=
  (QuotientGroup.quotientMulEquivOfEq ker_mulAutConj.symm).trans
    (QuotientGroup.quotientKerEquivRange (MulAut.conj (G := G)))

/-! ### Order formula for finite groups -/

/-- **Order formula.**  For a finite group `G`,
  `|Aut(G)| = |Out(G)| · |Inn(G)|`,
the Lagrange factorisation of the automorphism group along `Inn(G) ◁ Aut(G)`. -/
theorem card_mulAut_eq_card_out_mul_card_inn [Finite G] :
    Nat.card (MulAut G) = Nat.card (Out G) * Nat.card (Inn G) :=
  Subgroup.card_eq_card_quotient_mul_card_subgroup (Inn G)

/-- **Order formula, refined.**  Combining with `G/Z(G) ≃* Inn(G)`:
  `|Aut(G)| = |Out(G)| · |G / Z(G)|`. -/
theorem card_mulAut_eq_card_out_mul_card_quotient_center [Finite G] :
    Nat.card (MulAut G) = Nat.card (Out G) * Nat.card (G ⧸ Subgroup.center G) := by
  rw [card_mulAut_eq_card_out_mul_card_inn, Nat.card_congr quotientCenterEquivInn.toEquiv]

end CayleyOuter
