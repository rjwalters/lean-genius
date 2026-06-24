/-
Proof: The conjugation representation and the unification of the three regular
representations of a group.
Research: cayleys-theorem-oq-01-oq-02

Open question (from the `cayleys-theorem-oq-01` chain, second open question):
  Cayley's theorem realises a group `G` as permutations of itself in three
  classical ways:

  * the **left-regular** representation   `L g : x ↦ g * x`   (the parent),
  * the **right-regular** representation  `R g : x ↦ x * g⁻¹`  (sibling
    `cayleys-theorem-oq-01-oq-01-oq-02-oq-02`),
  * the **conjugation** representation     `C g : x ↦ g * x * g⁻¹`.

  The left- and right-regular companions are already in the gallery; this file
  formalises the *conjugation* companion as a first-class member of the family
  and proves the three structural facts that distinguish it from the other two:

  1.  **Unification.**  Conjugation is literally "left-multiply, then undo a
      right-multiply":
        `conjRep G g = leftReg G g * rightReg G g`   (composition in `Sym G`).
  2.  **Kernel = centre.**  Unlike the faithful regular reps, `C` has a kernel,
      and it is exactly the centre:  `(conjRep G).ker = Subgroup.center G`.
  3.  **First isomorphism theorem.**  Hence
        `G ⧸ Z(G) ≃* (conjRep G).range`,
      identifying the image of `C` — the inner automorphism group `Inn(G)` —
      with `G / Z(G)`.

We work directly over `Equiv.Perm G` for an arbitrary group `G` (no finiteness
assumption), matching the sibling files.  `leftReg`/`rightReg` are re-declared
self-containedly (identical conventions to
`cayleys-theorem-oq-01-oq-01-oq-02-oq-02`) so the entry compiles without
depending on absent oleans.

Mathlib supplies every primitive (`MulAut.conj`, `Subgroup.center`,
`QuotientGroup.quotientKerEquivRange`); the content here is the *assembly* tying
conjugation to the two regular representations and isolating its kernel.
-/

import Mathlib.Algebra.Group.End
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic

namespace CayleyConjugation

variable {G : Type*} [Group G]

/-- The **left-regular representation** `g ↦ (x ↦ g * x)` as a group
homomorphism into the symmetric group on `G`.  It is a homomorphism on the nose
because `Equiv.mulLeft` turns multiplication into composition. -/
def leftReg (G : Type*) [Group G] : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_one' := Equiv.mulLeft_one
  map_mul' := Equiv.mulLeft_mul

/-- The **right-regular representation** `g ↦ (x ↦ x * g⁻¹)` as a group
homomorphism.  The inverse on the argument is forced: plain right multiplication
is an *anti*-homomorphism, so inverting the argument repairs the order. -/
def rightReg (G : Type*) [Group G] : G →* Equiv.Perm G where
  toFun g := Equiv.mulRight g⁻¹
  map_one' := by rw [inv_one, Equiv.mulRight_one]
  map_mul' a b := by rw [mul_inv_rev, Equiv.mulRight_mul]

@[simp] theorem leftReg_apply (g x : G) : leftReg G g x = g * x := rfl

@[simp] theorem rightReg_apply (g x : G) : rightReg G g x = x * g⁻¹ := rfl

/-- The **conjugation representation** `g ↦ (x ↦ g * x * g⁻¹)` as a group
homomorphism into `Equiv.Perm G`.  Built from Mathlib's inner-automorphism
homomorphism `MulAut.conj`; since `MulAut` composes with the same convention as
`Equiv.Perm`, conjugation is a genuine homomorphism (not an anti-homomorphism). -/
def conjRep (G : Type*) [Group G] : G →* Equiv.Perm G where
  toFun g := (MulAut.conj g).toEquiv
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp [MulAut.conj_apply, mul_assoc]

@[simp] theorem conjRep_apply (g x : G) : conjRep G g x = g * x * g⁻¹ := by
  simp [conjRep, MulAut.conj_apply]

/-- **Unification of the three regular representations.**  Conjugation by `g`
factors as left-multiplication by `g` followed by (undoing) right-multiplication
by `g`:  `C(g) = L(g) · R(g)` in `Sym G`.  This makes precise the folklore that
conjugation is the "commutator" of the two regular actions. -/
theorem conjRep_eq_leftReg_mul_rightReg (g : G) :
    conjRep G g = leftReg G g * rightReg G g := by
  ext x
  simp [Equiv.Perm.mul_apply, mul_assoc]

/-- **The kernel of the conjugation representation is the centre.**  An element
`g` acts trivially by conjugation exactly when it commutes with everything. -/
theorem ker_conjRep : (conjRep G).ker = Subgroup.center G := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_center_iff, Equiv.ext_iff]
  constructor
  · intro h x
    have hx := h x
    rw [conjRep_apply, Equiv.Perm.one_apply, mul_inv_eq_iff_eq_mul] at hx
    exact hx.symm
  · intro h x
    rw [conjRep_apply, Equiv.Perm.one_apply, mul_inv_eq_iff_eq_mul]
    exact (h x).symm

/-- **The conjugation representation is faithful iff the centre is trivial.**
The regular representations are always faithful; conjugation is faithful exactly
for centreless groups. -/
theorem conjRep_injective_iff :
    Function.Injective (conjRep G) ↔ Subgroup.center G = ⊥ := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_conjRep]

/-- **First isomorphism theorem for the conjugation representation:**
`G ⧸ Z(G) ≃* (conjRep G).range`.  The image of `C` is the inner automorphism
group `Inn(G)`, here exhibited as a subgroup of `Equiv.Perm G`, and it is
isomorphic to the quotient of `G` by its centre. -/
noncomputable def quotientCenterEquivInn :
    G ⧸ Subgroup.center G ≃* (conjRep G).range :=
  (QuotientGroup.quotientMulEquivOfEq ker_conjRep.symm).trans
    (QuotientGroup.quotientKerEquivRange (conjRep G))

end CayleyConjugation
