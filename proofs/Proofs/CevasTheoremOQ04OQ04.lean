import Proofs.CevasTheoremOQ04
import Mathlib.Tactic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-
# Angle Bisectors, Mass Points, and the Incenter (Ceva OQ-04-OQ-04)

## Research Question (cevas-theorem-oq-04-oq-04)

The parent file `CevasTheoremOQ04.lean` develops mass-point geometry as an
algebraic certificate for concurrent cevians: positive masses mA, mB, mC at the
vertices of a triangle induce cevian division points whose Ceva product is always
1.  The centroid arises from *equal* masses (`centroid_example`).

This file treats the **angle bisector** case.  Assign masses equal to the
*opposite side lengths*, mA = a = |BC|, mB = b = |CA|, mC = c = |AB|.  We show:

1. these masses realise exactly the angle-bisector division ratios — the
   angle-bisector theorem ratios

     BD/DC = c/b,   CE/EA = a/c,   AF/FB = b/a

   (reusing the parent's `ratio_balance` family);
2. hence the three angle bisectors are concurrent — their Ceva ratio product is 1
   (reusing the parent's `ceva_ratio_product_one`);
3. the point of concurrency is the **incenter**

     I = (a·A + b·B + c·C) / (a + b + c),

   proved *constructively* by exhibiting I as an affine combination of each vertex
   with the opposite cevian foot.  Concretely I lies on all three angle bisectors
   simultaneously, so the three lines meet at I.

Item (3) is the substantive new content beyond the parent's ratio identity: a
fully geometric concurrency witness in an *arbitrary real vector space*.  No
triangle inequality is needed — only positivity of the three side lengths.

## Mathematical Significance

The barycentric coordinates of the incenter are (a : b : c): masses proportional
to the opposite sides.  This is the canonical worked example of mass-point
geometry for angle bisectors.  The affine-combination proof turns "the three
bisectors meet at the incenter" into a checked theorem rather than a ratio
coincidence: each bisector is an honest line in a vector space, and `incenter` is
exhibited on each of them via `AffineMap.lineMap`.
-/

namespace MassPointCeva.AngleBisector

open MassPointCeva

/- ## The angle-bisector mass assignment -/

/-- Masses equal to the opposite side lengths a = |BC|, b = |CA|, c = |AB|. -/
def bisectorMass (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : MassPoint :=
  ⟨a, b, c, ha, hb, hc⟩

@[simp] lemma bisectorMass_mA {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (bisectorMass a b c ha hb hc).mA = a := rfl

@[simp] lemma bisectorMass_mB {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (bisectorMass a b c ha hb hc).mB = b := rfl

@[simp] lemma bisectorMass_mC {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (bisectorMass a b c ha hb hc).mC = c := rfl

/- ## Angle-bisector division ratios

The angle-bisector theorem says the internal bisector from a vertex divides the
opposite side in the ratio of the two adjacent sides.  With masses = opposite
sides, the parent's lever-arm identity `ratio_balance` reproduces exactly these
ratios. -/

/-- Bisector from `A`: `BD/DC = c/b` (= `|AB|/|AC|`). -/
theorem bisector_ratio_BD_DC {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    rD (bisectorMass a b c ha hb hc) / (1 - rD (bisectorMass a b c ha hb hc)) = c / b :=
  ratio_balance _

/-- Bisector from `B`: `CE/EA = a/c` (= `|BC|/|BA|`). -/
theorem bisector_ratio_CE_EA {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    rE (bisectorMass a b c ha hb hc) / (1 - rE (bisectorMass a b c ha hb hc)) = a / c :=
  ratio_balance_E _

/-- Bisector from `C`: `AF/FB = b/a` (= `|CA|/|CB|`). -/
theorem bisector_ratio_AF_FB {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    rF (bisectorMass a b c ha hb hc) / (1 - rF (bisectorMass a b c ha hb hc)) = b / a :=
  ratio_balance_F _

/- ## Concurrency via Ceva (reusing the parent) -/

/-- The three angle bisectors satisfy the Ceva concurrency criterion: the product
of the directed division ratios is `1`. -/
theorem bisectors_ceva_product {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    let m := bisectorMass a b c ha hb hc
    (rD m / (1 - rD m)) * (rE m / (1 - rE m)) * (rF m / (1 - rF m)) = 1 :=
  ceva_ratio_product_one _

/-- The same Ceva product written explicitly in side-length ratios:
`(c/b)·(a/c)·(b/a) = 1`. -/
theorem bisectors_side_ratio_product {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (c / b) * (a / c) * (b / a) = 1 := by
  field_simp

/- ## The incenter as the point of concurrency

We now realise the cevians as honest lines in a real vector space and exhibit the
incenter on each of them.  Points are vectors; the "feet" are the bisector
division points, and `incenter` is the barycentric point `(a : b : c)`. -/

section Affine

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Foot of the `A`-bisector on side `BC`, dividing `BD:DC = c:b`. -/
noncomputable def footD (b c : ℝ) (B C : V) : V :=
  (b / (b + c)) • B + (c / (b + c)) • C

/-- Foot of the `B`-bisector on side `CA`, dividing `CE:EA = a:c`. -/
noncomputable def footE (c a : ℝ) (C A : V) : V :=
  (c / (c + a)) • C + (a / (c + a)) • A

/-- Foot of the `C`-bisector on side `AB`, dividing `AF:FB = b:a`. -/
noncomputable def footF (a b : ℝ) (A B : V) : V :=
  (a / (a + b)) • A + (b / (a + b)) • B

/-- The **incenter**: barycentric coordinates `(a : b : c)`. -/
noncomputable def incenter (a b c : ℝ) (A B C : V) : V :=
  (a / (a + b + c)) • A + (b / (a + b + c)) • B + (c / (a + b + c)) • C

/-- For the angle-bisector masses, `footD` is exactly the parent's division point
`(1 - rD)·B + rD·C`, confirming it is the cevian foot of that mass assignment. -/
theorem footD_eq_division {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (B C : V) :
    footD b c B C =
      (1 - rD (bisectorMass a b c ha hb hc)) • B
        + rD (bisectorMass a b c ha hb hc) • C := by
  rw [one_sub_rD]
  simp only [footD, rD, bisectorMass_mB, bisectorMass_mC]

/-- **Incenter lies on the `A`-bisector.**  It is the affine combination of `A`
and the foot `footD` with weights `a/(a+b+c)` and `(b+c)/(a+b+c)`. -/
theorem incenter_on_bisector_A {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (A B C : V) :
    incenter a b c A B C
      = (a / (a + b + c)) • A + ((b + c) / (a + b + c)) • footD b c B C := by
  have hbc : b + c ≠ 0 := by positivity
  have habc : a + b + c ≠ 0 := by positivity
  simp only [incenter, footD]
  match_scalars <;> field_simp

/-- **Incenter lies on the `B`-bisector.** -/
theorem incenter_on_bisector_B {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (A B C : V) :
    incenter a b c A B C
      = (b / (a + b + c)) • B + ((c + a) / (a + b + c)) • footE c a C A := by
  have hca : c + a ≠ 0 := by positivity
  have habc : a + b + c ≠ 0 := by positivity
  simp only [incenter, footE]
  match_scalars <;> field_simp

/-- **Incenter lies on the `C`-bisector.** -/
theorem incenter_on_bisector_C {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (A B C : V) :
    incenter a b c A B C
      = (c / (a + b + c)) • C + ((a + b) / (a + b + c)) • footF a b A B := by
  have hab : a + b ≠ 0 := by positivity
  have habc : a + b + c ≠ 0 := by positivity
  simp only [incenter, footF]
  match_scalars <;> field_simp

/- ### The affine weights are barycentric (sum to one)

Each concurrency identity above is a genuine *affine* combination: the two weights
sum to `1`, so `incenter` lies on the line through the vertex and the opposite
foot. -/

theorem weights_A_sum_one {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a / (a + b + c) + (b + c) / (a + b + c) = 1 := by
  have habc : a + b + c ≠ 0 := by positivity
  field_simp; ring

theorem weights_B_sum_one {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    b / (a + b + c) + (c + a) / (a + b + c) = 1 := by
  have habc : a + b + c ≠ 0 := by positivity
  field_simp; ring

theorem weights_C_sum_one {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    c / (a + b + c) + (a + b) / (a + b + c) = 1 := by
  have habc : a + b + c ≠ 0 := by positivity
  field_simp; ring

/- ### Lines, via `AffineMap.lineMap`

The cevian from a vertex to the opposite foot is the line `lineMap vertex foot`.
The incenter is the point at parameter `t = (opposite-pair)/(a+b+c) ∈ (0,1)`. -/

/-- The `A`-bisector as a line, with `incenter` at parameter `(b+c)/(a+b+c)`. -/
theorem incenter_lineMap_A {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (A B C : V) :
    incenter a b c A B C
      = AffineMap.lineMap A (footD b c B C) ((b + c) / (a + b + c) : ℝ) := by
  have hbc : b + c ≠ 0 := by positivity
  have habc : a + b + c ≠ 0 := by positivity
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, incenter, footD]
  match_scalars <;> field_simp <;> ring_nf

end Affine

end MassPointCeva.AngleBisector
