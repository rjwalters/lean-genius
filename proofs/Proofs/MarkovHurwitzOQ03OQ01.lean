/-
# Complete Classification of the a = 1 Markov–Hurwitz Slice

The classical Markov equation `x² + y² + z² = 3xyz` is the `a = 3` member of the
one–parameter **Markov–Hurwitz family** `x² + y² + z² = a · x · y · z`. The sibling
entry `markov-equation-oq-03` carries the *Vieta-jump infrastructure* of the parent
to this family — the coefficient-agnostic jump, the n-variable descent criterion,
and the parametric `+k` foliation. What it does **not** do is classify any new
member of the family.

This file supplies that missing piece for the second coefficient that admits
solutions, `a = 1`: it proves a **complete classification** of the positive
solutions of

  x² + y² + z² = x · y · z

by reducing them, exactly, to the Markov tree of the parent `Proofs.MarkovEquation`.

The main results are:

* **Mod-3 obstruction.** Every positive solution of `x²+y²+z² = xyz` has all three
  coordinates divisible by `3`. Modulo `3` the only residue triple satisfying the
  equation is `(0,0,0)` — a finite 27-case check (`decide`, not `native_decide`,
  so the result stays axiom-clean).

* **Scaling bijection.** `(x,y,z) ↦ (x/3, y/3, z/3)` is a bijection between `a = 1`
  solutions and Markov triples: `x²+y²+z² = xyz` holds iff `(x,y,z) = (3a,3b,3c)`
  for a Markov triple `(a,b,c)`.

* **Transported classification.** Composing the bijection with the parent's
  `markov_classification`, every positive `a = 1` solution is `(3a,3b,3c)` with
  `(a,b,c)` reachable from the root `(1,1,1)` in the Markov tree.

* **Coefficient rigidity.** A symmetric solution `(t,t,t)` of the family forces
  `a·t = 3`, hence `a ∈ {1, 3}` — exactly the two coefficients whose full solution
  sets are now classified (`a = 3` by the parent, `a = 1` here).

We also record the coefficient-agnostic Vieta jump in concrete ternary form, to keep
the file self-contained. Honest scope: we do **not** prove Hurwitz's full theorem
that no coefficient outside `{1,3}` admits any positive solution (only the diagonal
obstruction); the parametric `+k` and n-variable infrastructure live in the sibling
`markov-equation-oq-03` entry. The global non-existence statement needs a genuine
minimality/descent argument and is left as the natural next step.
-/
import Mathlib
import Proofs.MarkovEquation

namespace MarkovHurwitzOQ03OQ01

open MarkovEquation

/-- A **Markov–Hurwitz triple** with coefficient `a`: positive integers satisfying
`x² + y² + z² = a · x · y · z`. -/
def IsHurwitz (a x y z : ℤ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 + z ^ 2 = a * x * y * z

/-! ## Coefficient-agnostic Vieta jumping

Everything that drives the Markov descent depends only on the shape of the
equation, not on the value of `a`. We re-derive the core facts for general `a`. -/

/-- The product of the two `z`-roots of `t² − a·xy·t + (x²+y²) = 0` equals
`x² + y²`, independently of `a`. -/
theorem hurwitz_root_prod {a x y z : ℤ} (h : IsHurwitz a x y z) :
    z * (a * x * y - z) = x ^ 2 + y ^ 2 := by
  obtain ⟨_, _, _, he⟩ := h
  linear_combination -he

/-- **Vieta jump for general `a`.** Replacing `z` by its conjugate root
`a·xy − z` yields another Markov–Hurwitz triple with the same coefficient. -/
theorem hurwitz_vieta {a x y z : ℤ} (h : IsHurwitz a x y z) :
    IsHurwitz a x y (a * x * y - z) := by
  obtain ⟨hx, hy, hz, he⟩ := h
  have hzz : z * (a * x * y - z) = x ^ 2 + y ^ 2 := by linear_combination -he
  have hpos : 0 < x ^ 2 + y ^ 2 := by positivity
  refine ⟨hx, hy, ?_, by linear_combination he⟩
  nlinarith [hzz, hpos, hz]

/-- The Vieta jump is an involution in the third coordinate, for every `a`. -/
theorem hurwitz_vieta_involutive (a x y z : ℤ) :
    a * x * y - (a * x * y - z) = z := by ring

/-! ## The `a = 3` slice is the Markov equation -/

/-- For coefficient `a = 3`, the Markov–Hurwitz predicate is *definitionally* the
Markov predicate of the parent file. -/
theorem isHurwitz_three_iff_isMarkov (x y z : ℤ) :
    IsHurwitz 3 x y z ↔ IsMarkov x y z := by
  unfold IsHurwitz IsMarkov
  constructor <;> rintro ⟨hx, hy, hz, he⟩ <;> exact ⟨hx, hy, hz, by linear_combination he⟩

/-! ## The `a = 1` slice: divisibility by 3

The arithmetic heart of the `a = 1` classification is that *every* positive
solution of `x² + y² + z² = xyz` has all coordinates divisible by `3`. Modulo
`3`, squares are `0` or `1`; a finite (27-case) check shows the only residue
triple satisfying the equation is `(0,0,0)`. -/

/-- **Mod-3 obstruction.** Any integer solution of `x² + y² + z² = xyz` has all
three coordinates divisible by `3`. (No positivity needed.) -/
theorem three_dvd_all_of_hurwitz_one {x y z : ℤ}
    (he : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) :
    (3 : ℤ) ∣ x ∧ (3 : ℤ) ∣ y ∧ (3 : ℤ) ∣ z := by
  -- The only residue triple mod 3 satisfying the equation is (0,0,0).
  have key : ∀ a b c : ZMod 3, a ^ 2 + b ^ 2 + c ^ 2 = a * b * c →
      a = 0 ∧ b = 0 ∧ c = 0 := by decide
  -- Push the integer equation into `ZMod 3`.
  have hcast : (x : ZMod 3) ^ 2 + (y : ZMod 3) ^ 2 + (z : ZMod 3) ^ 2
      = (x : ZMod 3) * (y : ZMod 3) * (z : ZMod 3) := by
    have h := congrArg (Int.cast : ℤ → ZMod 3) he
    push_cast at h
    linear_combination h
  obtain ⟨hx0, hy0, hz0⟩ := key _ _ _ hcast
  refine ⟨?_, ?_, ?_⟩
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 3).mp hx0
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd y 3).mp hy0
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 3).mp hz0

/-! ## The scaling bijection `a = 1  ↔  3 × Markov` -/

/-- **Markov ⇒ Hurwitz(1).** Tripling a Markov triple gives an `a = 1` solution:
if `(a,b,c)` solves `a²+b²+c² = 3abc`, then `(3a,3b,3c)` solves the `a = 1`
equation `x²+y²+z² = xyz`. -/
theorem hurwitz_one_of_markov {a b c : ℤ} (h : IsMarkov a b c) :
    IsHurwitz 1 (3 * a) (3 * b) (3 * c) := by
  obtain ⟨ha, hb, hc, he⟩ := h
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  -- 9(a²+b²+c²) = 9·3abc = 27abc = (3a)(3b)(3c)
  linear_combination (9 : ℤ) * he

/-- **Hurwitz(1) ⇒ Markov.** Conversely every `a = 1` solution is `3 ×` a Markov
triple: there exist `a, b, c` with `x = 3a`, `y = 3b`, `z = 3c` and
`IsMarkov a b c`. -/
theorem markov_of_hurwitz_one {x y z : ℤ} (h : IsHurwitz 1 x y z) :
    ∃ a b c : ℤ, x = 3 * a ∧ y = 3 * b ∧ z = 3 * c ∧ IsMarkov a b c := by
  obtain ⟨hx, hy, hz, he⟩ := h
  have he' : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z := by linear_combination he
  obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ⟨c, rfl⟩⟩ := three_dvd_all_of_hurwitz_one he'
  refine ⟨a, b, c, rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · -- 9(a²+b²+c²) = (3a)(3b)(3c) = 27abc ⟹ a²+b²+c² = 3abc
    have h9 : (9 : ℤ) * (a ^ 2 + b ^ 2 + c ^ 2) = 9 * (3 * a * b * c) := by
      linear_combination he
    linarith

/-- **Bijection form.** `(x,y,z)` is an `a = 1` solution iff it is `3 ×` a Markov
triple. -/
theorem hurwitz_one_iff_markov_scaled {x y z : ℤ} :
    IsHurwitz 1 x y z ↔
      ∃ a b c : ℤ, x = 3 * a ∧ y = 3 * b ∧ z = 3 * c ∧ IsMarkov a b c := by
  constructor
  · exact markov_of_hurwitz_one
  · rintro ⟨a, b, c, rfl, rfl, rfl, hM⟩
    exact hurwitz_one_of_markov hM

/-! ## Complete classification of the `a = 1` solutions

Composing the scaling bijection with the parent's Markov-tree classification
yields a complete description of the `a = 1` solution set. -/

/-- **Classification at `a = 1`.** Every positive solution of `x²+y²+z² = xyz`
is `(3a, 3b, 3c)` for a triple `(a,b,c)` reachable from the root `(1,1,1)` in the
Markov tree. -/
theorem hurwitz_one_classification {x y z : ℤ} (h : IsHurwitz 1 x y z) :
    ∃ a b c : ℤ, x = 3 * a ∧ y = 3 * b ∧ z = 3 * c ∧
      Reachable (a, b, c) (1, 1, 1) := by
  obtain ⟨a, b, c, hx, hy, hz, hM⟩ := markov_of_hurwitz_one h
  exact ⟨a, b, c, hx, hy, hz, markov_classification hM⟩

/-! ## Coefficient rigidity (diagonal obstruction) -/

/-- A **diagonal** Markov–Hurwitz triple `(t,t,t)` forces `a · t = 3`. -/
theorem hurwitz_diagonal {a t : ℤ} (h : IsHurwitz a t t t) : a * t = 3 := by
  obtain ⟨ht, _, _, he⟩ := h
  -- 3t² = a·t³ and t > 0 ⇒ a·t = 3
  have ht2 : (0 : ℤ) < t ^ 2 := by positivity
  have hkey : t ^ 2 * (a * t) = t ^ 2 * 3 := by linear_combination -he
  exact mul_left_cancel₀ ht2.ne' hkey

/-- **Diagonal coefficients are `1` or `3`.** A positive diagonal solution exists
only for `a = 1` (with `t = 3`) or `a = 3` (with `t = 1`). -/
theorem hurwitz_diagonal_coeff {a t : ℤ} (h : IsHurwitz a t t t) :
    (a = 1 ∧ t = 3) ∨ (a = 3 ∧ t = 1) := by
  have hat : a * t = 3 := hurwitz_diagonal h
  obtain ⟨ht, _, _, _⟩ := h
  have ha : 0 < a := by nlinarith [hat, ht]
  have ht1 : 1 ≤ t := ht
  have hat3 : t ≤ 3 := by nlinarith [hat, ha]
  -- positive factorisations of 3
  interval_cases t <;> omega

/-! ## Small solutions -/

/-- `(3,3,3)` is the diagonal `a = 1` solution — the image of the Markov root. -/
theorem hurwitz_one_three_three_three : IsHurwitz 1 3 3 3 :=
  ⟨by norm_num, by norm_num, by norm_num, by ring⟩

/-- `(3,3,6)` is an `a = 1` solution — the image of the Markov triple `(1,1,2)`. -/
theorem hurwitz_one_three_three_six : IsHurwitz 1 3 3 6 :=
  ⟨by norm_num, by norm_num, by norm_num, by ring⟩

/-- `(3,6,15)` is an `a = 1` solution — the image of the Markov triple `(1,2,5)`. -/
theorem hurwitz_one_three_six_fifteen : IsHurwitz 1 3 6 15 :=
  ⟨by norm_num, by norm_num, by norm_num, by ring⟩

end MarkovHurwitzOQ03OQ01
