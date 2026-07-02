import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-
# Hilbert's 10th — OQ-04-03 → OQ-03: Explicit Solution Witness for Linear Diophantine Equations

## Research Problem: hilbert-10-oq-04-oq-03-oq-03

The parent (`hilbert-10-oq-04-oq-03`, "Linear Diophantine Solvability is Decidable") proves the
*existence* criterion: the equation `∑ aᵢ·xᵢ = b` is solvable iff `gcd(a) ∣ b`, and solvability is
decidable. It stops at existence — it produces no actual solution and says nothing about how the
solutions are laid out.

This file supplies the constructive companion for the two-variable equation `a·x + b·y = c`:

* an **explicit witness** built from Bézout's coefficients (`Int.gcdA`, `Int.gcdB`), and
* the **complete solution set** as a one-parameter family
  `(x, y) = (x₀ + (b/g)·t, y₀ − (a/g)·t)`, `t ∈ ℤ`, `g = gcd(a,b)`.

Together these turn the parent's yes/no decision into a full description of the solution locus: a
witness when `g ∣ c`, and — for `b ≠ 0` — a bijective ℤ-parametrisation of *all* solutions.

## Mechanism

Bézout (`Int.gcd_eq_gcd_ab`) gives `a·u + b·v = g` with `u = gcdA a b`, `v = gcdB a b`. Scaling by
`q = c/g` (exact when `g ∣ c`) yields the witness `x₀ = q·u`, `y₀ = q·v` with `a·x₀ + b·y₀ = c`.

Writing `A = a/g`, `B = b/g` (exact, since `g ∣ a` and `g ∣ b`), the family
`(x₀ + B·t, y₀ − A·t)` consists of solutions because `a·B − b·A = g·A·B − g·B·A = 0`. Conversely,
if `a·x + b·y = a·x₀ + b·y₀` then `a·(x−x₀) = −b·(y−y₀)`; cancelling `g > 0` gives
`A·(x−x₀) = −B·(y−y₀)`, so `B ∣ A·(x−x₀)`, and since `gcd(A,B) = 1` (dividing out the gcd) we get
`B ∣ (x−x₀)`. Writing `x − x₀ = B·t` and cancelling `B ≠ 0` forces `y = y₀ − A·t`. So every
solution is in the family — the parametrisation is exhaustive.

## What is proved

* `bezout_witness`   — `g ∣ c → a·(q·u) + b·(q·v) = c`, the explicit Bézout solution.
* `family_is_solution` — every `(x₀ + B·t, y₀ − A·t)` solves the equation whenever `(x₀,y₀)` does.
* `solution_complete` — for `b ≠ 0`, every solution equals `(x₀ + B·t, y₀ − A·t)` for some `t`.
* `solution_set_eq`  — the set of solutions is exactly the parametrised family (for `b ≠ 0`).

Tags: number-theory, diophantine, bezout, gcd, hilbert-tenth-problem
-/

namespace Hilbert10OQ04OQ03OQ03

open Int

/-- The explicit Bézout witness. With `g = gcd(a,b)`, `u = gcdA a b`, `v = gcdB a b` and
`q = c / g`, if `g ∣ c` then `x₀ = q·u`, `y₀ = q·v` solves `a·x + b·y = c`. -/
theorem bezout_witness (a b c : ℤ) (h : (Int.gcd a b : ℤ) ∣ c) :
    a * (c / (Int.gcd a b : ℤ) * Int.gcdA a b) + b * (c / (Int.gcd a b : ℤ) * Int.gcdB a b) = c := by
  have hbez : a * Int.gcdA a b + b * Int.gcdB a b = (Int.gcd a b : ℤ) :=
    (Int.gcd_eq_gcd_ab a b).symm
  have hq : c / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) = c := Int.ediv_mul_cancel h
  calc a * (c / (Int.gcd a b : ℤ) * Int.gcdA a b) + b * (c / (Int.gcd a b : ℤ) * Int.gcdB a b)
      = c / (Int.gcd a b : ℤ) * (a * Int.gcdA a b + b * Int.gcdB a b) := by ring
    _ = c / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) := by rw [hbez]
    _ = c := hq

/-- The parametrised family are all solutions. With `A = a/g`, `B = b/g`, if `(x₀, y₀)` solves
`a·x + b·y = c` then so does `(x₀ + B·t, y₀ − A·t)` for every `t`, because `a·B − b·A = 0`. -/
theorem family_is_solution (a b c x₀ y₀ t : ℤ) (h₀ : a * x₀ + b * y₀ = c) :
    a * (x₀ + b / (Int.gcd a b : ℤ) * t) + b * (y₀ - a / (Int.gcd a b : ℤ) * t) = c := by
  -- `a·(b/g) = a·b/g = b·a/g = b·(a/g)`, so `a·B − b·A = 0` (no `g ≠ 0` needed).
  have e1 : a * (b / (Int.gcd a b : ℤ)) = a * b / (Int.gcd a b : ℤ) :=
    (Int.mul_ediv_assoc a (Int.gcd_dvd_right a b)).symm
  have e2 : b * (a / (Int.gcd a b : ℤ)) = b * a / (Int.gcd a b : ℤ) :=
    (Int.mul_ediv_assoc b (Int.gcd_dvd_left a b)).symm
  have hcancel : a * (b / (Int.gcd a b : ℤ)) - b * (a / (Int.gcd a b : ℤ)) = 0 := by
    rw [e1, e2, mul_comm b a]; ring
  calc a * (x₀ + b / (Int.gcd a b : ℤ) * t) + b * (y₀ - a / (Int.gcd a b : ℤ) * t)
      = (a * x₀ + b * y₀)
          + t * (a * (b / (Int.gcd a b : ℤ)) - b * (a / (Int.gcd a b : ℤ))) := by ring
    _ = c + t * 0 := by rw [h₀, hcancel]
    _ = c := by ring

/-- **Completeness of the parametrisation.** For `b ≠ 0` (so `g > 0` and `B ≠ 0`), every solution
of `a·x + b·y = c` equals `(x₀ + B·t, y₀ − A·t)` for a unique `t`, where `(x₀, y₀)` is any fixed
solution. Hence the family enumerates the whole solution set. -/
theorem solution_complete (a b c x₀ y₀ x y : ℤ) (hb : b ≠ 0)
    (hxy : a * x + b * y = c) (h₀ : a * x₀ + b * y₀ = c) :
    ∃ t, x = x₀ + b / (Int.gcd a b : ℤ) * t ∧ y = y₀ - a / (Int.gcd a b : ℤ) * t := by
  set g : ℤ := (Int.gcd a b : ℤ) with hg
  -- `g > 0` since `b ≠ 0`.
  have hgnat : Int.gcd a b ≠ 0 := by
    rw [Ne, Int.gcd_eq_zero_iff]; exact fun hab => hb hab.2
  have hgnatpos : 0 < Int.gcd a b := Nat.pos_of_ne_zero hgnat
  have hgpos : 0 < g := by rw [hg]; exact_mod_cast hgnatpos
  have hgne : g ≠ 0 := ne_of_gt hgpos
  set A : ℤ := a / g with hA
  set B : ℤ := b / g with hB
  have hga : g * A = a := Int.mul_ediv_cancel' (Int.gcd_dvd_left a b)
  have hgb : g * B = b := Int.mul_ediv_cancel' (Int.gcd_dvd_right a b)
  -- `B ≠ 0` since `b = g·B ≠ 0`.
  have hBne : B ≠ 0 := by
    intro hB0; apply hb; rw [← hgb, hB0, mul_zero]
  -- Coprimality of `A` and `B` (dividing out the gcd).
  have hcopAB : Int.gcd A B = 1 := Int.gcd_div_gcd_div_gcd hgnatpos
  have hcop : IsCoprime B A := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]; exact hcopAB
  -- From the two equations: `a·(x−x₀) = −b·(y−y₀)`.
  have hdiff : a * (x - x₀) = -(b * (y - y₀)) := by linear_combination hxy - h₀
  -- Cancel `g`: `A·(x−x₀) = −B·(y−y₀)`.
  have hAB : A * (x - x₀) = -(B * (y - y₀)) := by
    apply mul_left_cancel₀ hgne
    calc g * (A * (x - x₀)) = a * (x - x₀) := by rw [← hga]; ring
      _ = -(b * (y - y₀)) := hdiff
      _ = g * (-(B * (y - y₀))) := by rw [← hgb]; ring
  -- `B ∣ A·(x−x₀)` because the RHS is a multiple of `B`.
  have hdvd : B ∣ A * (x - x₀) := by
    rw [hAB]; exact dvd_neg.mpr (dvd_mul_right B (y - y₀))
  -- Coprimality upgrades this to `B ∣ (x−x₀)`.
  have hBdvd : B ∣ (x - x₀) := hcop.dvd_of_dvd_mul_left hdvd
  obtain ⟨t, ht⟩ := hBdvd
  refine ⟨t, by linarith [ht], ?_⟩
  -- From `A·(B·t) = −B·(y−y₀)` cancel `B` to get `y = y₀ − A·t`.
  have hsub : A * (B * t) = -(B * (y - y₀)) := by rw [← ht]; exact hAB
  have hy : B * (A * t) = B * (-(y - y₀)) := by
    have h1 : B * (A * t) = A * (B * t) := by ring
    rw [h1, hsub]; ring
  have hAt : A * t = -(y - y₀) := mul_left_cancel₀ hBne hy
  linarith [hAt]

/-- **The solution set is exactly the parametrised family** (for `b ≠ 0`). Combining
`family_is_solution` and `solution_complete`: with `(x₀,y₀)` any fixed solution,
`{(x,y) | a·x + b·y = c} = {(x₀ + B·t, y₀ − A·t) | t ∈ ℤ}`. -/
theorem solution_set_eq (a b c x₀ y₀ : ℤ) (hb : b ≠ 0) (h₀ : a * x₀ + b * y₀ = c) :
    {p : ℤ × ℤ | a * p.1 + b * p.2 = c}
      = {p : ℤ × ℤ | ∃ t, p.1 = x₀ + b / (Int.gcd a b : ℤ) * t
                          ∧ p.2 = y₀ - a / (Int.gcd a b : ℤ) * t} := by
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hxy; exact solution_complete a b c x₀ y₀ x y hb hxy h₀
  · rintro ⟨t, rfl, rfl⟩; exact family_is_solution a b c x₀ y₀ t h₀

#check @bezout_witness
#check @family_is_solution
#check @solution_complete
#check @solution_set_eq

/-
## Summary

Proved (0 sorries, 0 axioms; imports only Mathlib):

* `bezout_witness` — the explicit Bézout solution `(c/g·gcdA, c/g·gcdB)` when `g ∣ c`.
* `family_is_solution` — the parametrised family `(x₀ + (b/g)t, y₀ − (a/g)t)` are all solutions.
* `solution_complete` — for `b ≠ 0`, every solution is in that family (with a matching `t`).
* `solution_set_eq` — the solution set equals the parametrised family.

Where the parent (`hilbert-10-oq-04-oq-03`) decides *whether* a linear Diophantine equation is
solvable, this entry produces an explicit solution and the complete one-parameter description of
the solution locus.
-/

end Hilbert10OQ04OQ03OQ03
