/-
# Linear Diophantine equations: a constructive solver

Follow-up to `Hilbert10OQ04OQ03` (open question oq-01 of that entry).

The parent file proves that the linear Diophantine equation `∑ aᵢ xᵢ = c` is
*decidable* (`LinearForm.decidableSolvable`) and, when solvable, that a solution
*exists* (`solvable_iff_gcd_dvd`). But that existence proof is **non-constructive**:
it pulls the witness out of an `Ideal.span` membership obtained through the
*noncomputable* principal-ideal generator (`Submodule.IsPrincipal.generator`). It
tells you a solution is there; it does not hand you one.

This file closes that gap. It builds an honest **computable** solver — the integer
analogue of the *extended* Euclidean algorithm — by folding pairwise Bézout
cofactors (`Int.gcdA` / `Int.gcdB`) across the coefficients:

* `bezout` : a computable function returning `(g, y)` with `∑ aᵢ yᵢ = g` and `g ∣ aᵢ`
  for every `i` (so `g` is a gcd of the coefficients), built purely from two-variable
  extended Euclid;
* `bezout_sum`, `bezout_dvd` : its correctness invariants;
* `exists_solution` : the **constructive** existence theorem — given `gcd a ∣ c`,
  there is an explicit `x` with `∑ aᵢ xᵢ = c`;
* `solve` : the end-to-end computable solver `(a, c) ↦ x`, and `solve_spec` its
  correctness. The witness can be evaluated (`#eval`), unlike the parent's.

Everything is `sorry`-free and `axiom`-free (only the foundational
`propext` / `Classical.choice` / `Quot.sound`; the `decide` in the worked example
uses kernel reduction, *not* `native_decide`, so `Lean.ofReduceBool` is not invoked).
-/
import Mathlib

namespace Hilbert10OQ04OQ03OQ01

/-- **Computable Bézout fold.** Given coefficients `a : Fin n → ℤ`, returns a pair
`(g, y)` where `g` is the (nonnegative) gcd of the `aᵢ` and `y : Fin n → ℤ` is an
explicit cofactor vector with `∑ aᵢ yᵢ = g`. Defined by recursion on `n`: the head
coefficient `a 0` is combined with the gcd `g'` of the tail via two-variable extended
Euclid, `gcd (a 0) g' = a 0 · gcdA + g' · gcdB`, and the tail cofactors are scaled by
`gcdB`. -/
def bezout : (n : ℕ) → (Fin n → ℤ) → ℤ × (Fin n → ℤ)
  | 0, _ => (0, Fin.elim0)
  | (n + 1), a =>
      ((Int.gcd (a 0) (bezout n (fun j => a j.succ)).1 : ℤ),
       Fin.cons (Int.gcdA (a 0) (bezout n (fun j => a j.succ)).1)
                (fun i => Int.gcdB (a 0) (bezout n (fun j => a j.succ)).1
                          * (bezout n (fun j => a j.succ)).2 i))

/-- The Bézout fold returns a genuine linear combination: `∑ aᵢ · yᵢ = g`. -/
theorem bezout_sum : ∀ (n : ℕ) (a : Fin n → ℤ),
    ∑ i, a i * (bezout n a).2 i = (bezout n a).1 := by
  intro n
  induction n with
  | zero => intro a; simp [bezout]
  | succ n ih =>
      intro a
      have IH : (∑ i : Fin n, a i.succ * (bezout n (fun j => a j.succ)).2 i)
              = (bezout n (fun j => a j.succ)).1 := ih (fun j => a j.succ)
      simp only [bezout, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      have hfactor : (∑ i : Fin n, a i.succ *
            (Int.gcdB (a 0) (bezout n (fun j => a j.succ)).1
              * (bezout n (fun j => a j.succ)).2 i))
          = Int.gcdB (a 0) (bezout n (fun j => a j.succ)).1
            * (∑ i : Fin n, a i.succ * (bezout n (fun j => a j.succ)).2 i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)
      rw [hfactor, IH, Int.gcd_eq_gcd_ab (a 0) (bezout n (fun j => a j.succ)).1]
      ring

/-- The first component of the Bézout fold is a common divisor of every coefficient,
so it is a gcd of the `aᵢ`. -/
theorem bezout_dvd : ∀ (n : ℕ) (a : Fin n → ℤ) (i : Fin n), (bezout n a).1 ∣ a i := by
  intro n
  induction n with
  | zero => intro a i; exact i.elim0
  | succ n ih =>
      intro a i
      induction i using Fin.cases with
      | zero => simp only [bezout]; exact Int.gcd_dvd_left ..
      | succ j =>
          simp only [bezout]
          exact (Int.gcd_dvd_right ..).trans (ih (fun j => a j.succ) j)

/-- **Constructive existence.** If the gcd of the coefficients divides `c`, then the
linear Diophantine equation `∑ aᵢ xᵢ = c` has an *explicit* integer solution. Unlike
the parent's `solvable_iff_gcd_dvd`, the witness here is produced computably from the
Bézout fold (scaled by the quotient `c / g`). -/
theorem exists_solution (n : ℕ) (a : Fin n → ℤ) (c : ℤ)
    (h : (Finset.univ.gcd a : ℤ) ∣ c) :
    ∃ x : Fin n → ℤ, ∑ i, a i * x i = c := by
  have hdvd : (bezout n a).1 ∣ (Finset.univ.gcd a : ℤ) :=
    Finset.dvd_gcd (fun i _ => bezout_dvd n a i)
  obtain ⟨k, hk⟩ := hdvd.trans h
  refine ⟨fun i => k * (bezout n a).2 i, ?_⟩
  have hsum := bezout_sum n a
  show ∑ i, a i * (k * (bezout n a).2 i) = c
  calc ∑ i, a i * (k * (bezout n a).2 i)
      = ∑ i, k * (a i * (bezout n a).2 i) := Finset.sum_congr rfl (fun i _ => by ring)
    _ = k * ∑ i, a i * (bezout n a).2 i := by rw [Finset.mul_sum]
    _ = k * (bezout n a).1 := by rw [hsum]
    _ = c := by rw [mul_comm k, ← hk]

/-- **Computable solver.** Returns an explicit solution vector for `∑ aᵢ xᵢ = c`
(correct whenever `gcd a ∣ c`, see `solve_spec`). This is the integer analogue of the
extended Euclidean algorithm: a `def`, so its output can be `#eval`-uated. -/
def solve (n : ℕ) (a : Fin n → ℤ) (c : ℤ) : Fin n → ℤ :=
  fun i => (c / (bezout n a).1) * (bezout n a).2 i

/-- The computable `solve` is correct: when the gcd divides the target, its output is
an actual solution of `∑ aᵢ xᵢ = c`. -/
theorem solve_spec (n : ℕ) (a : Fin n → ℤ) (c : ℤ)
    (h : (Finset.univ.gcd a : ℤ) ∣ c) :
    ∑ i, a i * solve n a c i = c := by
  have hdvd : (bezout n a).1 ∣ (Finset.univ.gcd a : ℤ) :=
    Finset.dvd_gcd (fun i _ => bezout_dvd n a i)
  have hgc : (bezout n a).1 ∣ c := hdvd.trans h
  have hsum := bezout_sum n a
  simp only [solve]
  calc ∑ i, a i * ((c / (bezout n a).1) * (bezout n a).2 i)
      = (c / (bezout n a).1) * ∑ i, a i * (bezout n a).2 i := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
    _ = (c / (bezout n a).1) * (bezout n a).1 := by rw [hsum]
    _ = (bezout n a).1 * (c / (bezout n a).1) := by ring
    _ = c := Int.mul_ediv_cancel' hgc

/-- The solver in action on `6x + 10y + 15z = 1` (the coefficients are pairwise
non-coprime yet jointly coprime, so no single pair suffices — the fold is essential).
`List.ofFn` exposes the computed witness as an evaluable list. -/
#eval (List.ofFn (solve 3 (![6, 10, 15] : Fin 3 → ℤ) 1))

/-- Machine-checked instantiation of the solver+spec for the `6,10,15` coefficients.
The target `0` is divisible by the gcd automatically (`dvd_zero`), so no finite gcd
computation is forced into the kernel; the `#eval` above exhibits the nontrivial
`c = 1` witness computationally. -/
example : ∑ i, (![6, 10, 15] : Fin 3 → ℤ) i * solve 3 ![6, 10, 15] 0 i = 0 :=
  solve_spec 3 ![6, 10, 15] 0 (dvd_zero _)

end Hilbert10OQ04OQ03OQ01
