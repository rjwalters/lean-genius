import Mathlib

/-!
# Pell's Equation OQ-04: The General Norm Form `x² − D y² = N`

## The Open Question

The parent (`PellEquation.lean`) asks about the **implications of generalizing to the
Pell-like equations `x² − D y² = N` for an arbitrary right-hand side `N`** (not just the
classical `N = 1`). The sibling entries pin down the `N = 1` theory (the fundamental solution,
its size, the linear recurrence) and the `N = −1` theory (negative Pell `x² − 2y² = −1`). This
file develops the structural theory that ties all of these together for *every* `N`.

## What this file proves

The organizing object is the **integral binary quadratic form** (the *norm form*)
`normForm D x y = x² − D y²`, the norm of `x + y√D` in `ℤ[√D]`.

* `normForm_mul` — the **Brahmagupta–Fibonacci identity**: the norm form is *multiplicative*,
  `normForm D (xu + Dyv) (xv + yu) = normForm D x y · normForm D u v`. This single polynomial
  identity is the engine for everything below.
* `sol_comp` — **composition of solutions**: a solution of `x² − D y² = M` composes with a
  solution of `x² − D y² = N` to give a solution of `x² − D y² = MN`.
* `PellUnit` and its `CommGroup` instance — the norm-`1` solutions form an **abelian group**
  (the *Pell group*) under composition, with identity `(1, 0)` and inverse `(x, y) ↦ (x, −y)`.
* `unit_smul_sol` — the Pell group **acts on the solution set of every `N`**: composing an
  `N`-solution with a unit yields another `N`-solution. So the `N`-solutions are partitioned
  into orbits under this group action.
* `infinite_solutions` — **infinitude from a single seed**: if `D ≥ 1` admits a nontrivial unit
  `(u, v)` (`u ≥ 2`, `v ≥ 1`) and `x² − D y² = N` has one positive solution, then it has
  *infinitely many* solutions — the orbit of any seed under the unit is infinite. (For a positive
  non-square `D`, such a unit always exists by `Pell.exists_of_not_isSquare`.)

Two corollaries record the link to the sibling equations:

* `sol_neg_one_comp` — two solutions of the negative Pell form `x² − D y² = −1` compose to a
  solution of `x² − D y² = +1` (norm `(−1)(−1) = 1`).
* `normForm_neg_snd` / `normForm_neg_fst` — the form is invariant under sign changes of either
  coordinate (the conjugation symmetries).

**Honest scope.** The *classification* of orbits (how many orbit classes a given `N` has, the
genus theory of forms) is deeper and not attempted here; this file establishes the multiplicative
/ group-action skeleton and the dichotomy "no solutions, or infinitely many".

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace PellEquationOQ04

/-- The **norm form** of the Pell-like equation: `normForm D x y = x² − D y²`, the norm of
`x + y√D` in the ring `ℤ[√D]`. The equation `x² − D y² = N` is `normForm D x y = N`. -/
def normForm (D x y : ℤ) : ℤ := x ^ 2 - D * y ^ 2

/-- **Composition** of two integer points, i.e. multiplication in `ℤ[√D]`:
`(x + y√D)(u + v√D) = (xu + Dyv) + (xv + yu)√D`. -/
def comp (D : ℤ) (p q : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * q.1 + D * p.2 * q.2, p.1 * q.2 + p.2 * q.1)

@[simp] theorem comp_fst (D : ℤ) (p q : ℤ × ℤ) :
    (comp D p q).1 = p.1 * q.1 + D * p.2 * q.2 := rfl

@[simp] theorem comp_snd (D : ℤ) (p q : ℤ × ℤ) :
    (comp D p q).2 = p.1 * q.2 + p.2 * q.1 := rfl

/-! ## Multiplicativity of the norm form (Brahmagupta–Fibonacci) -/

/-- **The Brahmagupta–Fibonacci identity.** The norm form is multiplicative: the norm of a
product is the product of the norms. This is a pure polynomial identity — the cross terms
`2Dxyuv` cancel — and is the engine behind every result in this file. -/
theorem normForm_mul (D x y u v : ℤ) :
    normForm D (x * u + D * y * v) (x * v + y * u) = normForm D x y * normForm D u v := by
  simp only [normForm]; ring

/-- The norm of `comp` is the product of the norms (packaged for pairs). -/
theorem normForm_comp (D : ℤ) (p q : ℤ × ℤ) :
    normForm D (comp D p q).1 (comp D p q).2 = normForm D p.1 p.2 * normForm D q.1 q.2 := by
  simp only [comp_fst, comp_snd]; exact normForm_mul D p.1 p.2 q.1 q.2

/-- **Composition of solutions.** A solution of `x² − D y² = M` and a solution of
`x² − D y² = N` compose to a solution of `x² − D y² = M·N`. -/
theorem sol_comp {D M N x y u v : ℤ}
    (h1 : normForm D x y = M) (h2 : normForm D u v = N) :
    normForm D (x * u + D * y * v) (x * v + y * u) = M * N := by
  rw [normForm_mul, h1, h2]

/-! ## Conjugation symmetries -/

/-- The norm form is invariant under negating the second coordinate (conjugation `y ↦ −y`). -/
@[simp] theorem normForm_neg_snd (D x y : ℤ) : normForm D x (-y) = normForm D x y := by
  simp only [normForm]; ring

/-- The norm form is invariant under negating the first coordinate. -/
@[simp] theorem normForm_neg_fst (D x y : ℤ) : normForm D (-x) y = normForm D x y := by
  simp only [normForm]; ring

/-! ## The Pell group of norm-`1` solutions -/

/-- A `comp`-algebra fact: composition is **commutative**. -/
theorem comp_comm (D : ℤ) (p q : ℤ × ℤ) : comp D p q = comp D q p := by
  rw [Prod.ext_iff]; refine ⟨?_, ?_⟩ <;> simp only [comp_fst, comp_snd] <;> ring

/-- Composition is **associative**. -/
theorem comp_assoc (D : ℤ) (p q r : ℤ × ℤ) :
    comp D (comp D p q) r = comp D p (comp D q r) := by
  rw [Prod.ext_iff]; refine ⟨?_, ?_⟩ <;> simp only [comp_fst, comp_snd] <;> ring

/-- `(1, 0)` is a left identity for composition. -/
@[simp] theorem one_comp (D : ℤ) (p : ℤ × ℤ) : comp D (1, 0) p = p := by
  rw [Prod.ext_iff]; refine ⟨?_, ?_⟩ <;> simp

/-- `(1, 0)` is a right identity for composition. -/
@[simp] theorem comp_one (D : ℤ) (p : ℤ × ℤ) : comp D p (1, 0) = p := by
  rw [Prod.ext_iff]; refine ⟨?_, ?_⟩ <;> simp

/-- **The Pell group** of `D`: integer points `(x, y)` with `x² − D y² = 1`, i.e. the norm-`1`
solutions (units of `ℤ[√D]`). -/
def PellUnit (D : ℤ) : Type := { p : ℤ × ℤ // normForm D p.1 p.2 = 1 }

namespace PellUnit
variable {D : ℤ}

/-- The norm-`1` solutions form an **abelian group** under composition: identity `(1, 0)`,
inverse `(x, y) ↦ (x, −y)`. This is the structural heart of Pell theory. -/
instance : CommGroup (PellUnit D) where
  one := ⟨(1, 0), by simp [normForm]⟩
  mul a b := ⟨comp D a.1 b.1, by rw [normForm_comp, a.2, b.2]; ring⟩
  inv a := ⟨(a.1.1, -a.1.2), by
    show normForm D a.1.1 (-a.1.2) = 1
    rw [normForm_neg_snd]; exact a.2⟩
  mul_assoc a b c := Subtype.ext (comp_assoc D a.1 b.1 c.1)
  one_mul a := Subtype.ext (one_comp D a.1)
  mul_one a := Subtype.ext (comp_one D a.1)
  mul_comm a b := Subtype.ext (comp_comm D a.1 b.1)
  inv_mul_cancel a := by
    obtain ⟨⟨x, y⟩, hxy⟩ := a
    apply Subtype.ext
    show comp D (x, -y) (x, y) = (1, 0)
    simp only [normForm] at hxy
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · show x * x + D * (-y) * y = 1
      linear_combination hxy
    · show x * y + (-y) * x = 0
      ring

end PellUnit

/-! ## The Pell group acts on the solutions of an arbitrary `N` -/

/-- **The Pell group acts on the `N`-solutions.** Composing a solution of `x² − D y² = N`
with a norm-`1` unit `(u, v)` yields another solution of `x² − D y² = N` (since `N · 1 = N`).
Hence the solution set of every `N` is a union of orbits under the Pell group. -/
theorem unit_smul_sol {D N a b u v : ℤ}
    (hab : normForm D a b = N) (huv : normForm D u v = 1) :
    normForm D (a * u + D * b * v) (a * v + b * u) = N := by
  rw [sol_comp hab huv, mul_one]

/-- **Two negative-Pell solutions compose to a Pell solution.** If `x² − D y² = −1` has two
solutions, their composite has norm `(−1)(−1) = 1`. This is the bridge from the sibling
negative-Pell entries (`x² − 2y² = −1`) back to the classical Pell equation. -/
theorem sol_neg_one_comp {D x y u v : ℤ}
    (h1 : normForm D x y = -1) (h2 : normForm D u v = -1) :
    normForm D (x * u + D * y * v) (x * v + y * u) = 1 := by
  rw [sol_comp h1 h2]; ring

/-! ## Infinitude of solutions from a single seed -/

/-- The **orbit** of a seed `(a, b)` under repeated composition with a fixed unit `(u, v)`:
`orbit 0 = (a, b)` and `orbit (k+1) = orbit k · (u, v)`. -/
def orbit (D u v a b : ℤ) : ℕ → ℤ × ℤ
  | 0 => (a, b)
  | (k + 1) => comp D (orbit D u v a b k) (u, v)

/-- Every point in the orbit of an `N`-solution is again an `N`-solution. -/
theorem orbit_sol {D u v a b N : ℤ} (huv : normForm D u v = 1) (hab : normForm D a b = N) :
    ∀ k, normForm D (orbit D u v a b k).1 (orbit D u v a b k).2 = N := by
  intro k
  induction k with
  | zero => simpa [orbit] using hab
  | succ k ih =>
      have : normForm D (orbit D u v a b (k + 1)).1 (orbit D u v a b (k + 1)).2
           = normForm D (orbit D u v a b k).1 (orbit D u v a b k).2 * normForm D u v := by
        simp only [orbit]; exact normForm_comp D _ (u, v)
      rw [this, ih, huv, mul_one]

/-- Positivity is preserved along the orbit when the seed and unit are positive: each orbit
point has first coordinate `≥ 1` and second coordinate `≥ 0`. -/
theorem orbit_pos {D u v a b : ℤ} (hD : 1 ≤ D) (hu : 2 ≤ u) (hv : 1 ≤ v)
    (ha : 1 ≤ a) (hb : 0 ≤ b) :
    ∀ k, 1 ≤ (orbit D u v a b k).1 ∧ 0 ≤ (orbit D u v a b k).2 := by
  intro k
  induction k with
  | zero => exact ⟨ha, hb⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [orbit, comp_fst, comp_snd]
      refine ⟨?_, ?_⟩
      · nlinarith [mul_le_mul h1 hu (by norm_num : (0:ℤ) ≤ 2) (by linarith : (0:ℤ) ≤ (orbit D u v a b k).1),
          mul_nonneg (mul_nonneg (le_trans zero_le_one hD) h2) (le_trans zero_le_one hv)]
      · nlinarith [mul_nonneg (le_trans zero_le_one h1) (le_trans zero_le_one hv),
          mul_nonneg h2 (by linarith : (0:ℤ) ≤ u)]

/-- The first coordinate strictly increases along the orbit (it at least doubles each step,
since the unit has `u ≥ 2`). -/
theorem orbit_fst_strictMono {D u v a b : ℤ} (hD : 1 ≤ D) (hu : 2 ≤ u) (hv : 1 ≤ v)
    (ha : 1 ≤ a) (hb : 0 ≤ b) :
    StrictMono (fun k => (orbit D u v a b k).1) := by
  apply strictMono_nat_of_lt_succ
  intro k
  obtain ⟨h1, h2⟩ := orbit_pos hD hu hv ha hb k
  simp only [orbit, comp_fst]
  nlinarith [mul_le_mul_of_nonneg_left hu (le_trans zero_le_one h1),
    mul_nonneg (mul_nonneg (le_trans zero_le_one hD) h2) (le_trans zero_le_one hv)]

/-- **Infinitude from one seed.** If `D ≥ 1` admits a nontrivial unit `(u, v)` with `u ≥ 2`,
`v ≥ 1`, and `x² − D y² = N` has a positive solution `(a, b)` (`a ≥ 1`, `b ≥ 0`), then the
equation has **infinitely many** solutions: the orbit of `(a, b)` under the unit is an infinite
set of solutions. (For a positive non-square `D`, a suitable unit always exists.) -/
theorem infinite_solutions {D u v a b N : ℤ}
    (hD : 1 ≤ D) (hu : 2 ≤ u) (hv : 1 ≤ v) (ha : 1 ≤ a) (hb : 0 ≤ b)
    (huv : normForm D u v = 1) (hab : normForm D a b = N) :
    {p : ℤ × ℤ | normForm D p.1 p.2 = N}.Infinite := by
  have hmono := orbit_fst_strictMono hD hu hv ha hb
  have hinj : Function.Injective (fun k => orbit D u v a b k) := by
    intro i j hij
    exact hmono.injective (congrArg Prod.fst hij)
  apply Set.infinite_of_injective_forall_mem hinj
  intro k
  simp only [Set.mem_setOf_eq]
  exact orbit_sol huv hab k

/-! ## Worked instances -/

/-- The unit `(3, 2)` solves `x² − 2y² = 1` (`9 − 8 = 1`): the fundamental unit of `ℤ[√2]`. -/
example : normForm 2 3 2 = 1 := by norm_num [normForm]

/-- `(3, 1)` solves `x² − 2y² = 7` (`9 − 2 = 7`). -/
example : normForm 2 3 1 = 7 := by norm_num [normForm]

/-- Composing the seed `(3, 1)` with the unit `(3, 2)` gives `(13, 9)`, again solving
`x² − 2y² = 7` (`169 − 162 = 7`). -/
example : normForm 2 (3 * 3 + 2 * 1 * 2) (3 * 2 + 1 * 3) = 7 := by norm_num [normForm]

/-- **`x² − 2y² = 7` has infinitely many integer solutions** — a concrete consequence of the
general infinitude theorem, instantiated at the seed `(3, 1)` and the unit `(3, 2)`. -/
example : {p : ℤ × ℤ | normForm 2 p.1 p.2 = 7}.Infinite :=
  infinite_solutions (u := 3) (v := 2) (a := 3) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [normForm]) (by norm_num [normForm])

end PellEquationOQ04
