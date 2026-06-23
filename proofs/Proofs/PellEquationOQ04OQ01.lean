import Mathlib

/-!
# Pell OQ-04-OQ-01: Complete finiteness classification of `x² − D y² = N`

## The open question

The parent entry `pell-equation-oq-04` (`PellEquationOQ04.lean`) develops the general norm
form `x² − D y² = N`: Brahmagupta multiplicativity, the Pell group of norm-`1` units, the
group action on the `N`-solutions, and *infinitude from a single positive seed*. It explicitly
left open the **classification side** ("how many orbit classes a given `N` has … is deeper and
not attempted here"). The most basic classification question is the **finiteness dichotomy**:

> For which right-hand sides `N` is the solution set of `x² − D y² = N` finite?

This entry settles that completely for every positive non-square `D`.

## Main results

Write `S_N = {(x, y) : ℤ × ℤ | x² − D y² = N}`. For a positive non-square `D`:

* `solutions_zero` — **the only finite *nonempty* case is `N = 0`**, where `S_0 = {(0,0)}` is the
  single trivial point (non-squareness forces `x = y = 0`, via `Zsqrtd.norm_eq_zero`).
* `solutions_infinite` — if `N ≠ 0` and `S_N` is nonempty, then `S_N` is **infinite**: a single
  solution, pushed around the orbit of a fundamental unit, yields infinitely many.
* `empty_or_infinite` — consequently, for `N ≠ 0`, `S_N` is **empty or infinite**.
* `infinite_iff` — **the clean equivalence**: `S_N` is infinite `⟺ N ≠ 0 ∧ S_N` nonempty.
* `nonempty_finite_iff_zero` — a nonempty `S_N` is finite `⟺ N = 0`.
* `solution_set_trichotomy` — **the headline trichotomy**: every `S_N` is *empty*, the *single
  point `{(0,0)}`* (exactly when `N = 0`), or *infinite*. There is no other possibility.

The two engines are Mathlib's `Pell.exists_of_not_isSquare` (a nontrivial unit exists for any
positive non-square `D`) and `Zsqrtd.norm_eq_zero` (the norm form vanishes only at the origin).
The orbit machinery is re-derived locally so the file is **self-contained** (imports only
Mathlib), mirroring the parent's `comp`/`orbit` constructions.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

namespace PellEquationOQ04OQ01

/-- The **norm form** `normForm D x y = x² − D y²`, the norm of `x + y√D` in `ℤ[√D]`. -/
def normForm (D x y : ℤ) : ℤ := x ^ 2 - D * y ^ 2

/-- **Composition** of integer points (multiplication in `ℤ[√D]`):
`(x + y√D)(u + v√D) = (xu + Dyv) + (xv + yu)√D`. -/
def comp (D : ℤ) (p q : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 * q.1 + D * p.2 * q.2, p.1 * q.2 + p.2 * q.1)

/-- **Brahmagupta multiplicativity**, packaged for `comp`: the norm of a product is the product
of the norms. -/
theorem normForm_comp (D : ℤ) (p q : ℤ × ℤ) :
    normForm D (comp D p q).1 (comp D p q).2
      = normForm D p.1 p.2 * normForm D q.1 q.2 := by
  simp only [normForm, comp]; ring

/-- The norm form is invariant under taking absolute values of both coordinates
(`|x|² = x²`). -/
theorem normForm_abs (D x y : ℤ) : normForm D |x| |y| = normForm D x y := by
  simp only [normForm, sq_abs]

/-! ## Orbit of a seed under a unit (re-derived compactly) -/

/-- The **orbit** of a seed `(a, b)` under repeated composition with a fixed unit `(u, v)`. -/
def orbit (D u v a b : ℤ) : ℕ → ℤ × ℤ
  | 0 => (a, b)
  | (k + 1) => comp D (orbit D u v a b k) (u, v)

/-- Every point of the orbit of an `N`-solution is again an `N`-solution. -/
theorem orbit_sol {D u v a b N : ℤ} (huv : normForm D u v = 1) (hab : normForm D a b = N) :
    ∀ k, normForm D (orbit D u v a b k).1 (orbit D u v a b k).2 = N := by
  intro k
  induction k with
  | zero => simpa [orbit] using hab
  | succ k ih =>
      have hstep : normForm D (orbit D u v a b (k + 1)).1 (orbit D u v a b (k + 1)).2
           = normForm D (orbit D u v a b k).1 (orbit D u v a b k).2 * normForm D u v := by
        simp only [orbit]; exact normForm_comp D _ (u, v)
      rw [hstep, ih, huv, mul_one]

/-- Positivity is preserved along the orbit when the seed and unit are positive. -/
theorem orbit_pos {D u v a b : ℤ} (hD : 1 ≤ D) (hu : 2 ≤ u) (hv : 1 ≤ v)
    (ha : 1 ≤ a) (hb : 0 ≤ b) :
    ∀ k, 1 ≤ (orbit D u v a b k).1 ∧ 0 ≤ (orbit D u v a b k).2 := by
  intro k
  induction k with
  | zero => exact ⟨ha, hb⟩
  | succ k ih =>
      obtain ⟨h1, h2⟩ := ih
      simp only [orbit, comp]
      refine ⟨?_, ?_⟩
      · nlinarith [mul_le_mul h1 hu (by norm_num : (0:ℤ) ≤ 2) (by linarith : (0:ℤ) ≤ (orbit D u v a b k).1),
          mul_nonneg (mul_nonneg (le_trans zero_le_one hD) h2) (le_trans zero_le_one hv)]
      · nlinarith [mul_nonneg (le_trans zero_le_one h1) (le_trans zero_le_one hv),
          mul_nonneg h2 (by linarith : (0:ℤ) ≤ u)]

/-- The first coordinate strictly increases along the orbit (it at least doubles each step). -/
theorem orbit_fst_strictMono {D u v a b : ℤ} (hD : 1 ≤ D) (hu : 2 ≤ u) (hv : 1 ≤ v)
    (ha : 1 ≤ a) (hb : 0 ≤ b) :
    StrictMono (fun k => (orbit D u v a b k).1) := by
  apply strictMono_nat_of_lt_succ
  intro k
  obtain ⟨h1, h2⟩ := orbit_pos hD hu hv ha hb k
  simp only [orbit, comp]
  nlinarith [mul_le_mul_of_nonneg_left hu (le_trans zero_le_one h1),
    mul_nonneg (mul_nonneg (le_trans zero_le_one hD) h2) (le_trans zero_le_one hv)]

/-- **Infinitude from one positive seed.** If `D ≥ 1` admits a nontrivial unit `(u, v)` with
`u ≥ 2`, `v ≥ 1`, and `x² − D y² = N` has a positive solution `(a, b)` (`a ≥ 1`, `b ≥ 0`), then
the equation has infinitely many solutions. -/
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

/-! ## A fundamental unit exists for positive non-squares -/

/-- **A nontrivial Pell unit exists** for any positive non-square `D`: there are `u ≥ 2`, `v ≥ 1`
with `u² − D v² = 1`. (From Mathlib's `Pell.exists_of_not_isSquare`, normalised by absolute
values.) -/
theorem exists_unit {D : ℤ} (hD : 0 < D) (hsq : ¬ IsSquare D) :
    ∃ u v : ℤ, 2 ≤ u ∧ 1 ≤ v ∧ normForm D u v = 1 := by
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare hD hsq
  have hD1 : 1 ≤ D := by omega
  have hya : 1 ≤ |y| := Int.one_le_abs hy
  have hy2 : 1 ≤ y ^ 2 := by
    nlinarith [sq_abs y, hya, abs_nonneg y, mul_le_mul hya hya zero_le_one (abs_nonneg y)]
  have hDy : 1 ≤ D * y ^ 2 := by nlinarith [mul_le_mul hD1 hy2 zero_le_one (by linarith : (0:ℤ) ≤ D)]
  have hx2 : 2 ≤ x ^ 2 := by nlinarith [hxy, hDy]
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx2
  have hxa : 1 ≤ |x| := Int.one_le_abs hx0
  refine ⟨|x|, |y|, ?_, hya, ?_⟩
  · -- 2 ≤ |x| : from x² ≥ 2 we cannot have |x| ≤ 1
    have hne1 : |x| ≠ 1 := by
      rintro h1
      have : x ^ 2 = 1 := by rw [← sq_abs, h1]; norm_num
      omega
    omega
  · rw [normForm_abs]; simpa only [normForm] using hxy

/-! ## The N = 0 case: only the trivial solution -/

/-- **For a non-square `D`, the only solution of `x² − D y² = 0` is `(0,0)`.** Non-squareness
makes the norm form anisotropic — it vanishes only at the origin (`Zsqrtd.norm_eq_zero`). -/
theorem solutions_zero {D : ℤ} (hsq : ¬ IsSquare D) :
    {p : ℤ × ℤ | normForm D p.1 p.2 = 0} = {(0, 0)} := by
  have hns : ∀ n : ℤ, D ≠ n * n := fun n hn => hsq ⟨n, hn⟩
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · intro h
    simp only [normForm] at h
    have hz : Zsqrtd.norm (⟨x, y⟩ : Zsqrtd D) = 0 := by
      show x * x - D * y * y = 0
      linear_combination h
    have h0 := (Zsqrtd.norm_eq_zero hns (⟨x, y⟩ : Zsqrtd D)).mp hz
    rw [Zsqrtd.ext_iff] at h0
    simpa using h0
  · rintro ⟨rfl, rfl⟩
    simp [normForm]

/-! ## From any nonzero-`N` solution to a positive seed -/

/-- **Normalising a solution to a positive seed.** Given a unit `(u, v)` and a solution `(x, y)`
of `x² − D y² = N` with `N ≠ 0`, there is a *positive* seed `(a, b)` (`a ≥ 1`, `b ≥ 0`) of the
same norm. If `x ≠ 0` take `(|x|, |y|)`; otherwise compose `(0, |y|)` once with the unit. -/
theorem exists_pos_seed {D u v x y N : ℤ} (hD : 1 ≤ D) (hu : 2 ≤ u) (hv : 1 ≤ v)
    (huv : normForm D u v = 1) (hN : N ≠ 0) (hxy : normForm D x y = N) :
    ∃ a b : ℤ, 1 ≤ a ∧ 0 ≤ b ∧ normForm D a b = N := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    have hy : y ≠ 0 := by
      rintro rfl
      apply hN
      have hz : normForm D 0 0 = 0 := by simp [normForm]
      rw [hz] at hxy; exact hxy.symm
    have hya : 1 ≤ |y| := Int.one_le_abs hy
    refine ⟨D * |y| * v, |y| * u, ?_, ?_, ?_⟩
    · calc (1 : ℤ) = 1 * 1 * 1 := by norm_num
        _ ≤ D * |y| * v := by gcongr
    · exact mul_nonneg (abs_nonneg y) (by linarith)
    · simp only [normForm] at huv hxy ⊢
      linear_combination (-D * |y| ^ 2) * huv + hxy + (-D) * (sq_abs y)
  · exact ⟨|x|, |y|, Int.one_le_abs hx, abs_nonneg y, by rw [normForm_abs]; exact hxy⟩

/-! ## The infinitude dichotomy for `N ≠ 0` -/

/-- **A nonempty nonzero-`N` solution set is infinite.** -/
theorem solutions_infinite {D u v N : ℤ} (hD : 1 ≤ D) (hu : 2 ≤ u) (hv : 1 ≤ v)
    (huv : normForm D u v = 1) (hN : N ≠ 0)
    (hne : {p : ℤ × ℤ | normForm D p.1 p.2 = N}.Nonempty) :
    {p : ℤ × ℤ | normForm D p.1 p.2 = N}.Infinite := by
  obtain ⟨⟨x, y⟩, hxy⟩ := hne
  simp only [Set.mem_setOf_eq] at hxy
  obtain ⟨a, b, ha, hb, hab⟩ := exists_pos_seed hD hu hv huv hN hxy
  exact infinite_solutions hD hu hv ha hb huv hab

/-- **Empty-or-infinite** for `N ≠ 0` (given a fundamental unit). -/
theorem empty_or_infinite {D u v N : ℤ} (hD : 1 ≤ D) (hu : 2 ≤ u) (hv : 1 ≤ v)
    (huv : normForm D u v = 1) (hN : N ≠ 0) :
    {p : ℤ × ℤ | normForm D p.1 p.2 = N} = ∅ ∨
      {p : ℤ × ℤ | normForm D p.1 p.2 = N}.Infinite := by
  rcases Set.eq_empty_or_nonempty {p : ℤ × ℤ | normForm D p.1 p.2 = N} with h | h
  · exact Or.inl h
  · exact Or.inr (solutions_infinite hD hu hv huv hN h)

/-! ## The complete classification (positive non-square `D`) -/

/-- **The clean equivalence.** For positive non-square `D`, the solution set of `x² − D y² = N`
is infinite if and only if `N ≠ 0` and the set is nonempty. -/
theorem infinite_iff {D N : ℤ} (hD : 0 < D) (hsq : ¬ IsSquare D) :
    {p : ℤ × ℤ | normForm D p.1 p.2 = N}.Infinite ↔
      (N ≠ 0 ∧ {p : ℤ × ℤ | normForm D p.1 p.2 = N}.Nonempty) := by
  have hD1 : 1 ≤ D := by omega
  obtain ⟨u, v, hu, hv, huv⟩ := exists_unit hD hsq
  constructor
  · intro hinf
    refine ⟨?_, hinf.nonempty⟩
    rintro rfl
    rw [solutions_zero hsq] at hinf
    exact hinf (Set.finite_singleton _)
  · rintro ⟨hN, hne⟩
    exact solutions_infinite hD1 hu hv huv hN hne

/-- **A nonempty solution set is finite iff `N = 0`** (positive non-square `D`). -/
theorem nonempty_finite_iff_zero {D N : ℤ} (hD : 0 < D) (hsq : ¬ IsSquare D)
    (hne : {p : ℤ × ℤ | normForm D p.1 p.2 = N}.Nonempty) :
    {p : ℤ × ℤ | normForm D p.1 p.2 = N}.Finite ↔ N = 0 := by
  constructor
  · intro hfin
    by_contra hN
    exact (infinite_iff hD hsq).mpr ⟨hN, hne⟩ hfin
  · rintro rfl
    rw [solutions_zero hsq]; exact Set.finite_singleton _

/-- **The headline trichotomy.** For positive non-square `D`, every solution set of
`x² − D y² = N` is exactly one of: empty, the single point `{(0,0)}` (which happens precisely
when `N = 0`), or infinite. -/
theorem solution_set_trichotomy {D N : ℤ} (hD : 0 < D) (hsq : ¬ IsSquare D) :
    {p : ℤ × ℤ | normForm D p.1 p.2 = N} = ∅ ∨
      {p : ℤ × ℤ | normForm D p.1 p.2 = N} = {(0, 0)} ∨
      {p : ℤ × ℤ | normForm D p.1 p.2 = N}.Infinite := by
  rcases eq_or_ne N 0 with rfl | hN
  · exact Or.inr (Or.inl (solutions_zero hsq))
  · have hD1 : 1 ≤ D := by omega
    obtain ⟨u, v, hu, hv, huv⟩ := exists_unit hD hsq
    rcases empty_or_infinite hD1 hu hv huv hN with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)

/-! ## Worked instances -/

/-- `x² − 2y² = 0` has only the trivial solution `(0,0)` (since `2` is not a square). -/
example : {p : ℤ × ℤ | normForm 2 p.1 p.2 = 0} = {(0, 0)} :=
  solutions_zero Int.prime_two.not_isSquare

/-- **`x² − 2y² = 7` has infinitely many integer solutions** — `7 ≠ 0` and `(3, 1)` is a
solution (`9 − 2 = 7`), so by the classification the set is infinite. -/
example : {p : ℤ × ℤ | normForm 2 p.1 p.2 = 7}.Infinite :=
  (infinite_iff (by norm_num) Int.prime_two.not_isSquare).mpr
    ⟨by norm_num, ⟨(3, 1), by norm_num [normForm]⟩⟩

/-- **`x² − 2y² = 2` has infinitely many integer solutions** — witness `(2, 1)` (`4 − 2 = 2`). -/
example : {p : ℤ × ℤ | normForm 2 p.1 p.2 = 2}.Infinite :=
  (infinite_iff (by norm_num) Int.prime_two.not_isSquare).mpr
    ⟨by norm_num, ⟨(2, 1), by norm_num [normForm]⟩⟩

end PellEquationOQ04OQ01
