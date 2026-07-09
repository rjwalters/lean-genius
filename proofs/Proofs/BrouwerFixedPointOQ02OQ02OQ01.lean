/-
# Brouwer Fixed Point — OQ-02-OQ-02-OQ-01: a priori / a posteriori error estimates for contraction iteration

The parent `BrouwerFixedPointOQ02OQ02` studies the query complexity of finding
approximate fixed points of contractions, proving the *a posteriori-free* error
bound `|xₙ − x*| ≤ Lⁿ·|x₀ − x*|` (which presupposes knowledge of the unknown
distance `|x₀ − x*|`).  This child supplies the two estimates that make the
contraction iteration *practically computable*, both standard consequences of the
Banach fixed-point setup and both absent from the parent:

  * `apriori_estimate`     — `|xₙ − x*| ≤ Lⁿ/(1−L) · |x₁ − x₀|`.  The bound is
    expressed entirely in terms of the *first step* `|x₁ − x₀|`, computable before
    iterating; it answers "how many steps for accuracy ε?" without knowing `x*`.
  * `aposteriori_estimate` — `|xₙ₊₁ − x*| ≤ L/(1−L) · |xₙ₊₁ − xₙ|`.  The bound
    uses only the *latest step* `|xₙ₊₁ − xₙ|`, giving a computable stopping
    criterion: iterate until the increment is below `(1−L)/L · ε`.

Both follow from the geometric decay `|xₙ − x*| ≤ Lⁿ·|x₀ − x*|` (`iterate_dist`,
reproved here self-containedly) together with the one-step distance estimate
`(1−L)·|x₀ − x*| ≤ |x₁ − x₀|` (`initial_dist`).  We also record the Lipschitz
composition law `|g(f x) − g(f y)| ≤ L₂L₁·|x − y|` (`lipschitz_comp`) and its
corollary that a composite of contractions is a contraction (`contraction_comp`),
the structural fact behind iterating several maps.

All results are fully machine-checked (0 axioms, 0 sorries) and self-contained:
the contraction is given abstractly as `∀ x y, |f x − f y| ≤ L·|x − y|` with a
fixed point `f x* = x*` and the iteration `xₙ₊₁ = f xₙ`.

Reference: Banach (1922); see also the query-complexity parent OQ-02-OQ-02.
-/

import Mathlib

namespace BrouwerOQ02OQ02OQ01

/-- **Geometric decay of the iteration error.**  For a contraction `f` with
    constant `L ≥ 0`, fixed point `x*`, and iteration `xₙ₊₁ = f xₙ`,
    `|xₙ − x*| ≤ Lⁿ · |x₀ − x*|`.  Reproved self-containedly (the parent states
    the analogous bound on `[0,1]`). -/
theorem iterate_dist (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) (n : ℕ) :
    |x n - xstar| ≤ L ^ n * |x 0 - xstar| := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := hf (x n) xstar
    rw [hfp, ← hx n] at h
    calc |x (n + 1) - xstar| ≤ L * |x n - xstar| := h
      _ ≤ L * (L ^ n * |x 0 - xstar|) := mul_le_mul_of_nonneg_left ih hL0
      _ = L ^ (n + 1) * |x 0 - xstar| := by ring

/-- **One-step distance estimate.**  `(1 − L)·|x₀ − x*| ≤ |x₁ − x₀|`, equivalently
    `|x₀ − x*| ≤ |x₁ − x₀| / (1 − L)`: the unknown distance to the fixed point is
    controlled by the (computable) first increment. -/
theorem initial_dist (f : ℝ → ℝ) (L : ℝ) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) :
    |x 0 - xstar| ≤ |x 1 - x 0| / (1 - L) := by
  have hcontr : (0 : ℝ) < 1 - L := by linarith
  have ht : |x 0 - xstar| ≤ |x 0 - x 1| + |x 1 - xstar| := abs_sub_le _ _ _
  rw [abs_sub_comm (x 0) (x 1)] at ht
  have hL : |x 1 - xstar| ≤ L * |x 0 - xstar| := by
    have h := hf (x 0) xstar
    rw [hfp, ← hx 0] at h
    exact h
  rw [le_div_iff₀ hcontr]
  nlinarith [ht, hL]

/-- **A priori error estimate.**  `|xₙ − x*| ≤ Lⁿ/(1−L) · |x₁ − x₀|`.  Expressed
    purely in terms of the first increment `|x₁ − x₀|`, so the number of
    iterations needed for a target accuracy can be bounded *before* iterating. -/
theorem apriori_estimate (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) (n : ℕ) :
    |x n - xstar| ≤ L ^ n / (1 - L) * |x 1 - x 0| := by
  have hcontr : (0 : ℝ) < 1 - L := by linarith
  have h1 := iterate_dist f L hL0 hf x hx xstar hfp n
  have h2 := initial_dist f L hL1 hf x hx xstar hfp
  have hLn : (0 : ℝ) ≤ L ^ n := pow_nonneg hL0 n
  calc |x n - xstar| ≤ L ^ n * |x 0 - xstar| := h1
    _ ≤ L ^ n * (|x 1 - x 0| / (1 - L)) := mul_le_mul_of_nonneg_left h2 hLn
    _ = L ^ n / (1 - L) * |x 1 - x 0| := by ring

/-- **A posteriori error estimate.**  `|xₙ₊₁ − x*| ≤ L/(1−L) · |xₙ₊₁ − xₙ|`.
    Expressed in terms of the latest increment, giving a computable stopping
    criterion: stop once `|xₙ₊₁ − xₙ| ≤ (1−L)/L · ε`. -/
theorem aposteriori_estimate (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) (n : ℕ) :
    |x (n + 1) - xstar| ≤ L / (1 - L) * |x (n + 1) - x n| := by
  have hcontr : (0 : ℝ) < 1 - L := by linarith
  have hstep := hf (x n) xstar
  rw [hfp, ← hx n] at hstep
  have ht : |x n - xstar| ≤ |x n - x (n + 1)| + |x (n + 1) - xstar| := abs_sub_le _ _ _
  rw [abs_sub_comm (x n) (x (n + 1))] at ht
  have hLt := mul_le_mul_of_nonneg_left ht hL0
  have key : (1 - L) * |x (n + 1) - xstar| ≤ L * |x (n + 1) - x n| := by
    nlinarith [hstep, hLt]
  rw [div_mul_eq_mul_div, le_div_iff₀ hcontr]
  nlinarith [key]

/-- **Lipschitz composition law.**  If `f` is `L₁`-Lipschitz and `g` is
    `L₂`-Lipschitz (`L₂ ≥ 0`), then `g ∘ f` is `L₂L₁`-Lipschitz. -/
theorem lipschitz_comp (f g : ℝ → ℝ) (L1 L2 : ℝ) (hL2 : 0 ≤ L2)
    (hf : ∀ x y, |f x - f y| ≤ L1 * |x - y|)
    (hg : ∀ x y, |g x - g y| ≤ L2 * |x - y|) (x y : ℝ) :
    |g (f x) - g (f y)| ≤ (L2 * L1) * |x - y| := by
  calc |g (f x) - g (f y)| ≤ L2 * |f x - f y| := hg (f x) (f y)
    _ ≤ L2 * (L1 * |x - y|) := mul_le_mul_of_nonneg_left (hf x y) hL2
    _ = (L2 * L1) * |x - y| := by ring

/-- **A composite of contractions is a contraction.**  If `f` is an `L₁`-contraction
    and `g` an `L₂`-contraction (`0 ≤ L₁, L₂ < 1`), then `g ∘ f` is a contraction
    with constant `L₂L₁ < 1`. -/
theorem contraction_comp (f g : ℝ → ℝ) (L1 L2 : ℝ)
    (hL1_0 : 0 ≤ L1) (hL1_1 : L1 < 1) (hL2_0 : 0 ≤ L2) (hL2_1 : L2 < 1)
    (hf : ∀ x y, |f x - f y| ≤ L1 * |x - y|)
    (hg : ∀ x y, |g x - g y| ≤ L2 * |x - y|) :
    L2 * L1 < 1 ∧ ∀ x y, |g (f x) - g (f y)| ≤ (L2 * L1) * |x - y| :=
  ⟨by nlinarith, fun x y => lipschitz_comp f g L1 L2 hL2_0 hf hg x y⟩

/-! ## Composing a whole family of maps

The two-map law `contraction_comp` above is the base case of a general fact: composing
an ordered *list* of maps `[f₀, f₁, …, f_{m-1}]`, with individual Lipschitz constants
`[L₀, …, L_{m-1}]`, yields a map whose Lipschitz constant is the **product** `∏ Lᵢ`, and
which is a contraction whenever the family is non-empty and every `Lᵢ < 1`.  Each map is
bundled with its constant as a pair `(fᵢ, Lᵢ) : (ℝ → ℝ) × ℝ`; the composite applies the
head last (outermost), matching `lipschitz_comp`'s `g ∘ f`. -/

/-- Apply an ordered list of maps to `x`, head applied last (outermost). -/
def applyAll : List ((ℝ → ℝ) × ℝ) → ℝ → ℝ
  | [],        x => x
  | p :: rest, x => p.1 (applyAll rest x)

/-- A product of reals each in `[0, 1]` is at most `1`. -/
theorem list_prod_le_one :
    ∀ (Ls : List ℝ), (∀ L ∈ Ls, 0 ≤ L) → (∀ L ∈ Ls, L ≤ 1) → Ls.prod ≤ 1
  | [], _, _ => by simp
  | a :: rest, hpos, hle => by
      rw [List.prod_cons]
      have ha0 : 0 ≤ a := hpos a (by simp)
      have hr0 : ∀ L ∈ rest, 0 ≤ L := fun L h => hpos L (List.mem_cons_of_mem _ h)
      have hr1 : ∀ L ∈ rest, L ≤ 1 := fun L h => hle L (List.mem_cons_of_mem _ h)
      have hrest := list_prod_le_one rest hr0 hr1
      have ha1 : a ≤ 1 := hle a (by simp)
      nlinarith [mul_nonneg ha0 (by linarith : (0:ℝ) ≤ 1 - rest.prod), ha1, hrest]

/-- A product of reals each in `[0, 1)` over a **non-empty** list is `< 1`. -/
theorem list_prod_lt_one :
    ∀ (Ls : List ℝ), Ls ≠ [] → (∀ L ∈ Ls, 0 ≤ L) → (∀ L ∈ Ls, L < 1) → Ls.prod < 1
  | [], hne, _, _ => absurd rfl hne
  | a :: rest, _, hpos, hlt => by
      rw [List.prod_cons]
      have ha0 : 0 ≤ a := hpos a (by simp)
      have ha1 : a < 1 := hlt a (by simp)
      have hr0 : ∀ L ∈ rest, 0 ≤ L := fun L h => hpos L (List.mem_cons_of_mem _ h)
      have hr1 : ∀ L ∈ rest, L ≤ 1 := fun L h => le_of_lt (hlt L (List.mem_cons_of_mem _ h))
      have hrest_le := list_prod_le_one rest hr0 hr1
      nlinarith [mul_le_mul_of_nonneg_left hrest_le ha0, ha1]

/-- **Lipschitz composition law for a list of maps.**  If each `(fᵢ, Lᵢ)` in the list is
    `Lᵢ`-Lipschitz with `Lᵢ ≥ 0`, then the composite `applyAll` is Lipschitz with constant
    the product `∏ Lᵢ`.  Generalises `lipschitz_comp` from two maps to arbitrarily many. -/
theorem lipschitz_comp_list :
    ∀ (fL : List ((ℝ → ℝ) × ℝ)) (x y : ℝ),
      (∀ p ∈ fL, 0 ≤ p.2) →
      (∀ p ∈ fL, ∀ a b, |p.1 a - p.1 b| ≤ p.2 * |a - b|) →
      |applyAll fL x - applyAll fL y| ≤ (fL.map Prod.snd).prod * |x - y|
  | [], x, y, _, _ => by simp [applyAll]
  | p :: rest, x, y, hpos, hlip => by
      have hp0 : 0 ≤ p.2 := hpos p (by simp)
      have hpl := hlip p (by simp)
      have ih := lipschitz_comp_list rest x y
        (fun q h => hpos q (List.mem_cons_of_mem _ h))
        (fun q h => hlip q (List.mem_cons_of_mem _ h))
      simp only [applyAll, List.map_cons, List.prod_cons]
      calc |p.1 (applyAll rest x) - p.1 (applyAll rest y)|
          ≤ p.2 * |applyAll rest x - applyAll rest y| := hpl _ _
        _ ≤ p.2 * ((rest.map Prod.snd).prod * |x - y|) := mul_le_mul_of_nonneg_left ih hp0
        _ = p.2 * (rest.map Prod.snd).prod * |x - y| := by ring

/-- **A composite of a list of contractions is a contraction.**  For a non-empty family
    where every `(fᵢ, Lᵢ)` is an `Lᵢ`-contraction (`0 ≤ Lᵢ < 1`), the composite `applyAll`
    is a contraction with constant `∏ Lᵢ < 1`.  This is the structural fact behind
    iterating several distinct maps, generalising `contraction_comp`. -/
theorem contraction_comp_list (fL : List ((ℝ → ℝ) × ℝ)) (hne : fL ≠ [])
    (hpos : ∀ p ∈ fL, 0 ≤ p.2) (hlt : ∀ p ∈ fL, p.2 < 1)
    (hlip : ∀ p ∈ fL, ∀ a b, |p.1 a - p.1 b| ≤ p.2 * |a - b|) :
    (fL.map Prod.snd).prod < 1 ∧
      ∀ x y, |applyAll fL x - applyAll fL y| ≤ (fL.map Prod.snd).prod * |x - y| := by
  have hne' : fL.map Prod.snd ≠ [] := by simpa using hne
  have hpos' : ∀ L ∈ fL.map Prod.snd, 0 ≤ L := by
    intro L hL; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hL; exact hpos p hp
  have hlt' : ∀ L ∈ fL.map Prod.snd, L < 1 := by
    intro L hL; obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hL; exact hlt p hp
  exact ⟨list_prod_lt_one _ hne' hpos' hlt',
    fun x y => lipschitz_comp_list fL x y hpos hlip⟩

/-! ### Well-definedness of `x*` and optimality of the geometric bound

Every estimate above is stated for a *given* fixed point `x*`, but for `L < 1` a
contraction has **at most one** fixed point, so the object `x*` the estimates refer
to is unambiguous.  Conversely the geometric decay `iterate_dist` is **best
possible**: the linear map `t ↦ L·t` is an `L`-contraction (with equality in the
Lipschitz bound) whose iteration `xₙ = Lⁿ·x₀` from any `x₀` satisfies
`|xₙ − x*| = Lⁿ·|x₀ − x*|` exactly. -/

/-- **Uniqueness of the fixed point.**  A contraction with constant `L < 1` has at
    most one fixed point: if `f p = p` and `f q = q` then `|p − q| = |f p − f q| ≤
    L·|p − q|`, so `(1 − L)·|p − q| ≤ 0` with `1 − L > 0`, forcing `p = q`.  This is
    what makes the `x*` in every estimate above well-defined. -/
theorem fixed_point_unique (f : ℝ → ℝ) (L : ℝ) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (p q : ℝ) (hp : f p = p) (hq : f q = q) : p = q := by
  have h := hf p q
  rw [hp, hq] at h
  have hnn : 0 ≤ |p - q| := abs_nonneg _
  have hq0 : |p - q| = 0 := by
    by_contra hne
    have hpos : 0 < |p - q| := lt_of_le_of_ne hnn (Ne.symm hne)
    nlinarith [h, hpos, hL1]
  exact sub_eq_zero.mp (abs_eq_zero.mp hq0)

/-- **Sharpness of the geometric decay `iterate_dist`.**  The bound
    `|xₙ − x*| ≤ Lⁿ·|x₀ − x*|` is attained, so it cannot be improved.  Witness: the
    linear map `t ↦ L·t` (`L ≥ 0`) is an `L`-contraction *with equality*, has fixed
    point `0`, and its iteration from `x₀` is `xₙ = Lⁿ·x₀`; for it the error decays
    at *exactly* the geometric rate.  The four conjuncts record, in order: the exact
    Lipschitz identity, the fixed-point equation, the iteration recurrence, and the
    equality form of the decay bound. -/
theorem iterate_dist_sharp (L : ℝ) (hL0 : 0 ≤ L) (x0 : ℝ) :
    (∀ a b : ℝ, |L * a - L * b| = L * |a - b|) ∧
    L * 0 = 0 ∧
    (∀ k : ℕ, L ^ (k + 1) * x0 = L * (L ^ k * x0)) ∧
    (∀ n : ℕ, |L ^ n * x0 - 0| = L ^ n * |x0 - 0|) := by
  refine ⟨fun a b => ?_, by ring, fun k => by rw [pow_succ]; ring, fun n => ?_⟩
  · rw [← mul_sub, abs_mul, abs_of_nonneg hL0]
  · rw [sub_zero, sub_zero, abs_mul, abs_of_nonneg (pow_nonneg hL0 n)]

end BrouwerOQ02OQ02OQ01
