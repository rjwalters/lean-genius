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

/-! ### Existence of the fixed point (closing the standing hypothesis)

Every estimate above takes the fixed point `x*` as a *hypothesis* (`f x* = x*`).
On the complete space `ℝ` that hypothesis is discharged automatically: a
contraction `|f x − f y| ≤ L·|x − y|` with `0 ≤ L < 1` *has* a fixed point, by the
Banach fixed-point theorem.  We bridge the raw real-analytic contraction bound to
Mathlib's `ContractingWith` (via `LipschitzWith.of_dist_le_mul` and
`Real.dist_eq`) and read off existence; combined with `fixed_point_unique` this
upgrades the setup to the full Banach existence-and-uniqueness statement, so `x*`
is a genuine object rather than a standing assumption. -/

/-- **Existence of the fixed point (Banach on `ℝ`).**  A contraction
    `|f x − f y| ≤ L·|x − y|` with `0 ≤ L < 1` on the complete space `ℝ` has a
    fixed point.  This discharges the standing `f x* = x*` hypothesis of every
    estimate above. -/
theorem exists_fixed_point (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    ∃ xstar : ℝ, f xstar = xstar := by
  have hlip : LipschitzWith L.toNNReal f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal L hL0]
    exact hf x y
  have hKlt : L.toNNReal < 1 := by
    have h : (L.toNNReal : ℝ) < 1 := by rw [Real.coe_toNNReal L hL0]; exact hL1
    exact_mod_cast h
  obtain ⟨y, hy, _, _⟩ :=
    ContractingWith.exists_fixedPoint ⟨hKlt, hlip⟩ 0 (edist_ne_top _ _)
  exact ⟨y, hy⟩

/-- **Banach fixed-point theorem on `ℝ` (existence and uniqueness).**  A
    contraction with `0 ≤ L < 1` has a *unique* fixed point: existence from
    `exists_fixed_point`, uniqueness from `fixed_point_unique`.  This is the
    self-contained Banach statement the whole estimate suite rests on. -/
theorem exists_unique_fixed_point (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) :
    ∃! xstar : ℝ, f xstar = xstar := by
  obtain ⟨xstar, hxs⟩ := exists_fixed_point f L hL0 hL1 hf
  exact ⟨xstar, hxs, fun y hy => fixed_point_unique f L hL1 hf y xstar hy hxs⟩

/-! ### Unconditional estimates (no assumed fixed point)

Every estimate above carries the fixed point `x*` as a *hypothesis* `f x* = x*`.
Since `exists_fixed_point` produces that `x*` from the contraction data alone on
the complete space `ℝ`, both practical estimates can be stated **without** any
`x*` input: there is a fixed point `x*` (necessarily the unique one, by
`fixed_point_unique`) for which the a priori / a posteriori bounds hold at every
step.  These are the fully self-contained, hypothesis-free forms — exactly what a
computation using the iteration `xₙ₊₁ = f xₙ` can invoke, knowing only `f`, `L`
and the iterates. -/

/-- **Unconditional a priori estimate.**  With no assumed fixed point: a
    contraction on `ℝ` has a fixed point `x*` for which
    `|xₙ − x*| ≤ Lⁿ/(1−L) · |x₁ − x₀|` at every step.  Produced by threading
    `exists_fixed_point` through `apriori_estimate`; `x*` is the unique fixed
    point by `fixed_point_unique`. -/
theorem apriori_estimate_unconditional (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n)) :
    ∃ xstar : ℝ, f xstar = xstar ∧
      ∀ n, |x n - xstar| ≤ L ^ n / (1 - L) * |x 1 - x 0| := by
  obtain ⟨xstar, hfp⟩ := exists_fixed_point f L hL0 hL1 hf
  exact ⟨xstar, hfp, fun n => apriori_estimate f L hL0 hL1 hf x hx xstar hfp n⟩

/-- **Unconditional a posteriori estimate.**  With no assumed fixed point: a
    contraction on `ℝ` has a fixed point `x*` for which
    `|xₙ₊₁ − x*| ≤ L/(1−L) · |xₙ₊₁ − xₙ|` at every step, the computable stopping
    criterion in its hypothesis-free form.  Produced by threading
    `exists_fixed_point` through `aposteriori_estimate`. -/
theorem aposteriori_estimate_unconditional (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n)) :
    ∃ xstar : ℝ, f xstar = xstar ∧
      ∀ n, |x (n + 1) - xstar| ≤ L / (1 - L) * |x (n + 1) - x n| := by
  obtain ⟨xstar, hfp⟩ := exists_fixed_point f L hL0 hL1 hf
  exact ⟨xstar, hfp, fun n => aposteriori_estimate f L hL0 hL1 hf x hx xstar hfp n⟩

/-! ### A matching a posteriori *lower* bound (two-sided residual control)

Every a posteriori bound above is an *upper* bound: it certifies that a small
increment `|xₙ₊₁ − xₙ|` guarantees a small error `|xₙ₊₁ − x*|`.  The complementary
*lower* bound `|xₙ₊₁ − xₙ| / (1 + L) ≤ |xₙ − x*|` says the increment cannot vastly
*over*-estimate the error either: a nonzero increment forces a genuinely nonzero
error, so the increment is a two-sided proxy for the distance to `x*`.  Together
with `aposteriori_estimate` this pins the error to a constant-factor band around
the observable increment, `|xₙ₊₁ − xₙ|/(1+L) ≤ |xₙ − x*|` and
`|xₙ₊₁ − x*| ≤ L/(1−L)·|xₙ₊₁ − xₙ|`.  Proof: the reverse triangle inequality
`|xₙ₊₁ − xₙ| ≤ |xₙ₊₁ − x*| + |x* − xₙ|` with `|xₙ₊₁ − x*| ≤ L·|xₙ − x*|` gives
`|xₙ₊₁ − xₙ| ≤ (1 + L)·|xₙ − x*|`. -/

/-- **A posteriori lower error bound.**  `|xₙ₊₁ − xₙ| / (1 + L) ≤ |xₙ − x*|`: the
    latest increment is, up to the factor `1 + L`, a *lower* bound on the current
    error, complementing the a posteriori *upper* bound `aposteriori_estimate`.
    Only `0 ≤ L` is needed (no `L < 1`). -/
theorem aposteriori_lower_estimate (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) (n : ℕ) :
    |x (n + 1) - x n| / (1 + L) ≤ |x n - xstar| := by
  have hpos : (0 : ℝ) < 1 + L := by linarith
  have hstep : |x (n + 1) - xstar| ≤ L * |x n - xstar| := by
    have h := hf (x n) xstar
    rw [hfp, ← hx n] at h
    exact h
  have ht : |x (n + 1) - x n| ≤ |x (n + 1) - xstar| + |xstar - x n| := abs_sub_le _ _ _
  rw [abs_sub_comm xstar (x n)] at ht
  rw [div_le_iff₀ hpos]
  nlinarith [ht, hstep]

/-- **Unconditional a posteriori lower bound.**  With no assumed fixed point: a
    contraction on `ℝ` has a fixed point `x*` for which
    `|xₙ₊₁ − xₙ| / (1 + L) ≤ |xₙ − x*|` at every step — the hypothesis-free form of
    `aposteriori_lower_estimate`, threading `exists_fixed_point`. -/
theorem aposteriori_lower_estimate_unconditional (f : ℝ → ℝ) (L : ℝ)
    (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n)) :
    ∃ xstar : ℝ, f xstar = xstar ∧
      ∀ n, |x (n + 1) - x n| / (1 + L) ≤ |x n - xstar| := by
  obtain ⟨xstar, hfp⟩ := exists_fixed_point f L hL0 hL1 hf
  exact ⟨xstar, hfp, fun n => aposteriori_lower_estimate f L hL0 hf x hx xstar hfp n⟩

/-! ### Convergence of the iteration (the qualitative limit behind the estimates)

The a priori/a posteriori theorems above are *quantitative* error bounds; the
underlying *qualitative* fact is that the iterates actually converge to the fixed
point, `xₙ → x*`.  It is an immediate consequence of the geometric decay
`iterate_dist` (`|xₙ − x*| ≤ Lⁿ·|x₀ − x*|`) together with `Lⁿ → 0` for `0 ≤ L < 1`,
sandwiched to `0`.  This completes the Banach picture: existence + uniqueness of `x*`
(`exists_unique_fixed_point`), the two computable error estimates, and now the
convergence they estimate the *rate* of. -/

/-- **Convergence of the iteration.**  For a contraction `f` on `ℝ` with fixed point
    `x*` and iteration `xₙ₊₁ = f xₙ`, the iterates converge to `x*`:
    `xₙ → x*` as `n → ∞`.  Proved by squeezing the error `|xₙ − x*|` between `0` and
    the geometric bound `Lⁿ·|x₀ − x*| → 0` (`iterate_dist` +
    `tendsto_pow_atTop_nhds_zero_of_lt_one`). -/
theorem iterate_tendsto (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n))
    (xstar : ℝ) (hfp : f xstar = xstar) :
    Filter.Tendsto x Filter.atTop (nhds xstar) := by
  rw [tendsto_iff_dist_tendsto_zero]
  have hbound : ∀ n, dist (x n) xstar ≤ L ^ n * |x 0 - xstar| := by
    intro n
    rw [Real.dist_eq]
    exact iterate_dist f L hL0 hf x hx xstar hfp n
  have hg : Filter.Tendsto (fun n : ℕ => L ^ n * |x 0 - xstar|) Filter.atTop (nhds 0) := by
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hL0 hL1
    simpa using h0.mul_const |x 0 - xstar|
  exact squeeze_zero (fun _ => dist_nonneg) hbound hg

/-- **Unconditional convergence.**  A contraction on `ℝ` has a fixed point `x*` to which
    every iteration sequence `xₙ₊₁ = f xₙ` converges — the hypothesis-free form of
    `iterate_tendsto`, threading `exists_fixed_point` for the existence of `x*`. -/
theorem exists_iterate_tendsto (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n)) :
    ∃ xstar : ℝ, f xstar = xstar ∧ Filter.Tendsto x Filter.atTop (nhds xstar) := by
  obtain ⟨xstar, hfp⟩ := exists_fixed_point f L hL0 hL1 hf
  exact ⟨xstar, hfp, iterate_tendsto f L hL0 hL1 hf x hx xstar hfp⟩

/-! ### Stability of the fixed point under perturbation of the map

The estimates above all concern a *single* contraction `f` and quantify how its
iterates approach its fixed point.  A complementary — and, for numerical work,
equally basic — question is how the fixed point itself *moves* when the map is
perturbed: if `g` is a second map that is uniformly `δ`-close to `f`
(`|f x − g x| ≤ δ` for all `x`), how far apart are their fixed points?  The answer
is the classic Lipschitz-stability bound

    |x*_f − x*_g| ≤ δ / (1 − L),

so the fixed point depends on the map in a `1/(1−L)`-Lipschitz way: the closer `L`
is to `1` (the weaker the contraction) the more sensitive the fixed point.  It is a
one-line consequence of the contraction hypothesis and the triangle inequality —
`|x*_f − x*_g| = |f x*_f − g x*_g| ≤ |f x*_f − f x*_g| + |f x*_g − g x*_g|
≤ L·|x*_f − x*_g| + δ` — and it is not recorded anywhere above, which only ever
compares iterates of one fixed map to one fixed point. -/

/-- **Stability of the fixed point under perturbation (conditional).**  If `f` is an
    `L`-contraction with `L < 1` and fixed point `xf`, and `g` is any map with a
    fixed point `xg` that is uniformly `δ`-close to `f` (`|f x − g x| ≤ δ` for all
    `x`), then the two fixed points satisfy `|xf − xg| ≤ δ / (1 − L)`.  Only `f`
    need be a contraction; `g` enters solely through its fixed-point equation and
    the closeness bound. -/
theorem fixed_point_stability (f g : ℝ → ℝ) (L δ : ℝ) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (xf xg : ℝ) (hxf : f xf = xf) (hxg : g xg = xg)
    (hclose : ∀ x, |f x - g x| ≤ δ) :
    |xf - xg| ≤ δ / (1 - L) := by
  have h1L : 0 < 1 - L := by linarith
  have hstep : |xf - xg| ≤ L * |xf - xg| + δ := by
    have e1 : xf - xg = (f xf - f xg) + (f xg - g xg) := by rw [hxf, hxg]; ring
    calc |xf - xg| = |(f xf - f xg) + (f xg - g xg)| := by rw [e1]
      _ ≤ |f xf - f xg| + |f xg - g xg| := abs_add_le _ _
      _ ≤ L * |xf - xg| + δ := by
          have ha := hf xf xg
          have hb := hclose xg
          linarith
  rw [le_div_iff₀ h1L]
  have hexp : |xf - xg| * (1 - L) = |xf - xg| - L * |xf - xg| := by ring
  rw [hexp]; linarith [hstep]

/-- **Stability of the fixed point under perturbation (unconditional).**  If `f` and
    `g` are contractions on `ℝ` (constants `L, M < 1`) that are uniformly `δ`-close
    (`|f x − g x| ≤ δ`), then each has a (unique) fixed point and the two are within
    `δ / (1 − L)`:  `∃ xf xg, f xf = xf ∧ g xg = xg ∧ |xf − xg| ≤ δ/(1−L)`.  The
    fixed points are produced by `exists_fixed_point` and the bound is
    `fixed_point_stability`; the asymmetry `1/(1−L)` (vs `1/(1−M)`) reflects that
    only `f`'s contraction rate is used to absorb the coupled term. -/
theorem fixed_point_stability_unconditional (f g : ℝ → ℝ) (L M δ : ℝ)
    (hL0 : 0 ≤ L) (hL1 : L < 1) (hM0 : 0 ≤ M) (hM1 : M < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hg : ∀ x y, |g x - g y| ≤ M * |x - y|)
    (hclose : ∀ x, |f x - g x| ≤ δ) :
    ∃ xf xg : ℝ, f xf = xf ∧ g xg = xg ∧ |xf - xg| ≤ δ / (1 - L) := by
  obtain ⟨xf, hxf⟩ := exists_fixed_point f L hL0 hL1 hf
  obtain ⟨xg, hxg⟩ := exists_fixed_point g M hM0 hM1 hg
  exact ⟨xf, xg, hxf, hxg, fixed_point_stability f g L δ hL1 hf xf xg hxf hxg hclose⟩

/-! ### The self-contained Cauchy estimate between iterates (no fixed point needed)

Every a priori bound above compares an iterate `xₙ` to the fixed point `x*`.  The
even more elementary — and genuinely `x*`-free — statement is the **Cauchy estimate**
directly *between two iterates*,

    |x_{n+m} − xₙ| ≤ Lⁿ/(1−L) · |x₁ − x₀|,

bounding the total drift over any number `m` of further steps purely by the *first*
increment and the current index `n`.  It mentions no fixed point at all (on a complete
space it is precisely what *proves* one exists, the sequence being Cauchy), and letting
`m → ∞` recovers `apriori_estimate`.  It rests on the geometric decay of the individual
increments, `|x_{k+1} − x_k| ≤ Lᵏ·|x₁ − x₀|` (`step_dist`), telescoped and summed as a
finite geometric series `∑_{j<m} Lⁿ⁺ʲ = Lⁿ(1−Lᵐ)/(1−L) ≤ Lⁿ/(1−L)`. -/

/-- **Geometric decay of the increments.**  `|x_{k+1} − x_k| ≤ Lᵏ · |x₁ − x₀|`: each
    successive step of the iteration is shorter than the previous one by a factor `L`.
    Proved by induction, applying the contraction bound to consecutive iterates. -/
theorem step_dist (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n)) (k : ℕ) :
    |x (k + 1) - x k| ≤ L ^ k * |x 1 - x 0| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := hf (x (k + 1)) (x k)
    rw [← hx (k + 1), ← hx k] at h
    calc |x (k + 1 + 1) - x (k + 1)| ≤ L * |x (k + 1) - x k| := h
      _ ≤ L * (L ^ k * |x 1 - x 0|) := mul_le_mul_of_nonneg_left ih hL0
      _ = L ^ (k + 1) * |x 1 - x 0| := by ring

/-- **Cauchy estimate between iterates (fixed-point-free a priori bound).**  For a
    contraction `f` on `ℝ` with `0 ≤ L < 1` and iteration `xₙ₊₁ = f xₙ`, any two iterates
    satisfy `|x_{n+m} − xₙ| ≤ Lⁿ/(1−L) · |x₁ − x₀|`.  No fixed point is assumed — this is
    the estimate exhibiting the iteration as a Cauchy sequence, and taking `m → ∞`
    reproduces `apriori_estimate`.  Proved from `step_dist` via the exact partial geometric
    sum `Lⁿ(1−Lᵐ)/(1−L)` carried as an induction invariant. -/
theorem cauchy_estimate (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L < 1)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (x : ℕ → ℝ) (hx : ∀ n, x (n + 1) = f (x n)) (n m : ℕ) :
    |x (n + m) - x n| ≤ L ^ n / (1 - L) * |x 1 - x 0| := by
  have hc : (0 : ℝ) < 1 - L := by linarith
  set S := |x 1 - x 0| with hS
  have hSnn : 0 ≤ S := abs_nonneg _
  -- exact partial-sum invariant, cleared of the division by `1 - L`
  have key : ∀ m, (1 - L) * |x (n + m) - x n| ≤ L ^ n * (1 - L ^ m) * S := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      show (1 - L) * |x (n + m + 1) - x n| ≤ L ^ n * (1 - L ^ (m + 1)) * S
      rw [pow_succ]
      have hstep := step_dist f L hL0 hf x hx (n + m)
      rw [pow_add] at hstep
      have htri : |x (n + m + 1) - x n| ≤ |x (n + m + 1) - x (n + m)| + |x (n + m) - x n| :=
        abs_sub_le _ _ _
      have hLnn : (0 : ℝ) ≤ L ^ n := pow_nonneg hL0 n
      have hLm : (0 : ℝ) ≤ L ^ m := pow_nonneg hL0 m
      nlinarith [mul_le_mul_of_nonneg_left htri hc.le,
                 mul_le_mul_of_nonneg_left hstep hc.le, ih, hLnn, hLm, hSnn,
                 mul_nonneg (mul_nonneg hLnn hLm) hSnn]
  have hbound : L ^ n * (1 - L ^ m) * S ≤ L ^ n * S := by
    have hLm : (0 : ℝ) ≤ L ^ m := pow_nonneg hL0 m
    nlinarith [pow_nonneg hL0 n, hSnn, hLm,
               mul_nonneg (mul_nonneg (pow_nonneg hL0 n) hLm) hSnn]
  have hfin : (1 - L) * |x (n + m) - x n| ≤ L ^ n * S := le_trans (key m) hbound
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  nlinarith [hfin]

/-! ### The `n`-fold iterate is an `Lⁿ`-contraction (structural composition law)

The composition laws `lipschitz_comp`/`lipschitz_comp_list` compose *distinct* maps; the
special case of composing one map `f` with itself `n` times says the iterate `f^[n]` is
`Lⁿ`-Lipschitz.  This is the structural fact underlying the geometric decay `iterate_dist`
(`xₙ = f^[n] x₀`) and, since `Lⁿ < 1`, gives an alternate route to a unique fixed point of
every iterate.  Stated with Mathlib's `Function.iterate` `f^[n]`. -/

/-- **The `n`-fold iterate of an `L`-contraction is `Lⁿ`-Lipschitz.**
    `|f^[n] x − f^[n] y| ≤ Lⁿ · |x − y|`.  Proved by induction on `n`, peeling one outer
    application via `Function.iterate_succ_apply'` and applying the contraction bound. -/
theorem iterate_lipschitz (f : ℝ → ℝ) (L : ℝ) (hL0 : 0 ≤ L)
    (hf : ∀ x y, |f x - f y| ≤ L * |x - y|) (n : ℕ) (x y : ℝ) :
    |f^[n] x - f^[n] y| ≤ L ^ n * |x - y| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc |f (f^[n] x) - f (f^[n] y)| ≤ L * |f^[n] x - f^[n] y| := hf _ _
      _ ≤ L * (L ^ n * |x - y|) := mul_le_mul_of_nonneg_left ih hL0
      _ = L ^ (n + 1) * |x - y| := by ring

end BrouwerOQ02OQ02OQ01
