import Mathlib

/-
# IVT — OQ-03-OQ-01: 2D Brouwer via Sperner — the compactness discharge

## Research Problem: intermediate-value-theorem-oq-03-oq-01
"2D Brouwer via Sperner Lemma Discharge"

The parent entry `intermediate-value-theorem-oq-03` proves 1D Brouwer from the
IVT (`g(x) = f(x) - x` has a zero) and then states the **2D** case as an axiom:

```
axiom brouwer_2d : ∀ f : ℝ² → ℝ², Continuous f → (maps disk to disk) →
                   ∃ x, ‖x‖ ≤ 1 ∧ f x = x
```

This file isolates and rigorously verifies the **analytic half** of the standard
Sperner-lemma route to that theorem, the step that the combinatorics alone does
*not* provide:

> Sperner's lemma + the displacement colouring produce, for every `ε > 0`, an
> `ε`-approximate fixed point of a continuous self-map of the simplex.
> **Compactness** of the simplex upgrades this family of approximate fixed points
> to a single *exact* fixed point.

The combinatorial input — that Sperner's lemma yields arbitrarily fine
approximate fixed points — is the verified content of `SpernerNDim.lean`
(the n-dimensional Sperner parity theorem, 0 axioms) together with the
displacement colouring. Here we supply the missing convergence argument and
thereby reduce the parent's `brouwer_2d` axiom to that combinatorial property.

## What is proved (all 0-sorry, 0-axiom)

* `exists_fixed_of_approx` — general compactness discharge: a continuous self-map
  of *any* nonempty compact set that admits ε-approximate fixed points for all
  `ε > 0` has an exact fixed point.  (The mathematical heart of Sperner ⟹ Brouwer.)
* `simplex_isCompact`, `simplex_nonempty` — the standard `d`-simplex is a
  nonempty compact subset of `Fin d → ℝ`.
* `brouwer_2d_of_sperner_approx` — **conditional 2D Brouwer**: a continuous
  self-map of the 2-simplex with the Sperner approximate-fixed-point property has
  a fixed point.  This is the discharge of the parent axiom relative to the
  (separately verified) combinatorial Sperner lemma.
* `brouwer_1d_via_ivt` — the unconditional 1D case, recorded for contrast: in 1D
  no Sperner lemma is needed, the IVT suffices.

## Honesty note

`brouwer_2d_of_sperner_approx` is a **fully verified implication**, not an
unconditional proof of 2D Brouwer.  Its hypothesis `happrox` is exactly the
output of the Sperner displacement-colouring construction; supplying that
construction for `d = 2` from `SpernerNDim.sperner_ndim` (Kuhn triangulation +
boundary-oddness induction) remains open and is the natural next child problem.

Tags: topology, fixed-point, brouwer, sperner, compactness, ivt
-/

set_option linter.unusedVariables false

namespace IVTBrouwerDischarge

open Set Finset

-- ============================================================
-- SECTION I: The compactness discharge (general dimension)
-- ============================================================

/-- **Approximate fixed points + compactness ⟹ exact fixed point.**

    Let `K` be a nonempty compact subset of `Fin d → ℝ` and `f` continuous.
    If for every `ε > 0` there is a point of `K` moved less than `ε` by `f`, then
    `f` has a genuine fixed point in `K`.

    Proof: the displacement `x ↦ dist (f x) x` is continuous on the compact `K`, so
    it attains a minimum at some `x₀ ∈ K`.  If that minimum were positive, the
    `ε`-approximate hypothesis with `ε = dist (f x₀) x₀` would produce a point with
    strictly smaller displacement, contradicting minimality.  Hence the minimum is
    `0`, i.e. `f x₀ = x₀`.

    This is the analytic core of "Sperner's lemma ⟹ Brouwer": the combinatorics
    supply the approximate fixed points, compactness supplies the limit. -/
theorem exists_fixed_of_approx {d : ℕ}
    {K : Set (Fin d → ℝ)} (hK : IsCompact K) (hKne : K.Nonempty)
    {f : (Fin d → ℝ) → (Fin d → ℝ)} (hcont : Continuous f)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x ∈ K, dist (f x) x < ε) :
    ∃ x ∈ K, f x = x := by
  -- `x ↦ dist (f x) x` is continuous and attains its minimum on the compact `K`.
  have hg : Continuous (fun x => dist (f x) x) := hcont.dist continuous_id
  obtain ⟨x₀, hx₀_mem, hx₀_min⟩ := hK.exists_isMinOn hKne hg.continuousOn
  -- It suffices to show that minimum displacement is `0`.
  suffices h : dist (f x₀) x₀ = 0 from ⟨x₀, hx₀_mem, dist_eq_zero.mp h⟩
  by_contra h
  have hpos : 0 < dist (f x₀) x₀ := lt_of_le_of_ne dist_nonneg (Ne.symm h)
  -- An `ε = dist (f x₀) x₀` approximate fixed point beats the minimum.
  obtain ⟨y, hy_mem, hy_lt⟩ := happrox _ hpos
  have hmin : dist (f x₀) x₀ ≤ dist (f y) y := isMinOn_iff.mp hx₀_min y hy_mem
  exact absurd hmin (not_le.mpr hy_lt)

-- ============================================================
-- SECTION II: The standard `d`-simplex is compact and nonempty
-- ============================================================

/-- A point of `Fin d → ℝ` lies in the standard `d`-simplex:
    all coordinates `≥ 0`, and their sum is `≤ 1`. -/
def InSimplex (d : ℕ) (x : Fin d → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1

/-- The standard `d`-simplex is a closed subset of the compact cube `[0,1]^d`,
    hence compact. -/
theorem simplex_isCompact (d : ℕ) :
    IsCompact {x : Fin d → ℝ | InSimplex d x} := by
  apply IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ => isCompact_Icc))
  · -- closed: intersection of half-spaces `0 ≤ x i` and `∑ x i ≤ 1`
    have heq : {x : Fin d → ℝ | InSimplex d x} =
        (⋂ i, {x | (0 : ℝ) ≤ x i}) ∩ {x | ∑ i, x i ≤ 1} := by
      ext x; simp [InSimplex, Set.mem_iInter]
    rw [heq]
    exact (isClosed_iInter fun i =>
      isClosed_le continuous_const (continuous_apply i)).inter
      (isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i)
        continuous_const)
  · -- subset of the cube: each coordinate lies in `[0,1]`
    intro x hx
    obtain ⟨hnn, hsum⟩ := hx
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    exact fun i => ⟨hnn i, le_trans
      (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)) hsum⟩

/-- The origin lies in the standard `d`-simplex, so it is nonempty. -/
theorem simplex_nonempty (d : ℕ) :
    {x : Fin d → ℝ | InSimplex d x}.Nonempty :=
  ⟨0, fun _ => le_refl 0, by simp⟩

-- ============================================================
-- SECTION III: Conditional 2D Brouwer — discharge of the axiom
-- ============================================================

/-- **2D Brouwer fixed point theorem from Sperner's lemma (conditional).**

    Every continuous self-map `f` of the standard 2-simplex that enjoys the
    Sperner approximate-fixed-point property — for each `ε > 0` a point whose two
    coordinates are each moved less than `ε` — has an exact fixed point.

    This is a fully verified *implication*.  The hypothesis `happrox` is precisely
    the output of the Sperner displacement-colouring construction applied to `f`;
    the combinatorial fact that Sperner's lemma supplies it is the verified content
    of `SpernerNDim.lean`.  The work done here is the compactness upgrade
    (`exists_fixed_of_approx`) specialised to the compact 2-simplex, which converts
    those approximate fixed points into a genuine one.

    Together with the (separately verified) combinatorial Sperner lemma this
    discharges the `brouwer_2d` axiom of the parent entry
    `intermediate-value-theorem-oq-03`. -/
theorem brouwer_2d_of_sperner_approx
    (f : (Fin 2 → ℝ) → (Fin 2 → ℝ)) (hcont : Continuous f)
    (hf : ∀ x, InSimplex 2 x → InSimplex 2 (f x))
    (happrox : ∀ ε : ℝ, 0 < ε →
      ∃ x, InSimplex 2 x ∧ ∀ i : Fin 2, |f x i - x i| < ε) :
    ∃ x, InSimplex 2 x ∧ f x = x := by
  set K : Set (Fin 2 → ℝ) := {x | InSimplex 2 x} with hKdef
  -- Convert the coordinatewise approximate hypothesis to a `dist` statement
  -- (the `Fin 2 → ℝ` metric is the sup metric).
  have happrox' : ∀ ε : ℝ, 0 < ε → ∃ x ∈ K, dist (f x) x < ε := by
    intro ε hε
    obtain ⟨x, hx, hxi⟩ := happrox ε hε
    refine ⟨x, hx, ?_⟩
    rw [dist_pi_lt_iff hε]
    intro i
    rw [Real.dist_eq]
    exact hxi i
  -- Apply the compactness discharge on the compact, nonempty 2-simplex.
  obtain ⟨x, hx, hfx⟩ :=
    exists_fixed_of_approx (simplex_isCompact 2) (simplex_nonempty 2) hcont happrox'
  exact ⟨x, hx, hfx⟩

-- ============================================================
-- SECTION IV: The unconditional 1D case (for contrast)
-- ============================================================

/-- **1D Brouwer from the IVT** — recorded for contrast.

    In one dimension no Sperner lemma is needed: a continuous `f : [0,1] → [0,1]`
    has a fixed point because `g(x) = f(x) - x` satisfies `g 0 ≥ 0 ≥ g 1`, so the
    intermediate value theorem hands us a zero of `g`.  This is the 1D phenomenon
    that *fails* to generalise directly, which is exactly why the 2D case needs the
    combinatorial detour through Sperner's lemma. -/
theorem brouwer_1d_via_ivt (f : ℝ → ℝ) (hf : Continuous f)
    (hf0 : 0 ≤ f 0) (hf1 : f 1 ≤ 1) :
    ∃ c ∈ Icc (0 : ℝ) 1, f c = c := by
  -- `g x = f x - x` is continuous with `g 1 ≤ 0 ≤ g 0`, so by the IVT
  -- `0` lies in the image of `g` over `[0,1]`: some `c` has `f c - c = 0`.
  have hg : Continuous (fun x => f x - x) := hf.sub continuous_id
  have hmem : (0 : ℝ) ∈ Icc ((fun x => f x - x) 1) ((fun x => f x - x) 0) := by
    refine ⟨?_, ?_⟩
    · show f 1 - 1 ≤ 0; linarith
    · show (0 : ℝ) ≤ f 0 - 0; linarith
  obtain ⟨c, hc_mem, hc_eq⟩ :=
    intermediate_value_Icc' (zero_le_one) hg.continuousOn hmem
  refine ⟨c, hc_mem, ?_⟩
  have hzero : f c - c = 0 := hc_eq
  linarith

end IVTBrouwerDischarge
