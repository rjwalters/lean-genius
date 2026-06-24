import Mathlib.NumberTheory.Real.Irrational
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-
# Ball–Rivoal: the linear-form engine and the dimension reduction (OQ-01-OQ-01-OQ-03)

Open Question from "Is ζ(5) Irrational? — Computational Bounds" (basel-problem-oq-01-oq-01).

The Ball–Rivoal theorem states that infinitely many odd zeta values
ζ(3), ζ(5), ζ(7), … are irrational.  A full formalization is far out of reach,
but the proof has a precise logical skeleton that *is* formalizable, and which
this file establishes with no axioms and no sorries.

Two ingredients drive every known irrationality result of this kind (Apéry 1978
for ζ(3); Rivoal 2000 / Ball–Rivoal for the whole odd family):

* **The linear-form criterion** (Part I).  If one can build integer sequences
  `pₙ, qₙ` with the real linear forms `qₙ·α − pₙ` nonzero but tending to `0`,
  then `α` is irrational.  This is the *sufficiency* engine: a single nonzero
  integer has absolute value `≥ 1`, so a rational `α = a/b` forces every nonzero
  form `qₙ·α − pₙ = (qₙ·a − pₙ·b)/b` to stay `≥ 1/|b|` away from `0`,
  contradicting convergence.  Mathlib has the Hurwitz characterization (good
  rational approximations at the fixed rate `1/q²`) but not this rate-free form,
  which is exactly what the Apéry/Ball–Rivoal hypergeometric constructions
  supply.

* **The dimension reduction** (Part II).  Rivoal's analytic input is a *lower
  bound* on `dim_ℚ span{1, ζ(3), ζ(5), …, ζ(2n+1)}` that grows without bound in
  `n`.  We prove the purely linear-algebraic step that converts unbounded
  dimension into the conclusion "infinitely many of the values are irrational":
  if only finitely many `xᵢ` were irrational, every span would sit inside a
  single fixed finite-dimensional ℚ-subspace, capping the dimension.

Axioms: 0
Sorries: 0
-/

open Filter Topology

namespace BaselProblemOQ01OQ01OQ03

-- ============================================================
-- Part I: The linear-form irrationality criterion (the engine)
-- ============================================================

/-- **Quantitative core.**  For a rational `α = a/b` with `b ≠ 0`, every integer
linear form `q·α − p` that is nonzero is bounded away from `0` by `1/|b|`.  The
form equals `(q·a − p·b)/b`, whose numerator is a nonzero integer, hence has
absolute value at least `1`. -/
theorem abs_linearForm_ge_of_rat (a b p q : ℤ) (hb : b ≠ 0)
    (hne : (q : ℝ) * ((a : ℝ) / (b : ℝ)) - (p : ℝ) ≠ 0) :
    1 / |(b : ℝ)| ≤ |(q : ℝ) * ((a : ℝ) / (b : ℝ)) - (p : ℝ)| := by
  have hbR : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hbpos : 0 < |(b : ℝ)| := abs_pos.mpr hbR
  have hform : (q : ℝ) * ((a : ℝ) / (b : ℝ)) - (p : ℝ)
      = ((q * a - p * b : ℤ) : ℝ) / (b : ℝ) := by
    push_cast; field_simp
  rw [hform] at hne ⊢
  have hnum : (q * a - p * b : ℤ) ≠ 0 := by
    intro h; apply hne; rw [h]; simp
  rw [abs_div, div_le_div_iff_of_pos_right hbpos, ← Int.cast_abs]
  exact_mod_cast Int.one_le_abs hnum

/-- **The linear-form irrationality criterion.**  Given integer sequences
`p, q : ℕ → ℤ` such that the real linear forms `qₙ·α − pₙ` are all nonzero yet
tend to `0`, the number `α` is irrational.

This is the abstract sufficiency theorem behind Apéry's proof that `ζ(3)` is
irrational and behind the Ball–Rivoal construction for the odd zeta family. -/
theorem irrational_of_linearForm_tendsto_zero {α : ℝ} (p q : ℕ → ℤ)
    (hne : ∀ n, (q n : ℝ) * α - (p n : ℝ) ≠ 0)
    (htend : Tendsto (fun n => (q n : ℝ) * α - (p n : ℝ)) atTop (𝓝 0)) :
    Irrational α := by
  rintro ⟨r, hr⟩
  -- `α = r = r.num / r.den`, rational; derive a uniform lower bound on the forms.
  have hden : ((r.den : ℤ)) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hαeq : α = (r.num : ℝ) / ((r.den : ℤ) : ℝ) := by
    rw [← hr, Rat.cast_def]; push_cast; ring
  set ε : ℝ := 1 / |((r.den : ℤ) : ℝ)| with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  -- Eventually the forms lie within `ε` of `0` …
  have hev : ∀ᶠ n in atTop, |(q n : ℝ) * α - (p n : ℝ)| < ε := by
    refine (htend.eventually (Metric.ball_mem_nhds (0 : ℝ) hεpos)).mono ?_
    intro n hn
    rwa [Real.dist_eq, sub_zero] at hn
  obtain ⟨n, hn⟩ := hev.exists
  -- … yet each nonzero form is at least `ε` away — contradiction.
  have hge : ε ≤ |(q n : ℝ) * α - (p n : ℝ)| := by
    rw [hε, hαeq]
    exact abs_linearForm_ge_of_rat r.num (r.den : ℤ) (p n) (q n) hden
      (by rw [← hαeq]; exact hne n)
  exact absurd hn (not_lt.mpr hge)

/-- **Decay-rate packaging.**  In practice one has an explicit upper bound
`|qₙ·α − pₙ| ≤ Cₙ` with `Cₙ → 0` (e.g. geometric decay `C·ρⁿ`, as Apéry obtains
with `ρ = (√2 − 1)⁴ ≈ 1/34`).  Together with non-vanishing this yields
irrationality. -/
theorem irrational_of_linearForm_le_tendsto_zero {α : ℝ} (p q : ℕ → ℤ)
    (C : ℕ → ℝ) (hne : ∀ n, (q n : ℝ) * α - (p n : ℝ) ≠ 0)
    (hle : ∀ n, |(q n : ℝ) * α - (p n : ℝ)| ≤ C n)
    (hC : Tendsto C atTop (𝓝 0)) :
    Irrational α := by
  apply irrational_of_linearForm_tendsto_zero p q hne
  -- two-sided squeeze: `−Cₙ ≤ formₙ ≤ Cₙ` with `±Cₙ → 0`.
  have hCneg : Tendsto (fun n => -C n) atTop (𝓝 0) := by simpa using hC.neg
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hCneg hC ?_ ?_
  · intro n; exact (abs_le.mp (hle n)).1
  · intro n; exact (abs_le.mp (hle n)).2

-- ============================================================
-- Part II: The Ball–Rivoal dimension reduction
-- ============================================================

/-- **Dimension cap from finitely many irrationals.**  View `ℝ` as a
`ℚ`-vector space.  If every value `x i` with index outside a finite set `T` is
rational, then the span of `{1} ∪ {x i : i ∈ s}` over *any* finite index set `s`
is contained in the fixed subspace spanned by `{1} ∪ {x i : i ∈ T}`, so its
`ℚ`-dimension never exceeds `T.card + 1`. -/
theorem finrank_span_le_of_irrational_subset (x : ℕ → ℝ) (T : Finset ℕ)
    (hrat : ∀ i ∉ T, ¬ Irrational (x i)) (s : Finset ℕ) :
    Module.finrank ℚ
      (Submodule.span ℚ (↑(insert (1 : ℝ) (s.image x)) : Set ℝ)) ≤ T.card + 1 := by
  classical
  set F : Finset ℝ := insert (1 : ℝ) (T.image x) with hF
  haveI hfin : Module.Finite ℚ ↥(Submodule.span ℚ (↑F : Set ℝ)) :=
    Module.Finite.iff_fg.mpr (Submodule.fg_span F.finite_toSet)
  have hsub : Submodule.span ℚ (↑(insert (1 : ℝ) (s.image x)) : Set ℝ)
      ≤ Submodule.span ℚ (↑F : Set ℝ) := by
    rw [Submodule.span_le]
    intro y hy
    simp only [Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
      Finset.mem_coe] at hy
    rcases hy with rfl | ⟨i, _, rfl⟩
    · exact Submodule.subset_span (by simp [hF])
    · by_cases hiT : i ∈ T
      · refine Submodule.subset_span ?_
        simp only [hF, Finset.coe_insert, Finset.coe_image, Set.mem_insert_iff, Set.mem_image,
          Finset.mem_coe]
        exact Or.inr ⟨i, hiT, rfl⟩
      · -- `x i` is rational, hence a ℚ-multiple of `1`, hence in the span.
        have hr := hrat i hiT
        rw [Irrational, not_not] at hr
        obtain ⟨c, hc⟩ := hr
        have hxi : x i = c • (1 : ℝ) := by rw [Rat.smul_one_eq_cast]; exact hc.symm
        rw [hxi]
        exact Submodule.smul_mem _ c (Submodule.subset_span (by simp [hF]))
  calc Module.finrank ℚ (Submodule.span ℚ (↑(insert (1 : ℝ) (s.image x)) : Set ℝ))
      ≤ Module.finrank ℚ (Submodule.span ℚ (↑F : Set ℝ)) := Submodule.finrank_mono hsub
    _ ≤ F.card := finrank_span_finset_le_card F
    _ ≤ T.card + 1 := by
        rw [hF]
        have h1 := Finset.card_insert_le (1 : ℝ) (T.image x)
        have h2 := Finset.card_image_le (s := T) (f := x)
        omega

/-- **Ball–Rivoal dimension reduction.**  If the `ℚ`-dimension of
`span{1} ∪ {x i : i ∈ s}` is unbounded as `s` ranges over finite index sets,
then infinitely many of the `x i` are irrational.

This is the linear-algebraic heart of Ball–Rivoal: Rivoal's analytic dimension
lower bound `(1 + o(1))·log n / (1 + log 2) → ∞` for the odd zeta values feeds
this lemma to conclude that infinitely many odd zeta values are irrational. -/
theorem infinite_irrational_of_unbounded_finrank (x : ℕ → ℝ)
    (hunb : ∀ N : ℕ, ∃ s : Finset ℕ,
      N < Module.finrank ℚ (Submodule.span ℚ (↑(insert (1 : ℝ) (s.image x)) : Set ℝ))) :
    {i | Irrational (x i)}.Infinite := by
  classical
  by_contra h
  rw [Set.not_infinite] at h
  set T : Finset ℕ := h.toFinset with hT
  have hrat : ∀ i ∉ T, ¬ Irrational (x i) := by
    intro i hi
    rw [hT, Set.Finite.mem_toFinset] at hi
    simpa using hi
  obtain ⟨s, hs⟩ := hunb (T.card + 1)
  have hcap := finrank_span_le_of_irrational_subset x T hrat s
  omega

end BaselProblemOQ01OQ01OQ03
