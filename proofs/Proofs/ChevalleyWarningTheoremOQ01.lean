import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Tactic

/-
# The Chevalley–Warning theorem and the nontrivial-solution corollary

## What This Proves

The **Chevalley–Warning theorem** (Chevalley 1935, Warning 1935) is a foundational
fact of finite-field arithmetic: if a finite system of polynomial equations over a
finite field `K` of characteristic `p` is *low degree* — the sum of the total
degrees of the polynomials is strictly smaller than the number of variables — then
the number of common zeros is divisible by `p`.

Mathlib proves the divisibility statements
(`char_dvd_card_solutions_of_sum_lt`, `char_dvd_card_solutions`,
`char_dvd_card_solutions_of_add_lt`, `char_dvd_card_solutions_of_fintype_sum_lt`)
in `Mathlib/FieldTheory/ChevalleyWarning.lean`, where the sole downstream consumer
is the Erdős–Ginzburg–Ziv theorem. It does **not** record the classical
existence corollary that Chevalley himself drew, and which is the genuinely new
content of this file.

* **Divisibility re-exports** (`chevalley_warning_dvd`,
  `chevalley_warning_dvd_univ`, `chevalley_warning_dvd_single`,
  `chevalley_warning_dvd_pair`). The Mathlib headlines restated as the baseline:
  the count of common zeros of a low-degree system is divisible by the
  characteristic `p`, in the `Finset`-indexed, full-`Fintype`-indexed, single-
  polynomial, and two-polynomial forms.

* **Chevalley's nontrivial-solution corollary** (`chevalley_warning_nontrivial`,
  `chevalley_warning_nontrivial_single`) — the new content. If, in addition to the
  degree condition, every polynomial vanishes at the origin (zero constant term, so
  `x = 0` is already a common zero), then there exists a **nonzero** common zero.
  Reason: the origin gives at least one solution, and `p ∣ #solutions` with `p`
  prime forces `#solutions ≥ p ≥ 2`, so a second, necessarily nonzero, solution
  must exist. Mathlib provides the divisibility but not this existence statement.

* **Concrete instances** (`chevalley_linear_F2`, `chevalley_quadratic_F2`). Two
  explicit nontrivial zeros over `𝔽₂`, computed: the linear form `X₀ + X₁` in two
  variables vanishes at `(1, 1)`, and the quadratic form `X₀·X₁ + X₂²` in three
  variables vanishes at `(1, 0, 0)` — small witnesses confirming the corollary
  numerically.

## Context

Chevalley–Warning underlies the Erdős–Ginzburg–Ziv theorem (its standard proof
applies the corollary to a pair of degree-`(n−1)` power-sum forms over `𝔽_p`),
Warning's second theorem on the number of solutions, the Ax–Katz refinement, and
the combinatorial-nullstellensatz circle of ideas. The nontrivial-solution form
proved here is the version actually used in those applications: a low-degree system
through the origin always has a solution away from the origin.
-/

namespace ChevalleyWarningTheoremOQ01

open MvPolynomial

/-! ## Divisibility: the Mathlib headlines restated -/

/-- **Chevalley–Warning (Finset form).** For a finite family `f : ι → MvPolynomial σ K`
indexed by a `Finset s`, if the total degrees sum to less than the number of
variables then the characteristic `p` divides the number of common zeros. Direct
re-export of `char_dvd_card_solutions_of_sum_lt`. -/
theorem chevalley_warning_dvd
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (h : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
  char_dvd_card_solutions_of_sum_lt p h

/-- **Chevalley–Warning (full Fintype form).** The same divisibility when the system
is indexed by the whole of a finite type `ι`. Re-export of
`char_dvd_card_solutions_of_fintype_sum_lt`. -/
theorem chevalley_warning_dvd_univ
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    [Fintype ι] (p : ℕ) [CharP K p] {f : ι → MvPolynomial σ K}
    (h : (∑ i, (f i).totalDegree) < Fintype.card σ) :
    p ∣ Fintype.card {x : σ → K // ∀ i, eval x (f i) = 0} :=
  char_dvd_card_solutions_of_fintype_sum_lt p h

/-- **Chevalley–Warning (single polynomial).** One polynomial of total degree less
than the number of variables has a number of zeros divisible by `p`. Re-export of
`char_dvd_card_solutions`. -/
theorem chevalley_warning_dvd_single
    {K σ : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {f : MvPolynomial σ K} (h : f.totalDegree < Fintype.card σ) :
    p ∣ Fintype.card {x : σ → K // eval x f = 0} :=
  char_dvd_card_solutions p h

/-- **Chevalley–Warning (two polynomials).** For two polynomials whose total degrees
sum to less than the number of variables, `p` divides the number of common zeros.
Re-export of `char_dvd_card_solutions_of_add_lt`. -/
theorem chevalley_warning_dvd_pair
    {K σ : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {f₁ f₂ : MvPolynomial σ K}
    (h : f₁.totalDegree + f₂.totalDegree < Fintype.card σ) :
    p ∣ Fintype.card {x : σ → K // eval x f₁ = 0 ∧ eval x f₂ = 0} :=
  char_dvd_card_solutions_of_add_lt p h

/-! ## Chevalley's nontrivial-solution corollary (the new content) -/

/-- **Chevalley's corollary (Finset form).** Suppose the total degrees of the system
`f : ι → MvPolynomial σ K` (indexed over `s`) sum to less than the number of
variables, and every `f i` vanishes at the origin (zero constant term), so the
origin `x = 0` is a common zero. Then there is a **nonzero** common zero.

The origin gives at least one solution; the Chevalley–Warning divisibility together
with `p` prime forces the number of solutions to be at least `p ≥ 2`, so a solution
distinct from the origin — necessarily nonzero — exists. Mathlib supplies the
divisibility but not this existence statement. -/
theorem chevalley_warning_nontrivial
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] [Fact p.Prime] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (hdeg : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ)
    (h0 : ∀ i ∈ s, eval (0 : σ → K) (f i) = 0) :
    ∃ x : σ → K, x ≠ 0 ∧ ∀ i ∈ s, eval x (f i) = 0 := by
  -- `p` divides the number of common zeros.
  have hdvd : p ∣ Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    char_dvd_card_solutions_of_sum_lt p hdeg
  -- The origin is a common zero, so there is at least one solution.
  have hpos : 0 < Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  -- `p` is prime, so `p ≥ 2`, and `p ∣ #solutions` with `#solutions ≥ 1` gives `#solutions ≥ 2`.
  have hp : p.Prime := Fact.out
  have h1lt : 1 < Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hdvd)
  -- A second solution, distinct from the origin, hence nonzero.
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h1lt ⟨0, h0⟩
  exact ⟨y.val, fun hc => hy (Subtype.ext hc), y.property⟩

/-- **Chevalley's corollary (single polynomial).** A single polynomial of total
degree less than the number of variables that vanishes at the origin has a nonzero
zero. The classical statement: a form of degree `d < n` in `n` variables with no
constant term has a nontrivial zero over a finite field. -/
theorem chevalley_warning_nontrivial_single
    {K σ : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] [Fact p.Prime] {f : MvPolynomial σ K}
    (hdeg : f.totalDegree < Fintype.card σ) (h0 : eval (0 : σ → K) f = 0) :
    ∃ x : σ → K, x ≠ 0 ∧ eval x f = 0 := by
  have hdvd : p ∣ Fintype.card {x : σ → K // eval x f = 0} :=
    char_dvd_card_solutions p hdeg
  have hpos : 0 < Fintype.card {x : σ → K // eval x f = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩
  have hp : p.Prime := Fact.out
  have h1lt : 1 < Fintype.card {x : σ → K // eval x f = 0} :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hdvd)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h1lt ⟨0, h0⟩
  exact ⟨y.val, fun hc => hy (Subtype.ext hc), y.property⟩

/-! ## Concrete instances over `𝔽₂` -/

/-- The linear form `X₀ + X₁` over `𝔽₂` (degree `1 < 2` variables) has the nonzero
common zero `(1, 1)`: `1 + 1 = 0` in `ZMod 2`. -/
theorem chevalley_linear_F2 :
    (fun _ => (1 : ZMod 2)) ≠ (0 : Fin 2 → ZMod 2) ∧
      eval (fun _ => (1 : ZMod 2)) (X 0 + X 1 : MvPolynomial (Fin 2) (ZMod 2)) = 0 := by
  refine ⟨?_, ?_⟩
  · intro h; have := congrFun h 0; simp at this
  · simp only [eval_add, eval_X]; decide

/-- The quadratic form `X₀·X₁ + X₂²` over `𝔽₂` (total degree `2 < 3` variables) has
the nonzero common zero `(1, 0, 0)`: `1·0 + 0² = 0`. A genuine degree-2 witness,
the typical shape in which Chevalley–Warning is applied. -/
theorem chevalley_quadratic_F2 :
    (![1, 0, 0] : Fin 3 → ZMod 2) ≠ 0 ∧
      eval (![1, 0, 0] : Fin 3 → ZMod 2)
        (X 0 * X 1 + X 2 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) = 0 := by
  refine ⟨?_, ?_⟩
  · intro h; have := congrFun h 0; simp at this
  · simp only [eval_add, eval_mul, eval_pow, eval_X]; decide

end ChevalleyWarningTheoremOQ01
