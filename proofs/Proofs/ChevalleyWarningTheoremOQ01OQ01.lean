import Proofs.ChevalleyWarningTheoremOQ01

/-
# Chevalley–Warning: the characteristic lower bound and the no-unique-solution law

## What This Proves

The parent file (`ChevalleyWarningTheoremOQ01`) records the Chevalley–Warning
divisibility `p ∣ #solutions` and Chevalley's nontrivial-solution corollary (an
origin-vanishing low-degree system has a *nonzero* common zero). This file extracts
the structural consequences of the bare divisibility that the corollary specializes,
none of which Mathlib packages:

* **The characteristic lower bound** (`card_zero_or_ge`, `card_zero_or_ge_single`).
  For a low-degree system the number of common zeros is **either `0` or at least the
  characteristic `p`** — there is no intermediate count between the empty solution set
  and a full coset's worth of `p` of them. (This is the elementary "0 or ≥ p" bound
  forced by `p ∣ #solutions`; it is far weaker than Warning's *second* theorem, whose
  bound is `0` or `≥ qⁿ⁻ᵈ`, and which is **not** proved here.)

* **The no-unique-solution law** (`card_ne_one`, `card_ne_one_single`). A low-degree
  system can **never have exactly one** common zero: `#solutions = 1` would give
  `p ∣ 1`, impossible for a prime. Equivalently, a low-degree system with a *unique*
  solution does not exist — any solution is one of at least `p`.

* **The second-solution theorem** (`exists_second_common_zero`,
  `exists_second_common_zero_single`). From **any** known common zero `x₀` — not only
  the origin — a *second*, distinct common zero must exist. The parent's
  `chevalley_warning_nontrivial` is exactly the `x₀ = 0` instance, recovered here as
  `exists_second_common_zero` applied at the origin.

* **The existence lower bound** (`char_le_card_of_exists`). If a low-degree system has
  even one common zero, it has at least `p` of them.

All proofs reduce the parent's `p ∣ #solutions` through `Nat.le_of_dvd` /
`Nat.dvd_one`; everything is `0`-axiom (no `sorry`, no `axiom`, no `native_decide`).

## Context

The "0 or ≥ p" dichotomy is the form of Chevalley–Warning actually invoked in the
Erdős–Ginzburg–Ziv argument and in counting-over-finite-fields applications: one shows
a solution exists (often the origin) and immediately concludes there are at least `p`,
hence a *second* one to exploit. Isolating that step from the divisibility makes the
downstream "find another zero" move a one-line application.
-/

namespace ChevalleyWarningTheoremOQ01OQ01

open MvPolynomial

/-! ## The characteristic lower bound: `0` or `≥ p` -/

/-- **Characteristic lower bound (Finset form).** For a finite system
`f : ι → MvPolynomial σ K` indexed over `s`, whose total degrees sum to less than the
number of variables, the number of common zeros is either `0` or at least the
characteristic `p`. There is no count strictly between `0` and `p`.

Immediate from Chevalley–Warning's `p ∣ #solutions`: a nonzero multiple of `p` is at
least `p`. (Much weaker than Warning's second theorem, which gives `0` or `≥ qⁿ⁻ᵈ`.) -/
theorem card_zero_or_ge
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (hdeg : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ) :
    Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} = 0 ∨
      p ≤ Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} := by
  have hdvd : p ∣ Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    char_dvd_card_solutions_of_sum_lt p hdeg
  rcases Nat.eq_zero_or_pos (Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0}) with h | h
  · exact Or.inl h
  · exact Or.inr (Nat.le_of_dvd h hdvd)

/-- **Characteristic lower bound (single polynomial).** A single polynomial of total
degree less than the number of variables has either `0` zeros or at least `p`. -/
theorem card_zero_or_ge_single
    {K σ : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {f : MvPolynomial σ K} (hdeg : f.totalDegree < Fintype.card σ) :
    Fintype.card {x : σ → K // eval x f = 0} = 0 ∨
      p ≤ Fintype.card {x : σ → K // eval x f = 0} := by
  have hdvd : p ∣ Fintype.card {x : σ → K // eval x f = 0} :=
    char_dvd_card_solutions p hdeg
  rcases Nat.eq_zero_or_pos (Fintype.card {x : σ → K // eval x f = 0}) with h | h
  · exact Or.inl h
  · exact Or.inr (Nat.le_of_dvd h hdvd)

/-! ## The no-unique-solution law: `#solutions ≠ 1` -/

/-- **No unique solution (Finset form).** A low-degree system can never have *exactly
one* common zero: `#solutions = 1` would force `p ∣ 1`, impossible for the prime
characteristic `p`. So the solution set is never a singleton. -/
theorem card_ne_one
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] [Fact p.Prime] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (hdeg : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ) :
    Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} ≠ 1 := by
  intro h
  have hdvd : p ∣ Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    char_dvd_card_solutions_of_sum_lt p hdeg
  rw [h] at hdvd
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hdvd)

/-- **No unique solution (single polynomial).** A single low-degree polynomial never
has exactly one zero. -/
theorem card_ne_one_single
    {K σ : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] [Fact p.Prime] {f : MvPolynomial σ K}
    (hdeg : f.totalDegree < Fintype.card σ) :
    Fintype.card {x : σ → K // eval x f = 0} ≠ 1 := by
  intro h
  have hdvd : p ∣ Fintype.card {x : σ → K // eval x f = 0} :=
    char_dvd_card_solutions p hdeg
  rw [h] at hdvd
  exact (Fact.out : p.Prime).ne_one (Nat.dvd_one.mp hdvd)

/-! ## Existence lower bound and the second-solution theorem -/

/-- **Existence lower bound (Finset form).** If a low-degree system has even one common
zero, then it has at least `p` of them. -/
theorem char_le_card_of_exists
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (hdeg : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ)
    (hx : ∃ x : σ → K, ∀ i ∈ s, eval x (f i) = 0) :
    p ≤ Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} := by
  have hdvd : p ∣ Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    char_dvd_card_solutions_of_sum_lt p hdeg
  obtain ⟨x, hx⟩ := hx
  have hpos : 0 < Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨x, hx⟩⟩
  exact Nat.le_of_dvd hpos hdvd

/-- **Second-solution theorem (Finset form).** Given **any** known common zero `x₀` of
a low-degree system, a *second* common zero distinct from `x₀` exists. The parent's
`chevalley_warning_nontrivial` (origin ⟹ nonzero zero) is the special case `x₀ = 0`.

`p ∣ #solutions` together with `#solutions ≥ 1` (witnessed by `x₀`) forces
`#solutions ≥ p ≥ 2`, so a point other than `x₀` is also a solution. -/
theorem exists_second_common_zero
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] [Fact p.Prime] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (hdeg : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ)
    {x₀ : σ → K} (hx₀ : ∀ i ∈ s, eval x₀ (f i) = 0) :
    ∃ x : σ → K, x ≠ x₀ ∧ ∀ i ∈ s, eval x (f i) = 0 := by
  have hdvd : p ∣ Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    char_dvd_card_solutions_of_sum_lt p hdeg
  have hpos : 0 < Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨x₀, hx₀⟩⟩
  have hp : p.Prime := Fact.out
  have h1lt : 1 < Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hdvd)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h1lt ⟨x₀, hx₀⟩
  exact ⟨y.val, fun hc => hy (Subtype.ext hc), y.property⟩

/-- **Second-solution theorem (single polynomial).** Given any known zero `x₀` of a
single low-degree polynomial, a distinct zero exists. -/
theorem exists_second_common_zero_single
    {K σ : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] [Fact p.Prime] {f : MvPolynomial σ K}
    (hdeg : f.totalDegree < Fintype.card σ)
    {x₀ : σ → K} (hx₀ : eval x₀ f = 0) :
    ∃ x : σ → K, x ≠ x₀ ∧ eval x f = 0 := by
  have hdvd : p ∣ Fintype.card {x : σ → K // eval x f = 0} :=
    char_dvd_card_solutions p hdeg
  have hpos : 0 < Fintype.card {x : σ → K // eval x f = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨x₀, hx₀⟩⟩
  have hp : p.Prime := Fact.out
  have h1lt : 1 < Fintype.card {x : σ → K // eval x f = 0} :=
    lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd hpos hdvd)
  obtain ⟨y, hy⟩ := Fintype.exists_ne_of_one_lt_card h1lt ⟨x₀, hx₀⟩
  exact ⟨y.val, fun hc => hy (Subtype.ext hc), y.property⟩

/-- **Recovering the parent corollary.** The origin-vanishing case: if every `f i`
vanishes at `0`, the second-solution theorem at `x₀ = 0` yields a nonzero common zero —
exactly `ChevalleyWarningTheoremOQ01.chevalley_warning_nontrivial`. -/
theorem nontrivial_of_origin
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] [Fact p.Prime] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (hdeg : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ)
    (h0 : ∀ i ∈ s, eval (0 : σ → K) (f i) = 0) :
    ∃ x : σ → K, x ≠ 0 ∧ ∀ i ∈ s, eval x (f i) = 0 :=
  exists_second_common_zero p hdeg h0

end ChevalleyWarningTheoremOQ01OQ01
