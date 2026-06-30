import Proofs.ChevalleyWarningTheoremOQ01OQ01

/-
# Chevalley–Warning: reifying the solution count into an explicit finite set

## What This Proves

The parent files record the Chevalley–Warning divisibility `p ∣ #solutions`
(`ChevalleyWarningTheoremOQ01`) and its first structural consequences — the `0`-or-`≥ p`
characteristic lower bound, the no-unique-solution law, and the *second-solution*
theorem producing **one** further common zero from any known one
(`ChevalleyWarningTheoremOQ01OQ01`).

Those results live at the level of cardinalities and existence. The pigeonhole arguments
that *use* Chevalley–Warning downstream — most notably the Erdős–Ginzburg–Ziv proof —
need more than "there is a second zero": they iterate over an **explicit finite set** of
common zeros. This file supplies that reification, which neither Mathlib nor the parents
package:

* **The explicit solution set** (`exists_finset_common_zeros`,
  `exists_finset_common_zeros_single`). If a low-degree system has even one common zero,
  there is a concrete `Finset (σ → K)` of **at least `p`** common zeros — the abstract
  bound `p ≤ Fintype.card {x // …}` turned into a finite set you can range over.

* **The `p − 1` other zeros** (`exists_finset_other_common_zeros`,
  `exists_finset_other_common_zeros_single`). From any known common zero `x₀`, there is an
  explicit finite set of **at least `p − 1`** common zeros, *none equal to `x₀`*. This is
  the quantitative strengthening of the parent's second-solution theorem: not just one
  other zero, but `p − 1` of them, packaged for pigeonhole.

* **The nonzero-zero count** (`exists_finset_nonzero_common_zeros`). The origin-vanishing
  case `x₀ = 0`: an origin-vanishing low-degree system has at least `p − 1` **nonzero**
  common zeros, as an explicit finite set.

All proofs reify the parent's `char_le_card_of_exists` through
`Finset.map`/`Finset.erase` cardinality lemmas; everything is `0`-axiom (no `sorry`, no
`axiom`, no `native_decide`).

## Context

The Erdős–Ginzburg–Ziv theorem is proved by applying Chevalley–Warning to two degree-`p−1`
polynomials in `2p − 1` variables: the common zeros are `{0,1}`-vectors selecting a
`p`-element zero-sum subset, and one argues there is a *nonzero* such selection by counting
solutions. Having the solution set as an honest `Finset` — rather than only its cardinality
— is exactly what lets one feed it into `Finset`-level pigeonhole and extract the
combinatorial object. Isolating the reification makes that step reusable.
-/

namespace ChevalleyWarningTheoremOQ01OQ01OQ01

open MvPolynomial

/-! ## The explicit solution set: a `Finset` of at least `p` common zeros -/

/-- **Explicit solution set (Finset form).** If a low-degree system `f` (total degrees
summing to less than the number of variables) has even one common zero, then there is a
concrete `Finset (σ → K)` containing **at least `p`** common zeros.

This reifies the parent's existence lower bound `char_le_card_of_exists`
(`p ≤ Fintype.card {x // …}`) into a finite set one can iterate over: take the image of the
solution subtype's universal finset under the injection `↑ : {x // …} → (σ → K)`. -/
theorem exists_finset_common_zeros
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (hdeg : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ)
    (hx : ∃ x : σ → K, ∀ i ∈ s, eval x (f i) = 0) :
    ∃ T : Finset (σ → K), p ≤ T.card ∧ ∀ x ∈ T, ∀ i ∈ s, eval x (f i) = 0 := by
  have hcard : p ≤ Fintype.card {x : σ → K // ∀ i ∈ s, eval x (f i) = 0} :=
    ChevalleyWarningTheoremOQ01OQ01.char_le_card_of_exists p hdeg hx
  refine ⟨(Finset.univ : Finset {x : σ → K // ∀ i ∈ s, eval x (f i) = 0}).map
      (Function.Embedding.subtype _), ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_univ]; exact hcard
  · intro x hx'
    rw [Finset.mem_map] at hx'
    obtain ⟨y, -, rfl⟩ := hx'
    exact y.property

/-- **Explicit solution set (single polynomial).** A single polynomial of total degree less
than the number of variables, with one known zero, has an explicit `Finset` of at least `p`
zeros. -/
theorem exists_finset_common_zeros_single
    {K σ : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {f : MvPolynomial σ K} (hdeg : f.totalDegree < Fintype.card σ)
    (hx : ∃ x : σ → K, eval x f = 0) :
    ∃ T : Finset (σ → K), p ≤ T.card ∧ ∀ x ∈ T, eval x f = 0 := by
  have hdvd : p ∣ Fintype.card {x : σ → K // eval x f = 0} :=
    char_dvd_card_solutions p hdeg
  obtain ⟨x₀, hx₀⟩ := hx
  have hpos : 0 < Fintype.card {x : σ → K // eval x f = 0} :=
    Fintype.card_pos_iff.mpr ⟨⟨x₀, hx₀⟩⟩
  have hcard : p ≤ Fintype.card {x : σ → K // eval x f = 0} := Nat.le_of_dvd hpos hdvd
  refine ⟨(Finset.univ : Finset {x : σ → K // eval x f = 0}).map
      (Function.Embedding.subtype _), ?_, ?_⟩
  · rw [Finset.card_map, Finset.card_univ]; exact hcard
  · intro x hx'
    rw [Finset.mem_map] at hx'
    obtain ⟨y, -, rfl⟩ := hx'
    exact y.property

/-! ## The `p − 1` other zeros: an explicit `Finset` avoiding a known solution -/

/-- **The `p − 1` other zeros (Finset form).** From **any** known common zero `x₀` of a
low-degree system, there is an explicit `Finset` of at least `p − 1` common zeros, **none of
which equals `x₀`**.

This is the quantitative strengthening of the parent's `exists_second_common_zero`, which
produces a single distinct zero: here we get `p − 1` of them, as a finite set ready for
pigeonhole. Obtained by deleting `x₀` from the explicit `p`-element solution set. -/
theorem exists_finset_other_common_zeros
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (hdeg : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ)
    {x₀ : σ → K} (hx₀ : ∀ i ∈ s, eval x₀ (f i) = 0) :
    ∃ T : Finset (σ → K), x₀ ∉ T ∧ p - 1 ≤ T.card ∧ ∀ x ∈ T, ∀ i ∈ s, eval x (f i) = 0 := by
  obtain ⟨T, hTcard, hTmem⟩ := exists_finset_common_zeros p hdeg ⟨x₀, hx₀⟩
  refine ⟨T.erase x₀, Finset.notMem_erase _ _, ?_, ?_⟩
  · by_cases hmem : x₀ ∈ T
    · rw [Finset.card_erase_of_mem hmem]; omega
    · rw [Finset.erase_eq_of_notMem hmem]; omega
  · intro x hx'
    exact hTmem x (Finset.mem_of_mem_erase hx')

/-- **The `p − 1` other zeros (single polynomial).** From any known zero `x₀` of a single
low-degree polynomial, an explicit `Finset` of at least `p − 1` zeros, none equal to `x₀`. -/
theorem exists_finset_other_common_zeros_single
    {K σ : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {f : MvPolynomial σ K} (hdeg : f.totalDegree < Fintype.card σ)
    {x₀ : σ → K} (hx₀ : eval x₀ f = 0) :
    ∃ T : Finset (σ → K), x₀ ∉ T ∧ p - 1 ≤ T.card ∧ ∀ x ∈ T, eval x f = 0 := by
  obtain ⟨T, hTcard, hTmem⟩ := exists_finset_common_zeros_single p hdeg ⟨x₀, hx₀⟩
  refine ⟨T.erase x₀, Finset.notMem_erase _ _, ?_, ?_⟩
  · by_cases hmem : x₀ ∈ T
    · rw [Finset.card_erase_of_mem hmem]; omega
    · rw [Finset.erase_eq_of_notMem hmem]; omega
  · intro x hx'
    exact hTmem x (Finset.mem_of_mem_erase hx')

/-! ## The nonzero-zero count: the origin-vanishing case -/

/-- **Nonzero common zeros (Finset form).** If every `f i` vanishes at the origin, then the
system has an explicit `Finset` of at least `p − 1` **nonzero** common zeros. This is the
`x₀ = 0` instance of `exists_finset_other_common_zeros`: the deleted point is the origin, so
every member of the returned set is a nonzero common zero. It is the explicit-set form of
the parent's `nontrivial_of_origin`. -/
theorem exists_finset_nonzero_common_zeros
    {K σ ι : Type*} [Field K] [Fintype K] [DecidableEq K] [Fintype σ] [DecidableEq σ]
    (p : ℕ) [CharP K p] {s : Finset ι} {f : ι → MvPolynomial σ K}
    (hdeg : (∑ i ∈ s, (f i).totalDegree) < Fintype.card σ)
    (h0 : ∀ i ∈ s, eval (0 : σ → K) (f i) = 0) :
    ∃ T : Finset (σ → K),
      (0 : σ → K) ∉ T ∧ p - 1 ≤ T.card ∧ ∀ x ∈ T, x ≠ 0 ∧ ∀ i ∈ s, eval x (f i) = 0 := by
  obtain ⟨T, hT0, hTcard, hTmem⟩ := exists_finset_other_common_zeros p hdeg h0
  refine ⟨T, hT0, hTcard, ?_⟩
  intro x hx
  exact ⟨fun hc => hT0 (hc ▸ hx), hTmem x hx⟩

end ChevalleyWarningTheoremOQ01OQ01OQ01
