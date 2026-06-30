/-
  The Jordan–Chevalley–Dunford decomposition
  Open Question (cayley-hamilton-minpoly-oq-01-oq-02)

  Question: Can every linear endomorphism `f` of a finite-dimensional vector space
  over a perfect field be written as `f = s + n`, where `s` is semisimple,
  `n` is nilpotent, `s` and `n` commute, and both are polynomial expressions in `f`?
  Is such a decomposition unique?

  Answer: YES on both counts.

  This is the **Jordan–Chevalley–Dunford decomposition**.  It is the
  coordinate-free, basis-independent shadow of the Jordan canonical form (the
  parent entry `cayley-hamilton-minpoly-oq-01`): instead of choosing a Jordan
  basis, one splits `f` itself into its commuting semisimple and nilpotent parts,
  each of which is a polynomial in `f`.

  Contrast with the parent.  The parent entry obtained the relationship between
  Jordan form and the minimal polynomial under three structural axioms
  (`jordan_normal_form_basis`, `minpoly_product_formula`,
  `maxGenEigenspaceIndex_exact`).  Here we work over a *perfect* field and use
  Mathlib's Newton-iteration proof of the decomposition, so the results below are
  fully machine-checked and **axiom-free**.

  Main results:
  * `jordan_chevalley_decomposition` : existence of the commuting semisimple +
    nilpotent splitting, with both summands exhibited as polynomials in `f`.
  * `jordan_chevalley_unique` : two such polynomial-in-`f` decompositions agree.
  * `jordan_chevalley_existsUnique` : the two combined — there is a unique pair
    of commuting `(s, n)` drawn from `K[f]` with `s` semisimple, `n` nilpotent,
    `f = s + n`.
  * Supporting: `commute_of_mem_adjoin_singleton`, plus the facts that the
    semisimple and nilpotent parts commute with `f`.

  Mathlib 4.26.0 status: `Module.End.exists_isNilpotent_isSemisimple` supplies
  existence (Newton's method, Chambert-Loir); `IsSemisimple.sub_of_commute` (sum of
  commuting semisimples is semisimple over a perfect field) supplies the missing
  ingredient for uniqueness, which Mathlib still lists as a TODO at the level of a
  packaged `ExistsUnique` statement.
-/

import Mathlib.LinearAlgebra.JordanChevalley
import Mathlib.Tactic

open Module.End Polynomial Algebra

namespace CayleyHamiltonMinpolyOQ01OQ02

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Any two elements of `K[f] = adjoin K {f}` commute: each is a polynomial in `f`,
and polynomials in a fixed endomorphism commute. -/
theorem commute_of_mem_adjoin_singleton {f a b : Module.End K V}
    (ha : a ∈ adjoin K {f}) (hb : b ∈ adjoin K {f}) : Commute a b := by
  obtain ⟨p, rfl⟩ := Algebra.adjoin_mem_exists_aeval K f ha
  obtain ⟨q, rfl⟩ := Algebra.adjoin_mem_exists_aeval K f hb
  show aeval f p * aeval f q = aeval f q * aeval f p
  rw [← map_mul, ← map_mul, mul_comm]

/-- The semisimple and nilpotent parts produced below are polynomials in `f`, hence
each commutes with `f`. -/
theorem commute_part_self {f a : Module.End K V} (ha : a ∈ adjoin K {f}) :
    Commute f a :=
  commute_of_mem_adjoin_singleton (self_mem_adjoin_singleton K f) ha

variable [FiniteDimensional K V] [PerfectField K]

/-- **Jordan–Chevalley–Dunford decomposition (existence).**
Every endomorphism `f` of a finite-dimensional vector space over a perfect field
splits as `f = s + n` with `s` semisimple, `n` nilpotent, `s` and `n` commuting,
and both `s` and `n` polynomial expressions in `f`. -/
theorem jordan_chevalley_decomposition (f : Module.End K V) :
    ∃ s n : Module.End K V,
      s.IsSemisimple ∧ IsNilpotent n ∧ Commute s n ∧ f = s + n ∧
      (∃ p : K[X], s = aeval f p) ∧ (∃ q : K[X], n = aeval f q) := by
  obtain ⟨n, hnmem, s, hsmem, hnil, hsemi, hfns⟩ :=
    exists_isNilpotent_isSemisimple (f := f)
  refine ⟨s, n, hsemi, hnil, commute_of_mem_adjoin_singleton hsmem hnmem, ?_, ?_, ?_⟩
  · rw [hfns, add_comm]
  · obtain ⟨p, hp⟩ := Algebra.adjoin_mem_exists_aeval K f hsmem; exact ⟨p, hp.symm⟩
  · obtain ⟨q, hq⟩ := Algebra.adjoin_mem_exists_aeval K f hnmem; exact ⟨q, hq.symm⟩

/-- **Uniqueness of the Jordan–Chevalley decomposition.**
If `f = s₁ + n₁ = s₂ + n₂` with each `sᵢ` semisimple, each `nᵢ` nilpotent, and all
four parts polynomials in `f` (so the two decompositions commute), then the
decompositions coincide. -/
theorem jordan_chevalley_unique {f s₁ n₁ s₂ n₂ : Module.End K V}
    (hs₁mem : s₁ ∈ adjoin K {f}) (hn₁mem : n₁ ∈ adjoin K {f})
    (hs₂mem : s₂ ∈ adjoin K {f}) (hn₂mem : n₂ ∈ adjoin K {f})
    (hs₁ : s₁.IsSemisimple) (hn₁ : IsNilpotent n₁) (he₁ : f = s₁ + n₁)
    (hs₂ : s₂.IsSemisimple) (hn₂ : IsNilpotent n₂) (he₂ : f = s₂ + n₂) :
    s₁ = s₂ ∧ n₁ = n₂ := by
  have hss : Commute s₁ s₂ := commute_of_mem_adjoin_singleton hs₁mem hs₂mem
  have hnn : Commute n₁ n₂ := commute_of_mem_adjoin_singleton hn₁mem hn₂mem
  -- `s₁ + n₁ = s₂ + n₂`.
  have hsum : s₁ + n₁ = s₂ + n₂ := he₁.symm.trans he₂
  -- Rearrange to `s₁ - s₂ = n₂ - n₁`.
  have hkey : s₁ - s₂ = n₂ - n₁ := by
    rw [sub_eq_sub_iff_add_eq_add, hsum]; exact add_comm s₂ n₂
  -- The left side is semisimple (difference of commuting semisimples)…
  have hsemi : (s₁ - s₂).IsSemisimple := IsSemisimple.sub_of_commute hss hs₁ hs₂
  -- …and, being equal to `n₂ - n₁`, it is also nilpotent.
  have hnil : IsNilpotent (s₁ - s₂) := by
    rw [hkey]; exact hnn.symm.isNilpotent_sub hn₂ hn₁
  -- A simultaneously semisimple and nilpotent endomorphism is zero.
  have hzero : s₁ - s₂ = 0 := eq_zero_of_isNilpotent_isSemisimple hnil hsemi
  have hs : s₁ = s₂ := sub_eq_zero.mp hzero
  refine ⟨hs, ?_⟩
  rw [hs] at hsum
  exact add_left_cancel hsum

/-- **Jordan–Chevalley–Dunford, packaged as existence-and-uniqueness.**
There is a unique pair `(s, n)` of commuting endomorphisms, both polynomials in
`f`, with `s` semisimple, `n` nilpotent, and `f = s + n`. -/
theorem jordan_chevalley_existsUnique (f : Module.End K V) :
    ∃! sn : Module.End K V × Module.End K V,
      (sn.1 ∈ adjoin K {f}) ∧ (sn.2 ∈ adjoin K {f}) ∧
      sn.1.IsSemisimple ∧ IsNilpotent sn.2 ∧ f = sn.1 + sn.2 := by
  obtain ⟨n, hnmem, s, hsmem, hnil, hsemi, hfns⟩ :=
    exists_isNilpotent_isSemisimple (f := f)
  refine ⟨(s, n), ⟨hsmem, hnmem, hsemi, hnil, by rw [hfns, add_comm]⟩, ?_⟩
  rintro ⟨s', n'⟩ ⟨hs'mem, hn'mem, hs', hn', he'⟩
  obtain ⟨hs_eq, hn_eq⟩ :=
    jordan_chevalley_unique hs'mem hn'mem hsmem hnmem hs' hn' he' hsemi hnil
      (by rw [hfns, add_comm])
  rw [Prod.ext_iff]
  exact ⟨hs_eq, hn_eq⟩

end CayleyHamiltonMinpolyOQ01OQ02
