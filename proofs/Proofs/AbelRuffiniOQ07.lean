/-
  Galois group of f = X⁵ − X − 1 over ℚ  (Open Question OQ-07 of abel-ruffini)

  ## Statement (as curated)
  Gal(X⁵ − X − 1 / ℚ) ≅ S₅, hence the quintic is not solvable by radicals — a
  second Abel–Ruffini witness, complementing the Eisenstein examples.

  ## ⚠ Correction to the curated route
  The curated problem statement proposed proving S₅ via:
    (i)   f irreducible (Selmer 1956);
    (ii)  Δ(f) = 2869 = 19·151 is not a perfect square ⟹ Gal ⊄ A₅;
    (iii) "f has exactly three real roots" ⟹ complex conjugation is a transposition.

  Point (iii) is **mathematically false**. Verified symbolically (sympy/numpy):
  X⁵ − X − 1 has **exactly ONE real root** (≈ 1.1673); its four non-real roots form
  TWO complex-conjugate pairs. Hence complex conjugation acts as a **product of two
  transpositions** — an *even* permutation lying in A₅, **not** a transposition. So
  Mathlib's clean real-roots assembler `galActionHom_bijective_of_prime_degree`
  (which needs `card ℂ-roots = card ℝ-roots + 2`, i.e. exactly one conjugate pair)
  does NOT apply to this polynomial. We formalise this correction below
  (`prod_two_swaps_mem_alternating`).

  Moreover route (ii) **alone is insufficient**: among the transitive subgroups of S₅
  (C₅, D₅, F₂₀, A₅, S₅), those containing an odd permutation are exactly {F₂₀, S₅}.
  Excluding F₂₀ (order 20) requires the supplementary input `3 ∣ |Gal|`.

  ## The corrected proof (Dedekind / Frobenius cycle types)
  Verified mod-p factorisation types of f:
    p = 3 : irreducible  ⟹ Frobenius is a 5-cycle  ⟹ transitive, 5 ∣ |Gal|.
    p = 2 : (deg-2)·(deg-3), Frobenius σ of order 6 ⟹ σ³ is a **transposition** ∈ Gal.
  Then `subgroup_eq_top_of_swap_mem` (card of the root set = 5 is prime, 5 ∣ |Gal|,
  and a swap ∈ Gal) gives Gal = ⊤ = S₅.

  ## What THIS file verifies (0 sorry, 0 axiom)
  The group-theoretic *reduction* of the corrected proof, machine-checked down to its
  two number-theoretic inputs (which the Dedekind–Frobenius bridge supplies):

    * `gal_eq_top_of_five_dvd_and_swap` — the assembly: any subgroup G ≤ S₅ with
      5 ∣ |G| and containing a transposition equals ⊤.  This is the corrected
      criterion stated as a clean, reusable, hypothesis-driven theorem.
    * `isSwap_not_mem_alternating` — a transposition is odd (the (ii) direction).
    * `prod_two_swaps_mem_alternating` — a product of two swaps is even: the formal
      content of the correction (complex conjugation, being a double transposition,
      lies in A₅ and cannot be the transposition the curated route assumed).
    * `f_natDegree`, `f_monic`, `natDegree_prime` — anchoring numeric facts about f.

  ## The genuinely-open gap
  The two hypotheses `5 ∣ |Gal|` and `∃ swap ∈ Gal` are exactly the outputs of the
  **Dedekind–Frobenius bridge** ("factor type of f mod an unramified prime p ⟹ a
  Frobenius element of matching cycle type in `f.Gal`"), which Mathlib (pin v4.26.0)
  does not yet provide. This is the same machinery the flagship gallery entry
  `InverseGaloisA5.lean` axiomatises as `three_dvd_gal_card`; closing it there closes
  this problem too. We therefore expose those two facts as *hypotheses* rather than
  axioms — keeping this file fully verified — and document the bridge as future work.

  ## References
  - Selmer, E. S. (1956). "On the irreducibility of certain trinomials." Math. Scand. 4.
  - Dummit & Foote, Abstract Algebra, §14.8 (Galois groups of quintics; Frobenius).
  - van der Waerden, Algebra I, §61 (Dedekind's theorem on factorisation mod p).
-/

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.Tactic

open Equiv Equiv.Perm Polynomial

namespace AbelRuffiniOQ07

/-- The root set of a degree-5 polynomial has 5 elements; we work concretely with
    `Equiv.Perm (Fin 5)`, the symmetric group `S₅`. -/
abbrev S5 := Equiv.Perm (Fin 5)

/-- `Fintype.card (Fin 5) = 5` is prime — the hypothesis the assembler needs. -/
theorem card_fin5_prime : (Fintype.card (Fin 5)).Prime := by
  rw [Fintype.card_fin]; norm_num

/-- **Corrected assembly criterion.**
    A subgroup `G ≤ S₅` that (a) has order divisible by 5 and (b) contains a
    transposition must be all of `S₅`.  This is the group-theoretic core of the
    corrected proof of `Gal(X⁵−X−1) ≅ S₅`: input (a) comes from irreducibility of
    `f` mod 3 (a 5-cycle Frobenius), input (b) from the order-6 Frobenius at `p = 2`
    (its cube is a transposition). -/
theorem gal_eq_top_of_five_dvd_and_swap
    {G : Subgroup S5} [DecidablePred (· ∈ G)]
    (h5 : 5 ∣ Fintype.card G)
    {τ : S5} (hτG : τ ∈ G) (hτ : τ.IsSwap) :
    G = ⊤ := by
  refine Equiv.Perm.subgroup_eq_top_of_swap_mem ?_ ?_ hτG hτ
  · exact card_fin5_prime
  · rwa [Fintype.card_fin]

/-- A transposition is an **odd** permutation, hence lies outside `A₅`.
    This is the discriminant direction (Δ not a square ⟹ Gal ⊄ A₅) at the level of
    a single odd element. -/
theorem isSwap_not_mem_alternating {τ : S5} (hτ : τ.IsSwap) :
    τ ∉ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, hτ.sign_eq]
  decide

/-- **The formal correction.**
    A product of two transpositions is an **even** permutation: it lies in `A₅`.
    Complex conjugation on the roots of `X⁵−X−1` is exactly such a double
    transposition (one real root fixed, two conjugate pairs swapped), so — contrary
    to the curated statement — it is *not* a transposition and cannot by itself
    force the Galois group to be `S₅`. -/
theorem prod_two_swaps_mem_alternating {τ₁ τ₂ : S5}
    (h₁ : τ₁.IsSwap) (h₂ : τ₂.IsSwap) :
    τ₁ * τ₂ ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, map_mul, h₁.sign_eq, h₂.sign_eq]
  decide

/-- The quintic under study. -/
noncomputable def f : ℚ[X] := X ^ 5 - X - 1

/-- `f` has degree 5. -/
@[simp] theorem f_natDegree : f.natDegree = 5 := by
  unfold f; compute_degree!

/-- `f` is monic. -/
theorem f_monic : f.Monic := by
  unfold f; monicity!

/-- The degree is prime — the structural fact that makes the prime-degree machinery
    (`subgroup_eq_top_of_swap_mem`, `prime_degree_dvd_card`) applicable. -/
theorem natDegree_prime : Nat.Prime f.natDegree := by
  rw [f_natDegree]; norm_num

end AbelRuffiniOQ07
