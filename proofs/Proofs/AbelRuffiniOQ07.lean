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
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.ZMod.Basic
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

/-! ## The order-divisibility input from the *real* Galois group

The witnesses below (`frob2`, `frob3`) model Frobenius elements as abstract cycle-type
representatives in `S₅`, and the capstone `gal_eq_top_of_frobenii` assembles `S₅` from
them *modulo* the Dedekind–Frobenius bridge that places those representatives inside the
genuine Galois group.  One half of that bridge — the order-`5` input `5 ∣ |Gal|`, which
`frob3` supplies abstractly — can be obtained **directly and unconditionally from
irreducibility**, with no Frobenius/Dedekind input at all:

Mathlib's `Polynomial.Gal.prime_degree_dvd_card` states that for a polynomial of prime
degree over a characteristic-zero field, the degree divides the cardinality of its Galois
group (the Galois group acts transitively on the roots, so the orbit-stabiliser theorem
forces `deg ∣ |Gal|`).  For `f = X⁵ − X − 1` this gives `5 ∣ |Gal(f)|` *for the actual
`Polynomial.Gal` of `f`* the instant we know `f` is irreducible — replacing the abstract
`frob3` half of the bridge by a purely algebraic fact.  Only the *transposition* input
(`frob2 ^ 3`, from the cycle type mod `2`) then remains genuinely Frobenius-dependent. -/

/-- **The `5 ∣ |Gal|` input from irreducibility, for the real Galois group.**
    If `f = X⁵ − X − 1` is irreducible over `ℚ`, then `5` divides the order of its
    genuine Galois group `f.Gal` — because a prime-degree irreducible polynomial over a
    characteristic-zero field has a Galois group acting transitively on its roots
    (`Polynomial.Gal.prime_degree_dvd_card`).  This discharges the order-divisibility
    half of the corrected proof *without* the Dedekind–Frobenius bridge: where `frob3`
    supplies `5 ∣ |G|` for an abstract subgroup `G ≤ S₅`, this supplies it for the actual
    `f.Gal`, modulo only the (separately classical) irreducibility of `f`. -/
theorem five_dvd_card_gal (hirr : Irreducible f) : 5 ∣ Nat.card f.Gal := by
  have h := Polynomial.Gal.prime_degree_dvd_card hirr natDegree_prime
  rwa [f_natDegree] at h

/-! ## Toward discharging `Irreducible f`: the reduction mod 3

`five_dvd_card_gal` is conditional on `Irreducible f`.  Classically that hypothesis is
established by **reduction mod 3**: `X⁵ − X − 1` stays degree-`5` and *irreducible* over
the finite field `𝔽₃ = ZMod 3`, and a monic integer polynomial whose mod-`p` reduction is
irreducible of the same degree is irreducible over `ℚ` (`Monic.irreducible_of_irreducible_map`
to lift `𝔽₃ → ℤ`, then Gauss's lemma `ℤ → ℚ`).

Irreducibility of a monic quintic over a field has two obstructions to rule out
(`Polynomial.Monic.irreducible_iff_lt_natDegree_lt`, with `natDegree / 2 = 2`):
a **linear** factor (a root) and a **quadratic** factor.  We discharge the *linear* half
here, completely and by `decide`: `X⁵ − X − 1` has **no root in `𝔽₃`**.  The arithmetic
core (`no_root_mod3`) is a finite check over the three elements of `ZMod 3`; the polynomial
restatement (`f3_no_root`) is the no-linear-factor input to the irreducibility criterion.

The remaining quadratic obstruction — that none of the three monic irreducible quadratics
over `𝔽₃` (`X²+1`, `X²+X+2`, `X²+2X+2`) divides `f` — is the only piece left before
`five_dvd_card_gal` becomes unconditional.  It resists `decide` (polynomial `%ₘ` does not
kernel-reduce through `Finsupp`), so it is left as documented future work, best handled by
Aristotle (a known finite-field computation) or a hand enumeration of the nine monic
quadratics. -/

/-- The reduction of `X⁵ − X − 1` to `(ZMod 3)[X] = 𝔽₃[X]`. -/
noncomputable def f3 : (ZMod 3)[X] := X ^ 5 - X - 1

/-- **Arithmetic core of the linear-factor obstruction.**
    `X⁵ − X − 1` has no zero in `𝔽₃`: a finite check over the three field elements
    (`0 ↦ −1`, `1 ↦ −1`, `2 ↦ 2⁵−2−1 = 29 ≡ 2`), none of which is `0`. -/
theorem no_root_mod3 : ∀ x : ZMod 3, x ^ 5 - x - 1 ≠ 0 := by decide

/-- **The no-linear-factor input mod 3.**
    `f` reduced mod `3` has no root in `𝔽₃`, hence no degree-`1` factor — the first of the
    two obstructions in `Monic.irreducible_iff_lt_natDegree_lt` for the quintic `f3`. -/
theorem f3_no_root (x : ZMod 3) : f3.eval x ≠ 0 := by
  simpa [f3] using no_root_mod3 x

/-! ## A concrete Frobenius witness at `p = 2`

The corrected proof's swap input — hypothesis `(b)` of
`gal_eq_top_of_five_dvd_and_swap` — comes from the factorisation of `f` modulo 2:

    X⁵ − X − 1  ≡  (X² + X + 1)(X³ + X² + 1)   (mod 2),

an irreducible quadratic times an irreducible cubic.  A Frobenius element of `f`
at `2` therefore has cycle type `(2, 3)`: it is conjugate to a disjoint product of
a transposition and a 3-cycle, an order-6 permutation.  Where the prose above only
*asserts* "σ of order 6 ⟹ σ³ is a transposition", we now exhibit such an element
`frob2 ∈ S₅` concretely and machine-check that its cube is exactly the
transposition that input `(b)` feeds into the assembly criterion — turning the
prose cycle-type computation into verified permutation data. -/

/-- A representative `(2, 3)`-cycle-type element of `S₅`: the transposition `(0 1)`
    times the 3-cycle `(2 3 4)`.  This models a Frobenius element of `f` at `p = 2`,
    whose factorisation type mod 2 is (irreducible quadratic)·(irreducible cubic). -/
def frob2 : S5 := Equiv.swap 0 1 * (Equiv.swap 2 3 * Equiv.swap 3 4)

/-- `frob2` is an **odd** permutation (sign `= −1`), so a `(2, 3)`-type element lies
    outside `A₅` — consistent with `Gal ⊄ A₅` and with the role this element plays
    as the *odd* Frobenius the discriminant route requires. -/
theorem frob2_not_mem_alternating : frob2 ∉ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide

/-- The cube of the order-6 element `frob2` is the transposition `(0 1)`: cubing
    kills the 3-cycle part and leaves the swap.  This is precisely the order-6 ⟹
    transposition step of the corrected proof, made concrete. -/
theorem frob2_pow_three_eq_swap : frob2 ^ 3 = Equiv.swap (0 : Fin 5) 1 := by decide

/-- Hence a `(2, 3)`-Frobenius element supplies exactly the transposition required
    by `gal_eq_top_of_five_dvd_and_swap`: `frob2 ^ 3` is a swap. -/
theorem frob2_pow_three_isSwap : (frob2 ^ 3).IsSwap :=
  frob2_pow_three_eq_swap ▸ ⟨0, 1, by decide, rfl⟩

/-! ## A concrete Frobenius witness at `p = 3`

The corrected proof's *order-divisibility* input — hypothesis `(a)`,
`5 ∣ |Gal|`, of `gal_eq_top_of_five_dvd_and_swap` — comes from the factorisation of
`f` modulo 3:

    X⁵ − X − 1  is irreducible   (mod 3).

A Frobenius element of `f` at `3` therefore has cycle type `(5)`: it is a single
`5`-cycle, an element of order `5`.  Such an element lies in the Galois group, so by
Lagrange `5 = orderOf(Frobenius) ∣ |Gal|`.  Where the prose above only *asserts*
"irreducible mod 3 ⟹ 5-cycle ⟹ 5 ∣ |Gal|", we now exhibit such an element
`frob3 ∈ S₅` concretely and machine-check that it has order `5`, then derive the
divisibility input for *any* subgroup containing it — turning the prose cycle-type
computation into verified permutation data, exactly as `frob2` does for the swap. -/

/-- A representative `5`-cycle of `S₅`, written as a product of adjacent
    transpositions: `(0 1)(1 2)(2 3)(3 4) = (0 1 2 3 4)`.  This models a Frobenius
    element of `f` at `p = 3`, whose factorisation type mod 3 is a single irreducible
    quintic, i.e. one `5`-cycle. -/
def frob3 : S5 := Equiv.swap 0 1 * (Equiv.swap 1 2 * (Equiv.swap 2 3 * Equiv.swap 3 4))

/-- `frob3 ^ 5 = 1`: the `5`-cycle returns to the identity after five steps. -/
theorem frob3_pow_five : frob3 ^ 5 = 1 := by decide

/-- `frob3 ≠ 1`: it genuinely moves points (so its order is not `1`). -/
theorem frob3_ne_one : frob3 ≠ 1 := by decide

/-- The `p = 3` Frobenius `frob3` has **order `5`**.  Since `5` is prime, its order
    divides `5` and is not `1`, hence equals `5` — the precise content of
    "irreducible mod 3 ⟹ a `5`-cycle Frobenius". -/
theorem orderOf_frob3 : orderOf frob3 = 5 := by
  have hdvd : orderOf frob3 ∣ 5 := orderOf_dvd_of_pow_eq_one frob3_pow_five
  rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ hdvd) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) frob3_ne_one
  · exact h

/-- **The `5 ∣ |Gal|` input, made concrete.**
    Any subgroup `G ≤ S₅` that contains the order-`5` Frobenius `frob3` has order
    divisible by `5` (Lagrange).  This supplies hypothesis `(a)` of
    `gal_eq_top_of_five_dvd_and_swap` from a single membership fact, replacing the
    prose appeal to transitivity / a `5`-cycle. -/
theorem five_dvd_card_of_frob3_mem {G : Subgroup S5} [DecidablePred (· ∈ G)]
    (h : frob3 ∈ G) : 5 ∣ Fintype.card G := by
  have hco : orderOf (⟨frob3, h⟩ : G) = 5 := by
    rw [Subgroup.orderOf_mk]; exact orderOf_frob3
  have hd : orderOf (⟨frob3, h⟩ : G) ∣ Fintype.card G := orderOf_dvd_card
  rwa [hco] at hd

/-- **Capstone: both Frobenius witnesses ⟹ the full Galois group is `S₅`.**
    A subgroup `G ≤ S₅` containing *both* the `p = 3` Frobenius `frob3` (a `5`-cycle)
    and the `p = 2` Frobenius `frob2` (a `(2,3)`-element) must be all of `S₅`:
    `frob3` forces `5 ∣ |G|`, while `frob2 ^ 3 ∈ G` is the transposition.  This is the
    corrected proof of `Gal(X⁵−X−1) ≅ S₅` assembled entirely from concrete
    permutation data — modulo the genuinely-open Dedekind–Frobenius bridge that places
    `frob2, frob3` (as cycle-type representatives) inside the actual Galois group. -/
theorem gal_eq_top_of_frobenii {G : Subgroup S5} [DecidablePred (· ∈ G)]
    (h3 : frob3 ∈ G) (h2 : frob2 ∈ G) : G = ⊤ :=
  gal_eq_top_of_five_dvd_and_swap (five_dvd_card_of_frob3_mem h3)
    (G.pow_mem h2 3) frob2_pow_three_isSwap

/-- **The two Frobenius witnesses generate all of `S₅`** (unconditional).

Specializing `gal_eq_top_of_frobenii` to the subgroup they generate, the two
explicit permutations `frob2 = (0 1)(2 3 4)` and `frob3 = (0 1 2 3 4)` together
generate the whole symmetric group: `⟨frob2, frob3⟩ = S₅`.  This is the concrete,
hypothesis-free form of the assembly criterion — the order-`5` cycle supplies
`5 ∣ |⟨frob2, frob3⟩|` and the cube of the order-`6` element supplies the
transposition, so the generated subgroup cannot be proper.  (Classically: a
transposition `(0 1)` together with the `5`-cycle `(0 1 2 3 4)` generate `S₅`.)

The genuinely-open content of OQ-07 is *not* this group-theoretic fact but the
Dedekind–Frobenius bridge placing cycle-type representatives inside the actual
Galois group of `X⁵ − X − 1`. -/
theorem closure_frobenii_eq_top :
    Subgroup.closure ({frob2, frob3} : Set S5) = ⊤ := by
  classical
  have h2 : frob2 ∈ Subgroup.closure ({frob2, frob3} : Set S5) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h3 : frob3 ∈ Subgroup.closure ({frob2, frob3} : Set S5) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  exact gal_eq_top_of_frobenii h3 h2

end AbelRuffiniOQ07
