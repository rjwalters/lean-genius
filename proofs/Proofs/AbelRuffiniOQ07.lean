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
    * `f_irreducible`, `five_dvd_card_gal_unconditional` — `X⁵−X−1` is irreducible over ℚ
      (Selmer, from Mathlib), hence `5 ∣ |Gal(X⁵−X−1)|` *unconditionally* for the real `f.Gal`.

  ## The genuinely-open gap (now just ONE input)
  The order-divisibility input `5 ∣ |Gal|` is now **fully discharged**: `five_dvd_card_gal`
  derives it for the real `f.Gal` from `Irreducible f` (via `Gal.prime_degree_dvd_card`), and
  `f_irreducible` supplies `Irreducible f` from Mathlib's Selmer theorem
  `X_pow_sub_X_sub_one_irreducible_rat` — no Dedekind–Frobenius bridge, no axioms.  The *only*
  remaining hypothesis is the transposition `∃ swap ∈ Gal`, which still requires the
  **Dedekind–Frobenius bridge** ("factor type of f mod an unramified prime p ⟹ a Frobenius
  element of matching cycle type in `f.Gal`") at `p = 2` — the same machinery the flagship
  gallery entry `InverseGaloisA5.lean` axiomatises as `three_dvd_gal_card`; closing it there
  closes this problem too. We expose that single fact as a *hypothesis* rather than an axiom —
  keeping this file fully verified — and document the bridge as future work.

  ## References
  - Selmer, E. S. (1956). "On the irreducibility of certain trinomials." Math. Scand. 4.
  - Dummit & Foote, Abstract Algebra, §14.8 (Galois groups of quintics; Frobenius).
  - van der Waerden, Algebra I, §61 (Dedekind's theorem on factorisation mod p).
-/

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.RingTheory.Polynomial.Selmer
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

/-- **The generic order-6 ⟹ transposition step.**
    In `S₅`, an element of order `6` necessarily has cycle type `(2,3)`, so its cube is a
    transposition.  This is the reusable form of the concrete `frob2_pow_three_isSwap`
    below; combined with the now-proved Dedekind–Frobenius bridge
    (`DedekindFrobeniusBridge.orderOf_arithFrobAt_eq_inertiaDegIn`, which supplies an
    order-6 element of `f.Gal` from the inertia degree at `p = 2`), it is exactly the form
    that discharges the last open input of `abel-ruffini-oq-07`.

    Proof of `orderOf_eq_six_pow_three_isSwap` obtained via Aristotle (job
    `ddd818e2`, originally in the unregistered companion `AbelRuffiniOQ07Order6Aristotle.lean`);
    folded here, verified under the repo's pinned Mathlib v4.26.0. -/
theorem orderOf_eq_six_pow_three_isSwap
    (σ : S5) (hσ : orderOf σ = 6) : (σ ^ 3).IsSwap := by
  -- `σ ≠ 1` and `σ ^ 6 = 1`.
  have hσne : σ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hσ; exact absurd hσ (by norm_num)
  have hσ6 : σ ^ 6 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  -- Step 1: classify the cycle type of `σ` as `{3, 2}`.
  have hsum : σ.cycleType.sum ≤ 5 := by
    have := σ.sum_cycleType_le; rwa [Fintype.card_fin] at this
  have hmem : ∀ x ∈ σ.cycleType, x = 2 ∨ x = 3 := by
    intro x hx
    have hdvd : x ∣ 6 := by have := dvd_of_mem_cycleType hx; rwa [hσ] at this
    have hge : 2 ≤ x := two_le_of_mem_cycleType hx
    have hle : x ≤ 5 :=
      le_trans (Multiset.single_le_sum (fun _ _ => Nat.zero_le _) x hx) hsum
    interval_cases x <;> omega
  have h3 : (3 : ℕ) ∈ σ.cycleType := by
    by_contra h3
    have hall2 : ∀ x ∈ σ.cycleType, x = 2 := fun x hx =>
      (hmem x hx).resolve_right (fun h => h3 (h ▸ hx))
    have hdvd : orderOf σ ∣ 2 := by
      rw [← lcm_cycleType]; exact Multiset.lcm_dvd.mpr fun b hb => by rw [hall2 b hb]
    rw [hσ] at hdvd; norm_num at hdvd
  have h2 : (2 : ℕ) ∈ σ.cycleType := by
    by_contra h2
    have hall3 : ∀ x ∈ σ.cycleType, x = 3 := fun x hx =>
      (hmem x hx).resolve_left (fun h => h2 (h ▸ hx))
    have hdvd : orderOf σ ∣ 3 := by
      rw [← lcm_cycleType]; exact Multiset.lcm_dvd.mpr fun b hb => by rw [hall3 b hb]
    rw [hσ] at hdvd; norm_num at hdvd
  have key : σ.cycleType = {3, 2} := by
    have e3 : σ.cycleType = 3 ::ₘ σ.cycleType.erase 3 := (Multiset.cons_erase h3).symm
    have h2' : (2 : ℕ) ∈ σ.cycleType.erase 3 :=
      (Multiset.mem_erase_of_ne (by norm_num : (2 : ℕ) ≠ 3)).mpr h2
    have e2 : σ.cycleType.erase 3 = 2 ::ₘ (σ.cycleType.erase 3).erase 2 :=
      (Multiset.cons_erase h2').symm
    have hrest : ((σ.cycleType.erase 3).erase 2).sum = 0 := by
      have hexp : σ.cycleType.sum = 3 + (2 + ((σ.cycleType.erase 3).erase 2).sum) := by
        conv_lhs => rw [e3, Multiset.sum_cons, e2, Multiset.sum_cons]
      omega
    have hrest0 : (σ.cycleType.erase 3).erase 2 = 0 := by
      by_contra hne
      obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero hne
      have hx2 : 2 ≤ x :=
        two_le_of_mem_cycleType (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hx))
      have hxle : x ≤ ((σ.cycleType.erase 3).erase 2).sum :=
        Multiset.single_le_sum (fun _ _ => Nat.zero_le _) x hx
      omega
    rw [e3, e2, hrest0]
  -- Step 2: `sign σ = -1` from the cycle type `{3, 2}` (sum `5`, two cycles).
  have hsign : Equiv.Perm.sign σ = -1 := by
    rw [sign_of_cycleType, key]; decide
  -- Step 3: `σ ^ 3` is an involution, so its cycle type is `replicate k 2`.
  have hpow2 : (σ ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact hσ6
  have hct3 : (σ ^ 3).cycleType
      = Multiset.replicate (Multiset.card (σ ^ 3).cycleType) 2 :=
    cycleType_of_pow_prime_eq_one (p := 2) hpow2
  set k := Multiset.card (σ ^ 3).cycleType with hk
  have hne3 : σ ^ 3 ≠ 1 := by
    intro h
    have hd : orderOf σ ∣ 3 := orderOf_dvd_of_pow_eq_one h
    rw [hσ] at hd; norm_num at hd
  have hpos : 0 < k := card_cycleType_pos.mpr hne3
  have le5 : (σ ^ 3).cycleType.sum ≤ 5 := by
    have := (σ ^ 3).sum_cycleType_le; rwa [Fintype.card_fin] at this
  have esum : (σ ^ 3).cycleType.sum = k * 2 := by
    rw [hct3, Multiset.sum_replicate, smul_eq_mul]
  have hk2 : k * 2 ≤ 5 := esum ▸ le5
  -- Step 4: parity forces `k = 1` (rule out the double-transposition `k = 2`).
  have hsignpow : Equiv.Perm.sign (σ ^ 3) = -1 := by rw [map_pow, hsign]; decide
  have hsignct : Equiv.Perm.sign (σ ^ 3) = (-1) ^ (k * 2 + k) := by
    rw [sign_of_cycleType, esum]
  have hodd : Odd (k * 2 + k) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    rw [hev.neg_one_pow] at hsignct
    rw [hsignpow] at hsignct
    exact absurd hsignct (by decide)
  obtain ⟨j, hj⟩ := hodd
  have hk1 : k = 1 := by omega
  -- Conclude: `(σ ^ 3).cycleType = {2}`, i.e. `σ ^ 3` is a transposition.
  rw [isSwap_iff_cycleType, hct3, hk1]; rfl

/-- **Order-6 assembly criterion (real Galois-group facing).**
    A subgroup `G ≤ S₅` with `5 ∣ |G|` that contains an order-6 element equals `⊤`.
    This is `gal_eq_top_of_five_dvd_and_swap` with the swap input replaced by the
    order-6 element the bridge produces, so the open gap of `abel-ruffini-oq-07` becomes
    exactly "`∃ σ ∈ Gal, orderOf σ = 6`" — the abstract bridge's output. -/
theorem gal_eq_top_of_five_dvd_and_order6
    {G : Subgroup S5} [DecidablePred (· ∈ G)]
    (h5 : 5 ∣ Fintype.card G)
    {σ : S5} (hσG : σ ∈ G) (hσ : orderOf σ = 6) :
    G = ⊤ :=
  gal_eq_top_of_five_dvd_and_swap h5 (G.pow_mem hσG 3)
    (orderOf_eq_six_pow_three_isSwap σ hσ)

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

/-! ## Discharging `Irreducible f` unconditionally — Selmer's theorem

The hypothesis `Irreducible f` of `five_dvd_card_gal` is exactly Selmer's 1956 result for the
trinomial `X⁵ − X − 1`, and Mathlib **already proves the whole Selmer family**: the unit-trinomial
argument `Polynomial.X_pow_sub_X_sub_one_irreducible_rat` shows `Xⁿ − X − 1` is irreducible over
`ℚ` for every `n ≠ 1` (via the Gauss-lemma lift of the corresponding `ℤ[X]` statement, itself
proved from `Complex.UnitTrinomial`).  Instantiating at `n = 5` discharges the hypothesis with no
assumptions, turning `five_dvd_card_gal` into the **unconditional** fact `5 ∣ |Gal(X⁵−X−1)|`. -/

/-- **`f = X⁵ − X − 1` is irreducible over `ℚ`** — Selmer's theorem, from Mathlib.
    A direct instance of `Polynomial.X_pow_sub_X_sub_one_irreducible_rat` at `n = 5`. -/
theorem f_irreducible : Irreducible f := by
  unfold f
  exact X_pow_sub_X_sub_one_irreducible_rat (by norm_num)

/-- **Unconditional: `5 ∣ |Gal(X⁵−X−1)|`.**
    Feeding `f_irreducible` (Selmer) into `five_dvd_card_gal` removes the last hypothesis: five
    divides the order of the *genuine* Galois group `f.Gal` of `X⁵ − X − 1`, with no assumptions,
    no axioms, and no Dedekind–Frobenius bridge.  This is the order-divisibility half of the
    corrected `Gal ≅ S₅` proof, now fully verified for the real polynomial. -/
theorem five_dvd_card_gal_unconditional : 5 ∣ Nat.card f.Gal :=
  five_dvd_card_gal f_irreducible

/-! ## Corroborating the mod-3 cycle type: the reduction mod 3

With `Irreducible f` now discharged unconditionally by Selmer's theorem above, the order-
divisibility input `5 ∣ |Gal|` is fully verified for the real Galois group and needs no
mod-`p` reasoning at all.  The mod-3 reduction nevertheless remains the source of the
*concrete* `frob3` 5-cycle witness: a Frobenius element at `p = 3` is a single 5-cycle
**precisely because** `X⁵ − X − 1` is irreducible over `𝔽₃ = ZMod 3`.

Irreducibility of a monic quintic over a field rules out two obstructions
(`Polynomial.Monic.irreducible_iff_lt_natDegree_lt`, with `natDegree / 2 = 2`):
a **linear** factor (a root) and a **quadratic** factor.  We verify the *linear* half here,
completely and by `decide`: `X⁵ − X − 1` has **no root in `𝔽₃`** — already enough to exclude
the `(1,4)`, `(1,1,3)`, … cycle types with a fixed point.  The arithmetic core
(`no_root_mod3`) is a finite check over the three elements of `ZMod 3`; the polynomial
restatement (`f3_no_root`) is the no-linear-factor input to the irreducibility criterion.

The remaining quadratic obstruction — that none of the three monic irreducible quadratics
over `𝔽₃` (`X²+1`, `X²+X+2`, `X²+2X+2`) divides `f3` (a true finite-field fact, verified by
hand: each leaves a nonzero remainder) — would upgrade `f3_no_root` to full irreducibility
mod 3 and so fully justify the `(5)` cycle type of `frob3`.  A coefficient-comparison `decide`
over the `3⁵` choices proves it, but the `ZMod 3` kernel reduction is prohibitively slow; it is
left as documented future work (best handled by `native_decide` in a separate companion, or by
Aristotle).  Note this is now purely *corroborative*: the headline `5 ∣ |Gal|` is already
unconditional via Selmer, independently of any mod-3 computation. -/

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

/-- The reduction of `X⁵ − X − 1` to `(ZMod 2)[X] = 𝔽₂[X]`.  Over `𝔽₂` we have
    `−1 = 1`, so `f` reduces to `X⁵ + X + 1`. -/
noncomputable def f2 : (ZMod 2)[X] := X ^ 5 - X - 1

/-- **The mod-2 factorisation, machine-checked.**
    `X⁵ − X − 1 ≡ (X² + X + 1)(X³ + X² + 1)` over `𝔽₂` — an (irreducible quadratic)·
    (irreducible cubic).  Where the prose above only *asserts* this factorisation, we
    now verify it as a polynomial identity in `𝔽₂[X]`: expanding the right-hand side
    gives `X⁵ + 2X⁴ + 2X³ + 2X² + X + 1`, and the `2`-coefficients vanish in
    characteristic `2`, leaving `X⁵ + X + 1 = X⁵ − X − 1 = f2`.  This is the arithmetic
    that *justifies* the `(2,3)` cycle type modelled by `frob2`. -/
theorem f2_factorization :
    f2 = (X ^ 2 + X + 1) * (X ^ 3 + X ^ 2 + 1) := by
  have h2 : (2 : (ZMod 2)[X]) = 0 := by
    simpa using CharP.cast_eq_zero ((ZMod 2)[X]) 2
  unfold f2
  linear_combination (-(X ^ 4 + X ^ 3 + X ^ 2 + X + 1)) * h2

/-- The quadratic factor `X² + X + 1` has **no root in `𝔽₂`** (a two-element check:
    `0 ↦ 1`, `1 ↦ 1`).  A degree-`2` polynomial with no root is irreducible, so this
    factor is one of the two irreducible factors of the `(2,3)` decomposition. -/
theorem quad_no_root_mod2 : ∀ x : ZMod 2, x ^ 2 + x + 1 ≠ 0 := by decide

/-- The cubic factor `X³ + X² + 1` has **no root in `𝔽₂`** (`0 ↦ 1`, `1 ↦ 1`).  A
    degree-`3` polynomial with no root is irreducible, completing the verification that
    the mod-2 factorisation is into an irreducible quadratic times an irreducible cubic
    — exactly the `(2,3)` factor type that forces `frob2`'s cycle structure. -/
theorem cubic_no_root_mod2 : ∀ x : ZMod 2, x ^ 3 + x ^ 2 + 1 ≠ 0 := by decide

/-- A representative `(2, 3)`-cycle-type element of `S₅`: the transposition `(0 1)`
    times the 3-cycle `(2 3 4)`.  This models a Frobenius element of `f` at `p = 2`,
    whose factorisation type mod 2 is (irreducible quadratic)·(irreducible cubic)
    (verified in `f2_factorization`, `quad_no_root_mod2`, `cubic_no_root_mod2`). -/
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
