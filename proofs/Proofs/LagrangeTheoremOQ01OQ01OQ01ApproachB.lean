/-
  pq-Groups: Approach B preliminaries — cyclic structure of `(ZMod q)ˣ`
  (lagrange-theorem-oq-01-oq-01-oq-01)

  **Open Question (OQ-01-OQ-01-OQ-01)** continued. Approach A
  (`Proofs.LagrangeTheoremOQ01OQ01OQ01`) handles the `p = 2`
  specialisation via Mathlib's `DihedralGroup q`. This file lays the
  foundation for Approach B (general primes `p < q` with `p ∣ (q - 1)`),
  which constructs a non-cyclic group of order `pq` as the semidirect
  product `ZMod q ⋊[φ] ZMod p` for a non-trivial homomorphism
  `φ : ZMod p →* MulAut (ZMod q)`.

  **S3a + S3b deliverables in this iteration**:

  * `isCyclic_units_zmod` — the unit group `(ZMod q)ˣ` is cyclic
    whenever `q` is prime (via Mathlib's
    `isCyclic_of_subgroup_isDomain`).
  * `card_units_zmod` — its cardinality is `q - 1` (via
    `ZMod.card_units_eq_totient` and `Nat.totient_prime`).
  * `exists_unit_of_order_p` — for each prime `p` dividing `q - 1`,
    `(ZMod q)ˣ` contains an element of order exactly `p`. The witness
    is `g₀ ^ ((q - 1) / p)` for a generator `g₀`; the order calculation
    follows the pattern of `Proofs.LagrangeTheoremOQ01OQ03` (Hall's
    theorem for cyclic groups, `orderOf_pow_div_of_dvd`).

  **Deferred to future iterations**:

  * S3c — Lift the unit of order `p` to a non-trivial group homomorphism
    `φ : ZMod p →* MulAut (ZMod q)`. Requires the field-of-fractions
    automorphism action on `ZMod q` (multiplication-by-unit gives a
    `MulAut`).
  * S3d — Assemble `ZMod q ⋊[φ] ZMod p`, verify `Nat.card = p * q`, and
    prove `¬ IsCyclic` (semidirect product with non-trivial action is
    non-abelian, hence non-cyclic).

  **API verification (Mathlib v4.26.0)**: Each Mathlib lemma used below
  is already exercised in `Proofs.PrimitiveRoots` (lines 81–86) and
  `Proofs.LagrangeTheoremOQ01OQ03` (lines 113–117). No new Mathlib
  surface; the construction relies only on `IsCyclic`, `orderOf`, and
  `ZMod` API at v4.26.0 already used elsewhere in this repository.

  References:
  - Dummit, D. & Foote, R. (2004). Abstract Algebra, §4.5, Theorem 17
    (groups of order `pq` for `p < q` primes).
  - Mathlib4 `Mathlib/RingTheory/IntegralDomain.lean`
    (`isCyclic_of_subgroup_isDomain`).
  - Mathlib4 `Mathlib/Data/ZMod/Basic.lean`
    (`ZMod.card_units_eq_totient`).
  - Mathlib4 `Mathlib/GroupTheory/OrderOfElement.lean`
    (`orderOf_pow'`).
  - Sister file: `Proofs.LagrangeTheoremOQ01OQ01OQ01` (Approach A).

  Tags: group-theory, lagrange, pq-groups, cyclic, units, ZMod,
  primitive-root, order-extraction, semidirect-product (deferred)
-/

import Mathlib
import Proofs.LagrangeTheoremOQ01OQ01OQ01

namespace LagrangeOQ01OQ01OQ01.ApproachB

variable {q : ℕ} [hqfact : Fact q.Prime]

/-! ## S3a: Cyclic structure and cardinality of `(ZMod q)ˣ`

For every prime `q`, the unit group `(ZMod q)ˣ` is finite cyclic of
order `q - 1`. Both facts are direct consequences of standard Mathlib
infrastructure and mirror the corresponding declarations in
`Proofs.PrimitiveRoots`. -/

/-- The unit group `(ZMod q)ˣ` of a prime modulus is cyclic.

    Proof: `(ZMod q)ˣ` is a finite subgroup of units in the integral
    domain `ZMod q` (which is a field for prime `q`); finite subgroups
    of units in integral domains are cyclic
    (`isCyclic_of_subgroup_isDomain`). -/
instance isCyclic_units_zmod : IsCyclic (ZMod q)ˣ :=
  isCyclic_of_subgroup_isDomain (Units.coeHom (ZMod q)) Units.val_injective

/-- The unit group `(ZMod q)ˣ` has cardinality `q - 1` for any prime
    `q`. This is the count of residues `1 ≤ a < q` coprime to `q`,
    namely Euler's totient `φ(q) = q - 1`. -/
theorem card_units_zmod : Fintype.card (ZMod q)ˣ = q - 1 := by
  rw [ZMod.card_units_eq_totient, Nat.totient_prime hqfact.out]

/-! ## S3b: Element of order `p` in `(ZMod q)ˣ` when `p ∣ (q - 1)`

For each prime `p` dividing the cyclic-group order `q - 1`, a
generator `g₀` of `(ZMod q)ˣ` raised to the power `(q - 1) / p` has
exact order `p`. This element is the seed of the non-trivial
homomorphism `φ : ZMod p →* MulAut (ZMod q)` constructed in S3c. -/

/-- **Order-`p` element extraction**. For each prime `p` dividing
    `q - 1`, the unit group `(ZMod q)ˣ` contains a unit of order
    exactly `p`. The explicit witness is `g₀ ^ ((q - 1) / p)` where
    `g₀` is any generator of `(ZMod q)ˣ`.

    Construction recipe (mirrors `orderOf_pow_div_of_dvd` in
    `Proofs.LagrangeTheoremOQ01OQ03`): in a cyclic group of order `n`,
    the element `g ^ (n / d)` has order exactly `d` for every divisor
    `d` of `n` with `d > 0`. -/
theorem exists_unit_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ g : (ZMod q)ˣ, orderOf g = p := by
  -- Step 1: extract a generator `g₀` of the cyclic group `(ZMod q)ˣ`.
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := (ZMod q)ˣ)
  -- Step 2: `orderOf g₀ = |(ZMod q)ˣ| = q - 1`.
  have h_ord : orderOf g₀ = q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg₀, Nat.card_eq_fintype_card,
        card_units_zmod]
  -- Step 3: lift the divisibility hypothesis through `h_ord`.
  have hp_dvd_ord : p ∣ orderOf g₀ := h_ord ▸ hp_dvd
  -- Step 4: take the witness `g₀ ^ ((q - 1) / p)`. Rewrite `q - 1` as
  -- `orderOf g₀` so the proof matches `orderOf_pow_div_of_dvd`.
  refine ⟨g₀ ^ ((q - 1) / p), ?_⟩
  -- Step 5: substitute `q - 1 = orderOf g₀` in the goal.
  rw [← h_ord]
  -- Step 6: compute `orderOf (g₀ ^ (orderOf g₀ / p))` via `orderOf_pow'`
  -- and `Nat.gcd_eq_right` (using `(orderOf g₀ / p) ∣ orderOf g₀`).
  have hd_pos : 0 < orderOf g₀ / p :=
    Nat.div_pos (Nat.le_of_dvd (orderOf_pos g₀) hp_dvd_ord) hp.pos
  rw [orderOf_pow' g₀ hd_pos.ne',
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hp_dvd_ord)]
  -- Step 7: the final identity `n / (n / d) = d` when `d ∣ n` and
  -- `0 ≤ n`. Matches the `orderOf_pow_div_of_dvd` signature used in
  -- `Proofs.LagrangeTheoremOQ01OQ03`.
  exact Nat.div_div_self hp_dvd_ord (orderOf_pos g₀).ne'

/-! ## S3c-i: lift the order-`p` unit to an additive automorphism of `ZMod q`

Three small declarations that bridge `(ZMod q)ˣ` to `AddAut (ZMod q)`,
preparing the assembly of the Approach-B semidirect product
`Multiplicative (ZMod q) ⋊[φ] Multiplicative (ZMod p)` (deferred to
S3c-ii / S3d).

The bridge `unitToAddAut` packages the canonical multiplicative action
`u • x = ↑u * x` as a group homomorphism into `AddAut (ZMod q)`. Its
injectivity is faithful-action machinery: `u • 1 = ↑u`, so equal
automorphisms force equal underlying values. Composed with
`exists_unit_of_order_p`, this yields an order-`p` element of
`AddAut (ZMod q)` for every prime `p ∣ (q - 1)`.

See `notes/2026-05-13-s3c-api-audit.md` Steps 1–3 for the verbatim
ACT skeleton this section implements (Mathlib API pinned to rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). -/

/-- The action of the units `(ZMod q)ˣ` on `ZMod q` by multiplication
    induces a group hom into the additive automorphism group. The
    underlying function is `u ↦ (x ↦ ↑u * x)`. -/
def unitToAddAut : (ZMod q)ˣ →* AddAut (ZMod q) :=
  DistribMulAction.toAddAut ((ZMod q)ˣ) (ZMod q)

/-- Pointwise computation: `unitToAddAut u x = ↑u * x`. Marked `@[simp]`
    so `unitToAddAut_injective` and downstream consumers (S3c-ii,
    S3d-i) reduce automorphism applications to ring multiplication. -/
@[simp]
theorem unitToAddAut_apply (u : (ZMod q)ˣ) (x : ZMod q) :
    unitToAddAut u x = (u : ZMod q) * x := by
  show (u : (ZMod q)ˣ) • x = (u : ZMod q) * x
  rw [Units.smul_def, smul_eq_mul]

/-- `unitToAddAut` is injective. The action of `(ZMod q)ˣ` on `ZMod q`
    is faithful: `u • 1 = ↑u`, so equal automorphisms force equal
    underlying values, hence equal units. -/
theorem unitToAddAut_injective : Function.Injective (unitToAddAut (q := q)) := by
  intro u v huv
  apply Units.ext
  have h : unitToAddAut (q := q) u 1 = unitToAddAut (q := q) v 1 :=
    DFunLike.congr_fun huv 1
  -- After `unitToAddAut_apply` (simp) and `mul_one`, h reduces to ↑u = ↑v.
  simpa using h

/-- For each prime `p ∣ q - 1`, `AddAut (ZMod q)` contains an additive
    automorphism of order exactly `p`. Combined with
    `exists_unit_of_order_p`, this is the order-`p` seed for the
    Approach-B action homomorphism `φ` constructed in S3c-ii / S3d. -/
theorem exists_addAut_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ θ : AddAut (ZMod q), orderOf θ = p := by
  obtain ⟨g, hg⟩ := exists_unit_of_order_p hp hp_dvd
  refine ⟨unitToAddAut g, ?_⟩
  rw [orderOf_injective unitToAddAut unitToAddAut_injective g, hg]

/-! ## Sanity check: instantiate at `p = 2, q = 3` and `p = 3, q = 7`

These finite specialisations cross-check that the existence theorem is
applicable in the canonical small-prime cases referenced by the parent
problem statement. -/

/-- Sanity: `(ZMod 3)ˣ` contains an element of order `2`. -/
example : ∃ g : (ZMod 3)ˣ, orderOf g = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact exists_unit_of_order_p (by norm_num : Nat.Prime 2) (by norm_num)

/-- Sanity: `(ZMod 7)ˣ` contains an element of order `3` (since
    `3 ∣ 6 = 7 - 1`). -/
example : ∃ g : (ZMod 7)ˣ, orderOf g = 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_unit_of_order_p (by norm_num : Nat.Prime 3) (by norm_num)

/-- Sanity: `(ZMod 11)ˣ` contains an element of order `5` (since
    `5 ∣ 10 = 11 - 1`). This is the seed of the order-55 non-abelian
    group `ZMod 11 ⋊ ZMod 5` from the deferred S3d construction. -/
example : ∃ g : (ZMod 11)ˣ, orderOf g = 5 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact exists_unit_of_order_p (by norm_num : Nat.Prime 5) (by norm_num)

/-- Sanity (S3c-i): `AddAut (ZMod 7)` contains an automorphism of order
    `3`. This is the additive-automorphism analogue of the order-`3`
    unit in `(ZMod 7)ˣ` and is the order-`3` seed for the deferred
    Approach-B order-21 non-abelian group `ZMod 7 ⋊ ZMod 3`. -/
example : ∃ θ : AddAut (ZMod 7), orderOf θ = 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_addAut_of_order_p (by norm_num : Nat.Prime 3) (by norm_num)

/-! ## S3c-ii: transport the order-`p` `AddAut` to a `MulAut` on `Multiplicative (ZMod q)`

Approach B assembles the semidirect product
`Multiplicative (ZMod q) ⋊[φ] Multiplicative (ZMod p)` for a
non-trivial homomorphism
`φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`.
This section provides the multiplicative-side existence seed: an
order-`p` element of `MulAut (Multiplicative (ZMod q))`, obtained from
the S3c-i `AddAut (ZMod q)` witness by transport along the canonical
Mathlib equivalence
`MulAutMultiplicative (ZMod q) : AddAut (ZMod q) ≃* MulAut (Multiplicative (ZMod q))`
(defined at `Mathlib/Algebra/Group/End.lean:887`), using
`MulEquiv.orderOf_eq` (at `Mathlib/GroupTheory/OrderOfElement.lean:343`)
to carry the order across the equivalence.

See `notes/2026-05-15-s3c-ii-preflight.md` for the bearer audit
(re-pinned at lake-manifest rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`), the corrected skeleton
options (A/B/C), and the rationale for shipping Option C below. -/

/-- For each prime `p ∣ q - 1`, `MulAut (Multiplicative (ZMod q))`
    contains a multiplicative automorphism of order exactly `p`.

    Obtained from `exists_addAut_of_order_p` (S3c-i) via the canonical
    equivalence
    `(MulAutMultiplicative (ZMod q)).symm : AddAut (ZMod q) ≃* MulAut (Multiplicative (ZMod q))`,
    pushing the order witness through with `MulEquiv.orderOf_eq`. Order
    is preserved because the carrier is a multiplicative isomorphism. -/
theorem exists_mulAut_mult_of_order_p {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ ψ : MulAut (Multiplicative (ZMod q)), orderOf ψ = p := by
  obtain ⟨θ, hθ⟩ := exists_addAut_of_order_p hp hp_dvd
  refine ⟨(MulAutMultiplicative (ZMod q)).symm θ, ?_⟩
  rw [(MulAutMultiplicative (ZMod q)).symm.orderOf_eq, hθ]

/-- Sanity (S3c-ii): `MulAut (Multiplicative (ZMod 7))` contains an
    automorphism of order `3`. Multiplicative analogue of the S3c-i
    `AddAut (ZMod 7)` order-`3` witness, transported via
    `(MulAutMultiplicative (ZMod 7)).symm`. Order-`3` seed for the
    deferred Approach-B order-21 non-abelian group
    `Multiplicative (ZMod 7) ⋊ Multiplicative (ZMod 3)`. -/
example : ∃ ψ : MulAut (Multiplicative (ZMod 7)), orderOf ψ = 3 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact exists_mulAut_mult_of_order_p (by norm_num : Nat.Prime 3) (by norm_num)

end LagrangeOQ01OQ01OQ01.ApproachB
