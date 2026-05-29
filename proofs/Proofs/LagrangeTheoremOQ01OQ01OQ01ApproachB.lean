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

/-! ## S3d-i: action homomorphism `Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`

Given the order-`p` automorphism `ψ : MulAut (Multiplicative (ZMod q))`
from S3c-ii, build the action homomorphism

```
actionHom : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))
```

that witnesses non-triviality of the Approach-B semidirect product

```
Multiplicative (ZMod q) ⋊[actionHom] Multiplicative (ZMod p).
```

The construction factors through the additive side: `ψ ^ p = 1` lifts
to a kernel condition on `zmultiplesHom _ (Additive.ofMul ψ) : ℤ →+ Additive G`
that lets `ZMod.lift p` descend to `ZMod p →+ Additive G`, from which
`AddMonoidHom.toMultiplicativeLeft` (Mathlib
`Mathlib/Algebra/Group/TypeTags/Hom.lean:111`) produces the desired
`Multiplicative (ZMod p) →* G`.

Mathlib bridges used (pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):
- `zmultiplesHom` (`Mathlib/Data/Int/Cast/Lemmas.lean:276`).
- `ZMod.lift` (`Mathlib/Data/ZMod/Basic.lean:1140`).
- `AddMonoidHom.toMultiplicativeLeft` (`Mathlib/Algebra/Group/TypeTags/Hom.lean:111`).
- `ofMul_zpow` / `ofMul_one` (`Mathlib/Algebra/Group/TypeTags/Basic.lean:438`/226).
- `zpow_natCast` / `pow_orderOf_eq_one` (standard).

See `notes/2026-05-13-s3c-api-audit.md` Step 5 for the recipe sketch.
This iteration realises the pseudo-code (`zpowersHom`/`ZMod.lift`
factoring) via the equivalent and cleaner `zmultiplesHom` +
`AddMonoidHom.toMultiplicativeLeft` route. -/

/-- The action homomorphism `φ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))`
    that witnesses non-triviality of the Approach-B semidirect product.

    The hom is built by lifting `Additive.ofMul ψ ∈ Additive G` (for `G`
    the multiplicative automorphism group) to a `ℤ →+ Additive G` via
    `zmultiplesHom`, observing that `ψ ^ p = 1` kills the image of
    `(p : ℤ)`, descending through `ZMod.lift p` to a `ZMod p →+ Additive G`,
    then translating back via `AddMonoidHom.toMultiplicativeLeft`. -/
noncomputable def actionHom {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q)) := by
  have hexists := exists_mulAut_mult_of_order_p hp hp_dvd
  set ψ := hexists.choose
  have hψ : orderOf ψ = p := hexists.choose_spec
  have hψ_pow : ψ ^ p = 1 := hψ ▸ pow_orderOf_eq_one ψ
  refine AddMonoidHom.toMultiplicativeLeft <|
    ZMod.lift p ⟨zmultiplesHom _ (Additive.ofMul ψ), ?_⟩
  show (p : ℤ) • Additive.ofMul ψ = 0
  rw [← ofMul_zpow, zpow_natCast, hψ_pow, ofMul_one]

/-- Sanity (S3d-i): `actionHom` is well-typed at `(p, q) = (3, 7)`.
    Produces a hom `Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 7))`,
    the action data for the deferred Approach-B order-21 non-abelian
    group `Multiplicative (ZMod 7) ⋊ Multiplicative (ZMod 3)`. -/
noncomputable example :
    Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 7)) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact actionHom (by norm_num : Nat.Prime 3) (by norm_num)

/-! ## S3d-ii: assemble the semidirect product and discharge the open question

For each prime `p ∣ q - 1`, package `actionHom hp hp_dvd` into the semidirect
product

  `Multiplicative (ZMod q) ⋊[actionHom hp hp_dvd] Multiplicative (ZMod p)`

and discharge `openQuestions[0]` of the parent (general case; Approach A handled
`p = 2`) by proving the witness group has order `p * q` and is non-cyclic.

The non-triviality of the action — the genuinely subtle step (rated high-risk in
the S10 PREP, which forecast a `sorry`) — is discharged here without any `sorry`
via `actionHom_ofAdd_one`: the generator `ofAdd 1` acts as the order-`p`
automorphism `ψ`, which is `≠ 1` since `p ≥ 2`, hence moves some element. -/

open SemidirectProduct in
/-- The Approach-B group: `ZMod q ⋊ ZMod p` (multiplicative wrappers) twisted
by `actionHom hp hp_dvd`. -/
abbrev approachBGroup {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) : Type :=
  SemidirectProduct
    (Multiplicative (ZMod q)) (Multiplicative (ZMod p))
    (actionHom hp hp_dvd)

/-- The generator `Multiplicative.ofAdd 1` acts via `actionHom` as exactly the
chosen order-`p` automorphism `ψ`. This is the key bridge that makes
non-triviality provable without a `sorry`: applying `actionHom` to the cyclic
generator recovers `ψ`, whose order `p ≥ 2` forces it to move some element.

Computation: `AddMonoidHom.toMultiplicativeLeft` evaluates `ofAdd 1` through
`ZMod.lift` (via `ZMod.lift_coe` at the integer `1`) and `zmultiplesHom`
(`1 • Additive.ofMul ψ = Additive.ofMul ψ`), then `Additive.toMul` recovers
`ψ`. -/
theorem actionHom_ofAdd_one {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    actionHom hp hp_dvd (Multiplicative.ofAdd (1 : ZMod p))
      = (exists_mulAut_mult_of_order_p hp hp_dvd).choose := by
  unfold actionHom
  simp only [AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, toAdd_ofAdd]
  first
  | rw [ZMod.lift_coe]
  | rw [show (1 : ZMod p) = ((1 : ℤ) : ZMod p) by simp, ZMod.lift_coe]
  simp

/-- Non-triviality of the order-`p` action: `actionHom hp hp_dvd (ofAdd 1)` does
not fix every element. Proved (no `sorry`) via `actionHom_ofAdd_one`: the action
is `ψ`, which has order `p ≥ 2`, hence `ψ ≠ 1`, hence moves some element. -/
theorem exists_actionHom_not_fixed
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ x : Multiplicative (ZMod q),
      actionHom hp hp_dvd (Multiplicative.ofAdd (1 : ZMod p)) x ≠ x := by
  have hψ_spec : orderOf (exists_mulAut_mult_of_order_p hp hp_dvd).choose = p :=
    (exists_mulAut_mult_of_order_p hp hp_dvd).choose_spec
  set ψ := (exists_mulAut_mult_of_order_p hp hp_dvd).choose with hψ_def
  have hψ_ne_one : ψ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hψ_spec
    have := hp.two_le
    omega
  have hmove : ∃ x, ψ x ≠ x := by
    by_contra hcon
    push_neg at hcon
    apply hψ_ne_one
    ext x
    simp only [MulAut.one_apply]
    exact hcon x
  obtain ⟨x, hx⟩ := hmove
  refine ⟨x, ?_⟩
  rw [actionHom_ofAdd_one]
  exact hx

/-- S3d-ii.A — the Approach-B group has order `p * q`. -/
theorem approachBGroup_card {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    Nat.card (approachBGroup hp hp_dvd) = p * q := by
  haveI : NeZero q := ⟨hqfact.out.pos.ne'⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  unfold approachBGroup
  rw [SemidirectProduct.card,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q),
      Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      ZMod.card q, ZMod.card p]
  ring

/-- S3d-ii.B — the Approach-B group is not cyclic. A cyclic group is
commutative, but `inr g` and `inl x` fail to commute precisely because the
action moves `x` (`exists_actionHom_not_fixed`). -/
theorem approachBGroup_not_isCyclic
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ¬ IsCyclic (approachBGroup hp hp_dvd) := by
  intro hcyc
  haveI : IsCyclic (approachBGroup hp hp_dvd) := hcyc
  obtain ⟨x, hx⟩ := exists_actionHom_not_fixed hp hp_dvd
  set g : Multiplicative (ZMod p) := Multiplicative.ofAdd 1 with hg
  have hcomm := (IsCyclic.commutative (α := approachBGroup hp hp_dvd)).comm
      (SemidirectProduct.inr g) (SemidirectProduct.inl x)
  have hL := congrArg SemidirectProduct.left hcomm
  simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
             SemidirectProduct.right_inl, SemidirectProduct.left_inr,
             SemidirectProduct.right_inr, map_one,
             one_mul, mul_one] at hL
  exact hx hL

/-- **S3d-ii main result.** For each pair of primes `p < q` with `p ∣ q - 1`, an
explicit non-cyclic group of order `p * q`. Together with Approach A (`p = 2` via
`DihedralGroup`), this discharges `openQuestions[0]` of
`lagrange-theorem-oq-01-oq-01` for the general case: whenever `p ∣ q - 1`, a
non-cyclic group of order `pq` exists. -/
theorem exists_noncyclic_of_pq_when_p_dvd_q_sub_one
    {p : ℕ} (hp : p.Prime) (hp_dvd : p ∣ q - 1) :
    ∃ (G : Type) (_ : Group G), Nat.card G = p * q ∧ ¬ IsCyclic G :=
  ⟨approachBGroup hp hp_dvd, inferInstance,
   approachBGroup_card hp hp_dvd, approachBGroup_not_isCyclic hp hp_dvd⟩

/-- Sanity (S3d-ii): the order-21 non-cyclic group exists (`p = 3, q = 7`). This
is the smallest case not covered by Approach A's `p = 2` family. -/
example : ∃ (G : Type) (_ : Group G), Nat.card G = 21 ∧ ¬ IsCyclic G := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨G, hG, hcard, hcyc⟩ :=
    exists_noncyclic_of_pq_when_p_dvd_q_sub_one (q := 7)
      (by norm_num : Nat.Prime 3) (by norm_num)
  exact ⟨G, hG, by simp [hcard], hcyc⟩

end LagrangeOQ01OQ01OQ01.ApproachB
