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
  isCyclic_of_subgroup_isDomain (Units.coeHom (ZMod q)) Units.ext

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
  exact Nat.div_div_self hp_dvd_ord (orderOf_pos g₀).le

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

end LagrangeOQ01OQ01OQ01.ApproachB
