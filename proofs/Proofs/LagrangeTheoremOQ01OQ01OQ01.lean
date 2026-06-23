/-
  pq-Groups: Explicit non-cyclic witness for `p = 2`
  (lagrange-theorem-oq-01-oq-01-oq-01)

  **Open Question (OQ-01-OQ-01-OQ-01)**: When `p, q` are distinct primes with
  `p ∣ (q - 1)`, the parent `pq-group` classification
  (`Proofs.LagrangeTheoremOQ01OQ01`) shows that *two* isomorphism classes of
  groups of order `pq` exist: the cyclic group `ℤ/pq` and a non-abelian
  semidirect product `ℤ/q ⋊ ℤ/p`. The parent file states the conditional
  fact `lagrange_pq_nonabelian_n_p_eq_q` *assuming* `¬ IsCyclic G`, but it
  does not exhibit an *explicit witness* of such a non-cyclic group.

  This file supplies the witness for the specialization `p = 2`:
  for every odd prime `q`, the dihedral group `DihedralGroup q` is a
  non-cyclic group of order `2q`. Together with the parent's general
  Sylow-classification, this completes the non-cyclic side of the
  `p ∣ (q-1)` branch in the case `p = 2`.

  **Strategy (Approach A from S1 survey)**: Use Mathlib's
  `DihedralGroup q` directly. The required API at pinned rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is:
  - `DihedralGroup.card [NeZero n] : Fintype.card (DihedralGroup n) = 2 * n`
  - `DihedralGroup.not_isCyclic (h1 : n ≠ 1) : ¬ IsCyclic (DihedralGroup n)`
  - `Group (DihedralGroup n)` (unconditional) and
    `Fintype (DihedralGroup n)` (requires `NeZero n`).

  The hypothesis `q ≠ 2` in the main existence theorem is documentary: it
  enforces that the OQ's divisibility hypothesis `2 ∣ (q - 1)` actually
  holds (which is equivalent to `q` being odd). The proof itself uses only
  `q ≠ 1` (immediate from primality).

  **Future iterations (deferred to OQ-01-OQ-01-OQ-01 S3+)**:
  Approach B — general `p, q` with `p ∣ (q-1)`. Construct
  `ZMod q ⋊[φ] ZMod p` where `φ : ZMod p →* MulAut (ZMod q)` is a
  non-trivial homomorphism extracted from the cyclic structure of
  `(ZMod q)ˣ`. This requires roughly 200 lines of new infrastructure and
  is deferred.

  References:
  - Dummit, D. & Foote, R. (2004). Abstract Algebra, §4.5, Example after
    Theorem 14 (the order-21 non-abelian group).
  - Mathlib4 `Mathlib/GroupTheory/SpecificGroups/Dihedral.lean`.
  - Parent: `Proofs.LagrangeTheoremOQ01OQ01`.

  Tags: group-theory, lagrange, dihedral, pq-groups, classification,
  existence, non-cyclic, semidirect-product, witness
-/

import Mathlib
import Proofs.LagrangeTheoremOQ01OQ01

namespace LagrangeOQ01OQ01OQ01

/-!
## Main Existence Theorem

For every odd prime `q`, an explicit non-cyclic group of order `2q` exists:
namely the dihedral group `DihedralGroup q`. This is the `p = 2`
specialization of the OQ's existence claim in the `p ∣ (q - 1)` regime.
-/

/-- **Existence witness** (Approach A, `p = 2` specialization).

    For every odd prime `q`, there is a group `G` of order `2q` that is not
    cyclic. The witness is `DihedralGroup q`, whose cardinality is `2q`
    (`DihedralGroup.card`) and which is non-cyclic for any `q ≠ 1`
    (`DihedralGroup.not_isCyclic`).

    The hypothesis `q ≠ 2` is documentary — it certifies that the OQ's
    divisibility premise `2 ∣ (q - 1)` holds (equivalently, `q` is odd).
    The proof itself relies only on `q ≠ 1`, which is automatic from
    primality (`Nat.Prime.one_lt`). -/
theorem exists_noncyclic_of_order_two_mul_odd_prime
    {q : ℕ} (hq : Nat.Prime q) (_hq_ne_two : q ≠ 2) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Fintype.card G = 2 * q ∧ ¬ IsCyclic G := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  refine ⟨DihedralGroup q, inferInstance, inferInstance,
          DihedralGroup.card, ?_⟩
  exact DihedralGroup.not_isCyclic hq.one_lt.ne'

/-!
## Divisibility Certificate

For every odd prime `q`, the divisibility `2 ∣ (q - 1)` holds. Combined
with the existence theorem above, this confirms that
`exists_noncyclic_of_order_two_mul_odd_prime` lands in the OQ's
`p ∣ (q - 1)` regime.
-/

/-- For any odd prime `q`, the divisibility `2 ∣ (q - 1)` is satisfied. -/
theorem two_dvd_sub_one_of_odd_prime {q : ℕ} (hq : Nat.Prime q)
    (hq_ne_two : q ≠ 2) : (2 : ℕ) ∣ (q - 1) := by
  rcases hq.eq_two_or_odd' with rfl | ⟨k, hk⟩
  · exact absurd rfl hq_ne_two
  · refine ⟨k, ?_⟩
    omega

/-!
## Concrete Corollaries

Specialise the main existence theorem to small odd primes, mirroring the
parent file's `order_*_non_unique` divisibility checks (orders 6, 10, 14,
22). Each corollary delivers a complete existence witness, not just the
divisibility certificate.
-/

/-- **Order 6 = 2 × 3**: a non-cyclic group of order 6 exists
    (`DihedralGroup 3 ≅ S₃`). -/
theorem exists_noncyclic_of_order_6 :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Fintype.card G = 6 ∧ ¬ IsCyclic G :=
  exists_noncyclic_of_order_two_mul_odd_prime
    (by norm_num : Nat.Prime 3) (by norm_num)

/-- **Order 10 = 2 × 5**: a non-cyclic group of order 10 exists
    (`DihedralGroup 5 ≅ D₅`). -/
theorem exists_noncyclic_of_order_10 :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Fintype.card G = 10 ∧ ¬ IsCyclic G :=
  exists_noncyclic_of_order_two_mul_odd_prime
    (by norm_num : Nat.Prime 5) (by norm_num)

/-- **Order 14 = 2 × 7**: a non-cyclic group of order 14 exists
    (`DihedralGroup 7 ≅ D₇`). -/
theorem exists_noncyclic_of_order_14 :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Fintype.card G = 14 ∧ ¬ IsCyclic G :=
  exists_noncyclic_of_order_two_mul_odd_prime
    (by norm_num : Nat.Prime 7) (by norm_num)

/-- **Order 22 = 2 × 11**: a non-cyclic group of order 22 exists
    (`DihedralGroup 11 ≅ D₁₁`). -/
theorem exists_noncyclic_of_order_22 :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Fintype.card G = 22 ∧ ¬ IsCyclic G :=
  exists_noncyclic_of_order_two_mul_odd_prime
    (by norm_num : Nat.Prime 11) (by norm_num)

end LagrangeOQ01OQ01OQ01
