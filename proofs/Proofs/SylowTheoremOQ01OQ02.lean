import Mathlib

/-
# Classification of Groups of Squarefree Order

## What This Proves

This answers the second open question of `sylow-theorems-oq-01`
("Classification of Groups of Order pq via Sylow Theorems"):

> Can the full squarefree-order classification be formalized? Every group of
> squarefree order n = p₁p₂···pₖ is a semidirect product of cyclic groups, with
> the structure determined by the divisibility relations among the pᵢ — a
> generalization of the pq case to multiple primes.

The parent entry handles the two-prime case `n = pq` by hand. Here we formalize
the **general squarefree case** for *any* number of prime factors, using
Mathlib's `IsZGroup` theory (a Z-group is a finite group all of whose Sylow
subgroups are cyclic). The decisive facts are:

* `IsZGroup.of_squarefree` — squarefree order forces every Sylow subgroup to be
  cyclic (each has prime order, hence is `ℤ/pᵢ`);
* `isZGroup_iff_exists_mulEquiv` — a finite Z-group is isomorphic to a semidirect
  product `N ⋊ H` of two cyclic subgroups of coprime order.

Composing these gives the structure theorem the open question asks for, plus the
standard consequences: such groups are **solvable**, **metacyclic** (cyclic normal
subgroup with cyclic quotient), and have **exponent equal to their order**.

## Honest scope

The hard mathematics (the Z-group structure theory, Schur–Zassenhaus splitting)
lives in Mathlib. The contribution here is to *assemble* it into the
squarefree-order classification narrative that the parent entry left open, as a
fully verified (0-axiom) gallery result. The "structure determined by the
divisibility relations among the pᵢ" — i.e. the explicit count of isomorphism
classes — is genuinely harder and remains open (see the open questions below).
-/

open scoped Classical

namespace SquarefreeOrderClassification

variable {G : Type*} [Group G] [Finite G]

/-! ## The key reduction: squarefree order ⇒ Z-group -/

/-- **A finite group of squarefree order is a Z-group**: every Sylow subgroup is
    cyclic. When `n = p₁⋯pₖ` is squarefree each Sylow `pᵢ`-subgroup has order
    exactly `pᵢ`, so it is cyclic. -/
theorem isZGroup_of_squarefree_order (h : Squarefree (Nat.card G)) : IsZGroup G :=
  IsZGroup.of_squarefree h

/-- **Every Sylow subgroup is cyclic.** For squarefree order each Sylow subgroup
    is `ℤ/pᵢ`. -/
theorem sylow_isCyclic (h : Squarefree (Nat.card G))
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) : IsCyclic P := by
  haveI := isZGroup_of_squarefree_order h
  infer_instance

/-! ## Structural consequences -/

/-- **Groups of squarefree order are solvable.** -/
theorem isSolvable_of_squarefree_order (h : Squarefree (Nat.card G)) : IsSolvable G := by
  haveI := isZGroup_of_squarefree_order h
  infer_instance

/-- **The commutator subgroup is cyclic.** -/
theorem isCyclic_commutator (h : Squarefree (Nat.card G)) : IsCyclic (commutator G) := by
  haveI := isZGroup_of_squarefree_order h
  exact IsZGroup.isCyclic_commutator G

/-- **The abelianization is cyclic.** -/
theorem isCyclic_abelianization (h : Squarefree (Nat.card G)) :
    IsCyclic (Abelianization G) := by
  haveI := isZGroup_of_squarefree_order h
  infer_instance

/-- **The exponent equals the order.** A group of squarefree order is "as close to
    cyclic as its order allows": its exponent is the full group order. -/
theorem exponent_eq_card (h : Squarefree (Nat.card G)) :
    Monoid.exponent G = Nat.card G := by
  haveI := isZGroup_of_squarefree_order h
  exact IsZGroup.exponent_eq_card G

/-! ## Metacyclic structure -/

/-- **Groups of squarefree order are metacyclic**: the commutator subgroup is a
    *cyclic normal* subgroup whose quotient (the abelianization `G ⧸ commutator G`)
    is also cyclic. This is the cyclic-by-cyclic extension structure. -/
theorem metacyclic_of_squarefree_order (h : Squarefree (Nat.card G)) :
    (commutator G).Normal ∧ IsCyclic (commutator G) ∧ IsCyclic (Abelianization G) := by
  haveI := isZGroup_of_squarefree_order h
  exact ⟨inferInstance, IsZGroup.isCyclic_commutator G, inferInstance⟩

/-! ## The classification: a semidirect product of cyclic groups -/

/-- **Classification of groups of squarefree order.** Every finite group whose
    order is squarefree is isomorphic to a semidirect product `N ⋊[φ] H` of two
    *cyclic* subgroups whose orders are *coprime*. This is precisely the
    "semidirect product of cyclic groups" structure the open question asks for,
    now for an arbitrary number of prime factors (the parent entry covered only
    `n = pq`).

    Concretely `N` may be taken to be the (cyclic) commutator subgroup and `H` a
    complement isomorphic to the (cyclic) abelianization; coprimality of their
    orders is what lets Schur–Zassenhaus split the extension. -/
theorem semidirectProduct_of_squarefree_order (h : Squarefree (Nat.card G)) :
    ∃ (N H : Subgroup G) (φ : H →* MulAut N) (_ : G ≃* N ⋊[φ] H),
      IsCyclic H ∧ IsCyclic N ∧ (Nat.card N).Coprime (Nat.card H) :=
  isZGroup_iff_exists_mulEquiv.mp (isZGroup_of_squarefree_order h)

/-! ## Specialization back to the order-`pq` case -/

/-- Sanity check: a group of order `p * q` with `p, q` distinct primes has
    squarefree order, so the classification above applies and recovers the parent
    entry's setting as the two-prime special case. -/
theorem squarefree_card_of_pq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (h : Nat.card G = p * q) : Squarefree (Nat.card G) := by
  rw [h]
  exact (Nat.squarefree_mul (by simpa using (Nat.coprime_primes hp hq).mpr hpq)).mpr
    ⟨hp.squarefree, hq.squarefree⟩

end SquarefreeOrderClassification
