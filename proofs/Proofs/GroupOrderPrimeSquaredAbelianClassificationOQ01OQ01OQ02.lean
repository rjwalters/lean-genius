/-
  Explicit Isomorphism Classification of Groups of Order p²

  Open question OQ-01-OQ-01-OQ-02
  (parent: group-order-prime-squared-abelian, via the exponent dichotomy OQ-01).

  The parent entry `GroupOrderPrimeSquaredAbelian` proves that a group `G` of order
  `p²` (`p` prime) is abelian, and supplies the *structural dichotomy*

      |G| = p²  ⟹  G is cyclic   XOR   G has exponent p (elementary abelian).

  That dichotomy is stated at the level of element orders. This entry upgrades it to
  an explicit **isomorphism classification**: every group of order `p²` is isomorphic,
  *as a group*, to exactly one of the two model groups

      ℤ/p²        (the cyclic group)      or      (ℤ/p)²   (elementary abelian).

  Mathlib supplies the general structure theorem for finite abelian groups
  (`CommGroup.equiv_prod_multiplicative_zmod_of_finite`), which decomposes any finite
  abelian group as a finite product of cyclic groups `Multiplicative (ZMod (n i))`
  with each `n i > 1`. The mathematical content of this entry is the **pin-down for
  the order `p²` case**: the product of the `n i` equals `p²`, each `n i` divides
  `p²` and exceeds `1`, hence each `n i ∈ {p, p²}`, and a short counting argument
  forces the index set to be a single point with value `p²` (cyclic case) or two
  points each with value `p` (elementary abelian case). The index-set juggling that
  turns the abstract finite product into the two named models `ZMod (p²)` and
  `ZMod p × ZMod p` is the new Lean infrastructure.

  ## Contents

  * `finTwoArrowAddEquiv` — the evaluation isomorphism `(Fin 2 → M) ≃+ M × M`.
  * `mulEquiv_classification_of_card_eq_prime_sq` — the classification: a group of
    order `p²` is isomorphic to `Multiplicative (ZMod (p²))` or to
    `Multiplicative (ZMod p × ZMod p)`.

  No axioms, no sorries.
-/
import Mathlib
import Proofs.GroupOrderPrimeSquaredAbelian

namespace GroupOrderPrimeSq

open scoped BigOperators

variable {G : Type*} [Group G]

/-- Evaluation at `0` and `1` is an additive isomorphism `(Fin 2 → M) ≃+ M × M`.
The underlying bijection is Mathlib's `finTwoArrowEquiv`; additivity is definitional
since `Pi` and `Prod` addition are both pointwise. -/
def finTwoArrowAddEquiv (M : Type*) [AddCommMonoid M] : (Fin 2 → M) ≃+ M × M :=
  { finTwoArrowEquiv M with map_add' := fun _ _ => rfl }

/-- Reindexing a constant-codomain function space along an index equivalence is an
additive isomorphism `(ι → M) ≃+ (ι' → M)`. It is precomposition by `e.symm`, which
is additive since addition on `ι' → M` is pointwise. -/
def arrowCongrLeftAddEquiv {ι ι' : Type*} (M : Type*) [AddCommMonoid M] (e : ι ≃ ι') :
    (ι → M) ≃+ (ι' → M) :=
  { Equiv.arrowCongr e (Equiv.refl M) with map_add' := fun _ _ => funext fun _ => rfl }

/-- **Explicit classification of groups of order `p²`.** A group `G` with
`Nat.card G = p²` (`p` prime) is isomorphic, as a group, to one of the two model
groups: the cyclic group `Multiplicative (ZMod (p²))`, or the elementary abelian
group `Multiplicative (ZMod p × ZMod p) ≅ (ℤ/p)²`.

The proof feeds the abelian structure theorem
`CommGroup.equiv_prod_multiplicative_zmod_of_finite` and pins the resulting finite
product down to `p²`: every factor divides `p²` and is `> 1`, so each is `p` or `p²`,
and counting the product `= p²` forces either a single factor `p²` (cyclic) or two
factors `p` (elementary abelian). -/
theorem mulEquiv_classification_of_card_eq_prime_sq {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) :
    Nonempty (G ≃* Multiplicative (ZMod (p ^ 2))) ∨
    Nonempty (G ≃* Multiplicative (ZMod p × ZMod p)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite G := Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 2 hp.pos.ne')
  letI : CommGroup G := { (‹Group G›) with
    mul_comm := mul_comm_of_card_eq_prime_sq hp hG }
  classical
  obtain ⟨ι, hι, n, hn1, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  haveI hnz : ∀ i, NeZero (n i) := fun i => ⟨by have := hn1 i; omega⟩
  -- The product of the factor orders is `p²`.
  have hcard : ∏ i, n i = p ^ 2 := by
    have h1 : Nat.card G = Nat.card (∀ i, Multiplicative (ZMod (n i))) :=
      Nat.card_congr e.toEquiv
    have h2 : Nat.card (∀ i, Multiplicative (ZMod (n i))) = ∏ i, n i := by
      rw [Nat.card_eq_fintype_card, Fintype.card_pi]
      exact Finset.prod_congr rfl (fun i _ => by
        rw [Fintype.card_multiplicative, ZMod.card])
    rw [hG] at h1
    exact (h1.trans h2).symm
  -- Each factor divides `p²`, hence equals `p` or `p²` (it is `> 1`).
  have hdvd : ∀ i, n i ∣ p ^ 2 := fun i => hcard ▸ Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  have hdich : ∀ i, n i = p ∨ n i = p ^ 2 := by
    intro i
    obtain ⟨k, hk, hke⟩ := (Nat.dvd_prime_pow hp).mp (hdvd i)
    interval_cases k
    · exfalso; have := hn1 i; simp at hke; omega
    · exact Or.inl (by simpa using hke)
    · exact Or.inr hke
  by_cases hcyc : ∃ i, n i = p ^ 2
  · -- Cyclic case: a single factor of order `p²`.
    obtain ⟨i₀, hi₀⟩ := hcyc
    have hrest : (∏ j ∈ Finset.univ.erase i₀, n j) = 1 := by
      have hsplit : n i₀ * ∏ j ∈ Finset.univ.erase i₀, n j = ∏ j, n j :=
        Finset.mul_prod_erase Finset.univ n (Finset.mem_univ i₀)
      rw [hcard, hi₀] at hsplit
      have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
      nth_rewrite 2 [← mul_one (p ^ 2)] at hsplit
      exact Nat.eq_of_mul_eq_mul_left hp2 hsplit
    have hsingle : (Finset.univ : Finset ι) = {i₀} := by
      have hempty : Finset.univ.erase i₀ = ∅ := by
        by_contra hne
        obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hjd : n j ∣ 1 := hrest ▸ Finset.dvd_prod_of_mem n hj
        have := Nat.le_of_dvd one_pos hjd
        have := hn1 j
        omega
      rw [Finset.erase_eq_empty_iff] at hempty
      rcases hempty with h | h
      · exact absurd (h ▸ Finset.mem_univ i₀) (Finset.notMem_empty i₀)
      · exact h
    haveI : Unique ι := ⟨⟨i₀⟩, fun j => by
      have : j ∈ ({i₀} : Finset ι) := hsingle ▸ Finset.mem_univ j
      simpa using this⟩
    have hdef : n (default : ι) = p ^ 2 := by
      rw [Subsingleton.elim (default : ι) i₀]; exact hi₀
    left
    refine ⟨e.trans <| (MulEquiv.piUnique (fun i => Multiplicative (ZMod (n i)))).trans ?_⟩
    rw [hdef]
  · -- Elementary abelian case: two factors, each of order `p`.
    push_neg at hcyc
    have hall : ∀ i, n i = p := fun i => (hdich i).resolve_right (hcyc i)
    have hcard2 : Fintype.card ι = 2 := by
      have hpow : p ^ Fintype.card ι = p ^ 2 := by
        have h := hcard
        rw [Finset.prod_congr rfl (fun i _ => hall i), Finset.prod_const,
          Finset.card_univ] at h
        exact h
      exact Nat.pow_right_injective hp.two_le hpow
    let e2 : ι ≃ Fin 2 := Fintype.equivFinOfCardEq hcard2
    have fibAdd : ∀ i, ZMod (n i) ≃+ ZMod p :=
      fun i => by rw [hall i]
    right
    refine ⟨e.trans <| (MulEquiv.piMultiplicative (fun i => ZMod (n i))).symm.trans
      (AddEquiv.toMultiplicative <|
        (AddEquiv.piCongrRight fibAdd).trans <|
          (arrowCongrLeftAddEquiv (ZMod p) e2).trans (finTwoArrowAddEquiv (ZMod p)))⟩

end GroupOrderPrimeSq
