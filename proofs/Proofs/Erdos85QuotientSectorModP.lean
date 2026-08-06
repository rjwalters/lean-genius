import Proofs.Erdos85MixedSectorMassQuotient

/-!
# The component quotient restricted modulo a length prime

Detailed balance makes the block from components of `p`-prime order into
components of `p`-divisible order vanish modulo `p`.  Consequently the
principal `p`-divisible sector inherits the quotient square equation modulo
`p`, even though that sector need not be invariant integrally.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Components whose orders are divisible by `p`. -/
def pDivisibleComponent {V : Type*} (D : SimpleGraph V) (p : ℕ) :=
  {c : D.ConnectedComponent // p ∣ c.supp.ncard}

noncomputable instance pDivisibleComponentFintype
    {V : Type*} (D : SimpleGraph V) (p : ℕ)
    [Fintype D.ConnectedComponent] : Fintype (pDivisibleComponent D p) :=
  by
    unfold pDivisibleComponent
    infer_instance

noncomputable instance pDivisibleComponentDecidableEq
    {V : Type*} (D : SimpleGraph V) (p : ℕ) :
    DecidableEq (pDivisibleComponent D p) := Classical.decEq _

/-- The principal component-quotient block on `p`-divisible components,
reduced to `ZMod p`. -/
noncomputable def pDivisibleComponentQuotientMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent] (p : ℕ) :
    Matrix (pDivisibleComponent D p) (pDivisibleComponent D p) (ZMod p) :=
  fun c e ↦ componentQuotientMatrix G D c.1 e.1

/-- An odd-dimensional square root of a scalar matrix forces the scalar to
be a square.  This determinant lemma is field-generic. -/
theorem Matrix.isSquare_scalar_of_sq_eq_scalar_one_of_odd_card
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (M : Matrix I I K) (a : K) (hodd : Odd (Fintype.card I))
    (hsq : M * M = a • (1 : Matrix I I K)) : IsSquare a := by
  obtain ⟨k, hk⟩ := hodd
  have hdet := congrArg Matrix.det hsq
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  rw [hk] at hdet
  by_cases ha : a = 0
  · subst a
    exact ⟨0, by simp⟩
  · refine ⟨Matrix.det M / a ^ k, ?_⟩
    rw [div_mul_div_comm, hdet]
    field_simp [ha]
    ring

/-- A quotient entry from a component whose order is prime to `p` into a
component whose order is divisible by `p` is itself divisible by `p`. -/
theorem prime_dvd_componentQuotient_of_targetLength_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hpc : ¬ p ∣ c.supp.ncard) (hpe : p ∣ e.supp.ncard) :
    p ∣ componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
  have hbalance := secondOrder_componentQuotientMatrix_balance
    G hfree hd heven hmin hcard c e
  have hprod : p ∣ c.supp.ncard *
      componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
    rw [hbalance]
    exact dvd_mul_of_dvd_left hpe _
  exact (hp.coprime_iff_not_dvd.mpr hpc).dvd_of_dvd_mul_left hprod

/-- Every complementary intermediate term in a path between two
`p`-divisible components vanishes modulo `p`. -/
theorem prime_dvd_sum_complementary_componentQuotient_products
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (s e : (secondOrderDefectGraph G).ConnectedComponent)
    (hpe : p ∣ e.supp.ncard) :
    p ∣ ∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          ¬ p ∣ c.supp.ncard),
      componentQuotientMatrix G (secondOrderDefectGraph G) s c *
        componentQuotientMatrix G (secondOrderDefectGraph G) c e := by
  apply Finset.dvd_sum
  intro c hc
  have hpc : ¬ p ∣ c.supp.ncard := (Finset.mem_filter.mp hc).2
  exact dvd_mul_of_dvd_right
    (prime_dvd_componentQuotient_of_targetLength_dvd G hfree hd heven
      hmin hcard hp c e hpc hpe) _

/-- The principal quotient sector indexed by `p`-divisible component orders
satisfies `Qₚ² ≡ (d-3)I (mod p)`.  This is the direct finite-field shadow of
the Moore quotient equation and uses the same prime that indexes the mixed
frequency sector. -/
theorem pDivisible_componentQuotient_sector_sq_modEq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (s e : (secondOrderDefectGraph G).ConnectedComponent)
    (_hps : p ∣ s.supp.ncard) (hpe : p ∣ e.supp.ncard) :
    Nat.ModEq p
      (∑ c ∈ Finset.univ.filter (fun c :
          (secondOrderDefectGraph G).ConnectedComponent ↦
            p ∣ c.supp.ncard),
        componentQuotientMatrix G (secondOrderDefectGraph G) s c *
          componentQuotientMatrix G (secondOrderDefectGraph G) c e)
      ((d - 3) * if s = e then 1 else 0) := by
  let Q := componentQuotientMatrix G (secondOrderDefectGraph G)
  let S := Finset.univ.filter (fun c :
    (secondOrderDefectGraph G).ConnectedComponent ↦ p ∣ c.supp.ncard)
  let T := Finset.univ.filter (fun c :
    (secondOrderDefectGraph G).ConnectedComponent ↦ ¬ p ∣ c.supp.ncard)
  have hcompDvd : p ∣ ∑ c ∈ T, Q s c * Q c e := by
    exact prime_dvd_sum_complementary_componentQuotient_products
      G hfree hd heven hmin hcard hp s e hpe
  have hcomp0 : (∑ c ∈ T, Q s c * Q c e) ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr hcompDvd
  have hlen0 : e.supp.ncard ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr hpe
  have hsplit :
      (∑ c ∈ S, Q s c * Q c e) + (∑ c ∈ T, Q s c * Q c e) =
        ∑ c, Q s c * Q c e := by
    exact Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun c : (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)
      (fun c ↦ Q s c * Q c e)
  have hsq := secondOrder_componentQuotientMatrix_sq_apply
    G hfree hd heven hmin hcard s e
  simp only [Matrix.mul_apply] at hsq
  change (∑ c, Q s c * Q c e) =
    (d - 3) * (if s = e then 1 else 0) + e.supp.ncard at hsq
  change Nat.ModEq p (∑ c ∈ S, Q s c * Q c e)
    ((d - 3) * if s = e then 1 else 0)
  calc
    (∑ c ∈ S, Q s c * Q c e) ≡
        (∑ c ∈ S, Q s c * Q c e) + (∑ c ∈ T, Q s c * Q c e)
        [MOD p] := by
          simpa only [add_zero] using
            (hcomp0.add_left (∑ c ∈ S, Q s c * Q c e)).symm
    _ = ∑ c, Q s c * Q c e := hsplit
    _ = (d - 3) * (if s = e then 1 else 0) + e.supp.ncard := hsq
    _ ≡ (d - 3) * (if s = e then 1 else 0) [MOD p] := by
      simpa only [add_zero] using
        hlen0.add_left ((d - 3) * (if s = e then 1 else 0))

/-- Matrix form of the sector square equation over `ZMod p`. -/
theorem pDivisibleComponentQuotientMatrix_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d p : ℕ} [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) :
    let I := pDivisibleComponent (secondOrderDefectGraph G) p
    let Qp := pDivisibleComponentQuotientMatrix G
      (secondOrderDefectGraph G) p
    Qp * Qp = ((d - 3 : ℕ) : ZMod p) • (1 : Matrix I I (ZMod p)) := by
  dsimp only
  ext s e
  have hm := pDivisible_componentQuotient_sector_sq_modEq
    G hfree hd heven hmin hcard hp s.1 e.1 s.2 e.2
  have hc := (ZMod.natCast_eq_natCast_iff _ _ p).mpr hm
  simp only [Matrix.mul_apply, pDivisibleComponentQuotientMatrix,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have hsum :
      (∑ x : {c : (secondOrderDefectGraph G).ConnectedComponent //
          p ∣ c.supp.ncard},
        (componentQuotientMatrix G (secondOrderDefectGraph G) s.1 x.1 :
          ZMod p) *
        (componentQuotientMatrix G (secondOrderDefectGraph G) x.1 e.1 :
          ZMod p)) =
      ∑ x ∈ Finset.univ.filter (fun c :
          (secondOrderDefectGraph G).ConnectedComponent ↦
            p ∣ c.supp.ncard),
        (componentQuotientMatrix G (secondOrderDefectGraph G) s.1 x :
          ZMod p) *
        (componentQuotientMatrix G (secondOrderDefectGraph G) x e.1 :
          ZMod p) := by
    simpa using Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent))
      (p := fun c ↦ p ∣ c.supp.ncard)
      (fun x ↦
        (componentQuotientMatrix G (secondOrderDefectGraph G) s.1 x :
          ZMod p) *
        (componentQuotientMatrix G (secondOrderDefectGraph G) x e.1 :
          ZMod p))
  change (∑ x : {c : (secondOrderDefectGraph G).ConnectedComponent //
      p ∣ c.supp.ncard},
    (componentQuotientMatrix G (secondOrderDefectGraph G) s.1 x.1 : ZMod p) *
      (componentQuotientMatrix G (secondOrderDefectGraph G) x.1 e.1 : ZMod p)) = _
  rw [hsum]
  simp only [Nat.cast_sum, Nat.cast_mul, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero] at hc
  by_cases hse : s = e
  · subst e
    simpa using hc
  · have hval : s.1 ≠ e.1 := by
      intro h
      exact hse (Subtype.ext h)
    simp only [hse, hval, if_false] at hc ⊢
    exact hc

/-- If an odd number of defect components have order divisible by `p`, then
`d-3` is a square modulo `p`. -/
theorem isSquare_d_sub_three_mod_prime_of_odd_pDivisibleComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d p : ℕ} [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hodd : Odd (Fintype.card
      (pDivisibleComponent (secondOrderDefectGraph G) p))) :
    IsSquare ((d - 3 : ℕ) : ZMod p) := by
  let Qp := pDivisibleComponentQuotientMatrix G
    (secondOrderDefectGraph G) p
  have hsq := pDivisibleComponentQuotientMatrix_sq
    G hfree hd heven hmin hcard hp
  letI : Fact p.Prime := ⟨hp⟩
  exact Matrix.isSquare_scalar_of_sq_eq_scalar_one_of_odd_card
    Qp ((d - 3 : ℕ) : ZMod p) hodd hsq

/-- Filter-cardinality interface matching the mixed-selection layer. -/
theorem isSquare_d_sub_three_mod_prime_of_odd_pDivisible_filter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d p : ℕ} [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime)
    (hodd : Odd ((Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card)) :
    IsSquare ((d - 3 : ℕ) : ZMod p) := by
  apply isSquare_d_sub_three_mod_prime_of_odd_pDivisibleComponent
    G hfree hd heven hmin hcard hp
  unfold pDivisibleComponent
  rw [Fintype.card_subtype]
  exact hodd

end

end Erdos85
