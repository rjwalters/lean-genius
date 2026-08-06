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

end

end Erdos85
