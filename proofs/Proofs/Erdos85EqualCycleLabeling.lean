import Proofs.Erdos85DefectCycleBlock
import Proofs.Erdos85GlobalCycleFactorization

/-!
# Global equal-cycle labeling of the second-order defect graph

Assuming every connected component of the second-order defect two-factor
has one common size `r`, this file extracts the complete labeling data
consumed by the frequency-pair terminals:

* cyclic parametrizations `u c : ZMod r → V` of every component, injective,
  covering exactly the component, stepping to the two defect neighbours,
  and separated across components;
* the arithmetic facts `3 ≤ r`, `Odd r`, an odd component count, and
  `#components * r = d(d-1) + 3`;
* a half-point `b` with `b + b = 1` in `ZMod r`;
* the elementary classification of an odd `r ≥ 3`: either `r` has a prime
  divisor `p ≥ 7` (automatically with odd cofactor), or `5 ∣ r`, or `r`
  is a power of three.

The single remaining input is the common-size hypothesis `hlen`; the
existing divisibility machinery
(`secondOrder_componentQuotientMatrix_pos_imp_size_dvd_or_dvd`) constrains
unequal components but does not yet force equality.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Odd products have odd factors. -/
theorem odd_and_odd_of_odd_mul {m n : ℕ} (h : Odd (m * n)) :
    Odd m ∧ Odd n := by
  rw [← Nat.not_even_iff_odd] at h ⊢
  rw [← Nat.not_even_iff_odd]
  rw [Nat.even_mul] at h
  tauto

/-- Any odd modulus admits a half-point. -/
theorem exists_add_self_eq_one_of_odd {r : ℕ} [NeZero r] (hrOdd : Odd r) :
    ∃ b : ZMod r, b + b = 1 := by
  obtain ⟨k, hk⟩ := hrOdd
  refine ⟨((k + 1 : ℕ) : ZMod r), ?_⟩
  have hsum : ((k + 1 : ℕ) : ZMod r) + ((k + 1 : ℕ) : ZMod r) =
      ((r + 1 : ℕ) : ZMod r) := by
    have h2 : (k + 1) + (k + 1) = r + 1 := by omega
    rw [← Nat.cast_add, h2]
  rw [hsum]
  push_cast [ZMod.natCast_self]
  ring

/-- **Equal-cycle labeling extraction.**  If every defect component has
size `r`, each component carries a cyclic `ZMod r` parametrization with
the exact hypothesis package of the frequency-pair terminals. -/
theorem exists_equalCycle_labeling
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ}
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hlen : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r) :
    ∃ u : (secondOrderDefectGraph G).ConnectedComponent → ZMod r → V,
      (∀ c, Function.Injective (u c)) ∧
      (∀ c, Set.range (u c) = c.supp) ∧
      (∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
        {u c (x - 1), u c (x + 1)}) ∧
      ∀ {c e : (secondOrderDefectGraph G).ConnectedComponent},
        c ≠ e → ∀ x y, u c x ≠ u e y := by
  classical
  have hdeg : ∀ z, (secondOrderDefectGraph G).degree z = 2 := fun z ↦
    secondOrderDefectGraph_degree_eq_two G hfree hd hdeven hmin hcard z
  have hchoice : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ∃ u0 : ZMod r → V, Function.Injective u0 ∧
        Set.range u0 = c.supp ∧
        ∀ z, (secondOrderDefectGraph G).neighborFinset (u0 z) =
          {u0 (z - 1), u0 (z + 1)} := by
    intro c
    obtain ⟨x, hx⟩ := c.nonempty_supp
    obtain ⟨p, hpcycle, hpverts⟩ :=
      exists_secondOrderDefect_cycle_spanning_component
        G hfree hd hdeven hmin hcard c hx
    have hplen : p.length = r := by
      calc
        p.length = Nat.card p.toSubgraph.verts :=
          (isCycle_card_verts_eq_length hpcycle).symm
        _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
        _ = c.supp.ncard := congrArg Set.ncard hpverts
        _ = r := hlen c
    subst hplen
    obtain ⟨u0, h1, h2, h3⟩ :=
      exists_zmod_cycleParam_neighborFinset hpcycle hdeg
    exact ⟨u0, h1, h2.trans hpverts, h3⟩
  choose u hu1 hu2 hu3 using hchoice
  refine ⟨u, hu1, hu2, hu3, ?_⟩
  intro c e hce x y heq
  have hxc : u c x ∈ c.supp := by
    rw [← hu2 c]
    exact ⟨x, rfl⟩
  have hxe : u c x ∈ e.supp := by
    rw [heq, ← hu2 e]
    exact ⟨y, rfl⟩
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hxc hxe
  exact hce (hxc.symm.trans hxe)

/-- **Equal-cycle arithmetic.**  With one common component size `r`, the
length is odd and at least three, the component count is odd, and the
sizes tile the boundary order exactly. -/
theorem equalCycle_length_facts
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d r : ℕ}
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hlen : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = r) :
    3 ≤ r ∧ Odd r ∧
      Odd (Fintype.card (secondOrderDefectGraph G).ConnectedComponent) ∧
      Fintype.card (secondOrderDefectGraph G).ConnectedComponent * r =
        d * (d - 1) + 3 := by
  classical
  have hparts : (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard) = Fintype.card V := by
    calc
      (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
          c.supp.ncard) =
          ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
            Fintype.card c.supp := by
        apply Finset.sum_congr rfl
        intro c _
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card
          (Σ c : (secondOrderDefectGraph G).ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr
          (vertexConnectedComponentEquiv (secondOrderDefectGraph G))).symm
  have htile : Fintype.card (secondOrderDefectGraph G).ConnectedComponent *
      r = d * (d - 1) + 3 := by
    rw [← hcard, ← hparts]
    rw [Finset.sum_congr rfl fun c _ ↦ hlen c, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
  have hoddV : Odd (d * (d - 1) + 3) := by
    have heven : Even (d * (d - 1)) := hdeven.mul_right (d - 1)
    exact heven.add_odd ⟨1, by norm_num⟩
  have hoddmul : Odd (Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent * r) := by
    rw [htile]
    exact hoddV
  obtain ⟨hoddC, hoddr⟩ := odd_and_odd_of_odd_mul hoddmul
  refine ⟨?_, hoddr, hoddC, htile⟩
  have hV0 : 0 < Fintype.card V := by
    rw [hcard]
    omega
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hV0
  set c := (secondOrderDefectGraph G).connectedComponentMk v with hc
  obtain ⟨x, hx⟩ := c.nonempty_supp
  obtain ⟨p, hpcycle, hpverts⟩ :=
    exists_secondOrderDefect_cycle_spanning_component
      G hfree hd hdeven hmin hcard c hx
  have hplen : p.length = r := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hpcycle).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = c.supp.ncard := congrArg Set.ncard hpverts
      _ = r := hlen c
  rw [← hplen]
  exact hpcycle.three_le_length

/-- **Odd-length classification.**  An odd length `r ≥ 3` either has a
prime divisor `p ≥ 7` — with odd cofactor for free — or is divisible by
five, or is a power of three. -/
theorem odd_cycleLength_classification {r : ℕ} (h3 : 3 ≤ r)
    (hodd : Odd r) :
    (∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ r ∧ Odd (r / p)) ∨
      5 ∣ r ∨ ∃ k : ℕ, r = 3 ^ k := by
  classical
  by_cases h5 : 5 ∣ r
  · exact Or.inr (Or.inl h5)
  by_cases h7 : ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ r
  · obtain ⟨p, hp, hp7, hpd⟩ := h7
    refine Or.inl ⟨p, hp, hp7, hpd, ?_⟩
    have hmul : r / p * p = r := Nat.div_mul_cancel hpd
    have hodd' : Odd (r / p * p) := by
      rw [hmul]
      exact hodd
    exact (odd_and_odd_of_odd_mul hodd').1
  · push_neg at h7
    refine Or.inr (Or.inr ?_)
    have hall : ∀ q : ℕ, q.Prime → q ∣ r → q = 3 := by
      intro q hq hqd
      have h2 : q ≠ 2 := by
        rintro rfl
        rw [← Nat.not_even_iff_odd] at hodd
        obtain ⟨k, rfl⟩ := hqd
        exact hodd ⟨k, two_mul k⟩
      have h5' : q ≠ 5 := by
        rintro rfl
        exact h5 hqd
      have hlt : q < 7 := by
        by_contra hge
        exact h7 q hq (by omega) hqd
      have hq2 := hq.two_le
      interval_cases q
      · exact absurd rfl h2
      · rfl
      · exact absurd hq (by norm_num)
      · exact absurd rfl h5'
      · exact absurd hq (by norm_num)
    exact ⟨r.primeFactorsList.length,
      Nat.eq_prime_pow_of_unique_prime_dvd (by omega)
        fun {q} hq hqd ↦ hall q hq hqd⟩

end

end Erdos85
