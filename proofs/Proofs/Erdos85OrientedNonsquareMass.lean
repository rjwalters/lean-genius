import Proofs.Erdos85OrientedMixedTrace
import Proofs.Erdos85MixedNonsquareMass

/-!
# The oriented nonsquare branch: effective anchor mass

The nonsquare-branch machinery generalizes beyond odd component lengths
through the orientation marking: with each `p`-divisible component
declared forward- or reverse-oriented, the restricted trace sees only the
forward components' anchor counts.  When the frequency scalar
`d - 1 - ζ - ζ⁻¹` is a nonsquare the trace vanishes, prime Fourier
uniformity forces all *oriented* projected anchor counts equal, and `p`
divides the oriented anchor mass — with no parity hypothesis on any
length.  The graph-side orientation dichotomy discharges the marking.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {K : Type*} [Field K] [CharZero K]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)] {p : ℕ} [NeZero p]

/-- Oriented projected anchor count: anchored same-cycle adjacencies at
displacement residue `s`, collected over the forward-oriented
`p`-divisible components only. -/
def orientedProjectedAnchor (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (o : C → Prop) [DecidablePred o]
    (p : ℕ) (s : ZMod p) : ℕ :=
  ∑ c ∈ Finset.univ.filter fun c : C ↦ p ∣ ℓ c ∧ o c,
    ((graphCycleBlockZeroSupport G (u c) (u c)).filter
      (fun t : ZMod (ℓ c) ↦ ((t.val : ℕ) : ZMod p) = s)).card

/-- Total anchor mass of the forward-oriented `p`-divisible sector. -/
def orientedAnchorMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (o : C → Prop) [DecidablePred o]
    (p : ℕ) : ℕ :=
  ∑ c ∈ Finset.univ.filter fun c : C ↦ p ∣ ℓ c ∧ o c,
    (graphCycleBlockZeroSupport G (u c) (u c)).card

/-- The oriented projected anchor counts sum to the oriented mass. -/
theorem sum_orientedProjectedAnchor_eq_mass (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : ∀ c : C, ZMod (ℓ c) → V)
    (o : C → Prop) [DecidablePred o] :
    ∑ s : ZMod p, orientedProjectedAnchor G u o p s =
      orientedAnchorMass G u o p := by
  rw [orientedAnchorMass]
  unfold orientedProjectedAnchor
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  exact (Finset.card_eq_sum_card_fiberwise
    (f := fun t : ZMod (ℓ c) ↦ ((t.val : ℕ) : ZMod p))
    (s := graphCycleBlockZeroSupport G (u c) (u c))
    (t := Finset.univ) (fun t _ ↦ Finset.mem_univ _)).symm

/-- The fibered Fourier weight of the oriented sector is the oriented
projected anchor count. -/
theorem sum_orientedLabeled_diag_eq_orientedProjectedAnchor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (o : C → Prop) [DecidablePred o]
    (s : ZMod p) :
    (∑ c ∈ Finset.univ.filter fun c : C ↦ p ∣ ℓ c ∧ o c,
      ∑ t ∈ Finset.univ.filter
        (fun t : ZMod (ℓ c) ↦ ((t.val : ℕ) : ZMod p) = s),
        mixedLabeledAdjMatrix K G u ⟨c, 0⟩ ⟨c, t⟩) =
      ((orientedProjectedAnchor G u o p s : ℕ) : K) := by
  rw [orientedProjectedAnchor, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro c _
  have hmem : ∀ t : ZMod (ℓ c),
      G.Adj (u c 0) (u c t) ↔
        t ∈ graphCycleBlockZeroSupport G (u c) (u c) := by
    intro t
    rw [graphCycleBlockZeroSupport, mem_zeroRowSupport_iff]
    simp [SimpleGraph.adjMatrix_apply]
  have hset : Finset.univ.filter
      (fun t : ZMod (ℓ c) ↦ G.Adj (u c 0) (u c t)) =
      graphCycleBlockZeroSupport G (u c) (u c) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmem t
  simp only [mixedLabeledAdjMatrix_apply, SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_boole]
  congr 1
  rw [Finset.filter_comm, hset]

/-- Forward adjacency invariance transports to the labeled matrix. -/
theorem mixedLabeledAdjMatrix_fwd_of_adj_shift_iff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) {c : C}
    (hiff : ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y + 1)) ↔ G.Adj (u c x) (u c y)) :
    ∀ x y : ZMod (ℓ c),
      mixedLabeledAdjMatrix K G u ⟨c, x + 1⟩ ⟨c, y + 1⟩ =
        mixedLabeledAdjMatrix K G u ⟨c, x⟩ ⟨c, y⟩ := by
  intro x y
  simp only [mixedLabeledAdjMatrix_apply, SimpleGraph.adjMatrix_apply,
    hiff x y]

/-- Reverse adjacency invariance transports to the labeled matrix. -/
theorem mixedLabeledAdjMatrix_rev_of_adj_shift_iff
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) {c : C}
    (hiff : ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y - 1)) ↔ G.Adj (u c x) (u c y)) :
    ∀ x y : ZMod (ℓ c),
      mixedLabeledAdjMatrix K G u ⟨c, x + 1⟩ ⟨c, y - 1⟩ =
        mixedLabeledAdjMatrix K G u ⟨c, x⟩ ⟨c, y⟩ := by
  intro x y
  simp only [mixedLabeledAdjMatrix_apply, SimpleGraph.adjMatrix_apply,
    hiff x y]

/-- **Graph-facing oriented trace identity.**  The restricted adjacency
trace on the mixed frequency space is twice the prime Fourier transform
of the oriented projected anchor counts. -/
theorem graph_mixed_trace_eq_two_mul_oriented_anchor_fourier
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (o : C → Prop) [DecidablePred o]
    (hfwdG : ∀ c : C, p ∣ ℓ c → o c → ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y + 1)) ↔ G.Adj (u c x) (u c y))
    (hrevG : ∀ c : C, p ∣ ℓ c → ¬ o c → ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y - 1)) ↔ G.Adj (u c x) (u c y))
    (hcomm : mixedLabeledAdjMatrix K G u * mixedDefectMatrix K ℓ =
      mixedDefectMatrix K ℓ * mixedLabeledAdjMatrix K G u)
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    LinearMap.trace K
        (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹))
        (defectEigenspaceRestrict (mixedLabeledAdjMatrix K G u) hcomm
          (ζ + ζ⁻¹)) =
      2 * ∑ s : ZMod p,
        ((orientedProjectedAnchor G u o p s : ℕ) : K) * ζ ^ s.val := by
  rw [trace_defectEigenspaceRestrict_mixed_oriented hcomm o
    (fun c hdvd hoc ↦
      mixedLabeledAdjMatrix_fwd_of_adj_shift_iff G u (hfwdG c hdvd hoc))
    (fun c hdvd hoc ↦
      mixedLabeledAdjMatrix_rev_of_adj_shift_iff G u (hrevG c hdvd hoc))
    (mixedLabeledAdjMatrix_isSymm G u) hp hp2 hζ]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [sum_orientedLabeled_diag_eq_orientedProjectedAnchor]

/-- **Oriented nonsquare uniformity.**  With a nonsquare frequency
scalar, all oriented projected anchor counts are equal — no parity
hypothesis on any length. -/
theorem orientedProjectedAnchor_all_eq_of_nonsquare
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (o : C → Prop) [DecidablePred o]
    (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hfwdG : ∀ c : C, p ∣ ℓ c → o c → ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y + 1)) ↔ G.Adj (u c x) (u c y))
    (hrevG : ∀ c : C, p ∣ ℓ c → ¬ o c → ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y - 1)) ↔ G.Adj (u c x) (u c y))
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hns : ¬ IsSquare ((d : K) - 1 - (ζ + ζ⁻¹))) :
    ∀ s t : ZMod p,
      orientedProjectedAnchor G u o p s =
        orientedProjectedAnchor G u o p t := by
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζsq : ζ ^ 2 ≠ 1 :=
    hζ.pow_ne_one_of_pos_of_lt (by norm_num) hp2
  have hζ1 : ζ ≠ 1 := fun h ↦ hζsq (by rw [h, one_pow])
  have hcomm := mixedLabeledAdjMatrix_comm_mixedDefectMatrix (K := K)
    G D u hℓ3 hbij huD hcommZ
  have hTsq := graph_mixed_defectEigenspaceRestrict_sq G D u hℓ3 hbij
    huD hsqZ hcomm hζp (by
      have := hp.two_le
      omega) hζ1
  have htrace0 := LinearMap.trace_eq_zero_of_sq_eq_nonsquare
    (defectEigenspaceRestrict (mixedLabeledAdjMatrix K G u) hcomm
      (ζ + ζ⁻¹)) ((d : K) - 1 - (ζ + ζ⁻¹)) hns hTsq
  have htr := graph_mixed_trace_eq_two_mul_oriented_anchor_fourier
    G u o hfwdG hrevG hcomm hp hp2 hζ
  rw [htrace0] at htr
  have hzero : ∑ s : ZMod p,
      ((orientedProjectedAnchor G u o p s : ℕ) : K) * ζ ^ s.val = 0 :=
    (mul_eq_zero.mp htr.symm).resolve_left two_ne_zero
  have hzero' : ∑ s : ZMod p,
      ((orientedProjectedAnchor G u o p s : ℤ) : K) *
        primitiveRootCharacter hζ s = 0 := by
    rw [← hzero]
    apply Finset.sum_congr rfl
    intro s _
    rw [primitiveRootCharacter_eq_pow_val hζ]
    push_cast
    ring
  let cFin : Fin p → ℤ := fun i ↦
    (orientedProjectedAnchor G u o p (ZMod.finEquiv p i) : ℤ)
  have hzeroFin : ∑ i : Fin p, (cFin i : K) * ζ ^ i.val = 0 := by
    calc
      (∑ i : Fin p, (cFin i : K) * ζ ^ i.val) =
          ∑ s : ZMod p,
            ((orientedProjectedAnchor G u o p s : ℤ) : K) *
              primitiveRootCharacter hζ s := by
        refine Fintype.sum_equiv (ZMod.finEquiv p) _ _ ?_
        intro i
        simp [cFin]
      _ = 0 := hzero'
  have hall := all_eq_of_prime_fourier_eq_zero hp hζ cFin hzeroFin
  intro s t
  have h := hall ((ZMod.finEquiv p).symm s) ((ZMod.finEquiv p).symm t)
  simp only [cFin] at h
  rw [(ZMod.finEquiv p).apply_symm_apply,
    (ZMod.finEquiv p).apply_symm_apply] at h
  exact_mod_cast h

/-- **Oriented nonsquare mass divisibility.**  With a nonsquare frequency
scalar, `p` divides the anchor mass of the forward-oriented
`p`-divisible sector — with no parity hypothesis on any length. -/
theorem prime_dvd_orientedAnchorMass_of_nonsquare
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (o : C → Prop) [DecidablePred o]
    (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hfwdG : ∀ c : C, p ∣ ℓ c → o c → ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y + 1)) ↔ G.Adj (u c x) (u c y))
    (hrevG : ∀ c : C, p ∣ ℓ c → ¬ o c → ∀ x y : ZMod (ℓ c),
      G.Adj (u c (x + 1)) (u c (y - 1)) ↔ G.Adj (u c x) (u c y))
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hns : ¬ IsSquare ((d : K) - 1 - (ζ + ζ⁻¹))) :
    p ∣ orientedAnchorMass G u o p := by
  have hall := orientedProjectedAnchor_all_eq_of_nonsquare G D u o hℓ3
    hbij huD hcommZ hsqZ hfwdG hrevG hp hp2 hζ hns
  have hmass := sum_orientedProjectedAnchor_eq_mass (p := p) G u o
  set a0 := orientedProjectedAnchor G u o p 0 with ha0
  have hconst : ∀ s : ZMod p, orientedProjectedAnchor G u o p s = a0 :=
    fun s ↦ hall s 0
  rw [← hmass, Finset.sum_congr rfl fun s _ ↦ hconst s,
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  exact Dvd.intro a0 rfl

end

end Erdos85
