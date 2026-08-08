import Proofs.Erdos85FrequencyPairMixedTransport
import Proofs.Erdos85PrimeFourierNonsquare

/-!
# The nonsquare branch is count-parity-free: divisible anchor mass

When the frequency scalar `d - 1 - ζ - ζ⁻¹` is a nonsquare, the
restricted operator has trace zero, so the mixed projected anchor
Fourier transform vanishes.  Prime Fourier uniformity then forces all
projected anchor counts to be **equal**, and hence `p` divides the total
anchor mass of the `p`-divisible components.

Crucially, this argument uses no parity hypothesis on the number of
`p`-divisible components: it constrains the *even* selected-count case
that the three-point parity terminal cannot see.  The residual question
it isolates is purely arithmetic — whether `p` can divide the
`p`-divisible-sector anchor mass compatibly with the quotient trace
identities.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {K : Type*} [Field K] [CharZero K]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)] {p : ℕ} [NeZero p]

/-- Total anchor mass of the `p`-divisible sector. -/
def pDivisibleAnchorMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (p : ℕ) : ℕ :=
  ∑ c ∈ Finset.univ.filter fun c : C ↦ p ∣ ℓ c,
    (graphCycleBlockZeroSupport G (u c) (u c)).card

/-- The projected anchor counts sum to the sector mass. -/
theorem sum_mixedProjectedAnchor_eq_mass (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : ∀ c : C, ZMod (ℓ c) → V) :
    ∑ s : ZMod p, mixedProjectedAnchor G u p s =
      pDivisibleAnchorMass G u p := by
  rw [pDivisibleAnchorMass]
  unfold mixedProjectedAnchor
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  exact (Finset.card_eq_sum_card_fiberwise
    (f := fun t : ZMod (ℓ c) ↦ ((t.val : ℕ) : ZMod p))
    (s := graphCycleBlockZeroSupport G (u c) (u c))
    (t := Finset.univ) (fun t _ ↦ Finset.mem_univ _)).symm

/-- **Nonsquare uniformity.**  With a nonsquare frequency scalar, all
mixed projected anchor counts are equal — no hypothesis on the number of
`p`-divisible components. -/
theorem mixedProjectedAnchor_all_eq_of_nonsquare
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hodd : ∀ c : C, p ∣ ℓ c → Odd (ℓ c))
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hns : ¬ IsSquare ((d : K) - 1 - (ζ + ζ⁻¹))) :
    ∀ s t : ZMod p,
      mixedProjectedAnchor G u p s = mixedProjectedAnchor G u p t := by
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
  have htr := graph_mixed_trace_eq_two_mul_projected_anchor_fourier
    G D u hℓ3 hbij huD hcommZ hodd hcomm hp hp2 hζ
  rw [htrace0] at htr
  have hzero : ∑ s : ZMod p,
      ((mixedProjectedAnchor G u p s : ℕ) : K) * ζ ^ s.val = 0 :=
    (mul_eq_zero.mp htr.symm).resolve_left two_ne_zero
  have hzero' : ∑ s : ZMod p,
      ((mixedProjectedAnchor G u p s : ℤ) : K) *
        primitiveRootCharacter hζ s = 0 := by
    rw [← hzero]
    apply Finset.sum_congr rfl
    intro s _
    rw [primitiveRootCharacter_eq_pow_val hζ]
    push_cast
    ring
  let cFin : Fin p → ℤ := fun i ↦
    (mixedProjectedAnchor G u p (ZMod.finEquiv p i) : ℤ)
  have hzeroFin : ∑ i : Fin p, (cFin i : K) * ζ ^ i.val = 0 := by
    calc
      (∑ i : Fin p, (cFin i : K) * ζ ^ i.val) =
          ∑ s : ZMod p,
            ((mixedProjectedAnchor G u p s : ℤ) : K) *
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

/-- **Nonsquare mass divisibility.**  With a nonsquare frequency scalar,
`p` divides the total anchor mass of the `p`-divisible sector —
independent of the selected-count parity. -/
theorem prime_dvd_pDivisibleAnchorMass_of_nonsquare
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hodd : ∀ c : C, p ∣ ℓ c → Odd (ℓ c))
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hns : ¬ IsSquare ((d : K) - 1 - (ζ + ζ⁻¹))) :
    p ∣ pDivisibleAnchorMass G u p := by
  have hall := mixedProjectedAnchor_all_eq_of_nonsquare G D u hℓ3 hbij
    huD hcommZ hsqZ hodd hp hp2 hζ hns
  have hmass := sum_mixedProjectedAnchor_eq_mass (p := p) G u
  set a0 := mixedProjectedAnchor G u p 0 with ha0
  have hconst : ∀ s : ZMod p, mixedProjectedAnchor G u p s = a0 :=
    fun s ↦ hall s 0
  rw [← hmass, Finset.sum_congr rfl fun s _ ↦ hconst s,
    Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
  exact Dvd.intro a0 rfl

end

end Erdos85
