import Proofs.Erdos85QuotientSectorModP
import Proofs.Erdos85ComponentFactorization

/-!
# The residue-prime signed count identity for the `p`-divisible sector

Over `ZMod p` the principal sector block satisfies `Qₚ² = (d-3)•I`.  When
`d-3` is a nonzero residue with square root `s`, the sector space splits
into `±s` eigenspaces and the trace becomes a *signed count*
`s·(a - b)` with `a + b = |Sₚ|`.  If the sector is odd and smaller than
`p`, the signed count cannot vanish modulo `p`, so the partial diagonal
trace `Σ_{p ∣ ℓc} Q(c,c)` — equivalently the selected anchor mass — is
nonzero mod `p`.  In particular the odd-count branch of the parity
program cannot have an empty sector diagonal at any prime `p` with
`p² > d(d-1)+3`: the even-dimensional zero-diagonal normal form
`[[0,1],[d-3,0]]` is a parity artefact, invisible at odd sector counts.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Signed rank count for square roots of scalars.**  A matrix squaring
to `s² • 1` with `s ≠ 0` (and `2 ≠ 0`) diagonalizes into `±s` eigenspaces:
its trace is `s·(a - b)` where the natural numbers `a`, `b` add up to the
dimension. -/
theorem Matrix.trace_eq_smul_rank_sub_of_sq_eq_smul_one
    {K I : Type*} [Field K] [Fintype I] [DecidableEq I]
    (M : Matrix I I K) (s : K) (h2 : (2 : K) ≠ 0) (hs : s ≠ 0)
    (hsq : M * M = (s * s) • (1 : Matrix I I K)) :
    ∃ a b : ℕ, a + b = Fintype.card I ∧
      Matrix.trace M = s * ((a : K) - (b : K)) := by
  have ht : (2 * s) ≠ 0 := mul_ne_zero h2 hs
  set P : Matrix I I K := (2 * s)⁻¹ • (s • (1 : Matrix I I K) + M)
    with hPdef
  have hexpand : (s • (1 : Matrix I I K) + M) *
      (s • (1 : Matrix I I K) + M) =
      (2 * s) • (s • (1 : Matrix I I K) + M) := by
    rw [add_mul, mul_add, mul_add, hsq]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    rw [smul_add, smul_smul]
    rw [show (2 : K) * s * s = s * s + s * s by ring,
      show (2 : K) * s = s + s by ring, add_smul, add_smul]
    abel
  have hPP : P * P = P := by
    calc
      P * P = (2 * s)⁻¹ • ((2 * s)⁻¹ •
          ((s • (1 : Matrix I I K) + M) *
            (s • (1 : Matrix I I K) + M))) := by
        rw [hPdef, smul_mul_assoc, mul_smul_comm]
      _ = (2 * s)⁻¹ • (((2 * s)⁻¹ * (2 * s)) •
          (s • (1 : Matrix I I K) + M)) := by
        rw [hexpand, smul_smul]
      _ = P := by rw [inv_mul_cancel₀ ht, one_smul, hPdef]
  have hfP : IsIdempotentElem (Matrix.toLin' P) := by
    show Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hPP]
  have hproj := LinearMap.IsIdempotentElem.isProj_range _ hfP
  set a : ℕ := Module.finrank K
    ↥(LinearMap.range (Matrix.toLin' P)) with hadef
  have htraceP : LinearMap.trace K (I → K) (Matrix.toLin' P) = (a : K) :=
    hproj.trace
  have haLe : a ≤ Fintype.card I := by
    have h1 : a ≤ Module.finrank K (I → K) := Submodule.finrank_le _
    rwa [Module.finrank_pi] at h1
  have htrP : Matrix.trace P = (a : K) := by
    rw [← Matrix.trace_toLin'_eq P]
    exact htraceP
  have hM : M = (2 * s) • P - s • (1 : Matrix I I K) := by
    rw [hPdef, smul_smul, mul_inv_cancel₀ ht, one_smul]
    abel
  refine ⟨a, Fintype.card I - a, by omega, ?_⟩
  have hcast : ((Fintype.card I - a : ℕ) : K) =
      (Fintype.card I : K) - (a : K) := Nat.cast_sub haLe
  rw [hM, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, htrP, hcast]
  simp only [smul_eq_mul]
  ring

/-- **Odd small dimension forces nonzero trace.**  Over `ZMod p` a square
root of a nonzero square scalar on an odd-dimensional space of dimension
less than `p` has nonzero trace: the signed count `a - b` is odd, both
summands are below `p`, so the count cannot vanish modulo `p`. -/
theorem Matrix.trace_ne_zero_of_sq_eq_smul_one_of_odd_card
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (ZMod p)) (s : ZMod p) (hs : s ≠ 0)
    (hsq : M * M = (s * s) • (1 : Matrix I I (ZMod p)))
    (hodd : Odd (Fintype.card I)) (hlt : Fintype.card I < p) :
    Matrix.trace M ≠ 0 := by
  have hp : p.Prime := Fact.out
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h20
    have h2n : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h20
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      ((ZMod.natCast_eq_zero_iff 2 p).mp h2n))
  intro htr
  obtain ⟨a, b, hab, htrace⟩ :=
    Matrix.trace_eq_smul_rank_sub_of_sq_eq_smul_one M s h2 hs hsq
  rw [htr] at htrace
  have h0 : ((a : ZMod p) - (b : ZMod p)) = 0 :=
    (mul_eq_zero.mp htrace.symm).resolve_left hs
  have hdiff : ((a : ℕ) : ZMod p) = ((b : ℕ) : ZMod p) :=
    sub_eq_zero.mp h0
  have hmod : a ≡ b [MOD p] := (ZMod.natCast_eq_natCast_iff a b p).mp hdiff
  have haLt : a < p := by omega
  have hbLt : b < p := by omega
  have hEq : a = b := by
    rwa [Nat.ModEq, Nat.mod_eq_of_lt haLt, Nat.mod_eq_of_lt hbLt] at hmod
  rcases hodd with ⟨k, hk⟩
  omega

/-- The orders of the connected components partition the vertex count. -/
theorem sum_connectedComponent_supp_ncard
    {V : Type*} [Fintype V] (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] :
    (∑ c : D.ConnectedComponent, c.supp.ncard) = Fintype.card V := by
  classical
  calc
    (∑ c : D.ConnectedComponent, c.supp.ncard) =
        ∑ c : D.ConnectedComponent, Fintype.card c.supp := by
          apply Finset.sum_congr rfl
          intro c _
          simpa [Nat.card_eq_fintype_card] using
            (Nat.card_coe_set_eq c.supp).symm
    _ = Fintype.card (Σ c : D.ConnectedComponent, c.supp) :=
      Fintype.card_sigma.symm
    _ = Fintype.card V :=
      (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm

/-- If `p²` exceeds the vertex count, fewer than `p` components can have
order divisible by `p`. -/
theorem pDivisible_filter_card_lt_of_card_lt_sq
    {V : Type*} [Fintype V] (D : SimpleGraph V)
    [Fintype D.ConnectedComponent] {p n : ℕ}
    (hp : 0 < p) (hcard : Fintype.card V = n) (hlt : n < p * p) :
    (Finset.univ.filter (fun c : D.ConnectedComponent ↦
      p ∣ c.supp.ncard)).card < p := by
  classical
  have hbound : p * (Finset.univ.filter (fun c : D.ConnectedComponent ↦
      p ∣ c.supp.ncard)).card ≤ n := by
    calc
      p * (Finset.univ.filter (fun c : D.ConnectedComponent ↦
          p ∣ c.supp.ncard)).card =
          ∑ _c ∈ Finset.univ.filter (fun c : D.ConnectedComponent ↦
            p ∣ c.supp.ncard), p := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ c ∈ Finset.univ.filter (fun c : D.ConnectedComponent ↦
            p ∣ c.supp.ncard), c.supp.ncard := by
        apply Finset.sum_le_sum
        intro c hc
        have hdvd : p ∣ c.supp.ncard := (Finset.mem_filter.mp hc).2
        have hpos : 0 < c.supp.ncard :=
          (Set.ncard_pos (Set.toFinite _)).mpr c.nonempty_supp
        exact Nat.le_of_dvd hpos hdvd
      _ ≤ ∑ c : D.ConnectedComponent, c.supp.ncard :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = Fintype.card V := sum_connectedComponent_supp_ncard D
      _ = n := hcard
  by_contra hge
  push_neg at hge
  have hpp : p * p ≤ p * (Finset.univ.filter
      (fun c : D.ConnectedComponent ↦ p ∣ c.supp.ncard)).card :=
    Nat.mul_le_mul_left p hge
  omega

/-- **The residue signed-count obstruction.**  At the exact even boundary,
if the number of `p`-divisible defect components is odd and smaller than
`p`, and `p ∤ d-3`, then the partial diagonal quotient trace over the
`p`-divisible sector is *not* divisible by `p`. -/
theorem secondOrder_not_dvd_sector_diagonal_trace_of_odd_small
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d p : ℕ} [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp2 : p ≠ 2) (hnd : ¬ p ∣ (d - 3))
    (hodd : Odd ((Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card))
    (hsmall : (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card < p) :
    ¬ p ∣ ∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard),
        componentQuotientMatrix G (secondOrderDefectGraph G) c c := by
  letI : Fact p.Prime := ⟨hp⟩
  intro hdvd
  obtain ⟨s, hs⟩ := isSquare_d_sub_three_mod_prime_of_odd_pDivisible_filter
    G hfree hd heven hmin hcard hp hodd
  have hsne : s ≠ 0 := by
    intro h0
    apply hnd
    rw [← ZMod.natCast_eq_zero_iff (d - 3) p, hs, h0, mul_zero]
  have hsq : pDivisibleComponentQuotientMatrix G
      (secondOrderDefectGraph G) p *
      pDivisibleComponentQuotientMatrix G (secondOrderDefectGraph G) p =
      ((d - 3 : ℕ) : ZMod p) •
        (1 : Matrix (pDivisibleComponent (secondOrderDefectGraph G) p)
          (pDivisibleComponent (secondOrderDefectGraph G) p) (ZMod p)) :=
    pDivisibleComponentQuotientMatrix_sq G hfree hd heven hmin hcard hp
  rw [hs] at hsq
  have hoddI : Odd (Fintype.card
      (pDivisibleComponent (secondOrderDefectGraph G) p)) := by
    unfold pDivisibleComponent
    rw [Fintype.card_subtype]
    exact hodd
  have hltI : Fintype.card
      (pDivisibleComponent (secondOrderDefectGraph G) p) < p := by
    unfold pDivisibleComponent
    rw [Fintype.card_subtype]
    exact hsmall
  have hsub : (∑ c : pDivisibleComponent (secondOrderDefectGraph G) p,
      ((componentQuotientMatrix G (secondOrderDefectGraph G) c.1 c.1 : ℕ) :
        ZMod p)) =
      ∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard),
        ((componentQuotientMatrix G (secondOrderDefectGraph G) c c : ℕ) :
          ZMod p) := by
    simpa using Finset.sum_subtype_eq_sum_filter
      (s := (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent))
      (p := fun c ↦ p ∣ c.supp.ncard)
      (fun c ↦
        ((componentQuotientMatrix G (secondOrderDefectGraph G) c c : ℕ) :
          ZMod p))
  have htr : Matrix.trace (pDivisibleComponentQuotientMatrix G
      (secondOrderDefectGraph G) p) =
      ((∑ c ∈ Finset.univ.filter (fun c :
          (secondOrderDefectGraph G).ConnectedComponent ↦
            p ∣ c.supp.ncard),
        componentQuotientMatrix G (secondOrderDefectGraph G) c c : ℕ) :
          ZMod p) := by
    rw [Matrix.trace]
    change (∑ c : pDivisibleComponent (secondOrderDefectGraph G) p,
      ((componentQuotientMatrix G (secondOrderDefectGraph G) c.1 c.1 : ℕ) :
        ZMod p)) = _
    rw [hsub, Nat.cast_sum]
  have hzero : Matrix.trace (pDivisibleComponentQuotientMatrix G
      (secondOrderDefectGraph G) p) = 0 := by
    rw [htr]
    exact (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
  exact Matrix.trace_ne_zero_of_sq_eq_smul_one_of_odd_card hp2
    (pDivisibleComponentQuotientMatrix G (secondOrderDefectGraph G) p)
    s hsne hsq hoddI hltI hzero

/-- **Odd sector counts force a sector diagonal at large residue primes.**
At the exact even boundary, a prime `p` with `p² > d(d-1)+3`, `p ∤ d-3`,
and an odd number of `p`-divisible components must see a `p`-divisible
component with positive diagonal quotient.  The even-dimensional
zero-diagonal model of the sector square equation is impossible at odd
sector counts. -/
theorem exists_positive_diagonalQuotient_of_odd_pDivisible_of_large_prime
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d p : ℕ} [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp2 : p ≠ 2) (hnd : ¬ p ∣ (d - 3))
    (hbig : d * (d - 1) + 3 < p * p)
    (hodd : Odd ((Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card)) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ c.supp.ncard ∧
        0 < componentQuotientMatrix G (secondOrderDefectGraph G) c c := by
  have hsmall := pDivisible_filter_card_lt_of_card_lt_sq
    (secondOrderDefectGraph G) hp.pos hcard hbig
  have hnotdvd := secondOrder_not_dvd_sector_diagonal_trace_of_odd_small
    G hfree hd heven hmin hcard hp hp2 hnd hodd hsmall
  by_contra hnone
  push_neg at hnone
  apply hnotdvd
  have hzero : (∑ c ∈ Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard),
      componentQuotientMatrix G (secondOrderDefectGraph G) c c) = 0 := by
    apply Finset.sum_eq_zero
    intro c hc
    have h := hnone c (Finset.mem_filter.mp hc).2
    omega
  rw [hzero]
  exact dvd_zero p

/-- **The selected anchor mass is nonzero mod `p` at odd residue primes.**
Transport of the signed-count obstruction through the mass bridge: with a
cycle labeling of the defect components, the `p`-divisible anchor mass is
not divisible by `p` — in particular it is positive.  This kills the
`mass = 0` branch of the sector-mass dichotomy in the odd-count case for
every prime with `p² > d(d-1)+3`. -/
theorem not_dvd_pDivisibleAnchorMass_of_odd_pDivisible_of_large_prime
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d p : ℕ} [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G)
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp2 : p ≠ 2) (hnd : ¬ p ∣ (d - 3))
    (hbig : d * (d - 1) + 3 < p * p)
    (hodd : Odd ((Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card))
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp) :
    ¬ p ∣ pDivisibleAnchorMass G u p := by
  rw [pDivisibleAnchorMass_eq_sum_diagonalQuotient G hfree hd heven hmin
    hcard u hu huRange]
  exact secondOrder_not_dvd_sector_diagonal_trace_of_odd_small
    G hfree hd heven hmin hcard hp hp2 hnd hodd
    (pDivisible_filter_card_lt_of_card_lt_sq
      (secondOrderDefectGraph G) hp.pos hcard hbig)

/-- Positivity form: the selected anchor mass cannot vanish at an odd
residue prime beyond the vertex-count square root. -/
theorem pDivisibleAnchorMass_pos_of_odd_pDivisible_of_large_prime
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d p : ℕ} [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G)
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp2 : p ≠ 2) (hnd : ¬ p ∣ (d - 3))
    (hbig : d * (d - 1) + 3 < p * p)
    (hodd : Odd ((Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card))
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp) :
    0 < pDivisibleAnchorMass G u p := by
  have hnd2 := not_dvd_pDivisibleAnchorMass_of_odd_pDivisible_of_large_prime
    G hfree hd heven hmin hcard hp hp2 hnd hbig hodd u hu huRange
  rcases Nat.eq_zero_or_pos (pDivisibleAnchorMass G u p) with h0 | hpos
  · exact absurd (h0 ▸ dvd_zero p) hnd2
  · exact hpos

end

end Erdos85
