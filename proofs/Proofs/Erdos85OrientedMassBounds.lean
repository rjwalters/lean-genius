import Proofs.Erdos85OrientationMarking
import Proofs.Erdos85DifferencePacking
import Proofs.Erdos85PrimeSectorSize

/-!
# Parity-free bounds for the oriented anchor mass

The inverse-pair Sidon bound for a forward-circulant diagonal block does not
use oddness of the defect cycle.  Thus every component selected by the
canonical forward orientation has diagonal quotient entry at most two.  An
even cycle may contribute one (the antipodal matching), so the old
`{0,2}` mass gap does not survive verbatim, but the uniform upper bound does.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A forward-oriented diagonal block on a defect cycle has quotient entry
at most two, independently of the parity of the cycle length. -/
theorem forwardComponent_diagonalQuotient_le_two
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (u : ZMod r → V) (hu : Function.Injective u)
    (huRange : Set.range u = c.supp)
    (hfwd : ∀ x y : ZMod r,
      G.Adj (u (x + 1)) (u (y + 1)) ↔ G.Adj (u x) (u y)) :
    componentQuotientMatrix G (secondOrderDefectGraph G) c c ≤ 2 := by
  let D := secondOrderDefectGraph G
  have htrans : ∀ x y : ZMod r,
      G.adjMatrix ℤ (u (x + 1)) (u (y + 1)) =
        G.adjMatrix ℤ (u x) (u y) := by
    intro x y
    simp only [SimpleGraph.adjMatrix_apply, hfwd x y]
  obtain ⟨A, hA⟩ :=
    exists_connectionSet_of_translationInvariantBlock G u u htrans
  have hAle : A.card ≤ 2 :=
    card_connectionSet_le_two_of_c4Free_self_circulantBlock
      G hfree u hu A hA
  have hu0c : u 0 ∈ c.supp := by
    rw [← huRange]
    exact ⟨0, rfl⟩
  have hQ := componentQuotientMatrix_apply_eq G D 2
    (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard)
    (adjMatrix_comm_secondOrderDefect_of_even_real
      G hfree hd heven hmin hcard) c c hu0c
  rw [hQ]
  have heq : componentNeighborFinset G D c (u 0) = A.image u := by
    ext y
    constructor
    · intro hy
      have hydata : G.Adj (u 0) y ∧ y ∈ c.supp := by
        simpa [componentNeighborFinset, SimpleGraph.mem_neighborFinset,
          and_comm] using hy
      have hyrange : y ∈ Set.range u := by simpa [huRange] using hydata.2
      obtain ⟨z, rfl⟩ := hyrange
      have hzA : z ∈ A := by
        simpa using (hA 0 z).mp hydata.1
      exact Finset.mem_image.mpr ⟨z, hzA, rfl⟩
    · intro hy
      obtain ⟨z, hzA, rfl⟩ := Finset.mem_image.mp hy
      have hzc : u z ∈ c.supp := by
        rw [← huRange]
        exact ⟨z, rfl⟩
      have hAdj : G.Adj (u 0) (u z) := by
        rw [hA]
        simpa using hzA
      have hzmk : D.connectedComponentMk (u z) = c :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff c (u z)).mp hzc
      simp [componentNeighborFinset, hAdj, hzmk]
  rw [heq, Finset.card_image_iff.mpr]
  · exact hAle
  · intro x _ y _ hxy
    exact hu hxy

/-- The oriented mass is the diagonal trace over the forward selected
components. -/
theorem orientedAnchorMass_eq_sum_diagonalQuotient
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (o : (secondOrderDefectGraph G).ConnectedComponent → Prop)
    [DecidablePred o] :
    orientedAnchorMass G u o p =
      ∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard ∧ o c),
        componentQuotientMatrix G (secondOrderDefectGraph G) c c := by
  unfold orientedAnchorMass
  apply Finset.sum_congr rfl
  intro c _
  exact card_graphCycleBlockZeroSupport_eq_componentQuotient G hfree hd
    heven hmin hcard c c (u c) (u c) (hu c) (huRange c) (huRange c)

/-- The canonical oriented mass is at most twice the number of its selected
forward components.  No component-order parity hypothesis is needed. -/
theorem orientedAnchorMass_forwardOriented_le_two_mul_component_card
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp) :
    orientedAnchorMass G u (forwardOriented G u) p ≤
      2 * (Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard ∧ forwardOriented G u c)).card := by
  classical
  rw [orientedAnchorMass_eq_sum_diagonalQuotient G hfree hd heven hmin
    hcard u hu huRange]
  calc
    (∑ c ∈ Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard ∧ forwardOriented G u c),
        componentQuotientMatrix G (secondOrderDefectGraph G) c c) ≤
        ∑ _c ∈ Finset.univ.filter (fun c :
          (secondOrderDefectGraph G).ConnectedComponent ↦
            p ∣ c.supp.ncard ∧ forwardOriented G u c), 2 := by
      apply Finset.sum_le_sum
      intro c hc
      exact forwardComponent_diagonalQuotient_le_two G hfree hd heven hmin
        hcard c (u c) (hu c) (huRange c) (Finset.mem_filter.mp hc).2.2
    _ = 2 * (Finset.univ.filter (fun c :
        (secondOrderDefectGraph G).ConnectedComponent ↦
          p ∣ c.supp.ncard ∧ forwardOriented G u c)).card := by
      simp [Nat.mul_comm]

/-- If the canonical oriented mass is a nonzero multiple of `p`, then the
boundary order is at least `p²/2`.  Equivalently, `p² > 2|V|` forces the
oriented mass to vanish. -/
theorem orientedAnchorMass_forwardOriented_eq_zero_of_dvd_of_large_prime
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      NeZero c.supp.ncard]
    (hfree : ¬ containsC4 V G) {d p : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : 0 < p) (hbig : 2 * (d * (d - 1) + 3) < p * p)
    (u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ZMod c.supp.ncard → V)
    (hu : ∀ c, Function.Injective (u c))
    (huRange : ∀ c, Set.range (u c) = c.supp)
    (hdvd : p ∣ orientedAnchorMass G u (forwardOriented G u) p) :
    orientedAnchorMass G u (forwardOriented G u) p = 0 := by
  classical
  by_contra hne
  have hpos : 0 < orientedAnchorMass G u (forwardOriented G u) p :=
    Nat.pos_of_ne_zero hne
  have hple : p ≤ orientedAnchorMass G u (forwardOriented G u) p :=
    Nat.le_of_dvd hpos hdvd
  let S := Finset.univ.filter (fun c :
    (secondOrderDefectGraph G).ConnectedComponent ↦
      p ∣ c.supp.ncard ∧ forwardOriented G u c)
  have hmass := orientedAnchorMass_forwardOriented_le_two_mul_component_card
    G hfree hd heven hmin hcard u hu huRange (p := p)
  have hsizeAll := prime_mul_pDivisible_component_card_le_card
    (secondOrderDefectGraph G) hp
  have hSsub : S.card ≤ (Finset.univ.filter (fun c :
      (secondOrderDefectGraph G).ConnectedComponent ↦
        p ∣ c.supp.ncard)).card := by
    apply Finset.card_le_card
    intro c hc
    simpa [S] using (Finset.mem_filter.mp hc).2.1
  have hpS : p ≤ 2 * S.card := by
    dsimp [S] at hmass ⊢
    exact hple.trans hmass
  have hmul : p * p ≤ 2 * Fintype.card V := by
    have hsector : p * S.card ≤ Fintype.card V :=
      (Nat.mul_le_mul_left p hSsub).trans hsizeAll
    nlinarith
  rw [hcard] at hmul
  omega

end

end Erdos85
