import Proofs.Erdos85SquareOrderDefectComponentBalance

/-!
# Dirichlet energy of square-order high incidence

The defect equation `(D+I)k=h1` and the degree law
`deg_D+k=d-1` turn variation of the high-incidence function into an exact
third-moment slack.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Abstract Dirichlet identity for a finite graph sector closed under
adjacency and satisfying the square-order incidence and degree equations. -/
theorem defectIncidence_orientedDirichlet_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (S : Finset V) (k : V → ℕ) (d h : ℕ)
    (hd : 1 ≤ d)
    (hclosed : ∀ ⦃x y : V⦄, x ∈ S → D.Adj x y → y ∈ S)
    (hpoint : ∀ x ∈ S,
      (∑ y ∈ D.neighborFinset x, k y) + k x = h)
    (hdegree : ∀ x ∈ S, D.degree x + k x = d - 1) :
    (∑ x ∈ S, ∑ y ∈ D.neighborFinset x,
        ((k x : ℤ) - k y) ^ 2) =
      2 * ∑ x ∈ S,
        ((d : ℤ) * (k x : ℤ) ^ 2 - (k x : ℤ) ^ 3 -
          (h : ℤ) * k x) := by
  classical
  have hswapNat :
      (∑ x ∈ S, ∑ y ∈ D.neighborFinset x, k y * k y) =
        ∑ x ∈ S, (k x * k x) * D.degree x :=
    sum_closed_neighbor_weights D S (fun x => k x * k x) hclosed
  have hswap :
      (∑ x ∈ S, ∑ y ∈ D.neighborFinset x, (k y : ℤ) ^ 2) =
        ∑ x ∈ S, (k x : ℤ) ^ 2 * D.degree x := by
    have hswapZ := congrArg (fun n : ℕ => (n : ℤ)) hswapNat
    push_cast at hswapZ
    simpa [pow_two] using hswapZ
  calc
    (∑ x ∈ S, ∑ y ∈ D.neighborFinset x,
        ((k x : ℤ) - k y) ^ 2) =
        ∑ x ∈ S, ((D.degree x : ℤ) * (k x : ℤ) ^ 2 +
          (∑ y ∈ D.neighborFinset x, (k y : ℤ) ^ 2) -
          2 * (k x : ℤ) *
            (∑ y ∈ D.neighborFinset x, (k y : ℤ))) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp_rw [sub_sq]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, nsmul_eq_mul]
      rw [D.card_neighborFinset_eq_degree]
      rw [Finset.mul_sum]
      ring
    _ = 2 * ∑ x ∈ S, ((D.degree x : ℤ) * (k x : ℤ) ^ 2 -
          (k x : ℤ) *
            (∑ y ∈ D.neighborFinset x, (k y : ℤ))) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hswap]
      have hcomm :
          (∑ x ∈ S, (k x : ℤ) ^ 2 * D.degree x) =
            ∑ x ∈ S, (D.degree x : ℤ) * (k x : ℤ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
      have htwo :
          (∑ x ∈ S, 2 * (k x : ℤ) *
              (∑ y ∈ D.neighborFinset x, (k y : ℤ))) =
            2 * ∑ x ∈ S, (k x : ℤ) *
              (∑ y ∈ D.neighborFinset x, (k y : ℤ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hcomm, htwo, Finset.sum_sub_distrib]
      ring
    _ = 2 * ∑ x ∈ S,
        ((d : ℤ) * (k x : ℤ) ^ 2 - (k x : ℤ) ^ 3 -
          (h : ℤ) * k x) := by
      congr 1
      apply Finset.sum_congr rfl
      intro x hx
      have hp := hpoint x hx
      have hdg := hdegree x hx
      have hpZ :
          ((∑ y ∈ D.neighborFinset x, k y : ℕ) : ℤ) + k x = h := by
        exact_mod_cast hp
      have hdgZ : (D.degree x : ℤ) + k x = (d : ℤ) - 1 := by
        have hdgZ' : (D.degree x : ℤ) + k x = ((d - 1 : ℕ) : ℤ) := by
          exact_mod_cast hdg
        rw [Nat.cast_sub hd] at hdgZ'
        simpa using hdgZ'
      have hsumZ :
          (∑ y ∈ D.neighborFinset x, (k y : ℤ)) =
            ((∑ y ∈ D.neighborFinset x, k y : ℕ) : ℤ) := by norm_cast
      rw [hsumZ]
      nlinarith

/-- With the square-order first two incidence moments inserted, the oriented
Dirichlet energy is exactly twice the third-moment slack. -/
theorem defectIncidence_orientedDirichlet_eq_thirdMomentSlack
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (S : Finset V) (k : V → ℕ) (d h : ℕ)
    (hd : 1 ≤ d)
    (hclosed : ∀ ⦃x y : V⦄, x ∈ S → D.Adj x y → y ∈ S)
    (hpoint : ∀ x ∈ S,
      (∑ y ∈ D.neighborFinset x, k y) + k x = h)
    (hdegree : ∀ x ∈ S, D.degree x + k x = d - 1)
    (hfirst : (∑ x ∈ S, k x) = (d + 1) * h)
    (hsecond : (∑ x ∈ S, (k x) ^ 2) = h * (h + d)) :
    (∑ x ∈ S, ∑ y ∈ D.neighborFinset x,
        ((k x : ℤ) - k y) ^ 2) =
      2 * ((h : ℤ) * ((d : ℤ) ^ 2 - h) -
        ∑ x ∈ S, (k x : ℤ) ^ 3) := by
  rw [defectIncidence_orientedDirichlet_eq
    D S k d h hd hclosed hpoint hdegree]
  have hfirstZ : (∑ x ∈ S, (k x : ℤ)) = ((d + 1 : ℕ) : ℤ) * h := by
    exact_mod_cast hfirst
  have hsecondZ : (∑ x ∈ S, (k x : ℤ) ^ 2) =
      (h : ℤ) * ((h + d : ℕ) : ℤ) := by
    have hz := congrArg (fun n : ℕ => (n : ℤ)) hsecond
    push_cast at hz
    simpa using hz
  congr 1
  simp_rw [Finset.sum_sub_distrib]
  rw [← Finset.mul_sum, ← Finset.mul_sum, hfirstZ, hsecondZ]
  push_cast
  ring

/-- The global square-order low sector satisfies the exact incidence
Dirichlet/third-moment identity. -/
theorem squareOrder_lowIncidence_orientedDirichlet_eq_thirdMomentSlack
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let H := squareOrderHighVertices G d
    let L := (Finset.univ : Finset V) \ H
    let D := secondOrderDefectGraph G
    let k := squareOrderHighIncidenceCount G d
    let h := H.card
    (∑ x ∈ L, ∑ y ∈ D.neighborFinset x,
        ((k x : ℤ) - k y) ^ 2) =
      2 * ((h : ℤ) * ((d : ℤ) ^ 2 - h) -
        ∑ x ∈ L, (k x : ℤ) ^ 3) := by
  classical
  let H := squareOrderHighVertices G d
  let L := (Finset.univ : Finset V) \ H
  let D := secondOrderDefectGraph G
  let k := squareOrderHighIncidenceCount G d
  let h := H.card
  dsimp only
  have hSlow : ∀ x ∈ L, G.degree x = d := by
    intro x hxL
    have hxnot : x ∉ H := (Finset.mem_sdiff.mp hxL).2
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree hd hmin hcover hcard x with hx | hx
    · exact hx
    · exact (hxnot (Finset.mem_filter.mpr ⟨by simp, hx⟩)).elim
  have hclosed : ∀ ⦃x y : V⦄, x ∈ L → D.Adj x y → y ∈ L := by
    intro x y hxL hxy
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, ?_⟩
    intro hyH
    have hyHigh : G.degree y = d + 1 := (Finset.mem_filter.mp hyH).2
    have hydeg0 : D.degree y = 0 :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree hd hmin hcard hyHigh).1
    have hyempty : D.neighborFinset y = ∅ := by
      apply Finset.card_eq_zero.mp
      simpa [D.card_neighborFinset_eq_degree] using hydeg0
    have hxyN : x ∈ D.neighborFinset y := by
      simpa [SimpleGraph.mem_neighborFinset, D.adj_comm] using hxy
    rw [hyempty] at hxyN
    exact Finset.notMem_empty x hxyN
  have hpoint : ∀ x ∈ L,
      (∑ y ∈ D.neighborFinset x, k y) + k x = h := by
    intro x hxL
    exact squareOrder_sum_highIncidence_over_defectNeighbors_add_self
      G hfree hd hmin hcard (hSlow x hxL)
  have hdegree : ∀ x ∈ L, D.degree x + k x = d - 1 := by
    intro x hxL
    exact squareOrder_defectDegree_add_highIncidence_eq_pred
      G hfree hd hmin hcover hcard (hSlow x hxL)
  have hkzero : ∀ x ∈ H, k x = 0 := by
    intro x hxH
    simpa [k, H, squareOrderHighIncidenceCount] using
      squareOrder_highNeighborCount_eq_zero_of_high G hcover hxH
  have hfirstAll : (∑ x : V, k x) = (d + 1) * h := by
    simpa [k, h, H, squareOrderHighIncidenceCount] using
      squareOrder_sum_highNeighborCount_eq G d
  have hsecondAll : (∑ x : V, (k x) ^ 2) = h * (h + d) := by
    simpa [k, h, H, squareOrderHighIncidenceCount] using
      squareOrder_sum_highNeighborCount_sq_eq
        G hfree hd hmin hcover hcard
  have hfirstSplit := Finset.sum_sdiff
    (show H ⊆ (Finset.univ : Finset V) by simp) (f := k)
  have hsecondSplit := Finset.sum_sdiff
    (show H ⊆ (Finset.univ : Finset V) by simp) (f := fun x => (k x) ^ 2)
  have hfirst : (∑ x ∈ L, k x) = (d + 1) * h := by
    have hz : (∑ x ∈ H, k x) = 0 := Finset.sum_eq_zero hkzero
    rw [hz, add_zero] at hfirstSplit
    simpa [L] using hfirstSplit.trans hfirstAll
  have hsecond : (∑ x ∈ L, (k x) ^ 2) = h * (h + d) := by
    have hz : (∑ x ∈ H, (k x) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro x hxH
      simp [hkzero x hxH]
    rw [hz, add_zero] at hsecondSplit
    simpa [L] using hsecondSplit.trans hsecondAll
  exact defectIncidence_orientedDirichlet_eq_thirdMomentSlack
    D L k d h (by omega) hclosed hpoint hdegree hfirst hsecond

/-- The low-sector third incidence moment is bounded by the exact Dirichlet
budget `h(d²-h)`. -/
theorem squareOrder_sum_low_highIncidence_cube_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ z : V, d ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let H := squareOrderHighVertices G d
    let L := (Finset.univ : Finset V) \ H
    let k := squareOrderHighIncidenceCount G d
    (∑ x ∈ L, (k x) ^ 3) ≤ H.card * (d * d - H.card) := by
  classical
  let H := squareOrderHighVertices G d
  let L := (Finset.univ : Finset V) \ H
  let D := secondOrderDefectGraph G
  let k := squareOrderHighIncidenceCount G d
  let h := H.card
  dsimp only
  have hid := squareOrder_lowIncidence_orientedDirichlet_eq_thirdMomentSlack
    G hfree hd hmin hcover hcard
  change (∑ x ∈ L, ∑ y ∈ D.neighborFinset x,
      ((k x : ℤ) - k y) ^ 2) =
    2 * ((h : ℤ) * ((d : ℤ) ^ 2 - h) -
      ∑ x ∈ L, (k x : ℤ) ^ 3) at hid
  have henergy_nonneg :
      0 ≤ ∑ x ∈ L, ∑ y ∈ D.neighborFinset x,
        ((k x : ℤ) - k y) ^ 2 := by positivity
  have hslackZ :
      (∑ x ∈ L, (k x : ℤ) ^ 3) ≤
        (h : ℤ) * ((d : ℤ) ^ 2 - h) := by nlinarith
  have hsubset : H ⊆ (Finset.univ : Finset V) := by simp
  have hhcard : h ≤ d * d := by
    calc
      h = H.card := rfl
      _ ≤ Fintype.card V := by simpa using Finset.card_le_card hsubset
      _ = d * d := hcard
  have hsumCast :
      ((∑ x ∈ L, (k x) ^ 3 : ℕ) : ℤ) =
        ∑ x ∈ L, (k x : ℤ) ^ 3 := by norm_cast
  have hbudgetCast :
      ((h * (d * d - h) : ℕ) : ℤ) =
        (h : ℤ) * ((d : ℤ) ^ 2 - h) := by
    rw [Nat.cast_mul, Nat.cast_sub hhcard]
    push_cast
    ring
  rw [← hsumCast, ← hbudgetCast] at hslackZ
  have hNat : (∑ x ∈ L, (k x) ^ 3) ≤ h * (d * d - h) := by
    exact_mod_cast hslackZ
  simpa [H, L, k, h] using hNat

end

end Erdos85
