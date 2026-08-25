import Proofs.Erdos85PureEndpointMinimumPrivateCutGrid
import Proofs.Erdos85PureEndpointPairPointTrade

/-!
# The pair-point obstruction to an equality private cut

The equality case of the exterior private-occupancy trade produces a grid:
every zero row and every double row already have a common point on the
complementary shore.  Linearity then prevents a pair point from lying on
both kinds of row.  On the other hand, the local private-incidence average
at a pair point is at most one.  These facts are incompatible with a double
row having any pair point.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

/-- Abstract terminal behind the pure-endpoint minimum-cut contradiction.

`Z` is the set of zero-weight rows, `W` a set of rows of weight at least two,
`U` is the grid-point shore, and `X` is the pair-point shore.  If every
zero/double pair already meets on `U`, linearity forbids it from meeting
again on `X`.  Thus a pair point on a double row sees no zero row, making
its average row weight strictly greater than one, contrary to `hlocal`.
-/
theorem linear_grid_pairPoint_average_contradiction
    {Point Row : Type*} [DecidableEq Point] [DecidableEq Row]
    (Inc : Row → Point → Prop) [DecidableRel Inc]
    (U X : Finset Point) (B Z W : Finset Row) (weight : Row → ℕ)
    (hzero : ∀ b ∈ B, weight b = 0 → b ∈ Z)
    (hWB : W ⊆ B)
    (hWtwo : ∀ w ∈ W, 2 ≤ weight w)
    (hgrid : ∀ z ∈ Z, ∀ w ∈ W,
      ∃ u ∈ U, Inc z u ∧ Inc w u)
    (hlinear : ∀ z ∈ Z, ∀ w ∈ W, ∀ u ∈ U, ∀ x ∈ X,
      Inc z u → Inc w u → Inc z x → Inc w x → False)
    (hlocal : ∀ x ∈ X,
      ∑ b ∈ B.filter (fun b => Inc b x), weight b ≤
        (B.filter fun b => Inc b x).card)
    (hWX : ∀ w ∈ W, ∃ x ∈ X, Inc w x) :
    W = ∅ := by
  classical
  by_contra hWne
  obtain ⟨w, hw⟩ := Finset.nonempty_iff_ne_empty.mpr hWne
  obtain ⟨x, hxX, hwx⟩ := hWX w hw
  let N := B.filter fun b => Inc b x
  have hwB : w ∈ B := hWB hw
  have hwN : w ∈ N := Finset.mem_filter.mpr ⟨hwB, hwx⟩
  have hnoZ : ∀ z ∈ Z, ¬ Inc z x := by
    intro z hz hzx
    obtain ⟨u, huU, hzu, hwu⟩ := hgrid z hz w hw
    exact hlinear z hz w hw u huU x hxX hzu hwu hzx hwx
  have hone : ∀ b ∈ N, 1 ≤ weight b := by
    intro b hb
    have hbB := (Finset.mem_filter.mp hb).1
    by_contra hnot
    have hbzero : weight b = 0 := by omega
    have hbZ := hzero b hbB hbzero
    exact hnoZ b hbZ (Finset.mem_filter.mp hb).2
  have hstrict : N.card < ∑ b ∈ N, weight b := by
    have hsum : ∑ b ∈ N, 1 < ∑ b ∈ N, weight b := by
      apply Finset.sum_lt_sum
      · intro b hb
        exact hone b hb
      · exact ⟨w, hwN, hWtwo w hw⟩
    simpa using hsum
  have hupper := hlocal x hxX
  change ∑ b ∈ N, weight b ≤ N.card at hupper
  omega

/-- A preconnected pure endpoint's private set cannot have defect cut `q`. -/
theorem c4Free_binarySquare_pureEndpoint_minimumPrivateCut_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hfour : 4 ∣ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V) (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v, (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    finsetGraphCutSize (secondOrderDefectGraph G)
      (S.filter fun x =>
        (G.neighborFinset x ∩ fullLineCenters G S q).card = 1) ≠ q := by
  classical
  intro hcut
  let F := fullLineCenters G S q
  let B := Fᶜ
  let P := S.filter fun p => (G.neighborFinset p ∩ F).card = 1
  let X := S.filter fun x => (G.neighborFinset x ∩ F).card = 2
  let U := Sᶜ
  let r : V → ℕ := fun b => (G.neighborFinset b ∩ P).card
  let Z := B.filter fun b => r b = 0
  let W := Finset.univ.filter fun b => r b = 2
  have hprofile :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hrows := c4Free_binarySquare_pureEndpoint_minimumPrivateCut_rowProfile
    G hfree hq hqm hfour hreg hcard S hempty hCcard hshore htri hcut
  have hWcard : 2 * W.card = q := by simpa [W, r, P, F] using hrows.2
  have hWpos : 0 < W.card := by omega
  have hWnonempty : W.Nonempty := Finset.card_pos.mp hWpos
  have hfull :=
    c4Free_binarySquare_pureEndpoint_fullCenter_privateOccupancy_one
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hWB : W ⊆ B := by
    intro w hw
    apply Finset.mem_compl.mpr
    intro hwF
    have h2 : r w = 2 := (Finset.mem_filter.mp hw).2
    have h1 : r w = 1 := by
      simpa [r, P, F] using hfull w (by simpa [F] using hwF)
    omega
  have hgrid0 := c4Free_binarySquare_pureEndpoint_minimumPrivateCut_grid
    G hfree hq hqm hfour hreg hcard hconn S hempty hCcard hshore htri hcut
  have hgrid : ∀ z ∈ Z, ∀ w ∈ W,
      ∃ u ∈ U, G.Adj z u ∧ G.Adj w u := by
    intro z hz w hw
    have hwTwo : r w = 2 := (Finset.mem_filter.mp hw).2
    have hrpos : 1 < r w := by rw [hwTwo]; omega
    have hc := hgrid0 z hz w (hWB hw) hrpos
    have hcpos : 0 <
        (U.filter fun u => G.Adj z u ∧ G.Adj w u).card := by
      rw [hc]
      simp
    obtain ⟨u, hu⟩ := Finset.card_pos.mp hcpos
    exact ⟨u, (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩
  have hlinear : ∀ z ∈ Z, ∀ w ∈ W, ∀ u ∈ U, ∀ x ∈ X,
      G.Adj z u → G.Adj w u → G.Adj z x → G.Adj w x → False := by
    intro z hz w hw u huU x hxX hzu hwu hzx hwx
    have hzw : z ≠ w := by
      intro h
      subst w
      have h0 := (Finset.mem_filter.mp hz).2
      have h2 := (Finset.mem_filter.mp hw).2
      omega
    have hux : u ≠ x := by
      intro h
      subst x
      exact (Finset.mem_compl.mp huU) (Finset.mem_filter.mp hxX).1
    exact hfree (containsC4_of_two_common hzw hux
      hzu.symm hwu.symm hzx.symm hwx.symm)
  have hlocal0 :=
    c4Free_binarySquare_pureEndpoint_pairPoint_privateOccupancy_add_defect
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hlocal : ∀ x ∈ X,
      ∑ b ∈ B.filter (fun b => G.Adj b x), r b ≤
        (B.filter fun b => G.Adj b x).card := by
    intro x hx
    have hi := hlocal0 x hx
    have heq : B.filter (fun b => G.Adj b x) =
        G.neighborFinset x ∩ B := by
      ext b
      simp [SimpleGraph.mem_neighborFinset, G.adj_comm, and_comm]
    rw [heq]
    change (∑ b ∈ G.neighborFinset x ∩ B,
      (G.neighborFinset b ∩ P).card) ≤ _
    change (∑ b ∈ G.neighborFinset x ∩ B,
      (G.neighborFinset b ∩ P).card) +
        ((secondOrderDefectGraph G).neighborFinset x ∩ P).card =
          (G.neighborFinset x ∩ B).card at hi
    omega
  have hSX : S = P ∪ X := by
    ext x
    simp only [P, X, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hx
      rcases (hprofile.1 x).mp hx with h1 | h2
      · exact Or.inl ⟨hx, by simpa [F] using h1⟩
      · exact Or.inr ⟨hx, by simpa [F] using h2⟩
    · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  have hPXdisj : Disjoint P X := by
    rw [Finset.disjoint_left]
    intro x hxP hxX
    have h1 := (Finset.mem_filter.mp hxP).2
    have h2 := (Finset.mem_filter.mp hxX).2
    omega
  have hWX : ∀ w ∈ W, ∃ x ∈ X, G.Adj w x := by
    intro w hw
    have hwNotF : w ∉ F := by simpa [B] using hWB hw
    have hmOcc :=
      (c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri w hwNotF).1
    have h2 : (G.neighborFinset w ∩ P).card = 2 := by
      simpa [r] using (Finset.mem_filter.mp hw).2
    have hsplit : (G.neighborFinset w ∩ S).card =
        (G.neighborFinset w ∩ P).card +
          (G.neighborFinset w ∩ X).card := by
      rw [hSX, Finset.inter_union_distrib_left,
        Finset.card_union_of_disjoint]
      exact hPXdisj.mono Finset.inter_subset_right Finset.inter_subset_right
    have hpos : 0 < (G.neighborFinset w ∩ X).card := by
      rw [hmOcc, h2] at hsplit
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    exact ⟨x, (Finset.mem_inter.mp hx).2,
      (G.mem_neighborFinset w x).mp (Finset.mem_inter.mp hx).1⟩
  have hzero : ∀ b ∈ B, r b = 0 → b ∈ Z := by
    intro b hb hr
    exact Finset.mem_filter.mpr ⟨hb, hr⟩
  have hcollapse := linear_grid_pairPoint_average_contradiction
    G.Adj U X B Z W r hzero hWB
    (by intro w hw; have := (Finset.mem_filter.mp hw).2; omega)
    hgrid hlinear hlocal hWX
  exact hWnonempty.ne_empty hcollapse

end

end Erdos85

#print axioms Erdos85.linear_grid_pairPoint_average_contradiction
#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_minimumPrivateCut_ne
