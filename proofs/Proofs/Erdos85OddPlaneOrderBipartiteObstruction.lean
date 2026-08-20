import Proofs.Erdos85GadgetDegreeSquares
import Proofs.Erdos101ProblemOQ02
import Proofs.Erdos85PositiveExcessLocalParity
import Proofs.Erdos85LocalTriangleParity
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-!
# The plane-minus-two target cannot be a bipartite incidence graph

The existence jaw at an odd plane order seeks a `q`-regular C4-free graph on
`q^2 - 1` vertices.  If such a graph were bipartite, its two sides would have
the same size.  The theorem below isolates the resulting incidence structure
and proves that its parameters are impossible by counting pairs on the other
side.
-/

namespace Erdos85

/-- There is no regular linear incidence structure with two equally-sized
parts whose combined order is `q^2 - 1` and whose degree is `q`.

`huniq` is the incidence form of C4-freeness: two distinct points lie on at
most one common line.  The two cardinality equations say that each part has
size `(q^2 - 1) / 2`, without introducing natural-number division. -/
theorem false_of_planeMinusTwo_regular_linear_incidence
    {Point Line : Type*}
    [Fintype Point] [Fintype Line]
    [DecidableEq Point] [DecidableEq Line]
    (Inc : Point → Line → Prop) [DecidableRel Inc]
    (q : ℕ) (hq : 2 ≤ q)
    (hPoint : 2 * Fintype.card Point + 1 = q * q)
    (hLine : 2 * Fintype.card Line + 1 = q * q)
    (hregular : ∀ ell : Line,
      (Erdos101OQ02ST.pointsOn Inc Finset.univ ell).card = q)
    (huniq : ∀ p ∈ (Finset.univ : Finset Point),
      ∀ r ∈ (Finset.univ : Finset Point), p ≠ r →
      ∀ ell₁ ∈ (Finset.univ : Finset Line),
      ∀ ell₂ ∈ (Finset.univ : Finset Line),
      Inc p ell₁ → Inc r ell₁ → Inc p ell₂ → Inc r ell₂ → ell₁ = ell₂) :
    False := by
  have hpair := Erdos101OQ02ST.sum_choose_two_le Inc
    (Finset.univ : Finset Point) (Finset.univ : Finset Line) huniq
  simp only [Finset.sum_const, Finset.card_univ, hregular,
    nsmul_eq_mul] at hpair
  have hcards : Fintype.card Point = Fintype.card Line := by omega
  have hPointPos : 0 < Fintype.card Point := by
    by_contra hz
    have hz' : Fintype.card Point = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz'] at hPoint
    norm_num at hPoint
    nlinarith
  have hqChoose := two_mul_choose_two q
  have hPointChoose := two_mul_choose_two (Fintype.card Point)
  rw [hcards] at hPoint
  rw [hcards] at hPointChoose
  rw [hcards] at hpair
  have hscaled :
      Fintype.card Line * (q * (q - 1)) ≤
        Fintype.card Line * (Fintype.card Line - 1) := by
    calc
      _ = 2 * (Fintype.card Line * q.choose 2) := by
        rw [← hqChoose]
        ring
      _ ≤ 2 * (Fintype.card Line).choose 2 := Nat.mul_le_mul_left 2 hpair
      _ = _ := hPointChoose
  have hLinePos : 0 < Fintype.card Line := by simpa [hcards] using hPointPos
  have hcancel : q * (q - 1) ≤ Fintype.card Line - 1 :=
    Nat.le_of_mul_le_mul_left hscaled hLinePos
  have hqPred : q - 1 + 1 = q := by omega
  have hLinePred : Fintype.card Line - 1 + 1 = Fintype.card Line := by omega
  nlinarith

/-- **Graph-facing bipartite obstruction at the plane-minus-two order.**
A `q`-regular C4-free graph on `q^2 - 1` vertices cannot be bipartite.

This is the form consumed by the odd-plane-order existence program.  It also
shows that the nonbipartite nature of the checked order-48 witness is forced,
rather than an artifact of its Cayley presentation. -/
theorem not_isBipartite_of_planeMinusTwo_regular_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℕ) (hq : 2 ≤ q)
    (horder : Fintype.card V + 1 = q * q)
    (hregular : ∀ v : V, G.degree v = q)
    (hfree : ¬ containsC4 V G) :
    ¬ G.IsBipartite := by
  intro hbip
  classical
  obtain ⟨s, t, hst⟩ := hbip.exists_isBipartiteWith
  let sF : Finset V := Finset.univ.filter (· ∈ s)
  let tF : Finset V := Finset.univ.filter (· ∈ t)
  have hstF : G.IsBipartiteWith (sF : Set V) (tF : Set V) := by
    simpa [sF, tF] using hst
  have hcover : sF ∪ tF = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hvSupport : v ∈ G.support := by
      rw [← G.degree_pos_iff_mem_support, hregular v]
      omega
    have hv := SimpleGraph.isBipartiteWith_support_subset hst hvSupport
    simpa [sF, tF] using hv
  have hdisjoint : Disjoint sF tF := by
    rw [Finset.disjoint_left]
    intro v hvs hvt
    have hvs' : v ∈ s := by simpa [sF] using hvs
    have hvt' : v ∈ t := by simpa [tF] using hvt
    exact Set.disjoint_left.mp hst.disjoint hvs' hvt'
  have hsum := SimpleGraph.isBipartiteWith_sum_degrees_eq hstF
  simp only [hregular, Finset.sum_const, nsmul_eq_mul] at hsum
  have hqPos : 0 < q := by omega
  have hcards : sF.card = tF.card := by
    exact Nat.eq_of_mul_eq_mul_right hqPos hsum
  have htotal : Fintype.card V = sF.card + tF.card := by
    rw [← Finset.card_univ, ← hcover, Finset.card_union_of_disjoint hdisjoint]
  have hside : 2 * sF.card + 1 = q * q := by
    rw [htotal, ← hcards] at horder
    omega
  have hlineRegular : ∀ ell ∈ tF,
      (Erdos101OQ02ST.pointsOn G.Adj sF ell).card = q := by
    intro ell hell
    rw [← hregular ell, ← G.card_neighborFinset_eq_degree]
    congr 1
    simpa [Erdos101OQ02ST.pointsOn] using
      (SimpleGraph.isBipartiteWith_neighborFinset' hstF hell).symm
  have huniq : ∀ p ∈ sF, ∀ r ∈ sF, p ≠ r →
      ∀ ell₁ ∈ tF, ∀ ell₂ ∈ tF,
      G.Adj p ell₁ → G.Adj r ell₁ →
      G.Adj p ell₂ → G.Adj r ell₂ → ell₁ = ell₂ := by
    intro p _ r _ hpr ell₁ _ ell₂ _ hp₁ hr₁ hp₂ hr₂
    by_contra hell
    exact hfree (containsC4_of_two_common hpr hell
      hp₁.symm hr₁.symm hp₂.symm hr₂.symm)
  have hpair := Erdos101OQ02ST.sum_choose_two_le G.Adj sF tF huniq
  have hpair' : tF.card * q.choose 2 ≤ sF.card.choose 2 := by
    calc
      _ = ∑ _ell ∈ tF, q.choose 2 := by simp
      _ = ∑ ell ∈ tF,
          (Erdos101OQ02ST.pointsOn G.Adj sF ell).card.choose 2 := by
        apply Finset.sum_congr rfl
        intro ell hell
        rw [hlineRegular ell hell]
      _ ≤ _ := hpair
  rw [← hcards] at hpair'
  have hsidePos : 0 < sF.card := by
    by_contra hz
    have hz' : sF.card = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz'] at hside
    norm_num at hside
    nlinarith
  have hqChoose := two_mul_choose_two q
  have hsideChoose := two_mul_choose_two sF.card
  have hscaled :
      sF.card * (q * (q - 1)) ≤ sF.card * (sF.card - 1) := by
    calc
      _ = 2 * (sF.card * q.choose 2) := by
        rw [← hqChoose]
        ring
      _ ≤ 2 * sF.card.choose 2 := Nat.mul_le_mul_left 2 hpair'
      _ = _ := hsideChoose
  have hcancel : q * (q - 1) ≤ sF.card - 1 :=
    Nat.le_of_mul_le_mul_left hscaled hsidePos
  have hqPred : q - 1 + 1 = q := by omega
  have hsidePred : sF.card - 1 + 1 = sF.card := by omega
  nlinarith

/-- At the plane-minus-two order, every vertex has at most `q-2`
triangle-free incident edges.  Thus a target construction cannot have an
independent neighborhood at any vertex. -/
theorem planeMinusTwo_triangleFreeNeighbors_card_le_sub_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (q : ℕ) (hq : 4 ≤ q)
    (horder : Fintype.card V + 1 = q * q)
    (hregular : ∀ v : V, G.degree v = q)
    (hfree : ¬ containsC4 V G) (x : V) :
    (triangleFreeNeighbors G x).card ≤ q - 2 := by
  have hqPred : q - 1 + 1 = q := by omega
  have hmul : q * (q - 1) + q = q * q := by
    calc
      _ = q * ((q - 1) + 1) := by ring
      _ = q * q := by rw [hqPred]
  have hcard : Fintype.card V = q * (q - 1) + 3 + (q - 4) := by
    omega
  have hle := triangleFreeNeighbors_card_le_excess_add_two
    G hfree (d := q) (e := q - 4) hregular hcard x
  omega

/-- Every vertex of a plane-minus-two target lies in a triangle, expressed as
nonemptiness of the edge set induced on its neighborhood. -/
theorem planeMinusTwo_localTriangleEdges_nonempty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (q : ℕ) (hq : 4 ≤ q)
    (horder : Fintype.card V + 1 = q * q)
    (hregular : ∀ v : V, G.degree v = q)
    (hfree : ¬ containsC4 V G) (x : V) :
    (G.induce (G.neighborSet x)).edgeFinset.Nonempty := by
  have hle := planeMinusTwo_triangleFreeNeighbors_card_le_sub_two
    G q hq horder hregular hfree x
  have hid := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  rw [hregular x] at hid
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hzero : (G.induce (G.neighborSet x)).edgeFinset.card = 0 := by
    rw [hempty]
    simp
  rw [hzero] at hid
  omega

/-- For odd `q`, every local neighborhood matching at the plane-minus-two
order is nonempty but not perfect.  Its edge count lies between `1` and
`(q-1)/2`; equivalently every vertex lies in a triangle and also has a
triangle-free incident edge. -/
theorem planeMinusTwo_localTriangleEdge_card_bounds_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (q : ℕ) (hq : 4 ≤ q) (hodd : Odd q)
    (horder : Fintype.card V + 1 = q * q)
    (hregular : ∀ v : V, G.degree v = q)
    (hfree : ¬ containsC4 V G) (x : V) :
    1 ≤ (G.induce (G.neighborSet x)).edgeFinset.card ∧
      (G.induce (G.neighborSet x)).edgeFinset.card ≤ (q - 1) / 2 := by
  have hlocalNonempty := planeMinusTwo_localTriangleEdges_nonempty
    G q hq horder hregular hfree x
  have htriangleFree := triangleFreeNeighbors_nonempty_of_odd_degree
    G hfree (x := x) (by simpa [hregular x] using hodd)
  have hid := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
  rw [hregular x] at hid
  have hlocalPos := Finset.card_pos.mpr hlocalNonempty
  have htriangleFreePos := Finset.card_pos.mpr htriangleFree
  constructor
  · exact hlocalPos
  · omega

end Erdos85
