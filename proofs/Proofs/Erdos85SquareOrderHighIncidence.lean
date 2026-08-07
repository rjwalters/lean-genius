import Proofs.Erdos85HighRootZeroSlack
import Proofs.Erdos85OrderFortyNineIncidence

/-!
# The high-vertex partial design at square order

For a tight-edge-cover witness on `d^2` vertices, the vertices of degree
`d+1` form a partial linear-space design on the degree-`d` vertices.  This
file records its first two incidence moments and the resulting symbolic
Cauchy constraint.  It is the parameter-free version of the order-49
incidence calculation.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The degree-`d+1` sector at square order. -/
def squareOrderHighVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) : Finset V :=
  Finset.univ.filter fun x => G.degree x = d + 1

/-- Since every degree is `d` or `d+1`, total degree excess is exactly the
number of high vertices. -/
theorem squareOrder_sum_degreeExcess_eq_card_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    (∑ x : V, (G.degree x - d)) = (squareOrderHighVertices G d).card := by
  calc
    (∑ x : V, (G.degree x - d)) =
        ∑ x : V, if G.degree x = d + 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree hd hmin hcover hcard x with hx | hx <;> simp [hx]
    _ = (squareOrderHighVertices G d).card := by
      rw [← Finset.sum_filter]
      simp [squareOrderHighVertices]

/-- Handshake parity: at square order, `d^3 + h` is even.  Equivalently the
high count has the same parity as `d`. -/
theorem squareOrder_even_cube_add_card_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    Even (d * d * d + (squareOrderHighVertices G d).card) := by
  let h := (squareOrderHighVertices G d).card
  have hexcess := squareOrder_sum_degreeExcess_eq_card_high
    G hfree hd hmin hcover hcard
  have hsum : (∑ x : V, G.degree x) = d * (d * d) + h := by
    calc
      (∑ x : V, G.degree x) =
          ∑ x : V, (d + (G.degree x - d)) := by
        apply Finset.sum_congr rfl
        intro x _
        have hx := hmin x
        omega
      _ = d * Fintype.card V + ∑ x : V, (G.degree x - d) := by
        rw [Finset.sum_add_distrib]
        simp [Nat.mul_comm]
      _ = d * (d * d) + h := by rw [hcard, hexcess]
  have hhand := G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhand
  rcases hhand with hhand
  refine ⟨G.edgeFinset.card, ?_⟩
  change d * d * d + h = G.edgeFinset.card + G.edgeFinset.card
  nlinarith [hhand]

/-- Every high vertex contributes `d+1` incidences. -/
theorem squareOrder_sum_highNeighborCount_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ) :
    (∑ x : V, (G.neighborFinset x ∩ squareOrderHighVertices G d).card) =
      (d + 1) * (squareOrderHighVertices G d).card := by
  rw [sum_card_neighbor_inter_eq_sum_degree]
  calc
    (∑ a ∈ squareOrderHighVertices G d, G.degree a) =
        ∑ _a ∈ squareOrderHighVertices G d, (d + 1) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    _ = (d + 1) * (squareOrderHighVertices G d).card := by
      simp [Nat.mul_comm]

/-- The high-incidence square moment is `h(h+d)`: diagonal pairs contribute
`d+1`, while every distinct pair contributes its unique common neighbor. -/
theorem squareOrder_sum_highNeighborCount_sq_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    (∑ x : V,
      ((G.neighborFinset x ∩ squareOrderHighVertices G d).card) ^ 2) =
      (squareOrderHighVertices G d).card *
        ((squareOrderHighVertices G d).card + d) := by
  rw [sum_neighbor_inter_sq_eq_sum_sum_common]
  have hterm : ∀ a ∈ squareOrderHighVertices G d,
      ∀ b ∈ squareOrderHighVertices G d,
      (G.neighborFinset a ∩ G.neighborFinset b).card =
        if a = b then d + 1 else 1 := by
    intro a ha b hb
    have haHigh : G.degree a = d + 1 := (Finset.mem_filter.mp ha).2
    have hbHigh : G.degree b = d + 1 := (Finset.mem_filter.mp hb).2
    by_cases hab : a = b
    · subst b
      rw [if_pos rfl, Finset.inter_self,
        G.card_neighborFinset_eq_degree, haHigh]
    · rw [if_neg hab]
      exact squareOrder_card_common_degree_succ_eq_one
        G hfree hd hmin hcover hcard haHigh hbHigh hab
  let H := squareOrderHighVertices G d
  calc
    (∑ a ∈ H, ∑ b ∈ H,
        (G.neighborFinset a ∩ G.neighborFinset b).card) =
        ∑ a ∈ H, ∑ b ∈ H, if a = b then d + 1 else 1 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hterm a ha b hb
    _ = H.card * (H.card + d) := by
      have hinner : ∀ a ∈ H,
          (∑ b ∈ H, if a = b then d + 1 else 1) = H.card + d := by
        intro a ha
        calc
          (∑ b ∈ H, if a = b then d + 1 else 1) =
              (∑ b ∈ H.erase a, if a = b then d + 1 else 1) + (d + 1) := by
            rw [← Finset.sum_erase_add _ _ ha]
            simp
          _ = (∑ _b ∈ H.erase a, 1) + (d + 1) := by
            congr 1
            apply Finset.sum_congr rfl
            intro b hb
            have hba : b ≠ a := (Finset.mem_erase.mp hb).1
            simp [hba.symm]
          _ = H.card + d := by
            rw [Finset.sum_const, Finset.card_erase_of_mem ha]
            change (H.card - 1) * 1 + (d + 1) = H.card + d
            rw [Nat.mul_one]
            have hpos : 0 < H.card := Finset.card_pos.mpr ⟨a, ha⟩
            omega
      rw [Finset.sum_congr rfl hinner, Finset.sum_const]
      simp

/-- A high vertex has no high neighbor, so all incidence moments are carried
by the low sector. -/
theorem squareOrder_highNeighborCount_eq_zero_of_high
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ}
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    {x : V} (hx : x ∈ squareOrderHighVertices G d) :
    (G.neighborFinset x ∩ squareOrderHighVertices G d).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hxy : G.Adj x y := by
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hy).1
  have hxHigh : G.degree x = d + 1 := (Finset.mem_filter.mp hx).2
  have hyHigh : G.degree y = d + 1 :=
    (Finset.mem_filter.mp (Finset.mem_inter.mp hy).2).2
  exact squareOrder_not_adj_degree_succ_of_tightEdgeCover
    G hcover hxHigh hyHigh hxy

/-- Every high neighbor of a low vertex has a distinct low triangle partner.
Consequently, if `k_x` is the number of high neighbors of a degree-`d`
vertex, then `2 k_x ≤ d`.  This is the parametric form of the order-49
bound `k_x ≤ 3`. -/
theorem squareOrder_two_mul_highNeighborCount_le_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) {x : V} (hx : G.degree x = d) :
    2 * (G.neighborFinset x ∩ squareOrderHighVertices G d).card ≤ d := by
  classical
  let S : Finset V :=
    G.neighborFinset x ∩ squareOrderHighVertices G d
  have hS_high : ∀ v ∈ S, G.degree v = d + 1 := by
    intro v hv
    exact (Finset.mem_filter.mp (Finset.mem_inter.mp hv).2).2
  have hS_adj : ∀ v ∈ S, G.Adj v x := by
    intro v hv
    have := (Finset.mem_inter.mp hv).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hpartner_card : ∀ v : {v // v ∈ S},
      (G.neighborFinset v.1 ∩ G.neighborFinset x).card = 1 := by
    intro v
    let xv : {z : V // z ∈ G.neighborSet v.1} :=
      ⟨x, hS_adj v.1 v.2⟩
    have hdeg :=
      (squareOrder_degree_succ_highRoot_structure
        G hfree hd hmin hcard (hS_high v.1 v.2)).2.2 xv
    rwa [degree_induce_neighborSet_eq_card_common] at hdeg
  let partner : {v // v ∈ S} → V := fun v =>
    ((Finset.card_pos.mp (by rw [hpartner_card v]; norm_num)).choose)
  have hpartner_mem : ∀ v : {v // v ∈ S},
      partner v ∈ G.neighborFinset v.1 ∩ G.neighborFinset x := by
    intro v
    exact (Finset.card_pos.mp
      (by rw [hpartner_card v]; norm_num)).choose_spec
  have hpartner_low : ∀ v : {v // v ∈ S},
      partner v ∉ squareOrderHighVertices G d := by
    intro v hvhigh
    have hpHigh : G.degree (partner v) = d + 1 :=
      (Finset.mem_filter.mp hvhigh).2
    have hvp : G.Adj v.1 (partner v) := by
      have := (Finset.mem_inter.mp (hpartner_mem v)).1
      simpa [SimpleGraph.mem_neighborFinset] using this
    exact squareOrder_not_adj_degree_succ_of_tightEdgeCover
      G hcover (hS_high v.1 v.2) hpHigh hvp
  have hpartner_injective : Function.Injective partner := by
    intro v w hp
    apply Subtype.ext
    by_contra hvw
    have hcommon := squareOrder_card_common_degree_succ_eq_one
      G hfree hd hmin hcover hcard
      (hS_high v.1 v.2) (hS_high w.1 w.2) hvw
    rcases Finset.card_eq_one.mp hcommon with ⟨q, hq⟩
    have hxmem : x ∈ G.neighborFinset v.1 ∩ G.neighborFinset w.1 := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hS_adj v.1 v.2, hS_adj w.1 w.2⟩
    have hpmem : partner v ∈
        G.neighborFinset v.1 ∩ G.neighborFinset w.1 := by
      simp only [Finset.mem_inter]
      have hvp := (Finset.mem_inter.mp (hpartner_mem v)).1
      have hwp := (Finset.mem_inter.mp (hpartner_mem w)).1
      rw [← hp] at hwp
      exact ⟨hvp, hwp⟩
    have hxq : x = q := by simpa [hq] using hxmem
    have hpq : partner v = q := by simpa [hq] using hpmem
    have hpx : partner v = x := hpq.trans hxq.symm
    have hpadj : G.Adj x (partner v) := by
      have := (Finset.mem_inter.mp (hpartner_mem v)).2
      simpa [SimpleGraph.mem_neighborFinset] using this
    exact G.loopless.irrefl x (hpx ▸ hpadj)
  let T : Finset V :=
    G.neighborFinset x \ squareOrderHighVertices G d
  let partnerLow : {v // v ∈ S} → {y // y ∈ T} := fun v =>
    ⟨partner v, by
      simp only [T, Finset.mem_sdiff]
      exact ⟨(Finset.mem_inter.mp (hpartner_mem v)).2,
        hpartner_low v⟩⟩
  have hpartnerLow_injective : Function.Injective partnerLow := by
    intro v w hp
    apply hpartner_injective
    exact congrArg Subtype.val hp
  have hST : S.card ≤ T.card := by
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
      partnerLow hpartnerLow_injective
  have hTcard : T.card = d - S.card := by
    dsimp [T]
    rw [Finset.card_sdiff, G.card_neighborFinset_eq_degree, hx]
    congr 1
    rw [Finset.inter_comm]
  rw [hTcard] at hST
  change 2 * S.card ≤ d
  omega

/-- The symbolic Cauchy constraint for the high-sector partial design.
Writing `h` for the number of high vertices, it says
`(d+1)^2 h^2 ≤ (d^2-h) h(h+d)`. -/
theorem squareOrder_high_incidence_cauchy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d) :
    let h := (squareOrderHighVertices G d).card
    ((d + 1) * h) * ((d + 1) * h) ≤
      (d * d - h) * (h * (h + d)) := by
  let H := squareOrderHighVertices G d
  let L := (Finset.univ : Finset V) \ H
  let k : V → ℕ := fun x => (G.neighborFinset x ∩ H).card
  have hfirstAll : (∑ x : V, k x) = (d + 1) * H.card := by
    simpa [H, k] using squareOrder_sum_highNeighborCount_eq G d
  have hsecondAll : (∑ x : V, k x * k x) = H.card * (H.card + d) := by
    simpa [H, k, pow_two] using
      squareOrder_sum_highNeighborCount_sq_eq
        G hfree hd hmin hcover hcard
  have hzero : ∀ x ∈ H, k x = 0 := by
    intro x hx
    exact squareOrder_highNeighborCount_eq_zero_of_high G hcover hx
  have hsplitFirst := Finset.sum_sdiff
    (show H ⊆ (Finset.univ : Finset V) by simp) (f := k)
  have hsplitSecond := Finset.sum_sdiff
    (show H ⊆ (Finset.univ : Finset V) by simp) (f := fun x => k x * k x)
  have hhighFirst : (∑ x ∈ H, k x) = 0 := Finset.sum_eq_zero hzero
  have hhighSecond : (∑ x ∈ H, k x * k x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hzero x hx]
    simp
  rw [hhighFirst, add_zero] at hsplitFirst
  rw [hhighSecond, add_zero] at hsplitSecond
  have hfirst : (∑ x ∈ L, k x) = (d + 1) * H.card := by
    simpa [L] using hsplitFirst.trans hfirstAll
  have hsecond : (∑ x ∈ L, k x * k x) = H.card * (H.card + d) := by
    simpa [L] using hsplitSecond.trans hsecondAll
  have hz := sq_sum_le_card_mul_sum_sq
    (s := L) (f := fun x => (k x : ℤ))
  have hcs : (∑ x ∈ L, k x) * (∑ x ∈ L, k x) ≤
      L.card * ∑ x ∈ L, k x * k x := by
    norm_num [pow_two] at hz
    exact_mod_cast hz
  have hLcard : L.card = d * d - H.card := by
    dsimp [L]
    rw [Finset.card_sdiff, Finset.card_univ, hcard]
    simp
  rw [hfirst, hsecond, hLcard] at hcs
  exact hcs

/-- After cancelling a nonempty high sector, Cauchy becomes the compact
polynomial restriction `h^2 + (3d+1)h ≤ d^3`. -/
theorem squareOrder_high_count_polynomial_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 2 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = d ∨ G.degree v = d)
    (hcard : Fintype.card V = d * d)
    (hpos : 0 < (squareOrderHighVertices G d).card) :
    let h := (squareOrderHighVertices G d).card
    h * h + (3 * d + 1) * h ≤ d * d * d := by
  let h := (squareOrderHighVertices G d).card
  have hcs := squareOrder_high_incidence_cauchy
    G hfree hd hmin hcover hcard
  dsimp only at hcs ⊢
  have hle : h ≤ d * d := by
    have := Finset.card_le_card
      (show squareOrderHighVertices G d ⊆ (Finset.univ : Finset V) by simp)
    simpa [h, hcard] using this
  have hcancel :
      (d + 1) * (d + 1) * h ≤ (d * d - h) * (h + d) := by
    have hmul :
        h * ((d + 1) * (d + 1) * h) ≤
          h * ((d * d - h) * (h + d)) := by
      convert hcs using 1 <;> ring
    exact Nat.le_of_mul_le_mul_left hmul hpos
  have hcomplement : d * d - h + h = d * d := Nat.sub_add_cancel hle
  nlinarith [hcancel, hcomplement]

end

end Erdos85
