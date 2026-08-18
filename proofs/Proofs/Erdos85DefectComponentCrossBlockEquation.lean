import Proofs.Erdos85ExcessDefectRegular
import Proofs.Erdos85BinarySquareRegularParity

/-! # The exact adjacency equation across a defect-component cut

For a regular C4-free graph, distinct second-order defect components have
exactly one common ambient neighbor.  In block-matrix form, cutting at any
one defect component gives the exact equation `H B + B C = J`.  This is the
exterior coupling that is absent from purely local defect/owner calibrations.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Defect-cut cross-block equation.**  If `H` and `C` are the ambient
adjacency blocks inside and outside a second-order defect component and `B`
is the cross-incidence block, then every cross pair has exactly one common
neighbor, equivalently `H B + B C` is the all-ones matrix. -/
theorem binarySquare_regular_defectComponent_crossBlock_eq_ones
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let H := (G.induce c.supp).adjMatrix ℤ
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    H * B + B * C = fun _ _ ↦ (1 : ℤ) := by
  classical
  let D := secondOrderDefectGraph G
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let H := (G.induce c.supp).adjMatrix ℤ
  let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
  let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular
    G hfree hreg
  have hblock := congrArg
    (fun X ↦ X.toBlock p (fun x ↦ ¬p x)) hsq
  rw [Matrix.toBlock_mul_eq_add p p (fun x ↦ ¬p x)] at hblock
  have hA11 : (G.adjMatrix ℤ).toBlock p p = H := by
    ext i j
    simp [H, p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  have hA12 : (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x) = B := rfl
  have hA22 : (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x)
      (fun x ↦ ¬p x) = C := rfl
  have hright : (((q : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ).toBlock
          p (fun x ↦ ¬p x) = fun _ _ ↦ (1 : ℤ) := by
    ext i j
    have hij : i.1 ≠ j.1 := fun h ↦ j.2 (h ▸ i.2)
    have hD : ¬D.Adj i.1 j.1 := by
      intro hadj
      exact j.2 ((c.mem_supp_congr_adj hadj).mp i.2)
    change (((q : ℤ) - 1) * (if i.1 = j.1 then 1 else 0) + 1 -
      (if D.Adj i.1 j.1 then 1 else 0)) = 1
    simp [hij, hD]
  rw [hA11, hA12, hA22, hright] at hblock
  exact hblock

/-- **Normalized-component outside-return identity.**  If the cut component
has order `q*m`, then it has internal degree `m` and exterior degree `q-m`.
Returning the cross-block equation through `Bᵀ` therefore gives the exact
square identity `(BC)Bᵀ = (q-m)J - H(BBᵀ)`. -/
theorem binarySquare_regular_normalizedComponent_outsideReturn_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q m : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * m) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let H := (G.induce c.supp).adjMatrix ℤ
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    (B * C) * B.transpose =
      ((q - m : ℕ) : ℤ) • FriendshipTheoremOQ01.onesMatrix c.supp -
        H * (B * B.transpose) := by
  classical
  let D := secondOrderDefectGraph G
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let H := (G.induce c.supp).adjMatrix ℤ
  let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
  let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
  let JHO : Matrix {x // p x} {x // ¬p x} ℤ := fun _ _ ↦ 1
  let JHH := FriendshipTheoremOQ01.onesMatrix c.supp
  have hcross : H * B + B * C = JHO := by
    simpa [H, B, C, JHO, p] using
      binarySquare_regular_defectComponent_crossBlock_eq_ones
        G hfree hreg c
  have hout : ∀ u : c.supp,
      ((G.neighborFinset u.1).filter fun x ↦ x ∉ c.supp).card = q - m := by
    intro u
    have hu := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard c c (x := u.1)
        ((ConnectedComponent.mem_supp_iff c u.1).mp u.2)
    rw [hc] at hu
    have hsel : (componentNeighborFinset G D c u.1).card = m :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hu
    have hins : ((G.neighborFinset u.1).filter fun x ↦
        x ∈ c.supp).card = m := by
      have heq : (G.neighborFinset u.1).filter (fun x ↦ x ∈ c.supp) =
          componentNeighborFinset G D c u.1 := by
        ext y
        simp [componentNeighborFinset, D,
          SimpleGraph.ConnectedComponent.mem_supp_iff]
      rw [heq, hsel]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset u.1) (fun x ↦ x ∈ c.supp)
    rw [hins, G.card_neighborFinset_eq_degree, hreg u.1] at hsplit
    omega
  have hreturn : JHO * B.transpose =
      ((q - m : ℕ) : ℤ) • JHH := by
    ext i j
    let S : Finset {x // ¬p x} :=
      Finset.univ.filter fun x ↦ G.Adj x.1 j.1
    let ι : {x // ¬p x} ↪ V :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hmap : S.map ι =
        (G.neighborFinset j.1).filter fun x ↦ x ∉ c.supp := by
      ext x
      simp [S, ι, p, G.adj_comm,
        SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hScard : S.card = q - m := by
      rw [← Finset.card_map ι, hmap, hout j]
    simp only [Matrix.mul_apply, JHO, JHH, B,
      FriendshipTheoremOQ01.onesMatrix, Matrix.transpose_apply,
      Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    calc
      (∑ x : {x // ¬p x}, 1 * if G.Adj j.1 x.1 then 1 else 0) =
          ∑ x : {x // ¬p x}, if G.Adj x.1 j.1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _hx
        simp [G.adj_comm]
      _ = (S.card : ℤ) := by simp [S]
      _ = (q - m : ℕ) := by rw [hScard]
      _ = (q - m : ℕ) * 1 := by ring
  have hBC : B * C = JHO - H * B := eq_sub_of_add_eq' hcross
  change (B * C) * B.transpose =
    ((q - m : ℕ) : ℤ) • JHH - H * (B * B.transpose)
  rw [hBC, Matrix.sub_mul, hreturn, Matrix.mul_assoc]

/-- Pointwise budget form of the normalized outside-return identity.  Every
entry of `H(BBᵀ)` is completed to the exterior degree `q-m` by a natural
number counting three-step paths that leave the component, take one exterior
edge, and return. -/
theorem binarySquare_regular_normalizedComponent_outsideReturn_entry_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q m : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * m) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let H := (G.induce c.supp).adjMatrix ℤ
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    ∀ u v : c.supp, ∃ n : ℕ,
      (H * (B * B.transpose)) u v + (n : ℤ) = (q - m : ℕ) := by
  classical
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let H := (G.induce c.supp).adjMatrix ℤ
  let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
  let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
  have hid := binarySquare_regular_normalizedComponent_outsideReturn_eq
    G hfree hq hreg hcard c hc
  change ∀ u v : c.supp, ∃ n : ℕ,
    (H * (B * B.transpose)) u v + (n : ℤ) = (q - m : ℕ)
  intro u v
  let M := (B * C) * B.transpose
  have hnon : 0 ≤ M u v := by
    dsimp only [M]
    rw [Matrix.mul_apply]
    apply Finset.sum_nonneg
    intro z _hz
    apply mul_nonneg
    · rw [Matrix.mul_apply]
      apply Finset.sum_nonneg
      intro y _hy
      simp only [B, C, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
      split_ifs <;> norm_num
    · simp only [B, Matrix.toBlock_apply, Matrix.transpose_apply,
        SimpleGraph.adjMatrix_apply]
      split_ifs <;> norm_num
  refine ⟨Int.toNat (M u v), ?_⟩
  have hnat : ((Int.toNat (M u v) : ℕ) : ℤ) = M u v :=
    Int.toNat_of_nonneg hnon
  have hid' : M = ((q - m : ℕ) : ℤ) •
      FriendshipTheoremOQ01.onesMatrix c.supp -
        H * (B * B.transpose) := by
    simpa [M, H, B, C, p] using hid
  have huv := congr_fun₂ hid' u v
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply, mul_one] at huv
  rw [hnat]
  omega

/-- An internal ambient edge already consumes the entire exterior-return
budget.  Equivalently, if `u` and `v` are adjacent inside a normalized defect
component, then the `(u,v)` entry of `H(BBᵀ)` is exactly the exterior degree
`q-m`; consequently the exterior three-step return entry is zero. -/
theorem binarySquare_regular_normalizedComponent_internalAdj_gram_saturates
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q m : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * m) (u v : c.supp)
    (huv : (G.induce c.supp).Adj u v) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let H := (G.induce c.supp).adjMatrix ℤ
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    (H * (B * B.transpose)) u v = (q - m : ℕ) := by
  classical
  let D := secondOrderDefectGraph G
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let H := (G.induce c.supp).adjMatrix ℤ
  let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
  have hsel := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
    G hfree hq hreg hcard c c (x := v.1)
      ((ConnectedComponent.mem_supp_iff c v.1).mp v.2)
  rw [hc] at hsel
  have hin : (componentNeighborFinset G D c v.1).card = m :=
    Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hsel
  have hout : ((G.neighborFinset v.1).filter fun x ↦
      x ∉ c.supp).card = q - m := by
    have hins : ((G.neighborFinset v.1).filter fun x ↦
        x ∈ c.supp).card = m := by
      have heq : (G.neighborFinset v.1).filter (fun x ↦ x ∈ c.supp) =
          componentNeighborFinset G D c v.1 := by
        ext y
        simp [componentNeighborFinset, D,
          SimpleGraph.ConnectedComponent.mem_supp_iff]
      rw [heq, hin]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset v.1) (fun x ↦ x ∈ c.supp)
    rw [hins, G.card_neighborFinset_eq_degree, hreg v.1] at hsplit
    omega
  let S : Finset {x // ¬p x} :=
    Finset.univ.filter fun x ↦ G.Adj v.1 x.1
  let ι : {x // ¬p x} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : S.map ι =
      (G.neighborFinset v.1).filter fun x ↦ x ∉ c.supp := by
    ext x
    simp [S, ι, p, SimpleGraph.mem_neighborFinset]
  have hScard : S.card = q - m := by
    rw [← Finset.card_map ι, hmap, hout]
  have hQdiag : (B * B.transpose) v v = (q - m : ℕ) := by
    rw [Matrix.mul_apply]
    simp only [B, Matrix.transpose_apply, Matrix.toBlock_apply,
      SimpleGraph.adjMatrix_apply]
    calc
      (∑ y : {x // ¬p x},
          (if G.Adj v.1 y.1 then 1 else 0) *
            if G.Adj v.1 y.1 then 1 else 0) =
          ∑ y : {x // ¬p x}, if G.Adj v.1 y.1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y _hy
        split_ifs <;> norm_num
      _ = (S.card : ℤ) := by simp [S]
      _ = (((G.neighborFinset v.1).filter fun x ↦
          x ∉ c.supp).card : ℤ) := by
        exact_mod_cast hScard.trans hout.symm
      _ = (q - m : ℕ) := by rw [hout]
  have hQnonneg (z : c.supp) : 0 ≤ (B * B.transpose) z v := by
    rw [Matrix.mul_apply]
    apply Finset.sum_nonneg
    intro y _hy
    simp only [B, Matrix.transpose_apply, Matrix.toBlock_apply,
      SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hlower : ((q - m : ℕ) : ℤ) ≤
      (H * (B * B.transpose)) u v := by
    rw [Matrix.mul_apply]
    calc
      ((q - m : ℕ) : ℤ) =
          H u v * (B * B.transpose) v v := by
        change G.Adj u.1 v.1 at huv
        simp [H, SimpleGraph.adjMatrix_apply, huv, hQdiag]
      _ ≤ ∑ z : c.supp, H u z * (B * B.transpose) z v := by
        apply Finset.single_le_sum
          (f := fun z ↦ H u z * (B * B.transpose) z v)
          (fun z _hz ↦ ?_) (Finset.mem_univ v)
        have hHnonneg : 0 ≤ H u z := by
          simp only [H, SimpleGraph.adjMatrix_apply]
          split_ifs <;> norm_num
        exact mul_nonneg hHnonneg (hQnonneg z)
  obtain ⟨n, hbudget⟩ :=
    binarySquare_regular_normalizedComponent_outsideReturn_entry_budget
      G hfree hq hreg hcard c hc u v
  change (H * (B * B.transpose)) u v = (q - m : ℕ)
  change (H * (B * B.transpose)) u v + (n : ℤ) =
    (q - m : ℕ) at hbudget
  omega

/-- Matrix form of the no-exterior-service consequence: an internal edge has
no three-step return that leaves the component, takes an exterior edge, and
comes back to the other endpoint. -/
theorem binarySquare_regular_normalizedComponent_internalAdj_outsideReturn_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q m : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * m) (u v : c.supp)
    (huv : (G.induce c.supp).Adj u v) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    ((B * C) * B.transpose) u v = 0 := by
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let H := (G.induce c.supp).adjMatrix ℤ
  let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
  let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
  have hid := binarySquare_regular_normalizedComponent_outsideReturn_eq
    G hfree hq hreg hcard c hc
  have hsat :=
    binarySquare_regular_normalizedComponent_internalAdj_gram_saturates
      G hfree hq hreg hcard c hc u v huv
  change ((B * C) * B.transpose) u v = 0
  have hid' : (B * C) * B.transpose =
      ((q - m : ℕ) : ℤ) • FriendshipTheoremOQ01.onesMatrix c.supp -
        H * (B * B.transpose) := by
    simpa [H, B, C, p] using hid
  have huvId := congr_fun₂ hid' u v
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply, mul_one] at huvId
  change (H * (B * B.transpose)) u v = (q - m : ℕ) at hsat
  rw [huvId, hsat]
  simp

/-- **Second-order exterior routing identity.**  Iterating `HB + BC = J`
once and using the internal/exterior row degrees gives
`BC² = ((q-m)-m)J + H²B`.  For the order-64 `[6,2]` small component this is
the concrete equation `BC² = 4J + H²B`; when `C` is C4-free its off-diagonal
square entries are Boolean, turning the identity into an exact distance-two
incidence ledger. -/
theorem binarySquare_regular_normalizedComponent_crossBlock_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q m : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * m) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let H := (G.induce c.supp).adjMatrix ℤ
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    let J : Matrix {x // p x} {x // ¬p x} ℤ := fun _ _ ↦ 1
    B * (C * C) =
      (((q - m : ℕ) : ℤ) - (m : ℤ)) • J + (H * H) * B := by
  classical
  let D := secondOrderDefectGraph G
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let H := (G.induce c.supp).adjMatrix ℤ
  let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
  let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
  let J : Matrix {x // p x} {x // ¬p x} ℤ := fun _ _ ↦ 1
  have hcross : H * B + B * C = J := by
    simpa [H, B, C, J, p] using
      binarySquare_regular_defectComponent_crossBlock_eq_ones
        G hfree hreg c
  have hinternal : ∀ u : c.supp,
      ((G.neighborFinset u.1).filter fun x ↦ x ∈ c.supp).card = m := by
    intro u
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard c c (x := u.1)
        ((ConnectedComponent.mem_supp_iff c u.1).mp u.2)
    rw [hc] at hmul
    have hsel : (componentNeighborFinset G D c u.1).card = m :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
    have heq : (G.neighborFinset u.1).filter (fun x ↦ x ∈ c.supp) =
        componentNeighborFinset G D c u.1 := by
      ext y
      simp [componentNeighborFinset, D,
        SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [heq, hsel]
  have hexternal : ∀ z : {x // ¬p x},
      ((G.neighborFinset z.1).filter fun x ↦ x ∉ c.supp).card = q - m := by
    intro z
    let source := D.connectedComponentMk z.1
    have hzsource : D.connectedComponentMk z.1 = source := rfl
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard source c (x := z.1) hzsource
    rw [hc] at hmul
    have hsel : (componentNeighborFinset G D c z.1).card = m :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
    have hins : ((G.neighborFinset z.1).filter fun x ↦
        x ∈ c.supp).card = m := by
      have heq : (G.neighborFinset z.1).filter (fun x ↦ x ∈ c.supp) =
          componentNeighborFinset G D c z.1 := by
        ext y
        simp [componentNeighborFinset, D,
          SimpleGraph.ConnectedComponent.mem_supp_iff]
      rw [heq, hsel]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset z.1) (fun x ↦ x ∈ c.supp)
    rw [hins, G.card_neighborFinset_eq_degree, hreg z.1] at hsplit
    omega
  have hHJ : H * J = (m : ℤ) • J := by
    ext u z
    rw [Matrix.mul_apply]
    simp only [J, mul_one, Matrix.smul_apply, smul_eq_mul]
    have hsum : (∑ y : c.supp, H u y) = (m : ℤ) := by
      simp only [H, SimpleGraph.adjMatrix_apply]
      let T : Finset c.supp :=
        Finset.univ.filter fun y ↦ G.Adj u.1 y.1
      let ι : c.supp ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
      have hmap : T.map ι =
          (G.neighborFinset u.1).filter fun x ↦ x ∈ c.supp := by
        ext x
        simp [T, ι, SimpleGraph.mem_neighborFinset]
      have hTcard : T.card = m := by
        rw [← Finset.card_map ι, hmap, hinternal u]
      rw [Finset.sum_boole]
      simpa [T] using congrArg (fun n : ℕ ↦ (n : ℤ)) hTcard
    rw [hsum]
  have hJC : J * C = ((q - m : ℕ) : ℤ) • J := by
    ext u z
    rw [Matrix.mul_apply]
    simp only [J, one_mul, Matrix.smul_apply, smul_eq_mul]
    let S : Finset {x // ¬p x} :=
      Finset.univ.filter fun x ↦ G.Adj x.1 z.1
    let ι : {x // ¬p x} ↪ V :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hmap : S.map ι =
        (G.neighborFinset z.1).filter fun x ↦ x ∉ c.supp := by
      ext x
      simp [S, ι, p, G.adj_comm,
        SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hScard : S.card = q - m := by
      rw [← Finset.card_map ι, hmap, hexternal z]
    have hsum : (∑ y : {x // ¬p x}, C y z) = ((q - m : ℕ) : ℤ) := by
      simp only [C, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
      rw [Finset.sum_boole]
      simpa [S, G.adj_comm] using congrArg (fun n : ℕ ↦ (n : ℤ)) hScard
    rw [hsum]
    simp
  have hBC : B * C = J - H * B := eq_sub_of_add_eq' hcross
  calc
    B * (C * C) = (B * C) * C := by rw [Matrix.mul_assoc]
    _ = (J - H * B) * C := by rw [hBC]
    _ = J * C - H * (B * C) := by
      rw [Matrix.sub_mul, Matrix.mul_assoc]
    _ = ((q - m : ℕ) : ℤ) • J - H * (J - H * B) := by
      rw [hJC, hBC]
    _ = ((q - m : ℕ) : ℤ) • J - (H * J - (H * H) * B) := by
      rw [Matrix.mul_sub, Matrix.mul_assoc]
    _ = ((q - m : ℕ) : ℤ) • J -
        ((m : ℤ) • J - (H * H) * B) := by rw [hHJ]
    _ = (((q - m : ℕ) : ℤ) - (m : ℤ)) • J + (H * H) * B := by
      module

/-- Order-64 normalized-size-two specialization of the second-order routing
identity. -/
theorem orderSixtyFour_sizeTwoComponent_crossBlock_sq
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) :
    let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
    let H := (G.induce c.supp).adjMatrix ℤ
    let B := (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x)
    let C := (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    let J : Matrix {x // p x} {x // ¬p x} ℤ := fun _ _ ↦ 1
    B * (C * C) = (4 : ℤ) • J + (H * H) * B := by
  have h := binarySquare_regular_normalizedComponent_crossBlock_sq
    G hfree (q := 8) (m := 2) (by norm_num) hreg (by norm_num) c hc
  norm_num at h
  exact h

end

#print axioms Erdos85.binarySquare_regular_defectComponent_crossBlock_eq_ones
#print axioms Erdos85.binarySquare_regular_normalizedComponent_outsideReturn_eq
#print axioms
  Erdos85.binarySquare_regular_normalizedComponent_outsideReturn_entry_budget
#print axioms
  Erdos85.binarySquare_regular_normalizedComponent_internalAdj_gram_saturates
#print axioms
  Erdos85.binarySquare_regular_normalizedComponent_internalAdj_outsideReturn_zero
#print axioms Erdos85.binarySquare_regular_normalizedComponent_crossBlock_sq
#print axioms Erdos85.orderSixtyFour_sizeTwoComponent_crossBlock_sq

end Erdos85
