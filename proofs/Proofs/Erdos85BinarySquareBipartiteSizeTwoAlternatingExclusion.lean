import Proofs.Erdos85BinarySquareRegularParity

/-!
# Bipartite size-two defect components are impossible

Let `G` be a `q`-regular `C₄`-free graph on `q²` vertices and `D` its
second-order defect graph, so `A² = (q-1)I + J - D` and `A` commutes with `D`.
Suppose the defect graph has a *size-two* component `c` (order `2q`) and no
other defect component of order exactly `q` (true in every stratum without a
size-one part: the two-component `[q-2, 2]` strata, `[q-4, 2, 2]`, …, and the
all-size-two stratum).  If `D[c]` is bipartite, then no such graph exists —
with **no hypothesis on the internal ambient factor of `c`**.

The proof is a short eigenvector argument.  Let `v = 1_X - 1_Y` (zero off
`c`), so `D v = -(q-1) v`, `Σ v = 0` and `A² v = 2(q-1) v`.  Every vertex of
`c` has exactly two ambient neighbours in `c`, so `(A v)(z) = ε(z) v(z)` on
`c` with `ε(z) ∈ {-2, 0, 2}` (both internal neighbours on the opposite side,
mixed, or both on the same side).  Commutation `D(Av) = A(Dv)` read on `c`
gives `Σ_{y ∈ D(z)} ε(y) = (q-1) ε(z)`, whose level sets are closed under
defect adjacency; since `c` is defect-connected, `ε ≡ λ` is constant.  Put
`w := A v - λ v`, supported off `c` with values in `{-2, 0, 2}` (each outside
vertex has exactly two neighbours in `c`).  Then `A w = (2(q-1) - λ²) v - λ w`
and `D w = -(q-1) w`.  For `λ = 0` the first identity is already impossible at
a vertex of `c` (`2(q-1) > 2(q-2)`).  For `λ = ±2` it forces some outside
neighbour `u₀` with `w = 0`; the second identity makes the zero fibre of `w`
closed under defect adjacency, so `w` vanishes on the whole defect component
`c₁` of `u₀`.  By the equitable law the base vertex has `|c₁|/q ≥ 2`
neighbours in `c₁`, so `|Σ w| ≤ 2(q-4)` over its outside neighbours — again
contradicting the first identity for `q ≥ 4`.

Everything is uniform in `q`; nothing is enumerated.  In the order-64
degree-eight campaign this kills the `[6,2]` stratum whenever the size-two
component is defect-bipartite (in particular the synchronized `K₈,₈ − PM`
model), in every colouring branch at once — alternating (`H ⊂ D`), all-in-
triangles, or mixed.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Adjacency-closed predicates propagate along reachability. -/
theorem reachable_induction_of_adj_closed {V : Type*} (D : SimpleGraph V)
    (P : V → Prop) (hP : ∀ x y, D.Adj x y → P x → P y) {u v : V}
    (h : D.Reachable u v) (hu : P u) : P v := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact hu
  | cons hadj _ ih => exact ih (hP _ _ hadj hu)

/-- **Bipartite size-two defect component: impossible whenever no other defect
component has order exactly `q`.**  No hypothesis on the internal ambient
factor is needed; see the module docstring for the argument.  The hypothesis
`hother` holds in every stratum without a size-one part — in particular in the
two-component `[q-2, 2]` strata and in the all-size-two stratum. -/
theorem binarySquare_regular_sizeTwoPart_bipartite_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hother : ∀ c' : (secondOrderDefectGraph G).ConnectedComponent,
      c' ≠ c → c'.supp.ncard ≠ q)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False := by
  have hq3 : 3 ≤ q := by omega
  -- membership in `c` as an equation of components
  have hmem : ∀ x, x ∈ c.supp ↔ (secondOrderDefectGraph G).connectedComponentMk x = c :=
    fun x => ConnectedComponent.mem_supp_iff c x
  -- defect degree is `q - 1`
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdeg : ∀ y : V, (secondOrderDefectGraph G).degree y = q - 1 := by
    intro y
    have h := secondOrderDefectGraph_degree_eq_excess_add_two G hfree hreg hcensus y
    change (secondOrderDefectGraph G).degree y = (q - 3) + 2 at h
    omega
  have hq1 : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]; simp
  have hDcard : ∀ y, ((secondOrderDefectGraph G).neighborFinset y).card = q - 1 := by
    intro y
    rw [(secondOrderDefectGraph G).card_neighborFinset_eq_degree, hDdeg]
  -- defect adjacency stays inside / outside `c`
  have hDin : ∀ x y, x ∈ c.supp → (secondOrderDefectGraph G).Adj x y → y ∈ c.supp := by
    intro x y hx hxy
    rw [hmem] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  have hDout : ∀ x y, x ∉ c.supp → (secondOrderDefectGraph G).Adj x y → y ∉ c.supp := by
    intro x y hx hxy hy
    exact hx (hDin y x hy hxy.symm)
  -- every vertex has exactly two ambient neighbours in `c`
  have htwo : ∀ x, ((G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).card = 2 := by
    intro x
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq3 hreg hcard ((secondOrderDefectGraph G).connectedComponentMk x) c
      (x := x) ((ConnectedComponent.mem_supp_iff _ x).mpr rfl)
    rw [hc] at h
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h
  -- the signed indicator of the bipartition, zero off `c`
  set s : V → ℤ := fun x =>
    if (secondOrderDefectGraph G).connectedComponentMk x = c then
      (if col x then 1 else -1) else 0 with hs
  have hs_in : ∀ x, x ∈ c.supp → s x = (if col x then 1 else -1) := by
    intro x hx
    simp only [hs, if_pos ((hmem x).mp hx)]
  have hs_out : ∀ x, x ∉ c.supp → s x = 0 := by
    intro x hx
    have : ¬ (secondOrderDefectGraph G).connectedComponentMk x = c :=
      fun h => hx ((hmem x).mpr h)
    simp only [hs, if_neg this]
  have hs_opp : ∀ x y, x ∈ c.supp → y ∈ c.supp → col x ≠ col y → s y = - s x := by
    intro x y hx hy hxy
    rw [hs_in x hx, hs_in y hy]
    cases hcx : col x <;> cases hcy : col y <;> simp_all
  have hs_sq : ∀ x, x ∈ c.supp → s x = 1 ∨ s x = -1 := by
    intro x hx
    rw [hs_in x hx]
    cases col x <;> simp
  have hs_mul_self : ∀ x, x ∈ c.supp → s x * s x = 1 := by
    intro x hx
    rcases hs_sq x hx with h | h <;> rw [h] <;> norm_num
  -- Step 1: `D s = -(q-1) s` pointwise
  have hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      -((q : ℤ) - 1) * s x := by
    intro x
    by_cases hx : x ∈ c.supp
    · have hall : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = - s x := by
        intro y hy
        have hxy : (secondOrderDefectGraph G).Adj x y :=
          ((secondOrderDefectGraph G).mem_neighborFinset x y).mp hy
        exact hs_opp x y hx (hDin x y hx hxy) (hbip x y hx (hDin x y hx hxy) hxy)
      rw [Finset.sum_congr rfl hall, Finset.sum_const, hDcard x, nsmul_eq_mul, hq1]
      ring
    · have hall : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y = 0 := by
        intro y hy
        exact hs_out y (hDout x y hx
          (((secondOrderDefectGraph G).mem_neighborFinset x y).mp hy))
      rw [Finset.sum_congr rfl hall, Finset.sum_const, smul_zero, hs_out x hx]
      ring
  -- Step 2: `a := A s`, and its restriction to the two internal neighbours
  set a : V → ℤ := fun x => ∑ y ∈ G.neighborFinset x, s y with ha
  have hAs_split : ∀ x, a x =
      ∑ y ∈ (G.neighborFinset x).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y := by
    intro x
    simp only [ha]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hy : (secondOrderDefectGraph G).connectedComponentMk y = c
    · simp [hy]
    · rw [if_neg hy, hs_out y (fun h => hy ((hmem y).mp h))]
  have ha_val : ∀ x, a x = -2 ∨ a x = 0 ∨ a x = 2 := by
    intro x
    rw [hAs_split x]
    obtain ⟨u, u', huu', hset⟩ := Finset.card_eq_two.mp (htwo x)
    rw [hset, Finset.sum_pair huu']
    have hu : u ∈ c.supp := by
      have : u ∈ (G.neighborFinset x).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) := by
        rw [hset]; simp
      exact (hmem u).mpr (Finset.mem_filter.mp this).2
    have hu' : u' ∈ c.supp := by
      have : u' ∈ (G.neighborFinset x).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) := by
        rw [hset]; simp
      exact (hmem u').mpr (Finset.mem_filter.mp this).2
    rcases hs_sq u hu with h1 | h1 <;> rcases hs_sq u' hu' with h2 | h2 <;>
      simp [h1, h2]
  -- Step 3: `Σ s = 0` (double count the defect degrees against `D s = -(q-1) s`)
  have hsum_zero : ∑ x, s x = 0 := by
    have hlhs : ∑ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
        ((q : ℤ) - 1) * ∑ x, s x := by
      have h1 : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
          ∑ y, ((secondOrderDefectGraph G).adjMatrix ℤ) x y * s y := by
        intro x
        rw [← SimpleGraph.adjMatrix_mulVec_apply]
        rfl
      simp_rw [h1]
      rw [Finset.sum_comm]
      have h2 : ∀ y, ∑ x, ((secondOrderDefectGraph G).adjMatrix ℤ) x y * s y =
          ((q : ℤ) - 1) * s y := by
        intro y
        rw [← Finset.sum_mul]
        have h3 : ∑ x, ((secondOrderDefectGraph G).adjMatrix ℤ) x y =
            ∑ x, ((secondOrderDefectGraph G).adjMatrix ℤ) y x := by
          apply Finset.sum_congr rfl
          intro x _
          simp [SimpleGraph.adjMatrix_apply, (secondOrderDefectGraph G).adj_comm]
        rw [h3]
        have h4 : ∑ x, ((secondOrderDefectGraph G).adjMatrix ℤ) y x =
            ((secondOrderDefectGraph G).degree y : ℤ) := by
          have := SimpleGraph.adjMatrix_mulVec_const_apply (α := ℤ)
            (G := secondOrderDefectGraph G) (a := 1) (v := y)
          simp only [Matrix.mulVec, dotProduct, Function.const_apply, mul_one] at this
          simpa using this
        rw [h4, hDdeg y, hq1]
      simp_rw [h2]
      rw [← Finset.mul_sum]
    have hrhs : ∑ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
        -((q : ℤ) - 1) * ∑ x, s x := by
      simp_rw [hDs]
      rw [← Finset.mul_sum]
    have hqne : ((q : ℤ) - 1) ≠ 0 := by
      have : (4 : ℤ) ≤ q := by exact_mod_cast hq
      omega
    have : 2 * ((q : ℤ) - 1) * ∑ x, s x = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exfalso; apply hqne; linarith
    · exact h
  -- Step 4: `A a = A² s = 2(q-1) s` pointwise
  have hAA : ∀ x, ∑ y ∈ G.neighborFinset x, a y = 2 * ((q : ℤ) - 1) * s x := by
    intro x
    have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg (d := q)
    have h1 : ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ s) x = ∑ y ∈ G.neighborFinset x, a y := by
      rw [← Matrix.mulVec_mulVec, SimpleGraph.adjMatrix_mulVec_apply]
      apply Finset.sum_congr rfl
      intro y _
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    have h2 : ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ s) x =
        ((q : ℤ) - 1) * s x + (∑ y, s y) -
          ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y := by
      rw [hsq, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [SimpleGraph.adjMatrix_mulVec_apply]
      congr 2
      simp [FriendshipTheoremOQ01.onesMatrix, Matrix.mulVec, dotProduct]
    rw [← h1, h2, hsum_zero, hDs x]
    ring
  -- Step 5: `D a = -(q-1) a` pointwise (commutation of `A` and `D`)
  have hDa : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, a y =
      -((q : ℤ) - 1) * a x := by
    intro x
    have hcomm := adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg (d := q)
    have h1 : (((secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ s) x =
        ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, a y := by
      rw [← Matrix.mulVec_mulVec, SimpleGraph.adjMatrix_mulVec_apply]
      apply Finset.sum_congr rfl
      intro y _
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    have h2 : ((G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ) *ᵥ s) x =
        ∑ y ∈ G.neighborFinset x, ∑ z ∈ (secondOrderDefectGraph G).neighborFinset y, s z := by
      rw [← Matrix.mulVec_mulVec, SimpleGraph.adjMatrix_mulVec_apply]
      apply Finset.sum_congr rfl
      intro y _
      rw [SimpleGraph.adjMatrix_mulVec_apply]
    have h12 : ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, a y =
        ∑ y ∈ G.neighborFinset x, ∑ z ∈ (secondOrderDefectGraph G).neighborFinset y, s z := by
      rw [← h1, ← h2, hcomm]
    rw [h12]
    simp_rw [hDs]
    rw [← Finset.mul_sum]
  -- Step 6: the side pattern `ε` of the internal factor is constant on `c`
  set e : V → ℤ := fun x => a x * s x with he
  have he_val : ∀ x, x ∈ c.supp → e x = -2 ∨ e x = 0 ∨ e x = 2 := by
    intro x hx
    simp only [he]
    rcases ha_val x with h | h | h <;> rcases hs_sq x hx with h' | h' <;>
      rw [h, h'] <;> norm_num
  have ha_eq : ∀ x, x ∈ c.supp → a x = e x * s x := by
    intro x hx
    simp only [he]
    rw [mul_assoc, hs_mul_self x hx, mul_one]
  have hrel : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, e y = ((q : ℤ) - 1) * e z := by
    intro z hz
    have h := hDa z
    have hall : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset z, a y = - s z * e y := by
      intro y hy
      have hxy : (secondOrderDefectGraph G).Adj z y :=
        ((secondOrderDefectGraph G).mem_neighborFinset z y).mp hy
      have hyc : y ∈ c.supp := hDin z y hz hxy
      rw [ha_eq y hyc, hs_opp z y hz hyc (hbip z y hz hyc hxy)]
      ring
    rw [Finset.sum_congr rfl hall, ← Finset.mul_sum, ha_eq z hz] at h
    rcases hs_sq z hz with hz1 | hz1 <;> rw [hz1] at h <;> linarith
  -- level sets of `e` are closed under defect adjacency inside `c`
  have hlevel : ∀ z y, z ∈ c.supp → (secondOrderDefectGraph G).Adj z y → e y = e z := by
    intro z y hz hzy
    have hyc : y ∈ c.supp := hDin z y hz hzy
    have hymem : y ∈ (secondOrderDefectGraph G).neighborFinset z :=
      ((secondOrderDefectGraph G).mem_neighborFinset z y).mpr hzy
    have hzmem : z ∈ (secondOrderDefectGraph G).neighborFinset y :=
      ((secondOrderDefectGraph G).mem_neighborFinset y z).mpr hzy.symm
    -- an extremal vertex forces all its defect neighbours to the same extreme
    have hpush : ∀ p r, p ∈ c.supp → r ∈ (secondOrderDefectGraph G).neighborFinset p →
        (e p = 2 → e r = 2) ∧ (e p = -2 → e r = -2) := by
      intro p r hp hr
      have hrc : r ∈ c.supp := hDin p r hp
        (((secondOrderDefectGraph G).mem_neighborFinset p r).mp hr)
      have hsum := hrel p hp
      constructor
      · intro hp2
        rw [hp2] at hsum
        have hnonneg : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset p, 0 ≤ 2 - e y := by
          intro y hy
          have hyc : y ∈ c.supp := hDin p y hp
            (((secondOrderDefectGraph G).mem_neighborFinset p y).mp hy)
          rcases he_val y hyc with h | h | h <;> rw [h] <;> norm_num
        have hle := Finset.single_le_sum hnonneg hr
        rw [Finset.sum_sub_distrib, Finset.sum_const, hDcard p, nsmul_eq_mul, hq1,
          hsum] at hle
        rcases he_val r hrc with h | h | h <;> rw [h] at hle ⊢ <;> linarith
      · intro hp2
        rw [hp2] at hsum
        have hnonneg : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset p, 0 ≤ e y + 2 := by
          intro y hy
          have hyc : y ∈ c.supp := hDin p y hp
            (((secondOrderDefectGraph G).mem_neighborFinset p y).mp hy)
          rcases he_val y hyc with h | h | h <;> rw [h] <;> norm_num
        have hle := Finset.single_le_sum hnonneg hr
        rw [Finset.sum_add_distrib, Finset.sum_const, hDcard p, nsmul_eq_mul, hq1,
          hsum] at hle
        rcases he_val r hrc with h | h | h <;> rw [h] at hle ⊢ <;> linarith
    rcases he_val z hz with h | h | h
    · rw [h]; exact (hpush z y hz hymem).2 h
    · rw [h]
      rcases he_val y hyc with h' | h' | h'
      · have := (hpush y z hyc hzmem).2 h'; rw [h] at this; norm_num at this
      · exact h'
      · have := (hpush y z hyc hzmem).1 h'; rw [h] at this; norm_num at this
    · rw [h]; exact (hpush z y hz hymem).1 h
  -- pick a base vertex of `c`; `λ := e z₀`
  have hne : c.supp.Nonempty := by
    rw [← Set.ncard_pos, hc]; omega
  obtain ⟨z₀, hz₀⟩ := hne
  set lam : ℤ := e z₀ with hlam
  have hlam_val : lam = -2 ∨ lam = 0 ∨ lam = 2 := he_val z₀ hz₀
  have hconst : ∀ z, z ∈ c.supp → e z = lam := by
    intro z hz
    have hreach : (secondOrderDefectGraph G).Reachable z₀ z :=
      ConnectedComponent.exact (((hmem z₀).mp hz₀).trans ((hmem z).mp hz).symm)
    have := reachable_induction_of_adj_closed (secondOrderDefectGraph G)
      (fun x => x ∈ c.supp ∧ e x = lam)
      (fun x y hxy hx => ⟨hDin x y hx.1 hxy, (hlevel x y hx.1 hxy).trans hx.2⟩)
      hreach ⟨hz₀, rfl⟩
    exact this.2
  -- Step 7: `w := a - λ s`
  set w : V → ℤ := fun x => a x - lam * s x with hw
  have hw_in : ∀ x, x ∈ c.supp → w x = 0 := by
    intro x hx
    simp only [hw]
    rw [ha_eq x hx, hconst x hx]
    ring
  have hw_val : ∀ x, w x = -2 ∨ w x = 0 ∨ w x = 2 := by
    intro x
    by_cases hx : x ∈ c.supp
    · exact Or.inr (Or.inl (hw_in x hx))
    · simp only [hw]
      rw [hs_out x hx, mul_zero, sub_zero]
      exact ha_val x
  -- `A w = (2(q-1) - λ²) s - λ w` pointwise
  have hAw : ∀ x, ∑ y ∈ G.neighborFinset x, w y =
      (2 * ((q : ℤ) - 1) - lam * lam) * s x - lam * w x := by
    intro x
    simp only [hw]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hAA x]
    have : ∑ y ∈ G.neighborFinset x, s y = a x := rfl
    rw [this]
    ring
  -- `D w = -(q-1) w` pointwise
  have hDw : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, w y =
      -((q : ℤ) - 1) * w x := by
    intro x
    simp only [hw]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hDa x, hDs x]
    ring
  -- Step 8: the zero fibre of `w` off `c` is closed under defect adjacency
  have hclosed : ∀ u u', u ∉ c.supp → w u = 0 →
      (secondOrderDefectGraph G).Adj u u' → w u' = 0 := by
    intro u u' hu hwu huu'
    have hu'mem : u ∈ (secondOrderDefectGraph G).neighborFinset u' :=
      ((secondOrderDefectGraph G).mem_neighborFinset u' u).mpr huu'.symm
    rcases hw_val u' with h | h | h
    · exfalso
      have hsum := hDw u'
      rw [h] at hsum
      have hnonneg : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset u', 0 ≤ 2 - w y := by
        intro y _
        rcases hw_val y with hy | hy | hy <;> rw [hy] <;> norm_num
      have hle := Finset.single_le_sum hnonneg hu'mem
      rw [hwu] at hle
      rw [Finset.sum_sub_distrib, Finset.sum_const, hDcard u', nsmul_eq_mul, hq1,
        hsum] at hle
      linarith
    · exact h
    · exfalso
      have hsum := hDw u'
      rw [h] at hsum
      have hnonneg : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset u', 0 ≤ w y + 2 := by
        intro y _
        rcases hw_val y with hy | hy | hy <;> rw [hy] <;> norm_num
      have hle := Finset.single_le_sum hnonneg hu'mem
      rw [hwu] at hle
      rw [Finset.sum_add_distrib, Finset.sum_const, hDcard u', nsmul_eq_mul, hq1,
        hsum] at hle
      linarith
  -- Step 9: read `A w` at the base vertex, over its outside neighbours
  have hzsum : ∑ y ∈ G.neighborFinset z₀, w y = (2 * ((q : ℤ) - 1) - lam * lam) * s z₀ := by
    rw [hAw z₀, hw_in z₀ hz₀]; ring
  set T := (G.neighborFinset z₀).filter
    (fun y => ¬ (secondOrderDefectGraph G).connectedComponentMk y = c) with hT
  have hTcard : T.card = q - 2 := by
    have h := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset z₀) (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)
    rw [htwo z₀, G.card_neighborFinset_eq_degree, hreg z₀] at h
    simp only [hT]
    omega
  have hq2 : ((q - 2 : ℕ) : ℤ) = (q : ℤ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ q)]; simp
  have hzsumT : ∑ y ∈ T, w y = (2 * ((q : ℤ) - 1) - lam * lam) * s z₀ := by
    rw [← hzsum]
    symm
    rw [← Finset.sum_filter_add_sum_filter_not (G.neighborFinset z₀)
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)]
    have hzero : ∑ y ∈ (G.neighborFinset z₀).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), w y = 0 := by
      apply Finset.sum_eq_zero
      intro y hy
      exact hw_in y ((hmem y).mpr (Finset.mem_filter.mp hy).2)
    rw [hzero, zero_add]
  -- crude bounds `|Σ_T w| ≤ 2 |T|`
  have hT_upper : ∑ y ∈ T, w y ≤ 2 * ((q : ℤ) - 2) := by
    have hnonneg : ∀ y ∈ T, 0 ≤ 2 - w y := by
      intro y _
      rcases hw_val y with hy | hy | hy <;> rw [hy] <;> norm_num
    have := Finset.sum_nonneg hnonneg
    rw [Finset.sum_sub_distrib, Finset.sum_const, hTcard, nsmul_eq_mul, hq2] at this
    linarith
  have hT_lower : -(2 * ((q : ℤ) - 2)) ≤ ∑ y ∈ T, w y := by
    have hnonneg : ∀ y ∈ T, 0 ≤ w y + 2 := by
      intro y _
      rcases hw_val y with hy | hy | hy <;> rw [hy] <;> norm_num
    have := Finset.sum_nonneg hnonneg
    rw [Finset.sum_add_distrib, Finset.sum_const, hTcard, nsmul_eq_mul, hq2] at this
    linarith
  have hq4 : (4 : ℤ) ≤ q := by exact_mod_cast hq
  -- `λ = 0` is immediately impossible; otherwise `λ² = 4`
  have hlam_sq : lam * lam = 4 := by
    rcases hlam_val with h | h | h
    · rw [h]; norm_num
    · exfalso
      rw [h] at hzsumT
      rcases hs_sq z₀ hz₀ with h' | h' <;> rw [h'] at hzsumT <;> linarith
    · rw [h]; norm_num
  rw [hlam_sq] at hzsumT
  -- some outside neighbour of `z₀` has `w = 0`
  have hexists : ∃ u ∈ T, w u = 0 := by
    by_contra hnone
    push Not at hnone
    have hdvd : (4 : ℤ) ∣ ∑ y ∈ T, (w y - 2) := by
      apply Finset.dvd_sum
      intro y hy
      rcases hw_val y with h | h | h
      · rw [h]; norm_num
      · exact absurd h (hnone y hy)
      · rw [h]; norm_num
    rw [Finset.sum_sub_distrib, Finset.sum_const, hTcard, nsmul_eq_mul, hzsumT, hq2] at hdvd
    rcases hs_sq z₀ hz₀ with h | h <;> rw [h] at hdvd <;> omega
  obtain ⟨u₀, hu₀T, hwu₀⟩ := hexists
  have hu₀ : u₀ ∉ c.supp := fun h => (Finset.mem_filter.mp hu₀T).2 ((hmem u₀).mp h)
  have hu₀N : u₀ ∈ G.neighborFinset z₀ := (Finset.mem_filter.mp hu₀T).1
  -- Step 10: `w` vanishes on the whole defect component `c₁` of `u₀`
  set c₁ := (secondOrderDefectGraph G).connectedComponentMk u₀ with hc₁
  have hc₁ne : c₁ ≠ c := fun h => hu₀ ((hmem u₀).mpr h)
  have hall₁ : ∀ u, (secondOrderDefectGraph G).connectedComponentMk u = c₁ → w u = 0 := by
    intro u hu
    have hreach : (secondOrderDefectGraph G).Reachable u₀ u :=
      ConnectedComponent.exact hu.symm
    have := reachable_induction_of_adj_closed (secondOrderDefectGraph G)
      (fun x => x ∉ c.supp ∧ w x = 0)
      (fun x y hxy hx => ⟨hDout x y hx.1 hxy, hclosed x y hx.1 hx.2 hxy⟩) hreach ⟨hu₀, hwu₀⟩
    exact this.2
  -- `z₀` has at least two neighbours in `c₁` (equitable law and `|c₁| ≠ q`)
  set T₁ := (G.neighborFinset z₀).filter
    (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c₁) with hT₁
  have hT₁card : 2 ≤ T₁.card := by
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq3 hreg hcard c c₁ (x := z₀) hz₀
    have hpos : 0 < T₁.card :=
      Finset.card_pos.mpr ⟨u₀, Finset.mem_filter.mpr ⟨hu₀N, rfl⟩⟩
    by_contra hlt
    have hone : T₁.card = 1 := by omega
    apply hother c₁ hc₁ne
    rw [← h]
    change q * T₁.card = q
    rw [hone, mul_one]
  have hT₁sub : T₁ ⊆ T := by
    intro y hy
    rw [Finset.mem_filter] at hy ⊢
    exact ⟨hy.1, fun hyc => hc₁ne (hy.2.symm.trans hyc)⟩
  have hsplit : ∑ y ∈ T \ T₁, w y + ∑ y ∈ T₁, w y = ∑ y ∈ T, w y :=
    Finset.sum_sdiff hT₁sub
  have hT₁zero : ∑ y ∈ T₁, w y = 0 :=
    Finset.sum_eq_zero (fun y hy => hall₁ y (Finset.mem_filter.mp hy).2)
  have hsdcard : (T \ T₁).card = T.card - T₁.card := Finset.card_sdiff_of_subset hT₁sub
  have hcast : ((T \ T₁).card : ℤ) ≤ (q : ℤ) - 4 := by
    rw [hsdcard, hTcard]
    omega
  have hup : ∑ y ∈ T \ T₁, w y ≤ 2 * ((T \ T₁).card : ℤ) := by
    have hle : ∀ y ∈ T \ T₁, w y ≤ 2 := by
      intro y _
      rcases hw_val y with hy | hy | hy <;> rw [hy] <;> norm_num
    have := Finset.sum_le_card_nsmul (T \ T₁) w 2 hle
    rw [nsmul_eq_mul] at this
    linarith
  have hlow : -(2 * ((T \ T₁).card : ℤ)) ≤ ∑ y ∈ T \ T₁, w y := by
    have hle : ∀ y ∈ T \ T₁, -2 ≤ w y := by
      intro y _
      rcases hw_val y with hy | hy | hy <;> rw [hy] <;> norm_num
    have := Finset.card_nsmul_le_sum (T \ T₁) w (-2) hle
    rw [nsmul_eq_mul] at this
    linarith
  rcases hs_sq z₀ hz₀ with h | h <;> rw [h] at hzsumT <;> linarith

/-- Connected-complement form: if the complement of `c` is defect-connected it
is a single component of order `q(q-2) ≠ q`, so `hother` holds. -/
theorem binarySquare_regular_sizeTwoPart_bipartite_connected_complement_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hrest : ∀ x y, x ∉ c.supp → y ∉ c.supp →
      (secondOrderDefectGraph G).Reachable x y)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False := by
  apply binarySquare_regular_sizeTwoPart_bipartite_false
    G hfree hq hreg hcard c hc _ col hbip
  intro c' hc' hcard'
  -- `c'.supp` is the complement of `c.supp`
  obtain ⟨x₀, hx₀⟩ := c'.exists_rep
  have hx₀c' : x₀ ∈ c'.supp := (ConnectedComponent.mem_supp_iff c' x₀).mpr hx₀
  have hx₀c : x₀ ∉ c.supp := fun h =>
    hc' (hx₀.symm.trans ((ConnectedComponent.mem_supp_iff c x₀).mp h))
  have hcompl : c'.supp = (c.supp)ᶜ := by
    ext y
    constructor
    · intro hy hyc
      exact hc' (((ConnectedComponent.mem_supp_iff c' y).mp hy).symm.trans
        ((ConnectedComponent.mem_supp_iff c y).mp hyc))
    · intro hy
      have hreach := hrest x₀ y hx₀c hy
      rw [ConnectedComponent.mem_supp_iff, ← hx₀]
      exact (ConnectedComponent.sound hreach).symm
  have hsum := Set.ncard_add_ncard_compl c.supp
  rw [← hcompl, hc, hcard', Nat.card_eq_fintype_card, hcard] at hsum
  -- `q * 2 + q = q * q` forces `q = 3`
  have : q * 3 = q * q := by linarith
  have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) this
  omega

/-- Two-component form: if the defect graph has exactly two components, the
complement of `c` is automatically defect-connected. -/
theorem binarySquare_regular_sizeTwoPart_bipartite_two_components_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hcount : Fintype.card (secondOrderDefectGraph G).ConnectedComponent = 2)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False := by
  apply binarySquare_regular_sizeTwoPart_bipartite_connected_complement_false
    G hfree hq hreg hcard c hc _ col hbip
  intro x y hx hy
  have hx' : (secondOrderDefectGraph G).connectedComponentMk x ≠ c := fun h =>
    hx ((ConnectedComponent.mem_supp_iff c x).mpr h)
  have hy' : (secondOrderDefectGraph G).connectedComponentMk y ≠ c := fun h =>
    hy ((ConnectedComponent.mem_supp_iff c y).mpr h)
  -- with exactly two components, the two components other than `c` coincide
  have hthree : ∀ a b : (secondOrderDefectGraph G).ConnectedComponent,
      a ≠ c → b ≠ c → a = b := by
    intro a b ha hb
    by_contra hab
    have hinj : Function.Injective (fun i : Fin 3 =>
        if i = 0 then c else if i = 1 then a else b) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have := Fintype.card_le_of_injective _ hinj
    rw [hcount, Fintype.card_fin] at this
    omega
  exact ConnectedComponent.exact (hthree _ _ hx' hy')

/-- All-size-two form: if every defect component has order `2q` (the
`[2,2,…,2]` stratum), no defect component is bipartite. -/
theorem binarySquare_regular_allSizeTwo_not_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, c.supp.ncard = q * 2)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False :=
  binarySquare_regular_sizeTwoPart_bipartite_false G hfree hq hreg hcard c (hsize c)
    (fun c' _ h => by rw [hsize c'] at h; omega) col hbip

/-! ### Specialisations kept for the outline ledger

The alternating (`H ⊂ D`) and `A[c] ⊆ D[c]` forms are now literal corollaries:
the internal-factor hypothesis is simply discarded. -/

/-- Alternating internal factor form (hypothesis now unused). -/
theorem binarySquare_regular_sizeTwoPart_bipartite_alternating_connected_complement_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hrest : ∀ x y, x ∉ c.supp → y ∉ c.supp →
      (secondOrderDefectGraph G).Reachable x y)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y)
    (_halt : ∀ x y, x ∈ c.supp → y ∈ c.supp → G.Adj x y → col x ≠ col y) :
    False :=
  binarySquare_regular_sizeTwoPart_bipartite_connected_complement_false
    G hfree hq hreg hcard c hc hrest col hbip

/-- The `A[c] ⊆ D[c]` (all internal edges triangle-free) form (hypothesis now
unused). -/
theorem binarySquare_regular_sizeTwoPart_bipartite_internal_subset_defect_connected_complement_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hrest : ∀ x y, x ∉ c.supp → y ∉ c.supp →
      (secondOrderDefectGraph G).Reachable x y)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y)
    (_hsub : ∀ x y, x ∈ c.supp → y ∈ c.supp → G.Adj x y →
      (secondOrderDefectGraph G).Adj x y) :
    False :=
  binarySquare_regular_sizeTwoPart_bipartite_connected_complement_false
    G hfree hq hreg hcard c hc hrest col hbip

/-- Two-component alternating form (internal-factor hypothesis now unused). -/
theorem binarySquare_regular_sizeTwoPart_bipartite_alternating_two_components_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 4 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hcount : Fintype.card (secondOrderDefectGraph G).ConnectedComponent = 2)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y)
    (_halt : ∀ x y, x ∈ c.supp → y ∈ c.supp → G.Adj x y → col x ≠ col y) :
    False :=
  binarySquare_regular_sizeTwoPart_bipartite_two_components_false
    G hfree hq hreg hcard c hc hcount col hbip

end

end Erdos85
