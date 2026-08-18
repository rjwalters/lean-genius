import Proofs.Erdos85BinarySquareRegularParity

/-!
# The signed-vector residue of a bipartite defect component (any size)

Let `G` be a `q`-regular `C₄`-free graph on `q²` vertices, `D` its second-order
defect graph (`A² = (q-1)I + J - D`, `AD = DA`, `D` is `(q-1)`-regular), and
`c` a defect component of order `m·q` whose induced defect graph is bipartite
with classes `X, Y`.  Write `s = 1_X - 1_Y` (zero off `c`).

We prove, uniformly in `q` and `m`, that the whole ambient interaction of `c`
is governed by two integers:

* a constant `λ` (`|λ| ≤ m`, `λ ≡ m (mod 2)`) with `A s = λ s` on `c` — the
  *side pattern* of the internal `m`-factor is the same at every vertex
  (`λ = #same-side − #opposite` internal neighbours);
* the vector `w := A s − λ s`, supported off `c`, with `|w| ≤ m`,
  `w ≡ m (mod 2)`, which **alternates along every defect edge off `c`**
  (`w y = −w x`), so `|w|` is constant on every other defect component and
  every other component meeting the support of `w` is itself bipartite;
* the row identity at every vertex `z` of `c`:
  `Σ_{y ∼ z} w y = (2(q−1) − λ²) · s z`.

Both structural facts are instances of one energy identity: if
`Σ_{y ∼ x} f y = σ k f x` on an adjacency-closed set of degree-`k` vertices
(`σ = ±1`), then `Σ_x Σ_{y ∼ x} (f y − σ f x)² = 0`, so `f y = σ f x` on every
edge.  Applied to `ε = (A s)·s` on `c` (`σ = +1`) it gives `λ`; applied to `w`
off `c` (`σ = −1`) it gives the alternation.

Consumers are per-stratum arithmetic: `Σ_{y ∼ z} w y` runs over the
`|c_i|/q` neighbours of `z` in each other component `c_i`, each contributing
`± t_i` with `t_i ≡ m (mod 2)`, `t_i ≤ m`.  For `m = 2` this recovers
`Erdos85BinarySquareBipartiteSizeTwoAlternatingExclusion`; the one-component
case (`c = V`) is killed here whenever `2(q-1)` is not a perfect square.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Double counting over an adjacency-closed set of degree-`k` vertices:
`Σ_{x ∈ S} Σ_{y ∼ x} g y = k · Σ_{y ∈ S} g y`. -/
theorem sum_sum_neighborFinset_eq_card_mul_sum_of_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V)
    (hclosed : ∀ x ∈ S, ∀ y, D.Adj x y → y ∈ S) {k : ℕ}
    (hdeg : ∀ x ∈ S, (D.neighborFinset x).card = k) (g : V → ℤ) :
    ∑ x ∈ S, ∑ y ∈ D.neighborFinset x, g y = ∑ y ∈ S, (k : ℤ) * g y := by
  have hnb : ∀ x ∈ S, D.neighborFinset x = S.filter (fun y => D.Adj x y) := by
    intro x hx
    ext y
    simp only [mem_neighborFinset, Finset.mem_filter]
    exact ⟨fun h => ⟨hclosed x hx y h, h⟩, fun h => h.2⟩
  calc
    ∑ x ∈ S, ∑ y ∈ D.neighborFinset x, g y
        = ∑ x ∈ S, ∑ y ∈ S, if D.Adj x y then g y else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [hnb x hx, Finset.sum_filter]
    _ = ∑ y ∈ S, ∑ x ∈ S, if D.Adj x y then g y else 0 := Finset.sum_comm
    _ = ∑ y ∈ S, (k : ℤ) * g y := by
          apply Finset.sum_congr rfl
          intro y hy
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          congr 1
          have : S.filter (fun x => D.Adj x y) = D.neighborFinset y := by
            ext x
            simp only [Finset.mem_filter, mem_neighborFinset]
            exact ⟨fun h => h.2.symm, fun h => ⟨hclosed y hy x h, h.symm⟩⟩
          rw [this, hdeg y hy]

/-- **Energy identity.**  On an adjacency-closed set of degree-`k` vertices,
an integer function with `Σ_{y ∼ x} f y = σ k f x` (`σ² = 1`) satisfies
`f y = σ f x` along every edge. -/
theorem eq_mul_of_adj_of_sum_neighborFinset_eq_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V)
    (hclosed : ∀ x ∈ S, ∀ y, D.Adj x y → y ∈ S) {k : ℕ}
    (hdeg : ∀ x ∈ S, (D.neighborFinset x).card = k)
    (f : V → ℤ) (σ : ℤ) (hσ : σ * σ = 1)
    (hharm : ∀ x ∈ S, ∑ y ∈ D.neighborFinset x, f y = σ * ((k : ℤ) * f x)) :
    ∀ x ∈ S, ∀ y, D.Adj x y → f y = σ * f x := by
  have hE : ∑ x ∈ S, ∑ y ∈ D.neighborFinset x, (f y - σ * f x) ^ 2 = 0 := by
    have hexp : ∀ x ∈ S, ∑ y ∈ D.neighborFinset x, (f y - σ * f x) ^ 2 =
        (∑ y ∈ D.neighborFinset x, f y ^ 2) - 2 * σ * f x * (∑ y ∈ D.neighborFinset x, f y)
          + (k : ℤ) * f x ^ 2 := by
      intro x hx
      have h1 : ∀ y, (f y - σ * f x) ^ 2 = f y ^ 2 - 2 * σ * f x * f y + f x ^ 2 := by
        intro y
        have : (f y - σ * f x) ^ 2 = f y ^ 2 - 2 * σ * f x * f y + (σ * σ) * f x ^ 2 := by ring
        rw [this, hσ, one_mul]
      simp_rw [h1]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        Finset.sum_const, hdeg x hx, nsmul_eq_mul]
    rw [Finset.sum_congr rfl hexp]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [sum_sum_neighborFinset_eq_card_mul_sum_of_closed D S hclosed hdeg (fun y => f y ^ 2)]
    have h2 : ∑ x ∈ S, 2 * σ * f x * (∑ y ∈ D.neighborFinset x, f y) =
        ∑ x ∈ S, 2 * (k : ℤ) * f x ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [hharm x hx]
      have : 2 * σ * f x * (σ * ((k : ℤ) * f x)) = 2 * (σ * σ) * (k : ℤ) * f x ^ 2 := by ring
      rw [this, hσ]; ring
    rw [h2, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro x _
    ring
  intro x hx y hxy
  have hnonneg : ∀ x ∈ S, 0 ≤ ∑ y ∈ D.neighborFinset x, (f y - σ * f x) ^ 2 :=
    fun x _ => Finset.sum_nonneg (fun y _ => sq_nonneg _)
  have hx0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hE x hx
  have hy0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg (f y - σ * f x))).mp hx0
    y ((D.mem_neighborFinset x y).mpr hxy)
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy0
  linarith

/-- The signed indicator `1_X − 1_Y` of a two-colouring of a defect component,
zero off the component. -/
def bipartiteSignVector {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (col : V → Bool) (x : V) : ℤ :=
  if (secondOrderDefectGraph G).connectedComponentMk x = c then
    (if col x then 1 else -1) else 0

/-- **Signed-vector residue of a bipartite defect component of order `m·q`.**
See the module docstring. -/
theorem binarySquare_regular_bipartite_defectComponent_signed_residue
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m : ℕ}
    (hc : c.supp.ncard = q * m)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    ∃ (lam : ℤ) (w : V → ℤ),
      Even (lam + m) ∧ |lam| ≤ m ∧
      (∀ z ∈ c.supp, ∑ y ∈ G.neighborFinset z, bipartiteSignVector G c col y =
        lam * bipartiteSignVector G c col z) ∧
      (∀ x ∈ c.supp, w x = 0) ∧
      (∀ x, x ∉ c.supp → w x = ∑ y ∈ G.neighborFinset x, bipartiteSignVector G c col y) ∧
      (∀ x, x ∉ c.supp → Even (w x + m) ∧ |w x| ≤ m) ∧
      (∀ x y, x ∉ c.supp → (secondOrderDefectGraph G).Adj x y → w y = -w x) ∧
      (∀ z ∈ c.supp, ∑ y ∈ G.neighborFinset z, w y =
        (2 * ((q : ℤ) - 1) - lam * lam) * bipartiteSignVector G c col z) := by
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
  -- every vertex has exactly `m` ambient neighbours in `c`
  have hm : ∀ x, ((G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).card = m := by
    intro x
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard ((secondOrderDefectGraph G).connectedComponentMk x) c
      (x := x) ((ConnectedComponent.mem_supp_iff _ x).mpr rfl)
    rw [hc] at h
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) h
  -- the signed indicator
  set s : V → ℤ := bipartiteSignVector G c col with hs
  have hs_in : ∀ x, x ∈ c.supp → s x = (if col x then 1 else -1) := by
    intro x hx
    simp only [hs, bipartiteSignVector, if_pos ((hmem x).mp hx)]
  have hs_out : ∀ x, x ∉ c.supp → s x = 0 := by
    intro x hx
    have : ¬ (secondOrderDefectGraph G).connectedComponentMk x = c :=
      fun h => hx ((hmem x).mpr h)
    simp only [hs, bipartiteSignVector, if_neg this]
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
  have hs_abs : ∀ x, |s x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ c.supp
    · rcases hs_sq x hx with h | h <;> rw [h] <;> norm_num
    · rw [hs_out x hx]; norm_num
  have hs_even : ∀ x, x ∈ c.supp → Even (s x - 1) := by
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
  -- Step 2: `a := A s`; it is a signed count over the `m` internal neighbours
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
  have ha_bound : ∀ x, |a x| ≤ m := by
    intro x
    rw [hAs_split x]
    calc
      |∑ y ∈ (G.neighborFinset x).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y|
          ≤ ∑ y ∈ (G.neighborFinset x).filter
              (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), |s y| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y ∈ (G.neighborFinset x).filter
              (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), (1 : ℤ) :=
            Finset.sum_le_sum (fun y _ => hs_abs y)
      _ = m := by rw [Finset.sum_const, hm x]; simp
  have ha_even : ∀ x, Even (a x + m) := by
    intro x
    rw [hAs_split x]
    have h1 : ∑ y ∈ (G.neighborFinset x).filter
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), s y + (m : ℤ) =
        ∑ y ∈ (G.neighborFinset x).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c), (s y - 1) +
          2 * (m : ℤ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, hm x]
      simp; ring
    rw [h1]
    apply Even.add _ (even_two_mul _)
    apply Finset.even_sum
    intro y hy
    exact hs_even y ((hmem y).mpr (Finset.mem_filter.mp hy).2)
  -- Step 3: `Σ s = 0`
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
      have : (3 : ℤ) ≤ q := by exact_mod_cast hq
      omega
    have : 2 * ((q : ℤ) - 1) * ∑ x, s x = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exfalso; apply hqne; linarith
    · exact h
  -- Step 4: `A a = 2(q-1) s`
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
  -- Step 5: `D a = -(q-1) a`
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
  -- Step 6: the side pattern `ε = a·s` is `(q-1)`-harmonic on `c`, hence constant
  set e : V → ℤ := fun x => a x * s x with he
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
  set Sc : Finset V := Finset.univ.filter
    (fun x => (secondOrderDefectGraph G).connectedComponentMk x = c) with hSc
  have hSc_mem : ∀ x, x ∈ Sc ↔ x ∈ c.supp := by
    intro x
    simp only [hSc, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hmem x).symm
  have hSc_closed : ∀ x ∈ Sc, ∀ y, (secondOrderDefectGraph G).Adj x y → y ∈ Sc := by
    intro x hx y hxy
    exact (hSc_mem y).mpr (hDin x y ((hSc_mem x).mp hx) hxy)
  have hlevel := eq_mul_of_adj_of_sum_neighborFinset_eq_mul (secondOrderDefectGraph G) Sc
    hSc_closed (k := q - 1) (fun x _ => hDcard x) e 1 (by norm_num)
    (fun x hx => by rw [hrel x ((hSc_mem x).mp hx), hq1, one_mul])
  -- pick a base vertex; `λ := e z₀`
  have hne : c.supp.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have h0 : c.supp.ncard = 0 := by rw [hempty, Set.ncard_empty]
    -- a connected component is nonempty
    obtain ⟨x₀, hx₀⟩ := c.exists_rep
    have : x₀ ∈ c.supp := (ConnectedComponent.mem_supp_iff c x₀).mpr hx₀
    rw [hempty] at this
    exact this
  obtain ⟨z₀, hz₀⟩ := hne
  set lam : ℤ := e z₀ with hlam
  have hconst : ∀ z, z ∈ c.supp → e z = lam := by
    intro z hz
    have hreach : (secondOrderDefectGraph G).Reachable z₀ z :=
      ConnectedComponent.exact (((hmem z₀).mp hz₀).trans ((hmem z).mp hz).symm)
    obtain ⟨p⟩ := hreach
    -- walk induction inside `c`
    have key : ∀ {u v : V} (_ : (secondOrderDefectGraph G).Walk u v),
        u ∈ c.supp → e u = lam → e v = lam := by
      intro u v p
      induction p with
      | nil => intro _ h; exact h
      | cons hadj _ ih =>
        intro hu h
        rename_i u' v' w' _
        have hv' : v' ∈ c.supp := hDin u' v' hu hadj
        have := hlevel u' ((hSc_mem u').mpr hu) v' hadj
        rw [one_mul] at this
        exact ih hv' (this.trans h)
    exact key p hz₀ rfl
  -- λ bounds
  have hlam_even : Even (lam + m) := by
    have h1 := ha_even z₀
    have h2 : e z₀ = a z₀ ∨ e z₀ = - a z₀ := by
      simp only [he]
      rcases hs_sq z₀ hz₀ with h | h <;> rw [h] <;> simp
    rcases h2 with h | h
    · rw [hlam, h]; exact h1
    · rw [hlam, h]
      have : -a z₀ + (m : ℤ) = (a z₀ + m) - 2 * a z₀ := by ring
      rw [this]
      exact h1.sub (even_two_mul _)
  have hlam_abs : |lam| ≤ m := by
    have : |e z₀| = |a z₀| := by
      simp only [he, abs_mul]
      rcases hs_sq z₀ hz₀ with h | h <;> rw [h] <;> simp
    rw [hlam, this]; exact ha_bound z₀
  -- `A s = λ s` on `c`
  have hAs_c : ∀ z ∈ c.supp, a z = lam * s z := by
    intro z hz
    rw [ha_eq z hz, hconst z hz]
  -- Step 7: `w := a - λ s`
  set w : V → ℤ := fun x => a x - lam * s x with hw
  have hw_in : ∀ x, x ∈ c.supp → w x = 0 := by
    intro x hx
    simp only [hw]
    rw [hAs_c x hx]; ring
  have hw_out : ∀ x, x ∉ c.supp → w x = a x := by
    intro x hx
    simp only [hw]
    rw [hs_out x hx]; ring
  have hAw : ∀ x, ∑ y ∈ G.neighborFinset x, w y =
      (2 * ((q : ℤ) - 1) - lam * lam) * s x - lam * w x := by
    intro x
    simp only [hw]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hAA x]
    have : ∑ y ∈ G.neighborFinset x, s y = a x := rfl
    rw [this]
    ring
  have hDw : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, w y =
      -((q : ℤ) - 1) * w x := by
    intro x
    simp only [hw]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hDa x, hDs x]
    ring
  -- Step 8: alternation off `c` by the energy identity
  set Sout : Finset V := Finset.univ.filter
    (fun x => ¬ (secondOrderDefectGraph G).connectedComponentMk x = c) with hSout
  have hSout_mem : ∀ x, x ∈ Sout ↔ x ∉ c.supp := by
    intro x
    simp only [hSout, Finset.mem_filter, Finset.mem_univ, true_and]
    exact not_congr (hmem x).symm
  have hSout_closed : ∀ x ∈ Sout, ∀ y, (secondOrderDefectGraph G).Adj x y → y ∈ Sout := by
    intro x hx y hxy
    exact (hSout_mem y).mpr (hDout x y ((hSout_mem x).mp hx) hxy)
  have halt := eq_mul_of_adj_of_sum_neighborFinset_eq_mul (secondOrderDefectGraph G) Sout
    hSout_closed (k := q - 1) (fun x _ => hDcard x) w (-1) (by norm_num)
    (fun x _ => by rw [hDw x, hq1]; ring)
  -- assemble
  refine ⟨lam, w, hlam_even, hlam_abs, hAs_c, hw_in, hw_out, ?_, ?_, ?_⟩
  · intro x hx
    rw [hw_out x hx]
    exact ⟨ha_even x, ha_bound x⟩
  · intro x y hx hxy
    have := halt x ((hSout_mem x).mpr hx) y hxy
    rw [this]; ring
  · intro z hz
    rw [hAw z, hw_in z hz]; ring

/-- One-component consumer: if the defect graph is connected and bipartite,
then `λ² = 2(q-1)`; so this is impossible whenever `2(q-1)` is not a perfect
square (e.g. `q = 8`). -/
theorem binarySquare_regular_oneComponent_bipartite_lam_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hall : ∀ x, x ∈ c.supp)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    ∃ lam : ℤ, lam * lam = 2 * ((q : ℤ) - 1) := by
  have hc : c.supp.ncard = q * q := by
    have : c.supp = Set.univ := Set.eq_univ_of_forall hall
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, hcard]
  obtain ⟨lam, w, -, -, -, hw_in, -, -, -, hrow⟩ :=
    binarySquare_regular_bipartite_defectComponent_signed_residue
      G hfree hq hreg hcard c hc col hbip
  obtain ⟨z₀, hz₀⟩ := c.exists_rep
  have hz₀c : z₀ ∈ c.supp := hall z₀
  have hzero : ∑ y ∈ G.neighborFinset z₀, w y = 0 :=
    Finset.sum_eq_zero (fun y _ => hw_in y (hall y))
  have h := hrow z₀ hz₀c
  rw [hzero] at h
  have hs : bipartiteSignVector G c col z₀ = 1 ∨ bipartiteSignVector G c col z₀ = -1 := by
    have hz₀' : (secondOrderDefectGraph G).connectedComponentMk z₀ = c := hz₀
    unfold bipartiteSignVector
    rw [if_pos hz₀']
    cases col z₀ <;> simp
  refine ⟨lam, ?_⟩
  rcases hs with hs | hs <;> rw [hs] at h <;> linarith

/-- At `q = 8` (order 64), a connected bipartite defect graph is impossible:
`14` is not a perfect square. -/
theorem orderSixtyFour_regular_oneComponent_not_bipartite
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hall : ∀ x, x ∈ c.supp)
    (col : Fin 64 → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False := by
  obtain ⟨lam, hlam⟩ := binarySquare_regular_oneComponent_bipartite_lam_sq
    G hfree (q := 8) (by norm_num) hreg (by simp) c hall col hbip
  norm_num at hlam
  -- `lam * lam = 14` has no integer solution
  have h1 : lam ≤ 3 ∨ 4 ≤ lam := by omega
  have h2 : -3 ≤ lam ∨ lam ≤ -4 := by omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> nlinarith [hlam]

end

end Erdos85
