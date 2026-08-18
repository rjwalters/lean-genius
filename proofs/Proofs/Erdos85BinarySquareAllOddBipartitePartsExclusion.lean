import Proofs.Erdos85BinarySquareBipartiteDefectComponentSpectralResidue
import Proofs.Erdos85BinarySquareBipartiteDefectComponentStrataConsumers
import Proofs.Erdos85BinarySquareSizeTwoJointEigenvectorMuOneExclusion

/-!
# BIP-ODD: all defect parts odd and bipartite is impossible when `4 ∣ q`

Let `G` be a `q`-regular `C₄`-free graph on `q²` vertices whose defect
components `c_i` all have odd sizes `m_i` (`|c_i| = q m_i`) and are all
bipartite, with sign vectors `s_i = 1_{X_i} − 1_{Y_i}`.

By the signed-vector residue of each part, `A s_i = λ_i s_i` on `c_i` with
`λ_i` odd, and on every other part `c_j` the restriction of `A s_i` alternates
along defect edges and is odd, hence equals `L_{ji} s_j` for an odd integer
`L_{ji}` (the ratio to `s_j` is constant on the connected `c_j`).  Symmetry of
`A` gives the reciprocity `m_j L_{ji} = m_i L_{ij}`, and reading `A² s_i =
2(q−1) s_i` on `c_i` gives `2(q−1) = λ_i² + Σ_{j≠i} L_{ji} L_{ij}`.  Modulo `8`
every odd square is `1`, so `L_{ji}L_{ij} ≡ m_i m_j` and
`2(q−1) ≡ m_i Σ_j m_j = m_i q (mod 8)`.  For `4 ∣ q` the right side is `0` or `4`
while the left side is `6`: contradiction.

Together with the size-two exclusion, (A′) and (B) this closes the bipartite
half of the extension node uniformly for every binary `q ≥ 4`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If `w` alternates along defect edges leaving `c₁` and `s` alternates along
defect edges inside `c₁`, the product `w · s` is constant on `c₁`. -/
theorem mul_eq_on_component_of_alternating {V : Type*}
    (D : SimpleGraph V) (c₁ : D.ConnectedComponent) (w s : V → ℤ)
    (halt_w : ∀ x y, x ∈ c₁.supp → D.Adj x y → w y = -w x)
    (halt_s : ∀ x y, x ∈ c₁.supp → y ∈ c₁.supp → D.Adj x y → s y = -s x) :
    ∀ x y, x ∈ c₁.supp → y ∈ c₁.supp → w x * s x = w y * s y := by
  intro x y hx hy
  have hreach : D.Reachable x y :=
    ConnectedComponent.exact
      (((ConnectedComponent.mem_supp_iff c₁ x).mp hx).trans
        ((ConnectedComponent.mem_supp_iff c₁ y).mp hy).symm)
  have := reachable_induction_of_adj_closed D (fun u => u ∈ c₁.supp ∧ w u * s u = w x * s x)
    (fun u v huv hu => by
      have hv : v ∈ c₁.supp := by
        rw [ConnectedComponent.mem_supp_iff] at hu ⊢
        rw [← hu.1]
        exact (ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm
      refine ⟨hv, ?_⟩
      rw [halt_w u v hu.1 huv, halt_s u v hu.1 hv huv, neg_mul_neg, hu.2])
    hreach ⟨hx, rfl⟩
  exact this.2.symm

/-- Odd integers square to `1` in `ZMod 8`. -/
theorem zmod8_odd_mul_self {n : ℤ} (hn : Odd n) : ((n : ZMod 8) * (n : ZMod 8)) = 1 := by
  obtain ⟨k, hk⟩ := hn
  have h : ∀ x : ZMod 8, (2 * x + 1) * (2 * x + 1) = 1 := by decide
  rw [hk]
  push_cast
  exact h _

/-- Odd naturals square to `1` in `ZMod 8`. -/
theorem zmod8_odd_mul_self_nat {n : ℕ} (hn : Odd n) : ((n : ZMod 8) * (n : ZMod 8)) = 1 := by
  have := zmod8_odd_mul_self (n := (n : ℤ)) (by exact_mod_cast hn)
  push_cast at this
  exact this

set_option maxHeartbeats 800000 in
/-- **BIP-ODD (general form).**  If every defect part is bipartite and at least
one part has odd size, then `4 ∣ q` is impossible.  Only the odd base part `c₀`
needs odd size: the coupling coefficients `L j c₀` are odd because `w_{c₀}` is,
and reciprocity `m_j L_{j c₀} = m_{c₀} L_{c₀ j}` gives
`L_{j c₀} L_{c₀ j} ≡ m_{c₀} m_j (mod 8)` for EVERY `j`, whatever the parity of `m_j`. -/
theorem binarySquare_regular_allBipartiteParts_oddPart_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hq4 : 4 ∣ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent) (hodd₀ : Odd (m c₀))
    (col : (secondOrderDefectGraph G).ConnectedComponent → V → Bool)
    (hbip : ∀ c x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col c x ≠ col c y) :
    False := by
  -- the residue data of every part
  have hres := fun c => binarySquare_regular_bipartite_defectComponent_signed_residue
    G hfree hq hreg hcard c (hm c) (col c) (hbip c)
  choose lam w hlam_par hlam_abs hAs hw_in hw_out hw_par halt hrow using hres
  set s : (secondOrderDefectGraph G).ConnectedComponent → V → ℤ :=
    fun c => bipartiteSignVector G c (col c) with hs
  -- basic facts about the sign vectors
  have hmem : ∀ (c : (secondOrderDefectGraph G).ConnectedComponent) x,
      x ∈ c.supp ↔ (secondOrderDefectGraph G).connectedComponentMk x = c :=
    fun c x => ConnectedComponent.mem_supp_iff c x
  have hs_in : ∀ c x, x ∈ c.supp → s c x = 1 ∨ s c x = -1 := by
    intro c x hx
    simp only [hs, bipartiteSignVector]
    rw [if_pos ((hmem c x).mp hx)]
    cases col c x <;> simp
  have hs_out : ∀ c x, x ∉ c.supp → s c x = 0 := by
    intro c x hx
    simp only [hs, bipartiteSignVector]
    rw [if_neg (fun h => hx ((hmem c x).mpr h))]
  have hs_sq : ∀ c x, x ∈ c.supp → s c x * s c x = 1 := by
    intro c x hx
    rcases hs_in c x hx with h | h <;> rw [h] <;> norm_num
  have hs_alt : ∀ c x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → s c y = -s c x := by
    intro c x y hx hy hxy
    have hne := hbip c x y hx hy hxy
    simp only [hs, bipartiteSignVector]
    rw [if_pos ((hmem c x).mp hx), if_pos ((hmem c y).mp hy)]
    cases hcx : col c x <;> cases hcy : col c y <;> rw [hcx, hcy] at hne
    · exact absurd rfl hne
    · norm_num
    · norm_num
    · exact absurd rfl hne
  -- disjointness of parts
  have hdisj : ∀ (i j : (secondOrderDefectGraph G).ConnectedComponent), i ≠ j →
      ∀ x, x ∈ j.supp → x ∉ i.supp := by
    intro i j hij x hxj hxi
    exact hij (((hmem i x).mp hxi).symm.trans ((hmem j x).mp hxj))
  -- `A s_i = w_i + λ_i s_i` everywhere
  have hAs_all : ∀ i x, ∑ y ∈ G.neighborFinset x, s i y = w i x + lam i * s i x := by
    intro i x
    by_cases hx : x ∈ i.supp
    · rw [hAs i x hx, hw_in i x hx]; ring
    · rw [hw_out i x hx, hs_out i x hx]; ring
  -- representatives
  have hrep : ∀ c : (secondOrderDefectGraph G).ConnectedComponent, ∃ x, x ∈ c.supp := by
    intro c
    obtain ⟨x, hx⟩ := c.exists_rep
    exact ⟨x, (hmem c x).mpr hx⟩
  choose rep hrep using hrep
  -- the coupling coefficients `L j i` (coefficient of `s_j` in `A s_i`)
  set L : (secondOrderDefectGraph G).ConnectedComponent →
      (secondOrderDefectGraph G).ConnectedComponent → ℤ :=
    fun j i => w i (rep j) * s j (rep j) with hL
  -- on `c_j` (`j ≠ i`): `w_i = L j i · s_j`
  have hfac : ∀ i j, j ≠ i → ∀ x, x ∈ j.supp → w i x = L j i * s j x := by
    intro i j hji x hx
    have hconst := mul_eq_on_component_of_alternating (secondOrderDefectGraph G) j (w i) (s j)
      (fun u v hu huv => halt i u v (hdisj i j (Ne.symm hji) u hu) huv)
      (fun u v hu hv huv => hs_alt j u v hu hv huv) x (rep j) hx (hrep j)
    simp only [hL]
    rw [← hconst, mul_assoc, hs_sq j x hx, mul_one]
  -- oddness at the odd base part `c₀`
  have hlam_odd : Odd (lam c₀) := by
    obtain ⟨k, hk⟩ := hlam_par c₀
    obtain ⟨r, hr⟩ := hodd₀
    exact ⟨k - r - 1, by push_cast at hk; omega⟩
  have hL_odd : ∀ j, j ≠ c₀ → Odd (L j c₀) := by
    intro j hji
    have hw := (hw_par c₀ (rep j) (hdisj c₀ j (Ne.symm hji) _ (hrep j))).1
    have hwodd : Odd (w c₀ (rep j)) := by
      obtain ⟨k, hk⟩ := hw
      obtain ⟨r, hr⟩ := hodd₀
      exact ⟨k - r - 1, by push_cast at hk; omega⟩
    simp only [hL]
    rcases hs_in j (rep j) (hrep j) with h | h <;> rw [h]
    · simpa using hwodd
    · simpa using hwodd.neg
  -- component orders as finsets
  have hcardc : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      (Finset.univ.filter (fun x => (secondOrderDefectGraph G).connectedComponentMk x = c)).card
        = q * m c := by
    intro c
    have h1 : c.supp.ncard = c.supp.toFinset.card := Set.ncard_eq_toFinset_card' c.supp
    have h2 : c.supp.toFinset = Finset.univ.filter
        (fun x => (secondOrderDefectGraph G).connectedComponentMk x = c) := by
      ext x
      simp only [Set.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hmem c x
    rw [← h2, ← h1, hm c]
  -- reciprocity `m_j L_{ji} = m_i L_{ij}` (`j ≠ i`)
  have hrec : ∀ i j, j ≠ i → (m j : ℤ) * L j i = (m i : ℤ) * L i j := by
    intro i j hji
    -- `Σ_x (A s_i)(x) s_j(x) = Σ_x s_i(x) (A s_j)(x)`
    have hsym : ∑ x, (∑ y ∈ G.neighborFinset x, s i y) * s j x =
        ∑ x, s i x * (∑ y ∈ G.neighborFinset x, s j y) := by
      have h1 : ∑ x, (∑ y ∈ G.neighborFinset x, s i y) * s j x =
          ∑ x ∈ Finset.univ, ∑ y ∈ (G.neighborFinset x).filter (fun y => y ∈ Finset.univ),
            s i y * s j x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_mul]
        apply Finset.sum_congr
        · ext y; simp
        · intros; rfl
      have h2 : ∑ x, s i x * (∑ y ∈ G.neighborFinset x, s j y) =
          ∑ y ∈ Finset.univ, ∑ x ∈ (G.neighborFinset y).filter (fun x => x ∈ Finset.univ),
            s i y * s j x := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
        apply Finset.sum_congr
        · ext x; simp
        · intros; rfl
      rw [h1, h2]
      exact sum_sum_filter_neighborFinset_comm G Finset.univ Finset.univ (fun x y => s i y * s j x)
    -- evaluate both sides
    have hlhs : ∑ x, (∑ y ∈ G.neighborFinset x, s i y) * s j x = L j i * (q * m j : ℕ) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => (secondOrderDefectGraph G).connectedComponentMk x = j)]
      have hz : ∑ x ∈ Finset.univ.filter
          (fun x => ¬ (secondOrderDefectGraph G).connectedComponentMk x = j),
          (∑ y ∈ G.neighborFinset x, s i y) * s j x = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [hs_out j x (fun h => (Finset.mem_filter.mp hx).2 ((hmem j x).mp h)), mul_zero]
      rw [hz, add_zero]
      have hall : ∀ x ∈ Finset.univ.filter
          (fun x => (secondOrderDefectGraph G).connectedComponentMk x = j),
          (∑ y ∈ G.neighborFinset x, s i y) * s j x = L j i := by
        intro x hx
        have hxj : x ∈ j.supp := (hmem j x).mpr (Finset.mem_filter.mp hx).2
        rw [hAs_all i x, hs_out i x (hdisj i j (Ne.symm hji) x hxj), mul_zero, add_zero,
          hfac i j hji x hxj, mul_assoc, hs_sq j x hxj, mul_one]
      rw [Finset.sum_congr rfl hall, Finset.sum_const, hcardc j, nsmul_eq_mul, mul_comm]
    have hrhs : ∑ x, s i x * (∑ y ∈ G.neighborFinset x, s j y) = L i j * (q * m i : ℕ) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun x => (secondOrderDefectGraph G).connectedComponentMk x = i)]
      have hz : ∑ x ∈ Finset.univ.filter
          (fun x => ¬ (secondOrderDefectGraph G).connectedComponentMk x = i),
          s i x * (∑ y ∈ G.neighborFinset x, s j y) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [hs_out i x (fun h => (Finset.mem_filter.mp hx).2 ((hmem i x).mp h)), zero_mul]
      rw [hz, add_zero]
      have hall : ∀ x ∈ Finset.univ.filter
          (fun x => (secondOrderDefectGraph G).connectedComponentMk x = i),
          s i x * (∑ y ∈ G.neighborFinset x, s j y) = L i j := by
        intro x hx
        have hxi : x ∈ i.supp := (hmem i x).mpr (Finset.mem_filter.mp hx).2
        rw [hAs_all j x, hs_out j x (hdisj j i hji x hxi), mul_zero, add_zero,
          hfac j i (Ne.symm hji) x hxi, mul_comm, mul_assoc, hs_sq i x hxi, mul_one]
      rw [Finset.sum_congr rfl hall, Finset.sum_const, hcardc i, nsmul_eq_mul, mul_comm]
    rw [hlhs, hrhs] at hsym
    push_cast at hsym
    have hqpos : (q : ℤ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
    have : (q : ℤ) * ((m j : ℤ) * L j i) = (q : ℤ) * ((m i : ℤ) * L i j) := by linarith
    exact mul_left_cancel₀ hqpos this
  -- the odd base part `i := c₀` and a representative
  set i := c₀ with hi
  obtain ⟨x₀, hx₀⟩ := i.exists_rep
  have hx₀' : (secondOrderDefectGraph G).connectedComponentMk x₀ = i := hx₀
  have hx₀i : x₀ ∈ i.supp := (hmem i x₀).mpr hx₀'
  -- diagonal identity: `2(q−1) − λ_i² = Σ_{j ≠ i} L_{ji} L_{ij}`
  have hdiag : 2 * ((q : ℤ) - 1) - lam i * lam i =
      ∑ j ∈ Finset.univ.erase i, L j i * L i j := by
    have hrow_i := hrow i x₀ hx₀i
    -- split `Σ_{y ∈ N(x₀)} w_i y` by the component of `y`
    have hfib : ∑ y ∈ G.neighborFinset x₀, w i y =
        ∑ j : (secondOrderDefectGraph G).ConnectedComponent,
          ∑ y ∈ (G.neighborFinset x₀).filter
            (fun y => (secondOrderDefectGraph G).connectedComponentMk y = j), w i y :=
      (Finset.sum_fiberwise (G.neighborFinset x₀)
        (fun y => (secondOrderDefectGraph G).connectedComponentMk y) (w i)).symm
    have hterm : ∀ j : (secondOrderDefectGraph G).ConnectedComponent,
        ∑ y ∈ (G.neighborFinset x₀).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = j), w i y =
        if j = i then 0 else L j i * L i j * s i x₀ := by
      intro j
      by_cases hji : j = i
      · rw [if_pos hji]
        apply Finset.sum_eq_zero
        intro y hy
        exact hw_in i y ((hmem i y).mpr (hji ▸ (Finset.mem_filter.mp hy).2))
      · rw [if_neg hji]
        have h1 : ∀ y ∈ (G.neighborFinset x₀).filter
            (fun y => (secondOrderDefectGraph G).connectedComponentMk y = j),
            w i y = L j i * s j y := fun y hy =>
          hfac i j hji y ((hmem j y).mpr (Finset.mem_filter.mp hy).2)
        rw [Finset.sum_congr rfl h1, ← Finset.mul_sum]
        -- `Σ_{y ∈ N(x₀) ∩ c_j} s_j y = (A s_j)(x₀) = w_j x₀ = L i j · s_i x₀`
        have h2 : ∑ y ∈ (G.neighborFinset x₀).filter
            (fun y => (secondOrderDefectGraph G).connectedComponentMk y = j), s j y =
            ∑ y ∈ G.neighborFinset x₀, s j y := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : (secondOrderDefectGraph G).connectedComponentMk y = j
          · simp [hy]
          · rw [if_neg hy, hs_out j y (fun h => hy ((hmem j y).mp h))]
        rw [h2, hAs_all j x₀, hs_out j x₀ (hdisj j i hji x₀ hx₀i), mul_zero, add_zero,
          hfac j i (Ne.symm hji) x₀ hx₀i]
        ring
    rw [hfib, Finset.sum_congr rfl (fun j _ => hterm j)] at hrow_i
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add] at hrow_i
    have hfilt : Finset.univ.filter (fun j => ¬ j = i) = Finset.univ.erase i := by
      ext j; simp [Finset.mem_erase, ne_comm]
    rw [hfilt, ← Finset.sum_mul] at hrow_i
    have hsne : s i x₀ ≠ 0 := by
      intro h; have := hs_sq i x₀ hx₀i; rw [h] at this; norm_num at this
    exact (mul_right_cancel₀ hsne hrow_i).symm
  -- `Σ_j m_j = q`
  have hsum_m : ∑ j : (secondOrderDefectGraph G).ConnectedComponent, m j = q := by
    have hsum := sum_connectedComponent_supp_ncard (secondOrderDefectGraph G)
    have htot : (∑ c : (secondOrderDefectGraph G).ConnectedComponent, c.supp.ncard) = q * q := by
      simpa [Nat.card_eq_fintype_card, hcard] using hsum
    simp_rw [hm] at htot
    rw [← Finset.mul_sum] at htot
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) htot
  -- pass to `ZMod 8`
  have hcast := congrArg (Int.cast : ℤ → ZMod 8) hdiag
  push_cast at hcast
  -- each term `L j i * L i j ≡ m_i m_j`, and `λ_i² ≡ m_i²`
  have hterm8 : ∀ j ∈ Finset.univ.erase i,
      ((L j i : ZMod 8) * (L i j : ZMod 8)) = (m i : ZMod 8) * (m j : ZMod 8) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    have hr := congrArg (Int.cast : ℤ → ZMod 8) (hrec i j hji)
    push_cast at hr
    have hmi8' := zmod8_odd_mul_self_nat hodd₀
    have hLji := zmod8_odd_mul_self (hL_odd j hji)
    linear_combination (-(L j i : ZMod 8) * (m i : ZMod 8)) * hr
      + ((m i : ZMod 8) * (m j : ZMod 8)) * hLji - ((L j i : ZMod 8) * (L i j : ZMod 8)) * hmi8'
  have hlam8 := zmod8_odd_mul_self hlam_odd
  have hmi8 := zmod8_odd_mul_self_nat hodd₀
  rw [Finset.sum_congr rfl hterm8, ← Finset.mul_sum] at hcast
  -- `Σ_{j ≠ i} m_j = q − m_i`
  have hsum_erase : ∑ j ∈ Finset.univ.erase i, (m j : ZMod 8) =
      (q : ZMod 8) - (m i : ZMod 8) := by
    have h := Finset.add_sum_erase Finset.univ (fun j => (m j : ZMod 8)) (Finset.mem_univ i)
    have hq' : ∑ j : (secondOrderDefectGraph G).ConnectedComponent, (m j : ZMod 8) =
        (q : ZMod 8) := by
      rw [← hsum_m]; push_cast; rfl
    rw [hq'] at h
    linear_combination h
  rw [hsum_erase] at hcast
  -- final arithmetic in `ZMod 8`
  obtain ⟨k, hk⟩ := hq4
  have hq8 : (q : ZMod 8) = 4 * (k : ZMod 8) := by rw [hk]; push_cast; ring
  rw [hq8] at hcast
  -- `2(4k − 1) − 1 = m (4k − m)` with `m² = 1` ⇒ `8k − 2 = 4km` in ZMod 8: impossible
  rw [hlam8] at hcast
  have hfinal : ∀ (kk mm : ZMod 8), mm * mm = 1 →
      2 * (4 * kk - 1) - 1 ≠ mm * (4 * kk - mm) := by decide
  exact hfinal (k : ZMod 8) (m i : ZMod 8) hmi8 hcast

/-- **BIP-ODD (all-odd form).**  All defect parts odd-sized and bipartite is
impossible when `4 ∣ q`. -/
theorem binarySquare_regular_allOddBipartiteParts_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hq4 : 4 ∣ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c) (hodd : ∀ c, Odd (m c))
    (col : (secondOrderDefectGraph G).ConnectedComponent → V → Bool)
    (hbip : ∀ c x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col c x ≠ col c y) :
    False := by
  have hV : Nonempty V := by
    rw [← Fintype.card_pos_iff, hcard]; positivity
  obtain ⟨x₀⟩ := hV
  exact binarySquare_regular_allBipartiteParts_oddPart_false G hfree hq hq4 hreg hcard m hm
    ((secondOrderDefectGraph G).connectedComponentMk x₀) (hodd _) col hbip

/-- Existential form of `binarySquare_regular_allOddBipartiteParts_false`. -/
theorem binarySquare_regular_allOddBipartiteParts_false'
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hq4 : 4 ∣ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hparts : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      (∃ m, Odd m ∧ c.supp.ncard = q * m) ∧
      ∃ col : V → Bool, ∀ x y, x ∈ c.supp → y ∈ c.supp →
        (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False := by
  have h1 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ∃ m, Odd m ∧ c.supp.ncard = q * m := fun c => (hparts c).1
  have h2 : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ∃ col : V → Bool, ∀ x y, x ∈ c.supp → y ∈ c.supp →
        (secondOrderDefectGraph G).Adj x y → col x ≠ col y := fun c => (hparts c).2
  choose m hm using h1
  choose col hbip using h2
  exact binarySquare_regular_allOddBipartiteParts_false G hfree hq hq4 hreg hcard m
    (fun c => (hm c).2) (fun c => (hm c).1) col hbip

/-- **CAPSTONE (uniform for `4 ∣ q`).**  No defect component of a `q`-regular
`C₄`-free graph on `q²` vertices is bipartite — no stratum hypothesis at all.
Proof: if some odd-sized part is bipartite, then every part is bipartite
(`..._odd_forces_others_bipartite`) and the general BIP-ODD kills it; otherwise
the bipartite part `c` is even-sized and every other part is non-bipartite or
even-sized, and the even-`q` mod-4 theorem kills it. -/
theorem binarySquare_regular_no_bipartite_defectComponent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hq4 : 4 ∣ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (col : V → Bool)
    (hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      (secondOrderDefectGraph G).Adj x y → col x ≠ col y) :
    False := by
  classical
  have hqeven : Even q := by
    obtain ⟨k, hk⟩ := hq4
    exact ⟨2 * k, by omega⟩
  -- Case A: some odd-sized part is bipartite
  by_cases hA : ∃ c₁ : (secondOrderDefectGraph G).ConnectedComponent, Odd (m c₁) ∧
      ∃ col₁ : V → Bool, ∀ x y, x ∈ c₁.supp → y ∈ c₁.supp →
        (secondOrderDefectGraph G).Adj x y → col₁ x ≠ col₁ y
  · obtain ⟨c₁, hodd₁, col₁, hbip₁⟩ := hA
    -- every part is bipartite
    have hall : ∀ c₂ : (secondOrderDefectGraph G).ConnectedComponent,
        ∃ col₂ : V → Bool, ∀ x y, x ∈ c₂.supp → y ∈ c₂.supp →
          (secondOrderDefectGraph G).Adj x y → col₂ x ≠ col₂ y := by
      intro c₂
      by_cases h : c₂ = c₁
      · subst h; exact ⟨col₁, hbip₁⟩
      · exact binarySquare_regular_bipartite_defectComponent_odd_forces_others_bipartite
          G hfree hq hreg hcard c₁ (hm c₁) hodd₁ col₁ hbip₁ c₂ h
    choose cols hcols using hall
    exact binarySquare_regular_allBipartiteParts_oddPart_false G hfree hq hq4 hreg hcard m hm
      c₁ hodd₁ cols hcols
  · -- Case B: no odd-sized part is bipartite, so `c` is even and every other
    -- part is non-bipartite or even
    push Not at hA
    have hmeven : Even (m c) := by
      by_contra hne
      obtain ⟨x, y, hx, hy, hxy, heq⟩ := hA c (Nat.not_even_iff_odd.mp hne) col
      exact hbip x y hx hy hxy heq
    apply binarySquare_regular_bipartite_evenPart_false_of_others_even_or_not_bipartite
      G hfree hq hqeven hreg hcard c (hm c) hmeven col hbip
    intro c₁ _
    by_cases hb : ∃ col₁ : V → Bool, ∀ x y, x ∈ c₁.supp → y ∈ c₁.supp →
        (secondOrderDefectGraph G).Adj x y → col₁ x ≠ col₁ y
    · obtain ⟨col₁, hbip₁⟩ := hb
      right
      refine ⟨m c₁, ?_, hm c₁⟩
      by_contra hne
      obtain ⟨x, y, hx, hy, hxy, heq⟩ := hA c₁ (Nat.not_even_iff_odd.mp hne) col₁
      exact hbip₁ x y hx hy hxy heq
    · left
      intro col₁ hbip₁
      exact hb ⟨col₁, hbip₁⟩

end

end Erdos85
