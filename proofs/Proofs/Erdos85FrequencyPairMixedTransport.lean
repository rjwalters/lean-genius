import Proofs.Erdos85FrequencyPairMixed
import Proofs.Erdos85FrequencyPairGraphBlocks
import Proofs.Erdos85FrequencyPairTransport
import Proofs.Erdos85EqualCycleLabeling
import Proofs.Erdos85ZeroRowDifference

/-!
# Mixed-length transport: the frequency-pair bridge without equal cycles

This file transports the mixed-length frequency-pair bridge to the actual
graph, with **no common-length hypothesis**:

* `exists_mixed_cycle_labeling` extracts, unconditionally, a cyclic
  `ZMod c.supp.ncard` parametrization of every defect component;
* the transported defect matrix is `mixedDefectMatrix` for the length
  function `ℓ c = c.supp.ncard`;
* commutation, the even second-order matrix equation, and symmetry
  transport to the labeled adjacency matrix on the sigma space;
* diagonal blocks of components of odd length are translation invariant
  (orientation dichotomy plus vanishing of reverse-oriented diagonal
  blocks), which is required only on the `p`-divisible components;
* the graph-facing mixed trace identity: `trace T` is twice the prime
  Fourier transform of the fibered anchor counts of the `p`-divisible
  components.

Together with the square identity this supplies the operator inputs of
the square/nonsquare dichotomy for every odd prime `p`, whether or not
the defect components share a common length.  The remaining open input on
this route is the mixed-length analogue of the diagonal-anchor parity
combinatorics.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

section MixedTransport

variable {K : Type*} [Field K]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {ℓ : C → ℕ} [∀ c, NeZero (ℓ c)] {p : ℕ}

/-- Total labeling map of a mixed-length cycle system. -/
def mixedCycleLabeling (u : ∀ c : C, ZMod (ℓ c) → V) :
    (Σ c : C, ZMod (ℓ c)) → V := fun x ↦ u x.1 x.2

/-- The adjacency matrix of `G` in mixed labeled cycle coordinates. -/
def mixedLabeledAdjMatrix (K : Type*) [Field K] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : ∀ c : C, ZMod (ℓ c) → V) :
    Matrix (Σ c : C, ZMod (ℓ c)) (Σ c : C, ZMod (ℓ c)) K :=
  (G.adjMatrix K).submatrix (mixedCycleLabeling u) (mixedCycleLabeling u)

@[simp] theorem mixedLabeledAdjMatrix_apply (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : ∀ c : C, ZMod (ℓ c) → V)
    (x y : Σ c : C, ZMod (ℓ c)) :
    mixedLabeledAdjMatrix K G u x y =
      G.adjMatrix K (u x.1 x.2) (u y.1 y.2) := rfl

/-- Total bijectivity from per-cycle injectivity, separation, and
covering. -/
theorem mixedCycleLabeling_bijective {u : ∀ c : C, ZMod (ℓ c) → V}
    (hu : ∀ c, Function.Injective (u c))
    (hsep : ∀ {c e : C}, c ≠ e → ∀ x y, u c x ≠ u e y)
    (hcover : ∀ v : V, ∃ c x, u c x = v) :
    Function.Bijective (mixedCycleLabeling u) := by
  constructor
  · rintro ⟨c, x⟩ ⟨e, y⟩ h
    by_cases hce : c = e
    · subst hce
      exact congrArg (Sigma.mk c) (hu c h)
    · exact absurd h (hsep hce x y)
  · intro v
    obtain ⟨c, x, hcx⟩ := hcover v
    exact ⟨⟨c, x⟩, hcx⟩

/-- The transported defect matrix of a mixed cycle system is the standard
mixed defect operator. -/
theorem submatrix_defect_eq_mixedDefectMatrix
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hinj : Function.Injective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)}) :
    (D.adjMatrix K).submatrix (mixedCycleLabeling u)
        (mixedCycleLabeling u) = mixedDefectMatrix K ℓ := by
  ext ⟨c, x⟩ ⟨e, y⟩
  rw [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply,
    mixedDefectMatrix]
  simp only [mixedCycleLabeling]
  by_cases hce : c = e
  · subst hce
    rw [Matrix.blockDiagonal'_apply_eq, Matrix.circulant_apply,
      defectKernel]
    have hadj : D.Adj (u c x) (u c y) ↔ (y = x - 1 ∨ y = x + 1) := by
      rw [← SimpleGraph.mem_neighborFinset, huD c x]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · exact Or.inl (sigma_mk_injective (β := fun c ↦ ZMod (ℓ c))
            (hinj (a₁ := ⟨c, y⟩) (a₂ := ⟨c, x - 1⟩) h))
        · exact Or.inr (sigma_mk_injective (β := fun c ↦ ZMod (ℓ c))
            (hinj (a₁ := ⟨c, y⟩) (a₂ := ⟨c, x + 1⟩) h))
      · rintro (rfl | rfl)
        · exact Or.inl rfl
        · exact Or.inr rfl
    have h1 : (x - y = 1) = (y = x - 1) := by
      apply propext
      exact ⟨fun h ↦ by linear_combination -h,
        fun h ↦ by linear_combination -h⟩
    have h2 : (x - y = -1) = (y = x + 1) := by
      apply propext
      exact ⟨fun h ↦ by linear_combination -h,
        fun h ↦ by linear_combination -h⟩
    have hxor : ¬(y = x - 1 ∧ y = x + 1) := by
      rintro ⟨rfl, habs⟩
      exact zmod_sub_one_ne_add_one_of_three_le (hℓ3 c) x habs
    simp only [h1, h2]
    by_cases hy1 : y = x - 1
    · rw [if_pos (hadj.mpr (Or.inl hy1)), if_pos hy1,
        if_neg fun hy2 ↦ hxor ⟨hy1, hy2⟩, add_zero]
    · by_cases hy2 : y = x + 1
      · rw [if_pos (hadj.mpr (Or.inr hy2)), if_neg hy1, if_pos hy2,
          zero_add]
      · rw [if_neg fun h ↦ (hadj.mp h).elim hy1 hy2, if_neg hy1,
          if_neg hy2, add_zero]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hce]
    have hnadj : ¬ D.Adj (u c x) (u e y) := by
      intro h
      rw [← SimpleGraph.mem_neighborFinset, huD c x] at h
      simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hce (congrArg Sigma.fst
          (hinj (a₁ := ⟨e, y⟩) (a₂ := ⟨c, x - 1⟩) h)).symm
      · exact hce (congrArg Sigma.fst
          (hinj (a₁ := ⟨e, y⟩) (a₂ := ⟨c, x + 1⟩) h)).symm
    rw [if_neg hnadj]

/-- Commutation transports to the mixed labeled model. -/
theorem mixedLabeledAdjMatrix_comm_mixedDefectMatrix
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ) :
    mixedLabeledAdjMatrix K G u * mixedDefectMatrix K ℓ =
      mixedDefectMatrix K ℓ * mixedLabeledAdjMatrix K G u := by
  have hcommK : G.adjMatrix K * D.adjMatrix K =
      D.adjMatrix K * G.adjMatrix K := by
    have h := congrArg (fun A ↦ A.map (Int.castRingHom K)) hcommZ
    simpa only [Matrix.map_mul, adjMatrix_map_intCast] using h
  rw [← submatrix_defect_eq_mixedDefectMatrix D u hℓ3 hbij.injective huD,
    mixedLabeledAdjMatrix, ← Equiv.coe_ofBijective _ hbij,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hcommK]

/-- The even second-order matrix equation transports to the mixed labeled
model. -/
theorem mixedLabeledAdjMatrix_sq
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ) :
    mixedLabeledAdjMatrix K G u * mixedLabeledAdjMatrix K G u =
      ((d : K) - 1) • (1 : Matrix (Σ c : C, ZMod (ℓ c))
          (Σ c : C, ZMod (ℓ c)) K) +
        (Matrix.of fun _ _ : Σ c : C, ZMod (ℓ c) ↦ (1 : K)) -
          mixedDefectMatrix K ℓ := by
  have hsqK : G.adjMatrix K * G.adjMatrix K =
      ((d : K) - 1) • (1 : Matrix V V K) +
        (Matrix.of fun _ _ : V ↦ (1 : K)) - D.adjMatrix K := by
    have h := congrArg (fun A ↦ A.map (Int.castRingHom K)) hsqZ
    simp only [Matrix.map_mul, adjMatrix_map_intCast] at h
    rw [h]
    ext a b
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      FriendshipTheoremOQ01.onesMatrix, SimpleGraph.adjMatrix_apply,
      smul_eq_mul]
    split_ifs <;> simp only [eq_intCast] <;> push_cast <;> ring
  rw [← submatrix_defect_eq_mixedDefectMatrix D u hℓ3 hbij.injective huD,
    mixedLabeledAdjMatrix, ← Equiv.coe_ofBijective _ hbij,
    Matrix.submatrix_mul_equiv, hsqK]
  ext z w
  simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul,
    Equiv.coe_ofBijective]
  congr 2
  simp [hbij.injective.eq_iff]

/-- Symmetry transports to the mixed labeled model. -/
theorem mixedLabeledAdjMatrix_isSymm (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : ∀ c : C, ZMod (ℓ c) → V) :
    (mixedLabeledAdjMatrix K G u).IsSymm := by
  rw [Matrix.IsSymm, mixedLabeledAdjMatrix, Matrix.transpose_submatrix,
    SimpleGraph.transpose_adjMatrix]

/-- Diagonal blocks of odd-length components are translation invariant.
Only the `p`-divisible components are ever needed by the trace. -/
theorem mixedLabeledAdjMatrix_diag_translationInvariant
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hodd : ∀ c : C, p ∣ ℓ c → Odd (ℓ c)) :
    ∀ c : C, p ∣ ℓ c → ∀ x y : ZMod (ℓ c),
      mixedLabeledAdjMatrix K G u ⟨c, x + 1⟩ ⟨c, y + 1⟩ =
        mixedLabeledAdjMatrix K G u ⟨c, x⟩ ⟨c, y⟩ := by
  intro c hdvd x y
  have huc : Function.Injective (u c) := by
    intro a b hab
    exact sigma_mk_injective (β := fun c ↦ ZMod (ℓ c))
      (hbij.injective (a₁ := ⟨c, a⟩) (a₂ := ⟨c, b⟩) hab)
  have hiff := graph_equalOddCycle_diagBlock_adj_shift_iff (hℓ3 c)
    (hodd c hdvd) G D (u c) huc hcommZ (huD c) x y
  simp only [mixedLabeledAdjMatrix_apply, SimpleGraph.adjMatrix_apply,
    hiff]

/-- **Mixed projected anchor count.**  The number of anchored same-cycle
adjacencies at displacement residue `s`, collected over the `p`-divisible
components. -/
def mixedProjectedAnchor (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (p : ℕ) (s : ZMod p) : ℕ :=
  ∑ c ∈ Finset.univ.filter fun c : C ↦ p ∣ ℓ c,
    ((graphCycleBlockZeroSupport G (u c) (u c)).filter
      (fun t : ZMod (ℓ c) ↦ ((t.val : ℕ) : ZMod p) = s)).card

/-- The fibered Fourier weight of the mixed labeled model is the mixed
projected anchor count. -/
theorem sum_mixedLabeled_diag_eq_mixedProjectedAnchor
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (s : ZMod p) :
    (∑ c ∈ Finset.univ.filter fun c : C ↦ p ∣ ℓ c,
      ∑ t ∈ Finset.univ.filter
        (fun t : ZMod (ℓ c) ↦ ((t.val : ℕ) : ZMod p) = s),
        mixedLabeledAdjMatrix K G u ⟨c, 0⟩ ⟨c, t⟩) =
      ((mixedProjectedAnchor G u p s : ℕ) : K) := by
  rw [mixedProjectedAnchor, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro c _
  have hmem : ∀ t : ZMod (ℓ c),
      G.Adj (u c 0) (u c t) ↔
        t ∈ graphCycleBlockZeroSupport G (u c) (u c) := by
    intro t
    rw [graphCycleBlockZeroSupport, mem_zeroRowSupport_iff]
    simp [SimpleGraph.adjMatrix_apply]
  have hset : Finset.univ.filter
      (fun t : ZMod (ℓ c) ↦ G.Adj (u c 0) (u c t)) =
      graphCycleBlockZeroSupport G (u c) (u c) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmem t
  simp only [mixedLabeledAdjMatrix_apply, SimpleGraph.adjMatrix_apply]
  rw [Finset.sum_boole]
  congr 1
  rw [Finset.filter_comm, hset]

/-- **Graph-facing mixed square identity**
`T² = (d - 1 - (ζ + ζ⁻¹)) • id`, with no common-length hypothesis. -/
theorem graph_mixed_defectEigenspaceRestrict_sq
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    {d : ℕ}
    (hsqZ : G.adjMatrix ℤ * G.adjMatrix ℤ =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V - D.adjMatrix ℤ)
    (hcomm : mixedLabeledAdjMatrix K G u * mixedDefectMatrix K ℓ =
      mixedDefectMatrix K ℓ * mixedLabeledAdjMatrix K G u)
    {ζ : K} (hζp : ζ ^ p = 1) (hp0 : p ≠ 0) (hζ1 : ζ ≠ 1) :
    defectEigenspaceRestrict (mixedLabeledAdjMatrix K G u) hcomm
        (ζ + ζ⁻¹) *
      defectEigenspaceRestrict (mixedLabeledAdjMatrix K G u) hcomm
        (ζ + ζ⁻¹) =
      ((d : K) - 1 - (ζ + ζ⁻¹)) • LinearMap.id := by
  haveI : NeZero p := ⟨hp0⟩
  exact defectEigenspaceRestrict_sq hcomm
    (mixedLabeledAdjMatrix_sq G D u hℓ3 hbij huD hsqZ)
    ones_mul_mixedDefectMatrix
    (zeta_add_inv_ne_two (r := p) hζp hζ1)

/-- **Graph-facing mixed trace identity.**  The trace of the restricted
adjacency operator on the mixed `μ = ζ + ζ⁻¹` frequency space is twice
the prime Fourier transform of the mixed projected anchor counts —
without any common-length hypothesis. -/
theorem graph_mixed_trace_eq_two_mul_projected_anchor_fourier
    [CharZero K] [NeZero p]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (u : ∀ c : C, ZMod (ℓ c) → V) (hℓ3 : ∀ c, 3 ≤ ℓ c)
    (hbij : Function.Bijective (mixedCycleLabeling u))
    (huD : ∀ c x, D.neighborFinset (u c x) = {u c (x - 1), u c (x + 1)})
    (hcommZ : G.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * G.adjMatrix ℤ)
    (hodd : ∀ c : C, p ∣ ℓ c → Odd (ℓ c))
    (hcomm : mixedLabeledAdjMatrix K G u * mixedDefectMatrix K ℓ =
      mixedDefectMatrix K ℓ * mixedLabeledAdjMatrix K G u)
    (hp : p.Prime) (hp2 : 2 < p) {ζ : K} (hζ : IsPrimitiveRoot ζ p) :
    LinearMap.trace K
        (defectEigenspace (mixedDefectMatrix K ℓ) (ζ + ζ⁻¹))
        (defectEigenspaceRestrict (mixedLabeledAdjMatrix K G u) hcomm
          (ζ + ζ⁻¹)) =
      2 * ∑ s : ZMod p,
        ((mixedProjectedAnchor G u p s : ℕ) : K) * ζ ^ s.val := by
  rw [trace_defectEigenspaceRestrict_mixed hcomm
    (mixedLabeledAdjMatrix_diag_translationInvariant G D u hℓ3 hbij huD
      hcommZ hodd)
    (mixedLabeledAdjMatrix_isSymm G u) hp hp2 hζ]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [sum_mixedLabeled_diag_eq_mixedProjectedAnchor]

end MixedTransport

/-! ## Unconditional labeling extraction -/

section MixedLabeling

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Unconditional mixed cycle labeling.**  Every defect component of
the extremal graph carries a cyclic parametrization by its own size —
with no equal-length hypothesis. -/
theorem exists_mixed_cycle_labeling
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (hdeven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    ∃ u : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        ZMod c.supp.ncard → V,
      (∀ c, Function.Injective (u c)) ∧
      (∀ c, Set.range (u c) = c.supp) ∧
      (∀ c x, (secondOrderDefectGraph G).neighborFinset (u c x) =
        {u c (x - 1), u c (x + 1)}) ∧
      (∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        3 ≤ c.supp.ncard) := by
  classical
  have hdeg : ∀ z, (secondOrderDefectGraph G).degree z = 2 := fun z ↦
    secondOrderDefectGraph_degree_eq_two G hfree hd hdeven hmin hcard z
  have hchoice : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ∃ u0 : ZMod c.supp.ncard → V, (Function.Injective u0 ∧
        Set.range u0 = c.supp ∧
        ∀ z, (secondOrderDefectGraph G).neighborFinset (u0 z) =
          {u0 (z - 1), u0 (z + 1)}) ∧ 3 ≤ c.supp.ncard := by
    intro c
    obtain ⟨x, hx⟩ := c.nonempty_supp
    obtain ⟨q, hqcycle, hqverts⟩ :=
      exists_secondOrderDefect_cycle_spanning_component
        G hfree hd hdeven hmin hcard c hx
    have hqlen : q.length = c.supp.ncard := by
      calc
        q.length = Nat.card q.toSubgraph.verts :=
          (isCycle_card_verts_eq_length hqcycle).symm
        _ = q.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
        _ = c.supp.ncard := congrArg Set.ncard hqverts
    rw [← hqlen]
    obtain ⟨u0, h1, h2, h3'⟩ :=
      exists_zmod_cycleParam_neighborFinset hqcycle hdeg
    exact ⟨u0, ⟨h1, h2.trans hqverts, h3'⟩, hqcycle.three_le_length⟩
  choose u hu using hchoice
  exact ⟨u, fun c ↦ (hu c).1.1, fun c ↦ (hu c).1.2.1,
    fun c ↦ (hu c).1.2.2, fun c ↦ (hu c).2⟩

end MixedLabeling

end

end Erdos85
